{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}

module Logic.DelCont where

import qualified GHC.Prim as Prim (newPromptTag#, prompt#, control0#, RealWorld, State#, PromptTag#)
import qualified GHC.Types as Types (IO(IO))

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Primitive
import Data.Functor.Compose
import Data.Coerce

import Logic.Class
import Unaligned.Base


-- These are just IO wrappers around the delimited continuations primops, to
-- save noise elsewhere.

newPromptTag :: (Prim.PromptTag# a -> IO r) -> IO r
newPromptTag k = Types.IO $ \ st ->
    case Prim.newPromptTag# st of
      (# st, tag #) -> unIO (k tag) st

prompt :: Prim.PromptTag# a -> IO a -> IO a
prompt tag = coerce (Prim.prompt# tag)

control0 :: forall a b . Prim.PromptTag# a -> ((IO b -> IO a) -> IO a) -> IO b
control0 tag f = Types.IO (Prim.control0# tag (coerce f))

unIO :: IO a -> Prim.State# Prim.RealWorld -> (# Prim.State# Prim.RealWorld , a #)
unIO (Types.IO io) = io


data Free f a = Pure a | Op (f (Free f a))

-- | The effect signature of the logic monad: free monad on 'empty', '<|>' and
-- 'cleanup'.
data LogicOp a where
  FailureOp :: LogicOp a
  ChooseOp  :: a -> a -> LogicOp a
  CleanupOp :: a -> IO () -> LogicOp a
  deriving Functor

type Comp m = Free (Compose LogicOp m)

pattern Failure :: Comp m a
pattern Failure = Op (Compose FailureOp)

pattern Choose :: m (Comp m a) -> m (Comp m a) -> Comp m a
pattern Choose x y = Op (Compose (ChooseOp x y))

pattern Cleanup :: m (Comp m a) -> IO () -> Comp m a
pattern Cleanup x y = Op (Compose (CleanupOp x y))

{-# COMPLETE Pure, Failure, Choose, Cleanup #-}


comp1 :: MonadIO m => Comp m a -> m (Maybe a)
comp1 (Pure x)     = pure (Just x)
comp1 Failure        = pure Nothing
comp1 (Choose m n) = do
  mb <- comp1 =<< m
  case mb of
    Just _  -> pure mb
    Nothing -> comp1 =<< n
comp1 (Cleanup m m_cleanup) = (comp1 =<< m) <* liftIO m_cleanup

compAll :: MonadIO m => Comp m a -> m [a]
compAll (Pure x)     = pure [x]
compAll Failure      = pure []
compAll (Choose m n) = (++) <$> (compAll =<< m) <*> (compAll =<< n)
compAll (Cleanup m m_cleanup) = (compAll =<< m) <* liftIO m_cleanup

compSplit :: MonadIO m => Comp m a -> m (View (WithCleanup a IO) (Comp m a))
compSplit (Pure x) = pure (x :&&: pure () :&: Failure)
compSplit Failure    = pure Empty
compSplit (Choose m n) = do
  mb <- compSplit =<< m
  case mb of
    vc :&: rest -> pure (vc :&: Choose (pure rest) n)
    Empty -> compSplit =<< n
compSplit (Cleanup m m_cleanup) = do
  x <- compSplit =<< m
  case x of
    Empty -> liftIO m_cleanup *> pure Empty
    v :&&: c :&: rest -> pure (v :&&: (c *> m_cleanup) :&: rest)


type Tag r = Prim.PromptTag# (Comp IO r)

-- | The monad is just a reader (to pass around the tag) over IO.  We don't use
-- 'ReaderT' because 'PromptTag#' is unlifted.
--
newtype Logic a = MkLogic { unLogic :: forall r . Tag r -> IO a }
  deriving (Functor)

instance Applicative Logic where
  pure x = MkLogic $ \ _ -> pure x
  mf <*> ma = MkLogic $ \ tag -> unLogic mf tag <*> unLogic ma tag

instance Monad Logic where
  ma >>= f = MkLogic $ \ tag -> unLogic ma tag >>= \ a -> unLogic (f a) tag

-- | This instance is dangerous: any effects executed may be duplicated when we
-- backtrack.
liftDupableIO :: IO a -> Logic a
liftDupableIO io = MkLogic $ \ _ -> io

instance Alternative Logic where
  empty = controlLogic $ \ _ __ -> Failure

  MkLogic m <|> MkLogic n = controlLogic $ \ tag f ->
      Choose (f (m tag))
             (f (n tag))

controlLogic :: (forall r . Tag r -> (IO a -> IO (Comp IO r)) -> Comp IO r) -> Logic a
controlLogic c = MkLogic $ \tag -> control0 tag $ pure . c tag

instance MonadPlus Logic

instance MonadLogic Logic where
  pureWithCleanup (a :&&: m_clean) = cleanup (pure a) m_clean

  cleanup (MkLogic x) (MkLogic y) = controlLogic $ \ tag f -> Cleanup (f (x tag)) (y tag)

  msplit m = liftDupableIO $ do
      c <- runLogic m
      mb <- compSplit c
      case mb of
        Empty -> pure Empty
        v :&&: c :&: rest -> pure (v :&&: liftDupableIO c :&: reflectLogic rest)

instance PrimMonad Logic where
  type PrimState Logic = RealWorld
  primitive f = MkLogic $ \ _ -> primitive f


runLogic :: forall r . Logic r -> IO (Comp IO r)
runLogic m =
    newPromptTag @(Comp IO r) $ \ tag ->

        let run :: Logic (Comp IO r) -> IO (Comp IO r)
            run (MkLogic m) = prompt tag (m tag) >>= pure . handle

            handle :: Comp IO r -> Comp IO r
            handle (Pure a)       = Pure a
            handle Failure        = Failure
            handle (Choose x y)   = Choose (run (liftDupableIO x)) (run (liftDupableIO y))
            handle (Cleanup x y)  = Cleanup (run (liftDupableIO x)) y
        in run (Pure <$> m)


reflectLogic' :: IO (Comp IO r) -> Logic r
reflectLogic' m = reflectLogic =<< liftDupableIO m

reflectLogic :: Comp IO a -> Logic a
reflectLogic (Pure x)              = pure x
reflectLogic Failure               = empty
reflectLogic (Choose x y)          = (reflectLogic' x) <|> (reflectLogic' y)
reflectLogic (Cleanup m m_cleanup) = cleanup (reflectLogic' m) (liftDupableIO m_cleanup)


observeAllT :: Logic r -> IO [r]
observeAllT = compAll <=< runLogic



test :: Logic [Int]
test = do
  x <- pure 1 <|> pure 2
  liftDupableIO $ print x
  y <- pure 3 <|> pure 4
  liftDupableIO $ print y
  when (x == 1) empty
  pure [x, y]

go1 :: Logic r -> IO (Maybe r)
go1 = comp1 <=< runLogic

eg :: IO [[Int]]
eg = observeAllT test
