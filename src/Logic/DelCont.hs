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
import Data.Maybe

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


-- | The effect signature of the logic monad: free monad on empty and <|>
--
data Free m f a = Pure a | Op (f (Compose m (Free m f)) a)

{-
deriving instance Functor (f (Compose m (Free m f))) => Functor (Free m f)

instance Functor (f (Compose m (Free m f))) => Applicative (Free m f) where
  pure = Pure
  (<*>) = ap

instance Functor (f (Compose m (Free m f))) => Monad (Free m f) where
  return = pure
  Pure a >>= f = f a
  Op x >>= f = _ 
-}

data LogicOp m a where
  FailureOp   :: LogicOp m a
  ChooseOp  :: m a -> m a -> LogicOp m a
  OnceOp    :: m a -> LogicOp m a
  CleanupOp :: m a -> IO () -> LogicOp m a

deriving instance Functor m => Functor (LogicOp m)

type Comp m = Free m LogicOp

pattern Failure :: Comp m a
pattern Failure = Op FailureOp

pattern Choose :: m (Comp m a) -> m (Comp m a) -> Comp m a
pattern Choose x y = Op (ChooseOp (Compose x) (Compose y))

pattern Once :: m (Comp m a) -> Comp m a
pattern Once x = Op (OnceOp (Compose x))

pattern Cleanup :: m (Comp m a) -> IO () -> Comp m a
pattern Cleanup x y = Op (CleanupOp (Compose x) y)

{-# COMPLETE Pure, Failure, Choose, Once, Cleanup #-}

compAll :: MonadIO m => Comp m a -> m [a]
compAll (Pure x)     = pure [x]
compAll Failure        = pure []
compAll (Choose m n) = (++) <$> (compAll =<< m) <*> (compAll =<< n)
compAll (Once m)     = fmap maybeToList . comp1 =<< m
compAll (Cleanup m m_cleanup) = (compAll =<< m) <* liftIO m_cleanup

compSplit :: MonadIO m => Comp m a -> m (View (WithCleanup a IO) (Comp m a))
compSplit (Pure x) = pure (x :&&: pure () :&: Failure)
compSplit Failure    = pure Empty
compSplit (Choose m n) = do
  mb <- compSplit =<< m
  case mb of
    vc :&: rest -> pure (vc :&: Choose (pure rest) n)
    Empty -> compSplit =<< n
compSplit (Once m) = do
  x <- compSplit =<< m
  case x of
    Empty -> pure Empty
    vc :&: _ -> pure (vc :&: Failure)
compSplit (Cleanup m m_cleanup) = do
  x <- compSplit =<< m
  case x of
    Empty -> liftIO m_cleanup *> pure Empty
    v :&&: c :&: rest -> pure (v :&&: (c *> m_cleanup) :&: rest)

comp1 :: MonadIO m => Comp m a -> m (Maybe a)
comp1 (Pure x)     = pure (Just x)
comp1 Failure        = pure Nothing
comp1 (Choose m n) = do
  mb <- comp1 =<< m
  case mb of
    Just _  -> pure mb
    Nothing -> comp1 =<< n
comp1 (Once m) = comp1 =<< m
comp1 (Cleanup m m_cleanup) = (comp1 =<< m) <* liftIO m_cleanup


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

{-
  once (MkLogic m) = controlLogic $ \ tag f -> Once (f (m tag))

  ifte t th el = MkLogic $ \tag -> do
        c <- runLogic t
        mb <- compSplit c
        case mb of
          Empty -> unLogic el tag
          v :&&: c :&: rest -> unLogic (cleanup (th v) (liftDupableIO c)) tag -- TODO rest
-}

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
            handle (Once x)       = Once (run (liftDupableIO x))
            handle (Cleanup x y)  = Cleanup (run (liftDupableIO x)) y
        in run (Pure <$> m)


reflectLogic' :: IO (Comp IO r) -> Logic r
reflectLogic' m = reflectLogic =<< liftDupableIO m

reflectLogic :: Comp IO a -> Logic a
reflectLogic (Pure x)              = pure x
reflectLogic Failure               = empty
reflectLogic (Choose x y)          = (reflectLogic' x) <|> (reflectLogic' y)
reflectLogic (Once m)              = once (reflectLogic' m)
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
