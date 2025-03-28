{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module DeBrujin where
import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.Functor.Identity (Identity)
import Data.List (findIndex)

newtype DBIndex = DBIndex Int
 deriving (Eq, Show)

newtype DeBrujin_T a m x = DeBrujin_T (StateT (Int, [a]) m x)
 deriving (Functor, Applicative)

bind :: Monad m => a -> DeBrujin_T a m DBIndex
bind x = DeBrujin_T $ do
  (ix, _) <- get
  modify (\(i, ds) -> (i+1, x:ds))
  return $ DBIndex ix

reference :: (Monad m, Eq a) => a -> DeBrujin_T a m (Maybe DBIndex)
reference x = DeBrujin_T $ do
  (_, ds) <- get
  return $ DBIndex <$> findIndex (== x) ds


lookup :: Monad m => DBIndex -> DeBrujin_T a m a
lookup (DBIndex i) = DeBrujin_T $ do
  (_, ds) <- get
  return (ds !! (length ds - i - 1))


runDeBrujin :: Monad m => DeBrujin_T a m x -> m x
runDeBrujin (DeBrujin_T s) = fst <$> runStateT s (0, [])

type DeBrujin a x = DeBrujin_T a Identity x
