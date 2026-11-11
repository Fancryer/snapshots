{-# LANGUAGE LambdaCase #-}
module Resume (
  ResumeInfo(..),
  toNatural,
  fromNatural
) where
import GHC.Natural (Natural)

data ResumeInfo = NoResume | OneResume | MultipleResume Int deriving (Show, Eq)

instance Semigroup ResumeInfo where x <> y = fromNatural (toNatural x + toNatural y)

instance Monoid ResumeInfo where mempty = NoResume

toNatural :: ResumeInfo -> Natural
toNatural = \case NoResume -> 0; OneResume -> 1; MultipleResume n -> fromIntegral n

fromNatural :: Natural -> ResumeInfo
fromNatural = \case 0 -> NoResume; 1 -> OneResume; n -> MultipleResume $ fromIntegral n