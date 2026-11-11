{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module Sexp (Sexp (..))
where
import GHC.Generics (Generic(Rep, from), M1 (M1), (:+:) (L1, R1), (:*:) ((:*:)), K1 (K1), Constructor (conName), C1, D1, S1, U1 (U1))
import qualified Data.Text as T
import Data.Text (Text)
import Data.Scientific (Scientific)

class Sexp a where
  sexp :: a -> String
  default sexp :: (Generic a, GSexp (Rep a)) => a -> String
  sexp = gsexp . from

class GSexp f where gsexp :: f a -> String

instance GSexp f => GSexp (D1 c f) where gsexp (M1 x) = gsexp x
instance (GSexp a, GSexp b) => GSexp (a :*: b) where
  gsexp (a :*: b) =
    case (gsexp a, gsexp b) of
      ("", "") -> ""
      ("", b') -> b'
      (a', "") -> a'
      (a', b') -> a' <> " " <> b'

instance (GSexp a, GSexp b) => GSexp (a :+: b) where
  gsexp (L1 x) = gsexp x; gsexp (R1 x) = gsexp x

instance (Constructor c, GSexp f) => GSexp (C1 c f) where
  gsexp m1@(M1 x) =
    case gsexp x of
      "" -> concat ["(", conName m1, ")"]
      s -> concat ["(", conName m1, " ", s, ")"]

instance GSexp f => GSexp (S1 c f) where gsexp (M1 x) = gsexp x

instance GSexp U1 where gsexp U1 = ""
instance Sexp a => GSexp (K1 i a) where gsexp (K1 x) = sexp x

instance Sexp a => Sexp (Maybe a) where sexp (Just x) = sexp x; sexp Nothing = ""
instance {-# OVERLAPPABLE #-} Sexp a => Sexp [a] where sexp x = concat ["[", unwords $ map sexp x, "]"]
instance {-# OVERLAPPABLE #-} Sexp String where sexp = show
instance Sexp Bool
instance Sexp Int where sexp = show
instance Sexp Integer where sexp = show
instance Sexp Scientific where sexp = show
instance Sexp Text where sexp = show . T.unpack
instance Sexp Char where sexp = show
instance (Sexp a, Sexp b) => Sexp (a, b) where
  sexp (a, b) = concat ["(", sexp a, ",", sexp b, ")"]