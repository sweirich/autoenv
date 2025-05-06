module Data.LocalName where

newtype LocalName = LocalName {name :: String}
  deriving (Eq, Ord)

instance Show LocalName where
  show (LocalName x) = x

internalName :: LocalName
internalName = LocalName "_internal"
