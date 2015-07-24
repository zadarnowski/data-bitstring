> module Data.BitString.Tiny (
>   BitString, length
> ) where

> import Data.Bits
> import Data.BitString.Element
> import Data.String
> import Prelude hiding (length)

> data BitString = BS !Int !Element  deriving (Data, Eq)

> length :: BitString -> Int
> length (BS s _) = s

> empty :: BitString
> empty = BS 0 0

> toBitString :: Integral a => Int -> a -> BitString
> toBitString s x
>   | (0 <= s <= elementBitSize) = BS s (fromIntegral x .&. (bit s - 1))
>   | otherwise = overflow

> overflow :: a
> overflow = error "Data.BitString.Tiny: overflow"

