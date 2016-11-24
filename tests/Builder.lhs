> {-# LANGUAGE TemplateHaskell #-}
> {-# OPTIONS_GHC -fno-warn-orphans #-}

> module Main where
> import Control.Monad
> import Data.Bits
> import Data.BitString.Builder (Builder)
> import Data.Bool
> import Data.ByteString (ByteString)
> import Data.String
> import System.Exit
> import Test.QuickCheck

> import qualified Data.BitString.Builder as Builder
> import qualified Data.ByteString as ByteString

> instance Arbitrary Builder where
>   arbitrary = fmap Builder.fromList arbitrary
>   shrink = fmap Builder.fromList . shrink . Builder.toList

> instance Arbitrary ByteString where
>   arbitrary = fmap ByteString.pack arbitrary
>   shrink = fmap ByteString.pack . shrink . ByteString.unpack

> prop_equality :: Builder -> Builder -> Bool
> prop_equality xs ys = ((xs == ys) == (Builder.toList xs == Builder.toList ys))

TODO: compare

> prop_show :: Builder -> Bool
> prop_show xs = (filter (/= ' ') (show xs) == show (fmap (bool '0' '1') $ Builder.toList xs))

> prop_read_show :: Builder -> Bool
> prop_read_show xs = (read (show xs) == xs)

> prop_read_bad_string_1 = null (reads "''" :: [(Builder, String)])
> prop_read_bad_string_2 = null (reads "\"" :: [(Builder, String)])
> prop_read_bad_string_3 = null (reads "\"01x\"" :: [(Builder, String)])
> prop_read_bad_string_4 = null (reads "\"012\"" :: [(Builder, String)])

> prop_from_string :: Builder -> Bool
> prop_from_string xs = (fromString (read (show xs)) == xs)

> prop_mempty :: Bool
> prop_mempty = (Builder.toList mempty == [])

TODO: mappend
TODO: mconcat

TODO: Bits instance

> prop_length :: Builder -> Bool
> prop_length xs = (Builder.length xs == length (Builder.toList xs))

> prop_list_conversion :: [Bool] -> Bool
> prop_list_conversion xs = (xs == Builder.toList (Builder.fromList xs))

> prop_bytestring_import :: ByteString -> Bool
> prop_bytestring_import xs = (Builder.toList (Builder.fromByteString xs) == [ testBit x i | x <- ByteString.unpack xs, i <- [0..7] ])

> prop_bytestring_export :: Builder -> Bool
> prop_bytestring_export xs = (take len (Builder.toList xs ++ repeat False) == [ testBit x i | x <- ByteString.unpack (Builder.toByteString xs), i <- [0..7] ])
>  where len = (Builder.length xs + 7) `quot` 8 * 8

TODO: integer conversions
TODO: resize operations

  ============================================================================

> return []
> main = $forAllProperties (quickCheckWithResult args) >>= flip unless exitFailure
>  where args = stdArgs { maxSuccess = 1000 }
