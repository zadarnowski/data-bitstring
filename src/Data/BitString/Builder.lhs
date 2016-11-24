> {-# LANGUAGE BangPatterns, CPP, MagicHash, RankNTypes, UnboxedTuples #-}
> {-# OPTIONS_GHC -funbox-strict-fields #-}

#include "MachDeps.h"

> module Data.BitString.Builder (
>   Builder,
>   length,
>   fromList, toList,
>   fromByteString, toByteString,
>   bits, nat,
>   resize, zeroExtend, signExtend,
> ) where

> import Data.Bool
> import Data.ByteString (ByteString)
> import Data.Char
> import Data.String
> import Foreign.ForeignPtr
> import Foreign.Ptr
> import Prelude hiding (length)
> import System.IO.Unsafe

> import GHC.ForeignPtr
> import GHC.Prim
> import GHC.Ptr
> import GHC.ST
> import GHC.Types

> import qualified Data.ByteString.Internal as ByteString


  Data Types
  ==========

  The only data type exported by this library is 'Builder'. In a builder of the form @B m q n ps@,
  @q@ contains the most-significant @m@ bits of the bit string, while the remaining bits are stored
  in the list of arrays @ps@, in the order of decreasting significance, so that the least significant
  bit is stored in the last element of @ps@. @n@ gives the total number of words in all the arrays from
  @ps@ put together. Each element in @ps@ is an array of @2^i@ words, and must be strictly larger than
  the preceding array in the string. It follows that the size of each array can be determined by
  traversing the bit pattern of @n@: for each bit set in @n@, @ps@ will contain an array of size @2^i@,
  where @i@ is the bit's location in @n@.

  For performance, all lists are represented by coinductive (infinite) structures padded to infinity
  with a sequence of empty arrays, since their actual shape is always determined uniquely by other
  builder parameters, and such padding prevents GHC from performing redundant runtime checks for empty
  lists.

  Invariants:

    0 <= m < wordBits
    q `shiftR` m = 0
    n == sum (map pageSize ps)
    forall i . (0 <= i) -> (pageSize (rs!i) == 2^i * (fromIntegral $ fromEnum $ testBit i n))

  (assumign the obvious implementation of 'map' and '!' for our coinductive list structures,
  and an omniscient implementation of 'sum' capable of summing up an infinite list of zeroes.)

> -- | The type of bit builders, with fast O(n×log(n)) construction.

> data Builder = B# Int# Word# Int# Pages

  Additional coninductive type representing an infinite list of builders, used to optimise
  implementation of 'mconcat':

> data Builders = BS !Builder Builders

  An implementation of coinductive page lists and individual pages:

> data Pages    = PS Page Pages
> data Page     = P# ByteArray#


  Instances
  =========

> instance Eq Builder where
>   (B# m1# q1# n1# ps1) == (B# m2# q2# n2# ps2) = case (m1# ==# m2#) `andI#` (q1# `eqWord#` q2#) `andI#` (n1# ==# n2#) of
>                                                    0# -> False
>                                                    _  -> case n1# of
>                                                            0# -> True
>                                                            _  -> loop n1# (firstPageSize# n1#) ps1 ps2
>    where
>     loop :: Int# -> Int# -> Pages -> Pages -> Bool
>     loop n# c# (PS (P# a1#) ps1') (PS (P# a2#) ps2') = loop' 0#
>      where
>       loop' :: Int# -> Bool
>       loop' i# = case eqWord# (indexWordArray# a1# i#) (indexWordArray# a2# i#) of
>                    0# -> False
>                    _  -> let ni# = i# +# 1#
>                           in case ni# ==# c# of
>                                0# -> loop' ni#
>                                _  -> let nn# = n# -# c#
>                                       in case nn# of
>                                            0# -> True
>                                            _  -> loop nn# (nextPageSize# nn# c#) ps1' ps2'


> instance Ord Builder where
>   compare = compareBuilders

> instance Show Builder where
>   showsPrec _ = shows . seps . fmap (bool '0' '1') . toList
>    where seps s = let (g, xs) = splitAt 8 s
>                    in g ++ if null xs then [] else ' ' : seps xs

> instance Read Builder where
>   readsPrec _ s = [ (fromString ds, xs) | (ds, xs) <- reads s, all (\c -> c == '0' || c == '1' || c == ',' || c == '_' || isSpace c) ds ]

> instance IsString Builder where
>   fromString = fromList . fmap fromDigit . filter (\c -> not (c == ',' || c == '_' || isSpace c))
>    where fromDigit '0' = False
>          fromDigit '1' = True
>          fromDigit  c  = error ("Data.BitString.Builder: invalid binary digit: " ++ show c)

> instance Monoid Builder where
>   mempty = emptyBuilder
>   mappend b1@(B# m1# _ n1# _) b2@(B# m2# _ n2# _) = concatBuilders m# n# (BS b2 (BS b1 emptyBuilders))
>    where
>     (# nt#, m# #) = quotRemInt# (m1# +# m2#) WORD_SIZE_IN_BITS#
>     n# = n1# +# n2# +# nt#
>   mconcat []  = mempty
>   mconcat [b] = b
>   mconcat bsl = loop 0# 0# emptyBuilders bsl
>    where
>     loop mm# nn# bs (b@(B# m# _ n# _) : bsl') = loop (mm# +# m#) (nn# +# n#) (BS b bs) bsl'
>     loop mm# nn# bs [] = let (# n#, m# #) = quotRemInt# mm# WORD_SIZE_IN_BITS# in concatBuilders m# (nn# +# n#) bs


  Trivial operations
  ==================

> -- | Returns the length of a builder, in bits.

> length :: Builder -> Int
> length (B# m# _ n# _) = I# (m# +# n# *# WORD_SIZE_IN_BITS#)
> {-# INLINE length #-}

  A builder of length 0.

> emptyBuilder :: Builder
> emptyBuilder = B# 0# (int2Word# 0#) 0# emptyPages

  An infinite list of empty builder pages, used to terminate the list of pages in every builder,
  avoiding the need for redundant nil-list checks during list traversal.

> emptyPages :: Pages
> emptyPages = withNewByteArray# 0# $ \ _ st# -> (# st#, \a# -> PS (P# a#) emptyPages #)

  An infinite list of empty builder pages, used to terminate the list of pages in every builder,
  avoiding the need for redundant nil-list checks during list traversal.

> emptyBuilders :: Builders
> emptyBuilders = BS emptyBuilder emptyBuilders


  List conversions
  ================

> -- | Lazily converts a builder into a list of boolean values.

> toList :: Builder -> [Bool]
> toList (B# m0# q0# n0# ps0) = pagesToList n0# ps0 (wordToList m0# q0# [])
>  where
>
>   pagesToList :: Int# -> Pages -> [Bool] -> [Bool]
>   pagesToList n# ps rs =
>     case n# of
>       0# -> rs
>       _  -> pagesToList' n# (firstPageSize# n#) ps rs
>
>   pagesToList' :: Int# -> Int# -> Pages -> [Bool] -> [Bool]
>   pagesToList' n# c# (PS (P# a#) ps') rs =
>     case nn# of
>       0# -> nrs
>       _  -> pagesToList' nn# (nextPageSize# nn# c#) ps' nrs
>    where
>     nn# = n# -# c#
>     nrs = pageToList 0# c# a# rs
>
>   pageToList :: Int# -> Int# -> ByteArray# -> [Bool] -> [Bool]
>   pageToList i# s# a# rs =
>     wordToList WORD_SIZE_IN_BITS# (indexWordArray# a# i#) nrs
>    where
>     ni# = i# +# 1#
>     nrs = case ni# ==# s# of
>             0# -> pageToList ni# s# a# rs
>             _  -> rs
>
>   wordToList :: Int# -> Word# -> [Bool] -> [Bool]
>   wordToList m# q# rs =
>     case m# of
>       0# -> rs
>       _  -> let !x = case andI# (word2Int# q#) 1# of
>                        0# -> False
>                        _  -> True
>              in x : wordToList (m# -# 1#) (uncheckedShiftRL# q# 1#) rs

> -- | @fromList xs@ constructs a builder from a list of boolean values @xs@,
> --   consuming the list lazily. The operation will perform
> --   @n/2 * log(n)@ word copies, where
> --   @n == ceiling(length(xs) / bitSize (0::Word)@.
> fromList :: [Bool] -> Builder
> fromList = loop 0# (int2Word# 0#) 0# emptyPages
>  where
>
>   loop :: Int# -> Word# -> Int# -> Pages -> [Bool] -> Builder
>   loop m# q# n# ps xs = case xs of
>                           (x:xs') -> let !(I# x#) = fromEnum x
>                                          nq# = or# q# (uncheckedShiftL# (int2Word# x#) m#)
>                                          nm# = m# +# 1#
>                                       in case nm# of
>                                            WORD_SIZE_IN_BITS# -> loop 0# (int2Word# 0#) (n# +# 1#) (appendWord# nq# n# ps) xs'
>                                            _ -> loop nm# nq# n# ps xs'
>                           [] -> B# m# q# n# ps

  Append a single word to a list of pages:

> appendWord# :: Word# -> Int# -> Pages -> Pages
> appendWord# q# n# ps0 = withNewByteArray# (uncheckedIShiftL# SIZEOF_HSWORD# (word2Int# (ctz# (not# (int2Word# n#))))) (makeNewPage# 0# 1# ps0)
>  where
>   makeNewPage# :: Int# -> Int# -> Pages -> MutableByteArray# s -> State# s -> (# State# s, ByteArray# -> Pages #)
>   makeNewPage# i# c# ps ma# st0# =
>     case andI# n# c# of
>       0# -> case writeWordArray# ma# i# q# st0# of st1# -> (# st1#, \a# -> PS (P# a#) ps #)
>       _  -> let bi# = i# *# SIZEOF_HSWORD#
>                 bc# = c# *# SIZEOF_HSWORD#
>                 ni# = i# +# c#
>                 nc# = uncheckedIShiftL# c# 1#
>                 !(PS (P# a#) ps') = ps
>              in case copyByteArray# a# 0# ma# bi# bc# st0# of st1# -> makeNewPage# ni# nc# ps' ma# st1#


  Bytestring converstions
  =======================

> -- | Constructs a builder from a byte string, interpreted in little-endian byte order.

> fromByteString :: ByteString -> Builder
> fromByteString bs = unsafeDupablePerformIO $ withForeignPtr fp $ \ptr -> return (loadFromBytes (plusPtr ptr off) len)
>  where (fp, off, len) = ByteString.toForeignPtr bs
> {-# INLINE fromByteString #-}

  Constructs a bit string out from a raw sequence of bytes, using fast bulk array copies.

> loadFromBytes :: Ptr a -> Int -> Builder
> loadFromBytes (Ptr src#) (I# len#) = case len# <# SIZEOF_HSWORD# of
>                                        0# -> let (# n#, bm# #) = quotRemInt# len# SIZEOF_HSWORD#
>                                               in loadPages# n# bm#
>                                        _  -> let m# = len# *# 8#
>                                               in B# m# (loadTail# m# src# 0# (int2Word# 0#)) 0# emptyPages
>  where
>
>   loadPages# :: Int# -> Int# -> Builder
>   loadPages# n# bm# = loop src# n# (lastPageSize# n#) emptyPages
>    where
>     loop :: Addr# -> Int# -> Int# -> Pages -> Builder
>     loop a# r# c# ps = let bc# = c# *# SIZEOF_HSWORD#
>                            nr# = r# -# c#
>                            na# = plusAddr# a# bc#
>                            nps = withNewByteArray# bc# $ \ ma# st0# -> case copyAddrToWordArrayLE# a# ma# 0# c# st0# of
>                                                                          st1# -> (# st1#, \aa# -> PS (P# aa#) ps #)
>                         in case nr# of
>                              0# -> let m# = bm# *# 8#
>                                     in B# m# (loadTail# m# na# 0# (int2Word# 0#)) n# nps
>                              _  -> loop na# nr# (previousPageSize# nr# c#) nps
>
>   loadTail# :: Int# -> Addr# -> Int# -> Word# -> Word#
>   loadTail# m# a# i# q# = case i# <# m# of
>                             0# -> q#
>                             _  -> loadTail# m# (plusAddr# a# 1#) (i# +# 8#) (or# q# (uncheckedShiftL# (indexWord8OffAddr# a# 0#) i#))

> -- | Converts a builder into a bytestring, using little-endian byte order and
> --   padding the bit string with zeros to a full byte size.

  The size of the array allocated for the byte string. For efficiency, we
  always include space for a full tail word, even if the tail word is empty,
  since it's unlikely to increase memory footprint, as memory allocators tend
  to round sizes of large objects up to nearest power of two anyway.

  Note that the he 'unsafeCoerce#' in the construction of the 'ForeignPtrContents'
  of the final bytestring is here to thaw a frozen 'ByteArray#' back into
  'MutableByteArray# RealWorld#', which, while ugly, is always safe.

> toByteString :: Builder -> ByteString
> toByteString (B# mm# qq# nn# ps) =
>   withNewPinnedByteArray# ((nn# +# 1#) *# SIZEOF_HSWORD#) $ \ma# st0# -> case writeWordArray# ma# nn# (littleEndian# qq#) st0# of
>                                                                            st1# -> writePages# ma# st1#
>  where
>
>   writePages# :: MutableByteArray# s -> State# s -> (# State# s, ByteArray# -> ByteString #)
>   writePages# ma# st0# =
>     case nn# of
>       0# -> (# st0#, makeByteString# #)
>       _  -> writePages## ma# nn# (firstPageSize# nn#) ps st0#
>
>   writePages## :: MutableByteArray# s -> Int# -> Int# -> Pages -> State# s -> (# State# s, ByteArray# -> ByteString #)
>   writePages## ma# n# c# (PS (P# a#) ps') st0# = let o# = n# -# c#
>                                                   in case copyWordArrayLE# a# 0# ma# o# c# st0# of
>                                                        st1# -> case o# of
>                                                                  0# -> (# st1#, makeByteString# #)
>                                                                  _  -> writePages## ma# o# (nextPageSize# o# c#) ps' st1#
>
>   makeByteString# :: ByteArray# -> ByteString
>   makeByteString# a# = ByteString.fromForeignPtr fp 0 bs
>    where
>     fp = ForeignPtr (byteArrayContents# a#) (PlainPtr (unsafeCoerce# a#))
>     bs = I# ((nn# *# SIZEOF_HSWORD#) +# uncheckedIShiftRA# (mm# +# 7#) 3#)


  Singleton Builders
  ==================

> -- | TODO...

> bits :: Num a => Int -> a -> Builder
> bits = error "TODO"
> {-# INLINE bits #-}

> -- | TODO...

> nat :: Integral a => Builder -> a
> nat = error "TODO"
> {-# INLINE nat #-}


  Size manipulation
  =================

> -- | @resize q n b@ resizes the builder @b@ to exactly @n@ bits in length;
> --   if @n > length b@, all newly-inserted bit positions will be set to @q@.

> resize :: Bool -> Int -> Builder -> Builder
> resize = error "TODO"

> -- | @zeroExtend n b@ resizes the builder @b@ to exactly @n@ bits in length;
> --   if @n > length b@, all newly-inserted bit positions will be set to @0@.

> zeroExtend :: Int -> Builder -> Builder
> zeroExtend = error "TODO"

> -- | @signExtend n b@ resizes the builder @b@ to exactly @n@ bits in length;
> --   if @n > length b@, all newly-inserted bit positions will be set to
> --   the value of @testBit b (n - 1)@.

> signExtend :: Int -> Builder -> Builder
> signExtend = error "TODO"

  Truncates a builder to @n@ bits:

> -- truncate :: Int -> Builder -> Builder
> -- truncate = error "TODO"



  Builder comparison
  ==================

> compareBuilders = error "TODO"


  Builder concatenation
  =====================

> concatBuilders = error "TODO"


  Truncation

> {-


  'Show' Instance
  ===============

> instance Show Builder where
>   showsPrec _ (B 0#  _ 0#  _) = showString "[bs| |]"
>   showsPrec _ (B m# q# n# ps) = showString "[bs| " . insertGrouping 72 "\n     " (insertGrouping 8 " " (showPages# n# ps (showTail# m# q# "")) "") . showString " |]"

> showPages# :: Int# -> Pages -> ShowS
> showPages# n# = foldl (.) id . map showWord# . unpackPages# n#

> showWord# :: Word -> ShowS
> showWord# (W# q#) = showTail# WORD_SIZE_IN_BITS# q#

> showTail# :: Int# -> Word# -> ShowS
> showTail# m# q# = case m# of
>                     0# -> id
>                     _  -> showHex (I# (andI# (word2Int# q#) 1#)) . showTail# (m# -# 1#) (uncheckedShiftRL# q# 1#)

> unpackPages# :: Int# -> Pages -> [Word]
> unpackPages# = loop []
>  where
>
>   loop :: [Word] -> Int# -> Pages -> [Word]
>   loop rs n# ps =
>     case n# of
>       0# -> rs
>       _  -> loop' rs n# (firstPageSize n#) ps
>
>   loop' :: [Word] -> Int# -> Int# -> Pages -> [Word]
>   loop' rs n# c# (PS (P a#) ps') = loop'' rs c# a# (n# -# c#) c# ps'
>
>   loop'' :: [Word] -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> [Word]
>   loop'' rs s# a# n# c# ps =
>     case s# of
>       0# -> loop''' rs n# c# ps
>       _  -> let i# = s# -# 1# in loop'' (W# (indexWordArray# a# i#) : rs) i# a# n# c# ps
>
>   loop''' :: [Word] -> Int# -> Int# -> Pages -> [Word]
>   loop''' rs n# c# ps =
>     case n# of
>       0# -> rs
>       _  -> loop' rs n# (nextPageSize n# c#) ps


  'Monoid' Instance
  =================

> instance Monoid Builder where
>   mempty = emptyBuilder
>   mappend b1@(B m1# _ n1# _) b2@(B m2# _ n2# _) = concatBuilders m# n# (BS b2 (BS b1 emptyBuilders))
>    where
>     (# nt#, m# #) = quotRemInt# (m1# +# m2#) WORD_SIZE_IN_BITS#
>     n# = n1# +# n2# +# nt#
>   mconcat []  = mempty
>   mconcat [b] = b
>   mconcat bsl = loop 0# 0# emptyBuilders bsl
>    where
>     loop mm# nn# bs (b@(B m# _ n# _) : bsl') = loop (mm# +# m#) (nn# +# n#) (BS b bs) bsl'
>     loop mm# nn# bs [] = let (# n#, m# #) = quotRemInt# mm# WORD_SIZE_IN_BITS# in concatBuilders m# (nn# +# n#) bs


  Singleton builders
  ==================


  Bytestring Conversion
  =====================

  Concatenation
  =============

  Concatenate a list of builders 'bs' into a single builder with 'nn' words and 'mm' trailing bits, given that:

  * '0 <= mm < WORD_SIZE_IN_BITS',
  * '0 <= nn', and
  * total number of bits in 'bs0' is 'mm + nn * WORD_SIZE_IN_BITS'.

> concatBuilders :: Int# -> Int# -> Builders -> Builder
> concatBuilders mm# nn# bs0 = makeTail bs0
>  where

    Start by collecting the most significant 'mm' bits of the resulting builder, where:

>   makeTail :: Builders -> Builder
>   makeTail (BS (B m# q# n# ps) bs') =
>     case rm# of
>       0# -> B mm# q# nn# (makePagesFromPiBi nn# n# ps bs')
>       _  -> case rm# ># 0# of
>               0# -> let nrm# = negateInt# rm#
>                         nrw# = WORD_SIZE_IN_BITS# -# nrm#
>                         nq#  = uncheckedShiftRL# q# nrm#
>                         nu#  = uncheckedShiftL# q# nrw#
>                      in B mm# nq# nn# (makePagesFromUPiB nn# (firstPageSize nn#) nrm# nrw# nu# n# ps bs')
>               _  -> makeTailFromP' (uncheckedShiftL# q# rm#) rm# n# ps bs'
>    where
>     rm# = mm# -# m#

    Collect the remaining most significant bits from the builder's pages, with:

    * 'rq' is the partially-constructed tail word, with all bits collected so far already in place,
    * 'rm' is the number of tail bits remaining to be collected,
    * 'n'  is the number of elements remaining in the page list 'ps'

    Invariants:
    * '0 < rm <= mm'
    * '0 <= n'

>   makeTailFromP' :: Word# -> Int# -> Int# -> Pages -> Builders -> Builder
>   makeTailFromP' rq# rm# n# ps bs =
>     case n# of
>       0# -> makeTailFromB' rq# rm# bs
>       _  -> makeTailFromP'' rq# rm# n# (firstPageSize n#) ps bs

    Invariants:
    * '0 < rm <= mm'
    * '0 < c <= n'

>   makeTailFromP'' :: Word# -> Int# -> Int# -> Int# -> Pages -> Builders -> Builder
>   makeTailFromP'' rq# rm# n# c# (PS (P a#) ps') bs =
>     B mm# (or# rq# (uncheckedShiftRL# q# m#)) nn# (makePagesFromUAPB nn# (firstPageSize nn#) m# w# u# s# a# (n# -# c#) c# ps' bs)
>    where
>     s# = c# -# 1#
>     q# = indexWordArray# a# s#
>     u# = uncheckedShiftL# q# rm#
>     m# = WORD_SIZE_IN_BITS# -# rm#
>     w# = rm#

    Collect the remaining most significant bits from subsequent builders, with:

    * 'rq' is the partially-constructed tail word, with all bits collected so far already in place,
    * 'rm' is the number of tail bits remaining to be collected

    Invariants:
    * '0 < rm <= mm'

>   makeTailFromB' :: Word# -> Int# -> Builders -> Builder
>   makeTailFromB' rq# rm# (BS (B m# q# n# ps) bs') =
>     case rrm# of
>       0# -> B mm# (or# rq# q#) nn# (makePagesFromPiBi nn# n# ps bs')
>       _  -> case rrm# ># 0# of
>               0# -> let nrm# = negateInt# rrm#
>                         nrw# = WORD_SIZE_IN_BITS# -# nrm#
>                         nq#  = uncheckedShiftRL# q# nrm#
>                         nu#  = uncheckedShiftL# q# nrw#
>                      in B mm# nq# nn# (makePagesFromUPiB nn# (firstPageSize nn#) nrm# nrw# nu# n# ps bs')
>               _  -> makeTailFromP' (or# rq# (uncheckedShiftL# q# rrm#)) rrm# n# ps bs'
>    where
>     rrm# = rm# -# m#


    Construct pages of the result builder.

    In the most general case, the page bits are obtained from the following sources,
    which, for easy of reference, we'll name with single-letter labels 'Q' or 'U', 'A', 'P' and 'B':

    Q. The 'm' least significant bits in a word 'q', where 'm <= 0 < WORD_SIZE_IN_BITS',

    U. The 'm' tail bits (where 'm <= 0 < WORD_SIZE_IN_BITS'),
       pre-shifted into the most significant bits of the word 'u',
       with an additional parameter 'w' equal to 'WORD_SIZE_IN_BITS - m',
       i.e. the number of vacant least-sigificant bits in 'u'.

    A. A byte array 'a' of 's' full words,

    P. The page list 'ps', with remaining element count 'n' and next page capacity 'c'.

    B. The builder list 'bs'.


    Cases that are aligned on word boundaries
    -----------------------------------------

    Invariants:
    * "0 <= n <= rn"

>   makePagesFromPiBi :: Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPiBi rn# n# ps bs =
>     case rn# ># n# of
>       0# -> ps
>       _  -> makePagesFromPiB' rn# (firstPageSize rn#) n# ps bs

    Invariants:
    * "0 <= n <= rn"
    * "prc == 2^i"
    * "rn .&. (2*prc - 1) == 0"

>   makePagesFromPiB :: Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPiB rn# prc# n# ps bs =
>     case rn# ># n# of
>       0# -> ps
>       _  -> makePagesFromPiB' rn# (nextPageSize rn# prc#) n# ps bs

    Invariants:
    * "0 <= n <= rn"
    * "prc == 2^i"
    * "rn .&. (2*prc - 1) == 0"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   makePagesFromPB :: Int# -> Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB rn# prc# n# pc# ps bs =
>     case rn# ># n# of
>       0# -> ps
>       _  -> makePagesFromPB' rn# (nextPageSize rn# prc#) n# pc# ps bs

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 <= n < rn"

>   makePagesFromPiB' :: Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPiB' rn# rc# n# ps bs =
>     case n# of
>       0# -> makePagesFromB' rn# rc# bs
>       _  -> makePagesFromPB'' rn# rc# n# (firstPageSize n#) ps bs

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 <= n < rn"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   makePagesFromPB' :: Int# -> Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB' rn# rc# n# pc# ps bs =
>     case n# of
>       0# -> makePagesFromB' rn# rc# bs
>       _  -> makePagesFromPB'' rn# rc# n# (nextPageSize n# pc#) ps bs

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 < c <= n < rn"
    * "c == (n .&. c) == 2^j"
    * "n .&. (c - 1) == 0"

>   makePagesFromPB'' :: Int# -> Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB'' rn# rc# n# c# (PS (P a#) ps') bs =
>     case rc# ==# c# of
>       0# -> makePagesFromAPB' rn# rc# c# a# (n# -# c#) c# ps' bs
>       _  -> PS (P a#) (makePagesFromPB (rn# -# rc#) rc# (n# -# c#) c# ps' bs)

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"

>   makePagesFromB' :: Int# -> Int# -> Builders -> Pages
>   makePagesFromB' rn# rc# (BS (B m# q# n# ps) bs') =
>     case m# of
>       0# -> makePagesFromPiB' rn# rc# n# ps bs'
>       _  -> let w# = WORD_SIZE_IN_BITS# -# m# in makePagesFromUPiB rn# rc# m# w# (uncheckedShiftL# q# w#) n# ps bs'

    Invariants:
    * "n + s <= rn"
    * "prc == 2^i"
    * "rn .&. (2*prc - 1) == 0"
    * "0 <= s <= sizeofByteArray a / SIZEOF_HSWORD"
    * "0 <= n"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   makePagesFromAPB :: Int# -> Int# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB rn# prc# s# a# n# pc# ps bs =
>     case s# of
>       0# -> makePagesFromPB rn# prc# n# pc# ps bs
>       _  -> makePagesFromAPB' rn# (nextPageSize rn# prc#) s# a# n# pc# ps bs

    Invariants:
    * "n + s <= rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 < s <= sizeofByteArray a / SIZEOF_HSWORD"
    * "0 <= n"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   makePagesFromAPB' :: Int# -> Int# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB' rn# rc# s# a# n# pc# ps bs =
>     runST $ ST $ \st0# -> case newByteArray# (rc# *# SIZEOF_HSWORD#) st0# of (# st1#, ma# #) -> fillPageFromAPB rn# rc# rc# ma# s# a# n# pc# ps bs st1#

    Invariants:
    * "n + s <= rn - rc + rs"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < s <= sizeofByteArray a / SIZEOF_HSWORD"
    * "0 <= n < rn"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   fillPageFromAPB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromAPB rn# rc# rs# rma# s# a# n# pc# ps bs st0# =
>     case rs# ># s# of
>       0# -> let ns# = s# -# rs#
>              in case copyWordArray# a# ns# rma# 0# rs# st0# of
>                   st1# -> emitPage rma# (makePagesFromAPB (rn# -# rc#) rc# ns# a# n# pc# ps bs) st1#
>       _  -> let nrs# = rs# -# s#
>              in case copyWordArray# a# 0# rma# nrs# s# st0# of
>                   st1# -> fillPageFromPB rn# rc# nrs# rma# n# pc# ps bs st1#

    Invariants:
    * "n <= rn - rc + rs"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 <= n"

>   fillPageFromPiB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromPiB rn# rc# rs# rma# n# ps bs st0# =
>     case n# of
>       0# -> fillPageFromB rn# rc# rs# rma# bs st0#
>       _  -> fillPageFromPB' rn# rc# rs# rma# n# (firstPageSize n#) ps bs st0#

    Invariants:
    * "n <= rn - rc + rs"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 <= n"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   fillPageFromPB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromPB rn# rc# rs# rma# n# pc# ps bs st0# =
>     case n# of
>       0# -> fillPageFromB rn# rc# rs# rma# bs st0#
>       _  -> fillPageFromPB' rn# rc# rs# rma# n# (nextPageSize n# pc#) ps bs st0#

    Invariants:
    * "n <= rn - rc + rs"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < n"
    * "c == (n .&. c) == 2^j"
    * "n .&. (c - 1) == 0"

>   fillPageFromPB' :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromPB' rn# rc# rs# rma# n# c# (PS (P a#) ps') bs st0# = fillPageFromAPB rn# rc# rs# rma# c# a# (n# -# c#) c# ps' bs st0#

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"

>   fillPageFromB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromB rn# rc# rs# rma# (BS (B m# q# n# ps) bs') st0 =
>     case m# of
>       0# -> fillPageFromPiB rn# rc# rs# rma# n# ps bs' st0
>       _  -> let w# = m# -# WORD_SIZE_IN_BITS#
>              in fillPageFromUPiB rn# rc# rc# rma# m# w# (uncheckedShiftL# q# w#) n# ps bs' st0


    Cases that are not aligned on word boundaries
    ---------------------------------------------

    Invariants:
    * "n < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * '0 <= n"

>   makePagesFromUPiB :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUPiB rn# rc# m# w# u# n# ps bs =
>     runST $ ST $ \st0# -> case newByteArray# (rc# *# SIZEOF_HSWORD#) st0# of (# st1#, ma# #) -> fillPageFromUPiB rn# rc# rc# ma# m# w# u# n# ps bs st1#

    Invariants:
    * "n + s < rn"
    * "rc == (rn .&. rc) == 2^i"
    * "rn .&. (rc - 1) == 0"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * "0 <= s"
    * "0 <= n"
    * "pc == 2^j"
    * "n .&. (2*pc - 1) == 0"

>   makePagesFromUAPB :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUAPB rn# rc# m# w# u# s# a# n# pc# ps bs =
>     runST $ ST $ \st0# -> case newByteArray# (rc# *# SIZEOF_HSWORD#) st0# of (# st1#, ma# #) -> fillPageFromUAPB rn# rc# rc# ma# m# w# u# s# a# n# pc# ps bs st1#

    Invariants:
    * "n < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * '0 <= n"

>   fillPageFromUPiB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUPiB rn# rc# rs# rma# m# w# u# n# ps bs st0# =
>     case n# of
>       0# -> fillPageFromUB rn# rc# rs# rma# m# w# u# bs st0#
>       _  -> fillPageFromUPB' rn# rc# rs# rma# m# w# u# n# (firstPageSize n#) ps bs st0#

    Invariants:
    * "n < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * '0 <= n"

>   fillPageFromUPB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUPB rn# rc# rs# rma# m# w# u# n# pc# ps bs st0# =
>     case n# of
>       0# -> fillPageFromUB rn# rc# rs# rma# m# w# u# bs st0#
>       _  -> fillPageFromUPB' rn# rc# rs# rma# m# w# u# n# (nextPageSize n# pc#) ps bs st0#

    Invariants:
    * "n < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * '0 < n"
    * "c == (n .&. c) == 2^j"
    * "n .&. (c - 1) == 0"

>   fillPageFromUPB' :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUPB' rn# rc# rs# rma# m# w# u# n# c# (PS (P a#) ps') bs st0# = fillPageFromUAPB' rn# rc# rs# rma# m# w# u# c# a# (n# -# c#) c# ps' bs st0#

    Invariants:
    * "n + s < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * "0 <= s"
    * "0 <= n"
    * "c == (n .&. c) == 2^j"
    * "n .&. (c - 1) == 0"

>   fillPageFromUAPB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUAPB rn# rc# rs# rma# m# w# u# s# a# n# pc# ps bs st0# =
>     case s# of
>       0# -> fillPageFromUPB rn# rc# rs# rma# m# w# u# n# pc# ps bs st0#
>       _  -> fillPageFromUAPB' rn# rc# rs# rma# m# w# u# s# a# n# pc# ps bs st0#

    Invariants:
    * "n + s < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"
    * "0 < s"
    * "0 <= n"
    * "c == (n .&. c) == 2^j"
    * "n .&. (c - 1) == 0"

>   fillPageFromUAPB' :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUAPB' rn# rc# rs# rma# m# w# u# s# a# n# pc# ps bs st0# =
>     case writeWordArray# rma# nrs# (or# u# (uncheckedShiftRL# q# m#)) st0# of
>       st1# -> case nrs# of
>                 0# -> emitPage rma# (makePagesFromUAPB (rn# -# rc#) rc# m# w# u# s# a# n# pc# ps bs) st1#
>                 _  -> fillPageFromUAPB rn# rc# nrs# rma# m# w# (uncheckedShiftL# q# w#) ns# a# n# pc# ps bs st1#
>    where
>     nrs# = rs# -# 1#
>     ns# = s# -# 1#
>     q# = indexWordArray# a# ns#

    Invariants:
    * "0 < rn"
    * "rc == (rn .&. rc) == 2^i == sizeofMutableByteArray rma / SIZEOF_HSWORD"
    * "rn .&. (rc - 1) == 0"
    * "0 < rs <= rc"
    * "0 < m < WORD_SIZE_IN_BITS"
    * "w == m - WORD_SIZE_IN_BITS"
    * "u .&. (2^w - 1) == 0"

>   fillPageFromUB :: Int# -> Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Word# -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromUB rn# rc# rs# rma# m# w# u# (BS (B bm# bq# n# ps) bs') st0# =
>     case bm# ==# w# of
>       0# -> case bm# ># w# of
>               0# -> let nw# = w# -# bm#
>                      in fillPageFromUPiB rn# rc# rs# rma# (m# +# bm#) nw# (or# u# (uncheckedShiftL# bq# nw#)) n# ps bs' st0#
>               _  -> let nm# = bm# -# w#
>                         nw# = WORD_SIZE_IN_BITS# -# nm#
>                         nu# = uncheckedShiftL# bq# nw#
>                         nrs# = rs# -# 1#
>                      in case writeWordArray# rma# nrs# (or# u# (uncheckedShiftRL# bq# nm#)) st0# of
>                           st1# -> case nrs# of
>                                     0# -> emitPage rma# (makePagesFromUPiB rn# rc# nm# nw# nu# n# ps bs') st1#
>                                     _  -> fillPageFromUPiB rn# rc# nrs# rma# nm# nw# nu# n# ps bs' st1#
>       _  -> let nrs# = rs# -# 1#
>              in case writeWordArray# rma# nrs# (or# u# bq#) st0# of
>                   st1# -> case nrs# of
>                             0# -> emitPage rma# (makePagesFromPiB (rn# -# rc#) rc# n# ps bs') st1#
>                             _  -> fillPageFromPiB rn# rc# nrs# rma# n# ps bs' st1#

> -}


  Page size derivation
  ====================

  Given a bitmask 'rn > 0', find the least 'rc',
  such that 'rc == 2^i' where 'i >= 0 && testBit rn i == True'.

> firstPageSize# :: Int# -> Int#
> firstPageSize# rn# = uncheckedIShiftL# 1# (word2Int# (ctz# (int2Word# rn#)))
> {-# INLINE firstPageSize# #-}

  Given 'rc == 2^i' and 'rn >= 2*rc', where 'i >= 0',
  find the least 'nrc == 2^j > rc', such that 'testBit rn j == True',

  The following iterative implementationis likely more efficient than the alternative using 'ctz#':

> nextPageSize# :: Int# -> Int# -> Int#
> nextPageSize# rn# rc# = let nrc# = uncheckedIShiftL# rc# 1#
>                          in case andI# rn# nrc# of
>                               0# -> nextPageSize# rn# nrc#
>                               _  -> nrc#

  Given a bitmask 'rn > 0', find the greatest 'rc',
  such that 'rc == 2^i' where 'i >= 0 && testBit rn i == True':

> lastPageSize# :: Int# -> Int#
> lastPageSize# rn# = uncheckedIShiftL# 1# (WORD_SIZE_IN_BITS# -# 1# -# word2Int# (clz# (int2Word# rn#)))
> {-# INLINE lastPageSize# #-}

  Given 'rc == 2^i' and '0 < rn < rc', where 'i >= 0',
  find the greatest 'nrc == 2^j < rc', such that 'testBit rn j == True'.

  The following iterative implementationis likely more efficient than the alternative using 'clz#'.

> previousPageSize# :: Int# -> Int# -> Int#
> previousPageSize# rn# rc# = let nrc# = uncheckedIShiftRL# rc# 1#
>                              in case andI# rn# nrc# of
>                                   0# -> previousPageSize# rn# nrc#
>                                   _  -> nrc#


  Byte-order operations
  =====================

  Last but not least, we deal with the target architecture's endianess.
  On little-endian machines, the in-memory byte order coincides precisely
  with that intended for our byte string, so we can perform our construction
  using fast bulk memory copies. On big-endian machines, however, we need to
  byte-swap each work en route to the target array.

> littleEndian# :: Word# -> Word#
> littleEndian# x# =
#ifdef WORDS_BIGENDIAN
>   byteSwap# x#
#else
>   x#
#endif
> {-# INLINE littleEndian# #-}

  Copies a byte array, also byte-swapping each word on big-endian platforms.
  All offsets and sizes are in words.

> copyWordArrayLE# :: ByteArray# -> Int# -> MutableByteArray# s -> Int# -> Int# -> State# s -> State# s
> copyWordArrayLE# a# o# ma# mo# n# st0# =
#ifdef WORDS_BIGENDIAN
>   loop o# mo# st0#
>  where
>   loop i# mi# st1# = case i# <# j# of
>                        0# -> st1#
>                        _  -> loop (i# +# 1#) (mi# +# 1#) (writeWordArray# ma# mi# (byteSwap# (indexWordArray# a# i#)) st1#)
>   j# = o# +# n#
#else
>  copyByteArray# a# (o# *# SIZEOF_HSWORD#) ma# (mo# *# SIZEOF_HSWORD#) (n# *# SIZEOF_HSWORD#) st0#
#endif
> {-# INLINE copyWordArrayLE# #-}

  Copies a memory region into a byte array, also byte-swapping each word on big-endian platforms.
  All offsets and sizes are in words.

> copyAddrToWordArrayLE# :: Addr# -> MutableByteArray# s -> Int# -> Int# -> State# s -> State# s
> copyAddrToWordArrayLE# a# ma# mo# n# st0# =
#ifdef WORDS_BIGENDIAN
>   loop 0# mo# st0#
>  where
>   loop i# mi# st1# = case i# <# n# of
>                        0# -> st1#
>                        _  -> loop (i# +# 1#) (mi# +# 1#) (writeWordArray# ma# mi# (byteSwap# (indexWordOffAddr# a# i#)) st1#)
#else
>   copyAddrToByteArray# a# ma# (mo# *# SIZEOF_HSWORD#) (n# *# SIZEOF_HSWORD#) st0#
#endif
> {-# INLINE copyAddrToWordArrayLE# #-}


  Low level array construction
  ============================

  Versions of the above with additional continuation,
  in cases where the ultimate result of the operation
  is best compupted while the array is still mutable:

> withNewByteArray# :: Int# -> (forall st . MutableByteArray# st -> State# st -> (# State# st, ByteArray# -> a #)) -> a
> withNewByteArray# c# f = runST $ ST $ \st0# ->
>   case newByteArray# c# st0# of
>     (# st1#, ma# #) -> case f ma# st1# of
>                          (# st2#, k #) -> case unsafeFreezeByteArray# ma# st2# of
>                                             (# st3#, a# #) -> (# st3#, k a# #)
> {-# INLINE withNewByteArray# #-}

> withNewPinnedByteArray# :: Int# -> (forall st . MutableByteArray# st -> State# st -> (# State# st, ByteArray# -> a #)) -> a
> withNewPinnedByteArray# c# f = runST $ ST $ \st0# ->
>   case newPinnedByteArray# c# st0# of
>     (# st1#, ma# #) -> case f ma# st1# of
>                          (# st2#, k #) -> case unsafeFreezeByteArray# ma# st2# of
>                                             (# st3#, a# #) -> (# st3#, k a# #)
> {-# INLINE withNewPinnedByteArray# #-}

> {-



> withNewPage :: Int# -> (forall st . MutableByteArray# st -> State# st -> State# st) -> (ByteArray# -> a) -> a
> withNewPage s# f k = freezePage k $ \st0# ->
>   case newPage# (s# *# SIZEOF_HSWORD#) st0# of (# st1#, ma# #) -> case f ma# st1# of st2# -> (# st2#, ma# #)
> {-# INLINE withNewPage #-}

> freezePage :: (ByteArray# -> a) -> (forall st . State# st -> (# State# st, MutableByteArray# st #)) -> a
> freezePage k f = runST $ ST $ \st0# ->
>   case f st0# of (# st1#, ma# #) -> case unsafeFreezeByteArray# ma# st1# of (# st2#, a# #) -> (# st2#, k a# #)
> {-# INLINE freezePage #-}

> copyWordArray# :: ByteArray# -> Int# -> MutableByteArray# st -> Int# -> Int# -> State# st -> State# st
> copyWordArray# a# o1# ma# o2# n# st0# = copyByteArray# a# (o1# *# SIZEOF_HSWORD#) ma# (o2# *# SIZEOF_HSWORD#) (n# *# SIZEOF_HSWORD#) st0#
> {-# INLINE copyWordArray# #-}

> emitPage :: MutableByteArray# st -> Pages -> State# st -> (# State# st, Pages #)
> emitPage rma# ps st0# = case unsafeFreezeByteArray# rma# st0# of (# st1#, ra# #) -> (# st1#, PS (P ra#) ps #)
> {-# INLINE emitPage #-}

> -}
