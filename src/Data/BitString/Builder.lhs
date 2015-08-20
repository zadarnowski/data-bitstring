> {-# LANGUAGE BangPatterns, CPP, MagicHash, RankNTypes, UnboxedTuples #-}
> {-# OPTIONS_GHC -funbox-strict-fields #-}

> #include "MachDeps.h"

> module Data.BitString.Builder (
>   Builder
> ) where

> import Data.List
> import Numeric (showHex)

> import GHC.Prim
> import GHC.ST
> import GHC.Types


  Data Types
  ==========

  In a builder of the form @B m q n ps@, @q@ contains the most-significant @m@
  bits of the bit string, while the remaining bits are stored in the list of arrays @ps@,
  in the order of decreasting significance, so that the least significant bit is stored
  in the last element of @ps@. Each element in @ps@ is either an empty array, or else an array
  of size @2^i@, where @i@ is the position of the element within @ps@.

  For performance, all lists are represented by coinductive (infinite) structures,
  since their actual shape is always determined uniquely by other builder parameters.

  Invariants:

    0 <= m < elementBitSize
    t `shiftR` m = 0
    n == sum (map elementArrayLength rs)
    forall i . (0 <= i) -> (elementArrayLength (rs!i) == 2^i * (fromIntegral $ fromEnum $ testBit i n))

  (assumign the obvious implementation of 'map' and '!' for our coinductive list structures,
  and an omniscient implementation of 'sum' capable of summing up an infinite list of zeroes.)

> data Builders = BS !Builder Builders
> data Builder  = B Int# Word# Int# Pages
> data Pages    = PS Page Pages
> data Page     = P ByteArray#

> emptyBuilders = BS emptyBuilder emptyBuilders
> emptyBuilder  = B 0# (int2Word# 0#) 0# emptyPages
> emptyPages    = withNewPage 0# (\ _ma# st# -> st#) (\ a# -> PS (P a#) emptyPages)


  'Show' Instance
  ===============

> instance Show Builder where
>   showsPrec _ (B 0#  _ 0#  _) = showString "[]"
>   showsPrec _ (B 0#  _ n# ps) = showPages# n# ps
>   showsPrec _ (B m# q# 0#  _) = showChar '[' . showTail# m# q# . showChar ']'
>   showsPrec _ (B m# q# n# ps) = showPages# n# ps . showChar ':' . showChar '[' . showTail# m# q# . showChar ']'

> showPages# :: Int# -> Pages -> ShowS
> showPages# n# = foldl (.) id . intersperse (showChar ':') . map showHex . unpackPages# n#

> showTail# :: Int# -> Word# -> ShowS
> showTail# 0# _  = id
> showTail# m# q# = showHex (I# (andI# (word2Int# q#) 1#)) . showTail# (m# -# 1#) (uncheckedShiftRL# q# 1#)

> unpackPages# :: Int# -> Pages -> [Word]
> unpackPages# = loop
>  where
>
>   loop :: Int# -> Pages -> [Word]
>   loop n# ps =
>     case n# of
>       0# -> []
>       _  -> loop' n# (firstPageSize n#) ps
>
>   loop' :: Int# -> Int# -> Pages -> [Word]
>   loop' n# c# (PS (P a#) ps') = loop'' c# a# (n# -# c#) c# ps'
>
>   loop'' :: Int# -> ByteArray# -> Int# -> Int# -> Pages -> [Word]
>   loop'' s# a# n# c# ps =
>     case s# of
>       0# -> loop''' n# c# ps
>       _  -> let i# = s# -# 1# in W# (indexWordArray# a# i#) : loop'' i# a# n# c# ps
>
>   loop''' n# c# ps =
>     case n# of
>       0# -> []
>       _  -> loop' n# (nextPageSize n# c#) ps


  'Monoid' Instance
  =================

> instance Monoid Builder where
>   mempty = emptyBuilder
>
>   mappend b1@(B m1# _ n1# _) b2@(B m2# _ n2# _) = concatBuilders m# n# bs
>     where
>       (# nt#, m# #) = quotRemInt# (m1# +# m2#) WORD_SIZE_IN_BITS#
>       n# = n1# +# n2# +# nt#
>       bs = BS b1 (BS b2 emptyBuilders)
>
>   mconcat []  = mempty
>   mconcat [b] = b
>   mconcat bsl = loop 0# 0# emptyBuilders bsl
>    where
>     loop mm# nn# bs (b@(B m# _ n# _) : bsl') = loop (mm# +# m#) (nn# +# n#) (BS b bs) bsl'
>     loop mm# nn# bs [] = let (# n#, m# #) = quotRemInt# mm# WORD_SIZE_IN_BITS# in concatBuilders m# (nn# +# n#) bs

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
>     runST $ ST $ \st0# -> case newByteArray# rc# st0# of (# st1#, ma# #) -> fillPageFromAPB rn# rc# rc# ma# s# a# n# pc# ps bs st1#

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
>     runST $ ST $ \st0# -> case newByteArray# rc# st0# of (# st1#, ma# #) -> fillPageFromUPiB rn# rc# rc# ma# m# w# u# n# ps bs st1#

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
>     runST $ ST $ \st0# -> case newByteArray# rc# st0# of (# st1#, ma# #) -> fillPageFromUAPB rn# rc# rc# ma# m# w# u# s# a# n# pc# ps bs st1#

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


  Miscellaneous
  =============

  Given a bitmask 'rn > 0', find the least 'rc',
  such that 'rc == 2^i' for some 'i >= 0', 'testBit rn i == True' and,
  for all '0 <= j < i', 'testBit rn j == False'.

> firstPageSize :: Int# -> Int#
> firstPageSize rn# = uncheckedIShiftL# 1# (word2Int# (ctz# (int2Word# rn#)))

  Given 'rc == 2^i' and 'rn >= 2*rc', where 'i >= 0',
  find the least 'nrc == 2^ni > rc', such that 'testBit rn ni == True' and,
  for all 'i < j < ni', 'testBit rn j == False'.

> nextPageSize :: Int# -> Int# -> Int#
> nextPageSize rn# rc# =
>   case andI# rn# rc'# of
>     0# -> nextPageSize rn# rc'#
>     _  -> rc'#
>  where
>   rc'# = uncheckedIShiftL# rc# 1#


  Low level array construction
  ============================

> withNewPage :: Int# -> (forall st . MutableByteArray# st -> State# st -> State# st) -> (ByteArray# -> a) -> a
> withNewPage s# f k = freezePage k $ \st0# ->
>   case newByteArray# s# st0# of (# st1#, ma# #) -> case f ma# st1# of st2# -> (# st2#, ma# #)
> {-# INLINE withNewPage #-}

> freezePage :: (ByteArray# -> a) -> (forall st . State# st -> (# State# st, MutableByteArray# st #)) -> a
> freezePage k f = runST $ ST $ \st0# ->
>   case f st0# of (# st1#, ma# #) -> case unsafeFreezeByteArray# ma# st1# of (# st2#, a# #) -> (# st2#, k a# #)
> {-# INLINE freezePage #-}

> copyWordArray# :: ByteArray# -> Int# -> MutableByteArray# st -> Int# -> Int# -> State# st -> State# st
> copyWordArray# a# o1# ma# o2# n# st# = copyByteArray# a# (o1# *# SIZEOF_HSWORD#) ma# (o2# *# SIZEOF_HSWORD#) (n# *# SIZEOF_HSWORD#) st#
> {-# INLINE copyWordArray# #-}

> emitPage :: MutableByteArray# st -> Pages -> State# st -> (# State# st, Pages #)
> emitPage rma# ps st0# = case unsafeFreezeByteArray# rma# st0# of (# st1#, ra# #) -> (# st1#, PS (P ra#) ps #)
> {-# INLINE emitPage #-}
