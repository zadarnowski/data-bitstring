> {-# LANGUAGE BangPatterns, CPP, MagicHash, RankNTypes, UnboxedTuples #-}
> {-# OPTIONS_GHC -funbox-strict-fields #-}

> #include "MachDeps.h"

> module Data.BitString.Builder (
>   Builder
> ) where

> import Data.Bits
> import Data.BitString.Internal
> import Data.List
> import Foreign.Storable
> import Numeric (showHex)

> import GHC.Prim
> import GHC.ST
> import GHC.Types
> import GHC.Word


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
> emptyPages    = withNewPage 0# (\ ma# st# -> st#) (\ a# -> PS (P a#) emptyPages)


  'Show' Instance
  ===============

> instance Show Builder where
>   showsPrec _ (B 0#  _ 0#  _) = showString "[]"
>   showsPrec _ (B 0#  _ n# ps) = showPages# n# ps
>   showsPrec _ (B m# q# 0#  _) = showChar '[' . showTail# m# q# . showChar ']'
>   showsPrec _ (B m# q# n# ps) = showPages# n# ps . showChar ':' . showChar '[' . showTail# n# q# . showChar ']'

> showPages# :: Int# -> Pages -> ShowS
> showPages# n# = foldl (.) id . intersperse (showChar ':') . map showHex . unpackPages# n# 1#

> showTail# :: Int# -> Word# -> ShowS
> showTail# 0# _  = id
> showTail# m# q# = showHex (I# (word2Int# q# `andI#` 1#)) . showTail# (m# -# 1#) (q# `uncheckedShiftRL#` 1#)

> unpackPages# :: Int# -> Int# -> Pages -> [Word]
> unpackPages# n# c# ps =
>   case n# of
>     0# -> []
>     _  -> case (n# `andI#` c#) of
>             0# -> unpackPages# n# (c# `uncheckedIShiftL#` 1#) ps
>             _  -> case ps of
>                     (PS (P a#) ps') -> let loop s# = case s# of
>                                                        0# -> unpackPages# (n# `xorI#` c#) (c# `uncheckedIShiftL#` 1#) ps'
>                                                        _  -> let s'# = s# -# 1# in W# (indexWordArray# a# s'#) : loop s'#
>                                         in loop c#


  'Monoid' Instance
  =================

> instance Monoid Builder where
>   mempty = emptyBuilder
>   mappend b1 b2 = mconcat [b1, b2]
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
>       0# -> B mm# q# nn# (makePagesFromPB nn# n# ps bs')
>       _  -> case rm# ># 0# of
>               0# -> let nrm# = negateInt# rm#
>                         nrw# = WORD_SIZE_IN_BITS# -# nrm#
>                         nq#  = uncheckedShiftRL# q# nrm#
>                         nu#  = uncheckedShiftL# q# nrw#
>                      in B mm# nq# nn# (makePagesFromUPB' nn# (firstPageSize nn#) nrm# nrw# nu# n# ps bs')
>               _  -> makeTailFromP' (uncheckedShiftL# q# rm#) rm# n# ps bs'
>    where
>     rm# = mm# -# m#

    Collect the remaining most significant bits from the builder's pages, with:

    * 'rq' is the partially-constructed tail word, with all bits collected so far already in place,
    * 'rm' is the number of tail bits remaining to be collected,
    * 'n'  is the number of elements remaining in the page list 'ps'

    Invariants:
    * '0 <= rm <= mm'
    * '0 <= n'

>   makeTailFromP :: Word# -> Int# -> Int# -> Pages -> Builders -> Builder
>   makeTailFromP rq# rm# n# ps bs =
>     case rm# of
>       0# -> B mm# rq# nn# (makePagesFromPB nn# n# ps bs)
>       _  -> makeTailFromP' rq# rm# n# ps bs

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
>     B mm# (or# rq# (uncheckedShiftRL# q# m#)) nn# (makePagesFromUAPB' nn# (firstPageSize nn#) m# w# u# s# a# (n# -# c#) ps' bs)
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
>       0# -> B mm# (or# rq# q#) nn# (makePagesFromPB nn# n# ps bs')
>       _  -> case rrm# ># 0# of
>               0# -> let nrm# = negateInt# rrm#
>                         nrw# = WORD_SIZE_IN_BITS# -# nrm#
>                         nq#  = uncheckedShiftRL# q# nrm#
>                         nu#  = uncheckedShiftL# q# nrw#
>                      in B mm# nq# nn# (makePagesFromUPB' nn# (firstPageSize nn#) nrm# nrw# nu# n# ps bs')
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


    Invariants:
    * '0 < rc <= rn'

>   makePagesFromB' :: Int# -> Int# -> Builders -> Pages
>   makePagesFromB' rn# rc# (BS (B m# q# n# ps) bs') =
>     case m# of
>       0# -> makePagesFromPB' rn# rc# n# ps bs'
>       _  -> error "TODO: misaligned copy"

    Invariants:
    * '0 <= n <= rn'

>   makePagesFromPB :: Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB rn# n# ps bs =
>     case rn# ># n# of
>       0# -> ps
>       _  -> makePagesFromPB' rn# (firstPageSize rn#) n# ps bs

    Invariants:
    * '0 < rc <= rn'
    * '0 <= n < rn'

>   makePagesFromPB' :: Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB' rn# rc# n# ps bs =
>     case n# of
>       0# -> makePagesFromB' rn# rc# bs
>       _  -> makePagesFromPB'' rn# rc# n# (firstPageSize n#) ps bs

    Invariants:
    * '0 < rc <= rn'
    * '0 < c <= n < rn'

>   makePagesFromPB'' :: Int# -> Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB'' rn# rc# n# c# (PS (P a#) ps') bs =
>     case rc# ==# c# of
>       0# -> makePagesFromAPB'' rn# rc# c# a# (n# -# c#) ps' bs
>       _  -> PS (P a#) (makePagesFromPB (rn# -# rc#) (n# -# c#) ps' bs)

    Invariants:
    * '0 <= rn'
    * '0 <= s'
    * '0 <= n'

>   makePagesFromAPB :: Int# -> Int# -> ByteArray# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB rn# s# a# n# ps bs =
>     case s# of
>       0# -> makePagesFromPB rn# n# ps bs
>       _  -> makePagesFromAPB' rn# s# a# n# ps bs

    Invariants:
    * '0 < rn'
    * '0 < s'
    * '0 <= n'

>   makePagesFromAPB' :: Int# -> Int# -> ByteArray# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB' rn# s# a# n# ps bs = error "TODO: extract body from makePagesFromPB''"

    Invariants:
    * '0 < rc <= rn'
    * '0 < s /= rc'
    * '0 <= n'

>   makePagesFromAPB'' :: Int# -> Int# -> Int# -> ByteArray# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB'' rn# rc# s# a# n# ps bs =
>     runST $ ST $ \st0# -> case newByteArray# rc# st0# of (# st1#, ma# #) -> fillPageFromAPB (rn# -# rc#) rc# ma# s# a# n# ps bs st1#

    Invariants:
    * '0 <= rn'
    * '0 < rs'
    * '0 < s'
    * '0 <= n'

>   fillPageFromAPB :: Int# -> Int# -> MutableByteArray# st -> Int# -> ByteArray# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromAPB rn# rs# rma# s# a# n# ps bs st0# =
>     case rs# ># s# of
>       0# -> let ns# = s# -# rs#
>              in case copyWordArray# a# ns# rma# 0# rs# st0# of
>                   st1# -> case unsafeFreezeByteArray# rma# st1# of
>                             (# st2#, ra# #) -> (# st2#, PS (P ra#) (makePagesFromAPB rn# ns# a# n# ps bs) #)
>       _  -> let nrs# = rs# -# s#
>              in case copyWordArray# a# 0# rma# nrs# s# st0# of
>                   st1# -> fillPageFromPB rn# nrs# rma# n# ps bs st1#

>   fillPageFromPB :: Int# -> Int# -> MutableByteArray# st -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromPB rn# rs# rma# n# ps bs st0# =
>     case n# of
>       0# -> fillPageFromB rn# rs# rma# bs st0#
>       _  -> fillPageFromPB' rn# rs# rma# n# (firstPageSize n#) ps bs st0#

>   fillPageFromPB' :: Int# -> Int# -> MutableByteArray# st -> Int# -> Int# -> Pages -> Builders -> State# st -> (# State# st, Pages #)
>   fillPageFromPB' rn# rs# rma# n# c# (PS (P a#) ps') bs st0# =
>     fillPageFromAPB rn# rs# rma# c# a# (n# -# c#) ps' bs st0#

>   fillPageFromB = error "TODO"

> {-

> case rc# ># c# of
>                            0# -> case copyWordArray# a# (c# -# rc#) ma# 0# rc# st1# of
>                                    st2# -> case unsafeFreezeByteArray# ma# st2# of
>                                              (# st3#, aa# #) -> PS (P aa#) (error "TODO: make more pages")
>                            _  -> case copyWordArray# a# 0# ma# (rc# - c#) c# st1# of
>                                    st2# -> makeMorePages 

> $ \aa# -> PS (P aa#) makeMorePages
>    where
>     fillPage
>     makeMorePages = ..
> case d# ># 0# of
>               0# -> let fillPage ma# st# = copyWordArray# a# s# ma# 0# rc# st#
>                         s# = negateInt# d#
>                         nrn# = rn# -# rc#
>                         nrc# = nextPageSize nrn# rc#
>                      in withNewPage rc# fillPage $ \aa# -> PS (P aa#) (makePagesFromAPB nrn# nrc# s# a# (n# - c#) ps' bs) -- NOTE: next copy from a# MUST be a merge
>               _  -> error "TODO: merging"
>    where
>     d# = rc# -# c#

> -}

    TODO:

    Invariants:
    * '0 < rc <= rn'
    * '0 < m < WORD_SIZE_IN_BITS'
    * '0 <= n < rn'

>   makePagesFromUPB' :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUPB' rn# rc# m# w# u# n# ps bs = error "TODO"

    Invariants:
    * '0 < rc <= rn'
    * '0 < m < WORD_SIZE_IN_BITS'
    * '0 <= s'
    * '0 <= n <= rn'

>   makePagesFromUAPB' :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> ByteArray# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUAPB' rn# rc# m# w# u# s# a# n# ps bs = error "TODO"


 ================================================================================

> {-

>   makePagesFromB, makePagesFromB', makePagesFromB'' :: Int# -> Int# -> Builders -> Pages
>   makePagesFromB rn# rc# bs =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromB' rn# rc# bs
>   makePagesFromB' rn# rc# bs {- where rn > 0 -} =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromB' rn# (rc# `uncheckedIShiftL#` 1#) bs
>       _  -> makePagesFromB'' rn# rc# bs
>   makePagesFromB'' rn# rc# (BS (B m# q# n# ps) bs') {- where rn .&. rc > 0 -} =
>     makePagesFromQPB'' rn# rc# m# q# n# 1# ps bs'

>   makePagesFromPB, makePagesFromPB', makePagesFromPB'', makePagesFromPB''', makePagesFromPB'''' ::
>     Int# -> Int# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromPB rn# rc# n# c# ps bs =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromPB' rn# rc# n# c# ps bs
>   makePagesFromPB' rn# rc# n# c# ps bs {- where rn > 0 -} =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromPB' rn# (rc# `uncheckedIShiftL#` 1#) n# c# ps bs
>       _  -> makePagesFromPB'' rn# rc# n# c# ps bs
>   makePagesFromPB'' rn# rc# n# c# ps bs {- where rn .&. rc > 0 -} =
>     case n# of
>       0# -> makePagesFromB'' rn# rc# bs
>       _  -> makePagesFromPB''' rn# rc# n# c# ps bs
>   makePagesFromPB''' rn# rc# n# c# ps bs {- where rn .&. rc > 0 && n > 0 -} =
>     case n# `andI#` c# of
>       0# -> makePagesFromPB''' rn# rc# n# (c# `uncheckedIShiftL#` 1#) ps bs
>       _  -> makePagesFromPB'''' rn# rc# n# c# ps bs
>   makePagesFromPB'''' rn# rc# n# c# (PS (P a#) ps') bs {- where rn .&. rc > 0 && n .&. c > 0 -} =
>     case d# >=# 0# of
>       0# -> error "TODO: merge blocks"
>       _  -> case d# of
>               0# -> PS (P a#) (makePagesFromPB rn'# rc'# n'# c'# ps' bs)
>               _  -> let fill ma# st# = copyByteArray# a# (d# *# SIZEOF_HSWORD#) ma# 0# (rc# *# SIZEOF_HSWORD#) st#
>                      in withNewPage rc# fill $ \a'# -> PS (P a'#) (makePagesFromAPB' rn'# rc'# d# a# n'# c'# ps' bs) -- NOTE: d# > 0 so rn'# > 0
>    where
>     d#   = rc# -# c#
>     rn'# = rn# `xorI#` rc#
>     rc'# = rc# `uncheckedIShiftL#` 1#
>     n'#  = n# `xorI#` c#
>     c'#  = c# `uncheckedIShiftL#` 1#

>   makePagesFromAPB, makePagesFromAPB', makePagesFromAPB'' :: Int# -> Int# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromAPB rn# rc# s# a# n# c# ps bs {- where 0 < s < rc -} =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromAPB' rn# rc# s# a# n# c# ps bs
>   makePagesFromAPB' rn# rc# s# a# n# c# ps bs {- where 0 < s < rc and rn > 0 -} =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromAPB' rn# (rc# `uncheckedIShiftL#` 1#) s# a# n# c# ps bs
>       _  -> makePagesFromAPB'' rn# rc# s# a# n# c# ps bs
>   makePagesFromAPB'' rn# rc# s# a# n# c# ps bs {- where 0 < s < rc and rn .&. rc > 0 -} =
>     error "TODO: merge blocks"

>   makePagesFromQPB, makePagesFromQPB', makePagesFromQPB'' :: Int# -> Int# -> Int# -> Word# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromQPB rn# rc# m# q# n# c# ps bs =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromQPB' rn# rc# m# q# n# c# ps bs
>   makePagesFromQPB' rn# rc# m# q# n# c# ps bs =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromQPB' rn# (rc# `uncheckedIShiftL#` 1#) m# q# n# c# ps bs
>       _  -> makePagesFromQPB'' rn# rc# m# q# n# c# ps bs
>   makePagesFromQPB'' rn# rc# m# q# n# c# ps bs =
>     case m# of
>       0# -> makePagesFromPB'' rn# rc# n# c# ps bs
>       _  -> let w# = WORD_SIZE_IN_BITS# -# m#
>              in makePagesFromUPB'' rn# rc# m# w# (q# `uncheckedShiftL#` w#) n# c# ps bs

>   makePagesFromUPB, makePagesFromUPB', makePagesFromUPB'' :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUPB rn# rc# m# w# u# n# c# ps bs =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromUPB' rn# rc# m# w# u# n# c# ps bs
>   makePagesFromUPB' rn# rc# m# w# u# n# c# ps bs =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromUPB' rn# (rc# `uncheckedIShiftL#` 1#) m# w# u# n# c# ps bs
>       _  -> makePagesFromUPB'' rn# rc# m# w# u# n# c# ps bs
>   makePagesFromUPB'' rn# rc# m# w# u# n# c# ps bs = error "TODO"

>   makePagesFromUAPB, makePagesFromUAPB', makePagesFromUAPB'' :: Int# -> Int# -> Int# -> Int# -> Word# -> Int# -> ByteArray# -> Int# -> Int# -> Pages -> Builders -> Pages
>   makePagesFromUAPB rn# rc# m# w# u# s# a# n# c# ps bs =
>     case rn# of
>       0# -> emptyPages
>       _  -> makePagesFromUAPB' rn# rc# m# w# u# s# a# n# c# ps bs
>   makePagesFromUAPB' rn# rc# m# w# u# s# a# n# c# ps bs =
>     case rn# `andI#` rc# of
>       0# -> makePagesFromUAPB' rn# (rc# `uncheckedIShiftL#` 1#) m# w# u# s# a# n# c# ps bs
>       _  -> makePagesFromUAPB'' rn# rc# m# w# u# s# a# n# c# ps bs
>   makePagesFromUAPB'' rn# rc# m# w# u# s# a# n# c# ps bs = error "TODO"

> -}


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


> {-

  Merge the list of builders 'bs' into a single builder with 'nn' words and 'mm' trailing bits'.
  The first builder in 'bs' contains the most sigificant bits of the result.

> mergeBuilders :: Int -> Int -> Builders -> Builder
> mergeBuilders mm  0 bs = mergeTiny mm 0 mm bs
> mergeBuilders mm nn bs = mergeLarge mm nn bs

  Merge a list of builders into a tiny builder with less than 'elementBitSize' of bits in total.
  This is special as we know that all contributing builders must come with an empty page list.

> mergeTiny :: Int -> Word -> Int -> [Builder] -> Builder
> mergeTiny mm !qq rm (B m q _ _ : bs')
>   | (rm' > 0) = mergeTiny mm (qq .|. (q `unsafeShiftL` rm')) rm' bs'
>   | otherwise = B mm (qq .|. q) 0 emptyPages
>  where
>   rm' = rm - m
> mergeTiny mm qq rm [] = B mm qq 0 emptyPages

  Merge a list of builders into a builder with no trailing bits:

> mergeAligned :: Int -> [Builder] -> Builder
> mergeAligned nn (B m q _ _ : bs')
    

>   | (mm == 0) = error "TODO"
>   | otherwise = merge1 mm nn mm 0 bs
>  where

  Collect the remaining 'rm' trailing bits of the result, and add them to the existing bits in 'rq',
  starting with the trailing bits of the first builder:

> merge1 mm nn rm rq (B m q n ps : bs') =
>   case compare m rm of
>     LT -> merge2 mm nn (rm - m) (rq .|. (q `unsafeShiftL` (rm - m))) n 1 ps bs'
>     EQ -> error "TODO"
>     GT -> error "TODO"

  Collect more trailing bits of the result from the head page 'p' of the first builder in 'bs',
  with the total remaining word count 'n' and current page capacity 'c'. Note that the first
  non-empty page is guaranteed to satisfy the demand.

> merge2 mm nn rm rq n c (P a ps') bs
>   | (n == 0)  = merge1 mm nn rm rq bs -- no more pages in this builder
>   | (even n)  = merge2 mm nn rm rq n2 c2 ps' bs -- next page is empty
>   | otherwise = merge3 mm (rq .|. (q `unsafeShiftR` ro)) nn nn 1 rm ro (q `unsafeShiftL` rm) s a n2 c2 a ps' bs
>  where
>   s  = c - 1
>   q  = lookupElementArray a s
>   ro = elementBitSize - rm
>   n2 = n `unsafeShiftR` 1
>   c2 = c `unsafeShiftL` 1

  We have now completed the trailing bits 'qq'.
  The next 'ro' bits will come from the MSW of the page 'a' prefetched into 'q',
  followed by 'rm' bits from the next MSW of 'a', with 'rm + ro == elementBitSize'.
  's' is the number of remaining words in 'a', 'n' is the number of remaining words in 'ps',
  and 'c' is the capacity of the first page of 'ps'.

  'rn' is the remaining number of words to produce for the resulting builder,
  and 'rc' is the capacity of the next page to produce.

> merge3 mm qq nn rn rc rm ro q s a n c ps bs
>   | (nn == 0) = B 
>   | 



    Fill a mutable array 'ra' of size 'sra' (in words) with input bits from the
    following sources, beginning with the most significat bit first:

    1. the most significant 'sq' bits of the word 'q' (0 < m < elementBitSize)
    2. the first 'spa' words of the word array 'pa',
    3. the array list 'pas', using the builder size 'n' and the head capacity 'c',
    4. subsequent builders 'bs'.

> mergeBuilders :: Int# -> MutableByteArray# st ->
>                  Int# -> Word# ->
>                  Int# -> ByteArray# ->
>                  Int# -> Int# -> [ElementArray] ->
>                  [Builder] ->
>                  ST st Builder
> mergeBuilders sra# ra# sq# q# spa# pa# n# c# pas bs = do
>   let spa'# = spa# -# 1#
>   let qpa#  = indexWordArray# pa# spa'#
>   let sra'# = sra# -# 1#
>   let sq'#  = elementBitSize -# sq#
>   pokeElement# ra# sra'# (q# `or#` (qpa# `uncheckedShiftRL#` sq#))
>   mergeBuilders sra'# ra# sq# (qpa# `uncheckedShiftL#` sq'#) spa'# pa# n# c# pas bs

> pokeElement# :: MutableByteArray# st -> Int# -> Word# -> ST st ()
> pokeElement# ma# i# x# = ST $ \st# -> (# writeWordArray# ma# i# x# st#, () #)


> instance Monoid Builder where
>   mempty  = emptyBuilder
>   mappend = appendBuilders

> emptyBuilder :: Builder
> emptyBuilder = B 0 0 0 []

> appendBuilders :: Builder -> Builder -> Builder
> appendBuilders b1 (B m2 t2 0 _) = appendTiny b1 m2 t2
> appendBuilders (B 0 _ n1 rs1) (B m2 t2 n2 rs2) = B m2 t2 n' (mergeAligned n' 1 0 (rs2 ++ rs1))
>  where n' = n1 + n2
> appendBuilders b1 b2 = concatBuilders [b1, b2]

> appendTiny :: Builder -> Int -> Element -> Builder
> appendTiny (B m t n rs) mm tt
>   | (m' < elementBitSize) = B m' t' n rs
>   | otherwise = B (m' - elementBitSize) (tt `unsafeShiftR` (elementBitSize - m)) (n + 1) (pushSingleton [elementArray t'] n rs)
>  where
>   m' = m + mm
>   t' = t .|. (tt `unsafeShiftL` m)

> pushSingleton :: [ElementArray] -> Word -> [ElementArray] -> [ElementArray]
> pushSingleton qs n (r:rs')
>   | odd n = mempty : pushSingleton (r:qs) (n `unsafeShiftR` 1) rs'
>   | otherwise = mconcat qs : rs'
> pushSingleton qs _ [] = [mconcat qs]

> mergeAligned :: Word -> Int -> Int -> [ElementArray] -> [ElementArray]
> mergeAligned n s o rs
>   | (n == 0) = []
>   | odd n = merge [] s o rs
>   | otherwise = mempty : mergeMore o rs
>  where
>   mergeMore o' rs' = n' `seq` s' `seq` mergeAligned n' s' o' rs'
>    where
>     n' = n `unsafeShiftR` 1
>     s' = s * 2
>   merge qs qm ro rs'@(r:rs'')
>     | (rr > 0) = case compare qm rr of
>                    LT -> fromElementArraySlices (elementArraySlice ro qm r : qs) : mergeMore (ro + qm) rs'
>                    EQ -> fromElementArraySlices (elementArraySlice ro rr r : qs) : mergeMore 0 rs''
>                    GT -> merge (elementArraySlice ro rr r : qs) (qm - rr) 0 rs''
>     | otherwise = merge qs qm 0 rs'
>    where
>     rr = elementArrayLength r - ro

> concatBuilders [] = mempty
> concatBuilders [b] = b
> concatBuilders bs = loop0 (mm `mod` elementBitSize) 0 (reverse bs)
>  where
>   mm = sum [ m | B m _ _ _ <- bs ]
>   nn = fromIntegral (mm `div` elementBitSize) + sum [ n | B _ _ n _ <- bs ]

    Start by collecting the most significant @rm@ bits from @rbs@
    to form the tail of the resulting builder. Here, @rt@ is the builder
    constructed so far; the successive bits will be pushed in to the left of @rt@.

    Preconditions: @0 <= rm < elementBitSize@.

>   loop0 rm rt (B m t n rs : bs')
>     | (m <= rm) = loop1 (rm - m) ((rt `unsafeShiftL` m) .|. t) n rs bs'
>     | otherwise = error "TODO: loop4 (rt `unsafeShiftL` rr .|. (t `unsafeShiftR` m')) m' (t `unsafeShiftL` (elementBitSize - m')) n 1 rs bs'"
>    where
>     m' = m - rm
>   loop0 _ rt [] = B m rt 0 [] -- this can only happen if the sum of tails is less than 'elementBitSize'

    We've exhausted the tail input bits,
    but still may need to collect @rm@ bits of the tail subword @rt@.

    Preconditions: @0 <= rm < elementBitSize@.

>   loop1 rm rt n rs bs'
>     | (rm > 0) = loop2 rm rt n 1 rs bs'
>     | otherwise = error "TODO: loop4a rt n rs bs'"

    Collect the remaining @rm@ tail bits out of the first non-empty block @r@ in @rs@,
    or, failing that, from @bs'@. @s@ is the presumed size of @r@.

    Note that we could skip the case of @null rs@ by checking for @n == 0@ instead.

    Preconditions: @0 < rm < elementBitSize@.

>   loop2 rm rt n s (r:rs') bs'
>     | (n .&. s != 0) = loop3 rm rt n s r rs' bs'
>     | otherwise = n' `seq` s' `seq` loop2 rm rt n' s' rs' bs'
>    where
>     n' = n `unsafeShiftR` 1
>     s' = s * 2
>   loop2 rm rt _ _ [] bs' = loop0 rm rt bs'

    Extract the remaining @rm@ tail bits out of the most significant element of @r@:

>   loop3 rm rt n s r rs' bs' = loop4 rt' rm' (t' `unsafeShiftL` rm) n s s' r rs' bs'
>    where
>     s'  = s - 1
>     t'  = lookupElementArray r s'
>     rt' = (rt `unsafeShiftL` rm) .|. (t' `unsafeShiftR` rm')
>     rm' = elementBitSize - rm

    We now have a complete set of tail bits @rt@; the next @m@ bits of the
    bitstring are stored in the most-significant bits of @u@, followed by
    the remaining @s@ words of @r@, followed by @rs'@ and finally @bs'@.

    This variant is for misaligned data, so @0 < rm < elementBitSize@.

>   loop4 rt rm u n s s r rs' bs'
>     | (s > 0) =
>     | otherwise =


    Look into 'rs' for more tail bits:

>   loop3 rm rt n s (r:rs') bs'
>     | odd n = loop3' rr rt n s r rs' bs'
>     | otherwise = loop3 rr rt (n `unsafeShiftR` 1) (s * 2) rs' bs'
>   loop3 rr rt _ [] bs' = loop0 rr rt bs'

    Found the remaining tail bits in the most significant element of 'r':

>   loop3' rr rt n s r rs' bs' = loop4' (rt `unsafeShiftL` rr .|. (t `unsafeShiftR` m)) m (t `unsafeShiftL` (elementBitSize - m)) n s s' r rs' bs'
>    where
>     t = lookupElementArray r s'
>     m = elementBitSize - rr
>     s' = s - 1

    We've completed the tail subword "tt", and are ready to start on the body,
    with some input tail bits left:

>   loop4 tt m u n rs bs' = error "TODO"

    Same as "loop4", but without any tail bits:

>   loop4a tt n rs bs' = error "TODO"


> -}

