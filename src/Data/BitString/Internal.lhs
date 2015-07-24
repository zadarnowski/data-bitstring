> {-# LANGUAGE BangPatterns, CPP, MagicHash, RankNTypes, UnboxedTuples #-}

> #include "MachDeps.h"

> module Data.BitString.Internal (
>   Element, elementSize, elementBitSize,
>   ElementArray, elementArray, elementArrayLength, lookupElementArray,
>   ElementArraySlice, elementArraySlice, fromElementArraySlice, fromElementArraySlices,
> ) where

> import Data.Bits
> import Data.Monoid
> import Foreign.Storable

> import GHC.Prim
> import GHC.ST
> import GHC.Types
> import GHC.Word

> type Element = Word

> elementSize :: Int
> elementSize = SIZEOF_HSWORD

> elementBitSize :: Int
> elementBitSize = WORD_SIZE_IN_BITS

  Element Arrays
  ==============

> data ElementArray = EA# ByteArray#

> instance Monoid ElementArray where
>   mempty = runNewElementArray 0# $ \ _ st# -> st#
>   mappend (EA# a1#) (EA# a2#) = runNewElementArray (s1# +# s2#) $ \ ma# st0# ->
>     case copyByteArray# a1# 0# ma# 0# s1# st0# of st1# -> copyByteArray# a2# 0# ma# s1# s2# st1#
>    where
>     s1# = sizeofByteArray# a1#
>     s2# = sizeofByteArray# a2#
>   mconcat [] = mempty
>   mconcat [ea] = ea
>   mconcat eas = runNewElementArray ss# $ \ ma# st0# -> loop# eas ma# 0# st0#
>    where
>     !(I# ss#) = sum [ I# (sizeofByteArray# a#) | EA# a# <- eas ]
>     loop# (EA# a# : eas') ma# mo# st0# = case copyByteArray# a# 0# ma# mo# s# st0# of st1# -> loop# eas' ma# (mo# +# s#) st1#
>      where s# = sizeofByteArray# a#
>     loop# [] _ _ st# = st#

> elementArray :: Element -> ElementArray
> elementArray (W# e#) = runNewElementArray SIZEOF_HSWORD# $ \ ma# st# -> writeWordArray# ma# 0# e# st#

> elementArrayLength :: ElementArray -> Int
> elementArrayLength (EA# a#) = I# (sizeofByteArray# a# `quotInt#` SIZEOF_HSWORD#)

> lookupElementArray :: ElementArray -> Int -> Element
> lookupElementArray (EA# a#) (I# i#) = W# (indexWordArray# a# i#)

> data ElementArraySlice = ES# Int# Int# ByteArray#

> instance Monoid ElementArraySlice where
>   mempty = runNewElementArraySlice 0# $ \ _ st# -> st#
>   mappend (ES# o1# s1# a1#) (ES# o2# s2# a2#) = runNewElementArraySlice (s1# +# s2#) $ \ ma# st0# ->
>     case copyByteArray# a1# o1# ma# 0# s1# st0# of st1# -> copyByteArray# a2# o2# ma# s1# s2# st1#
>   mconcat = elementArraySlice 0 0 . fromElementArraySlices

> elementArraySlice :: Int -> Int -> ElementArray -> ElementArraySlice
> elementArraySlice (I# o#) (I# s#) (EA# a#) = ES# (o# *# SIZEOF_HSWORD#) (s# *# SIZEOF_HSWORD#) a#

> elementArraySliceLength :: ElementArraySlice -> Int
> elementArraySliceLength (ES# _ s# _) = I# (s# `quotInt#` SIZEOF_HSWORD#)

> fromElementArraySlice :: ElementArraySlice -> ElementArray
> fromElementArraySlice (ES# o# s# a#) =
>   case (o# `orI#` (s# `xorI#` sizeofByteArray# a#)) of
>     0# -> EA# a#
>     _  -> runNewElementArray s# $ \ ma# st0# -> copyByteArray# a# o# ma# 0# s# st0#

> fromElementArraySlices :: [ElementArraySlice] -> ElementArray
> fromElementArraySlices [] = mempty
> fromElementArraySlices [es] = fromElementArraySlice es
> fromElementArraySlices ess = runNewElementArray ss# $ \ ma# st0# -> loop# ess ma# 0# st0#
>  where
>   !(I# ss#) = sum [ I# s# | ES# _ s# _ <- ess ]
>   loop# (ES# o# s# a# : ess') ma# mo# st0# = case copyByteArray# a# o# ma# mo# s# st0# of st1# -> loop# ess' ma# (mo# +# s#) st1#
>   loop# [] _ _ st# = st#


  Low-level element array construction
  ====================================

> runElementArray :: (forall st . State# st -> (# State# st, MutableByteArray# st #)) -> ElementArray
> runElementArray act = runST $ ST $ \st0# ->
>   case act st0# of (# st1#, ma# #) -> case unsafeFreezeByteArray# ma# st1# of (# st2#, a# #) -> (# st2#, EA# a# #)

> runNewElementArray :: Int# -> (forall st . MutableByteArray# st -> State# st -> State# st) -> ElementArray
> runNewElementArray s# act = runElementArray $ \st0# ->
>   case newByteArray# s# st0# of (# st1#, ma# #) -> case act ma# st1# of st2# -> (# st2#, ma# #)

> runElementArraySlice :: (forall st . State# st -> (# State# st, MutableByteArray# st #)) -> ElementArraySlice
> runElementArraySlice act = runST $ ST $ \st0# ->
>   case act st0# of (# st1#, ma# #) -> case unsafeFreezeByteArray# ma# st1# of (# st2#, a# #) -> (# st2#, ES# 0# (sizeofByteArray# a#) a# #)

> runNewElementArraySlice :: Int# -> (forall st . MutableByteArray# st -> State# st -> State# st) -> ElementArraySlice
> runNewElementArraySlice s# act = runElementArraySlice $ \st0# ->
>   case newByteArray# s# st0# of (# st1#, ma# #) -> case act ma# st1# of st2# -> (# st2#, ma# #)
