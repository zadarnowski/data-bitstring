> module Data.BitString.Dense (
> ) where

> import GHC.ForeignPtr (ForeignPtr, mallocPlainForeignPtrBytes)

> import Data.Bits
> import Data.Bool
> import Data.Int
> import Data.Word
> import Foreign.ForeignPtr
> import Foreign.Storable

  Internal representation of a dense bytestring consists of:

  1. @p@, a pointer to an array of string “elements”,
  2. @n@, the total number of elements in @p@,
  3. @i@, the number of least-significant /leading padding bits/,
     which should be igored in the first element of @p@, and
  4. @j@, the number of most-significant /trailing padding bits/,
     which should be igored in the final element of @p@.

> data BitString    = BS !ElementPtr !ElementCount !BitOffset !BitOffset
> type ElementPtr   = Ptr Element
> type Element      = Word64
> type BitOffset    = Int8
> type BitCount     = Int
> type ElementCount = Int

> instance Eq BitString where
>   (==) = bs_eq
>   (/=) = not . bs_eq

> instance Ord BitString where
>   compare = bs_cmp
>   (<)  = bs_lt
>   (<=) = bs_leq
>   (>)  = flip . bs_lt
>   (>=) = flip . bs_leq
>   min  = bs_max
>   max  = bs_min


  Empty bit string
  ================

> empty :: BitString
> empty = BS nullPtr 0 0 0


  Unary operators
  ===============

> bs_complement :: BitString -> BitString
> bs_complement (BS p n i j)
>   | (n == 0) = empty
>   | otherwise = BS (unsafePerformIO perform) n i j
>  where
>   perform_complement = do
>     p' <- malloc_elements n
>     perform_complement' p p'
>     return p'
>   perform_complement' p p'
>     | (p < ep) = peek p >>= poke . complement >> perform_complement' (nextElementPtr p) (nextElementPtr p')
>     | otherwise = return ()
>   ep = p `plusElementCount` n


  Binary operators
  ================

> bs_bitwise_operation :: (Element -> Element -> Element) -> BitString -> BitString
> bs_bitwise_operation (BS p1 n1 i1 j1) (BS p2 n2 i2 j2)
>   | (n1 == 0 || n2 == 0) = empty
>   | otherwise = case compare i1 i2 of
>                   LT -> misaligned_operation p1 p2 
>                   EQ -> aligned_operation p1 
>                   GT -> misaligned_operation p2 p1



>>= perform'
>   perform' p 
>     p' <- malloc_elements n
>     
  


  Binary operations
  =================

> bs_b



  Relational operations
  =====================

  Compare two bit strings for equality:

> bs_eq :: BitString -> BitString -> Bool
> bs_eq (BS p1 n1 i1 j1) (BS p2 n2 i2 j2)
>   | (p1 == p2) = (n1 == n2 && i1 == i2 && j1 == j2) -- covers the case of @p1 == p2 == nullPtr@
>   | (i1 == i2) = aligned_eq -- covers the remaining cases of @p1 = nullPtr || p2 = nullPtr@
>   | otherwise  = misaligned_eq
>  where

    Compare two element-aligned bit strings:

>   aligned_eq
>     | (n1 /= n2 || j1 /= j2) = False
>     | (n1 <= 1) = unsafePerformIO (pure short_aligned_eq <*> peek p1 <*> peek p2)
>     | otherwise = unsafePerformIO perform_aligned_eq

    Compare two aligned single-element bit strings:

>   short_aligned_eq x1 x2 = (((x1 `xor` x2) `unsafeShiftL` j1 `unsafeShiftR` (j1 + i1)) == 0)

    Compare two aligned multi-element bit strings:

>   perform_aligned_eq = do
>     e1 <- peek p1
>     e2 <- peek p2
>     if ((e1 `xor` e2) `unsafeShiftR` i1) != 0 then
>       return False
>     else
>       perform_aligned_eq' p1 p2
>   perform_aligned_eq' q1 q2 = do
>     e1 <- peek q1'
>     e2 <- peek q2'
>     if q1' == qe then
>       return (((e1 `xor` e2) `unsafeShiftL` j1) == 0)
>     else if e1 /= e2 then
>       return False
>     else
>       perform_aligned_eq' q1' q2'
>    where
>     q1' = nextElementPtr q1
>     q2' = nextElementPtr q2

    Compare two misaligned bit strings:

>   misaligned_eq
>     | (n1 * elementBitSize - i1 - j1 /= n2 * elementBitSize - i2 - j2) = False
>     | (i
>     | otherwise = perform_misaligned_eq
>   perform_misaligned_eq = do
>     e1 <- peek p1
>     e2 <- peek p2
>     if (e1 `unsafeShiftR` i1) != (e2 `unsafeShiftR` i2)
>       return False
>     else
>       perform_aligned_eq' p1 p2



  Compare two offset-aligned bit strings for equality:

> es_eq :: ElementPtr -> ElementPtr -> ElementIndex -> Bool
> es_eq p q n = unsafePerformIO $ loop p q
>  where
>   loop p q | (p < ep) = liftM3 (==) (peek p) (peek q) >>= bool (return False) (loop (nextElementPtr p) (nextElementPtr q))
>            | otherwise = return True
>   ep = elementPtr p n



  Element array options
  =====================

  Actual bit string data is stored in plain arrays of words.
  As in byte strings, we refer to them through low-level pointers for speed,
  but, unlike byte strings, we require them to be stored on the Haskell heap,
  since, due to their alignment requirements, it's unlikely that a bit string
  could refer to a foreign language object directly.

> -- | Individual element size in bytes:

> elementByteSize :: Int
> elementByteSize = sizeOf (0::Element)

> -- | Individual element size, in bits:

> elementBitSize :: BitCount
> elementBitSize = finiteBitSize (0::Element)

> -- | Converts a bit index into an element index

> elementIndex :: BitIndex -> ElementIndex
> elementIndex n = n + elementBitSizeMinusOne `div` elementBitSize
>  where elemenBittSizeMinusOne = elementBitSize - 1

> -- | Obtains a pointer to an element with the specified bit index:

> bitPtr :: ElementPtr -> BitIndex -> ElementPtr
> bitPtr es n = es `plusPtr` elementIndex n

> -- | Obtains a pointer to an element with the specified element index:

> elementPtr :: ElementPtr -> ElementIndex -> ElementPtr
> elementPtr es n = es `plusPtr` n * elementByteSize

> -- | Obtains a pointer to the next element of an array:

> nextElementPtr :: ElementPtr -> ElementPtr
> nextElementPtr es = es `plusPtr` elementByteSize

> -- | Bit mask to be applied to the leading element element bit mask:

>    where lm = -1 `unsafeShiftL` fromIntegral i1 -- leading bit mask
>          tm = -1 `unsafeShiftR` fromIntegral j1 -- trailing bit mask


  Compare two element-aligned arrays:

> es_eq :: BitCount -> ElementPtr -> ElementPtr -> Bool
> es_eq n p q 



> -- | Compares two element arrays of an equal size for equality:

> es_eq :: ElementPtr -> ElementPtr -> ElementIndex -> Bool
> es_eq p q n = unsafePerformIO $ loop p q
>  where
>   loop p q | (p < ep) = liftM3 (==) (peek p) (peek q) >>= bool (return False) (loop (nextElementPtr p) (nextElementPtr q))
>            | otherwise = return True
>   ep = elementPtr p n

> -- | Compares two bit strings for equality:equally-sized bit ranges for equality:

> bs_eq ::  ElementPtr -> BitIndex -> ElementPtr -> BitIndex -> BitIndex -> Bool
> bs_eq p1 m1 p2 m2 n2 | m1 == 
>   



> bs_eq :: BitString -> BitString -> BitString
> bs_eq (BS es1 m1 n1) (BS es2 m2 n2)
>   | (n1 == n2) = unsafePerformIO es_eq p1 p2 n1
>   | otherwise  = False

> es_eq :: Es -> Es





> length :: BitString -> Int
> length (P _ m n) = n

> data LazyBitString = LP !BitString | LPS LazyBitString LazyBitString

> zeroExtend :: Int -> BitString -> BitString
> zeroExtend n' bs@(BS fp m n) =
>   case compare n n' of
>     LT -> extend
>     EQ -> bs
>     GT -> BS fp m n'
>  where
>   extend = unsafePerformIO $ do
>     p' <- mallocElements n'
>     withForeignPtr p' $ \es -> do
>       clearElements es n n'
>     copyBits p m n p' 0
>     clearElementBits p' 0 n'
>     return (BS p' 0 n')

> signExtend :: Int -> BitString -> BitString
> signExtend n' bs@(BS p m n) =
>   case compare n n' of
>     LT -> extend
>     EQ -> bs
>     GT -> BS p m n'
>  where
>   extend = unsafePerformIO $ do
>     p' <- mallocElements n'
>     copyBits p m n p' 0
>     fillBits (testBit p' (n - 1)) p' n n'
>     return (BS p' 0 n')

> clearElements :: Ptr E -> Ptr E -> IO ()
> clearElements p m n =
>   | (m <= n)  = poke p m 0 >> clearElements p (m + 1) n
>   | otherwise = return ()
>

> mallocElements :: Int -> IO ForeignPtr
> mallocElements = mallocPlainForeignPtrBytes . bitElementIndex

> bitElementIndex :: Int -> Int
> bitElementIndex n = n + elementSizeMinusOne `div` elementSize
>  where elementSizeMinusOne = elementSize - 1




