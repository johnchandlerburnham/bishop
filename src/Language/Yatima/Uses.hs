module Language.Yatima.Uses where

data Uses = Zero | Once | Many deriving (Eq,Show, Ord, Enum)

(+#) :: Uses -> Uses -> Uses
Zero +# x    = x
Once  +# Zero = Once
Once  +# x    = Many
Many +# x    = Many

(*#) :: Uses -> Uses -> Uses
Zero *# x    = Zero
Once  *# x    = x
Many *# Once  = Many
Many *# x    = x

(≤#) :: Uses -> Uses -> Bool
Zero ≤# x    = True
Once  ≤# Zero = False
Once  ≤# x    = True
Many ≤# Many = True
Many ≤# x    = False

-- Division of multiplicities: x/y is defined as the largest d such that d*y is not larger than x
(/#) :: Uses -> Uses -> Uses
x   /# Zero = Many
x   /# Once  = x
Once /# Many = Zero
x   /# Many = x

-- Subtraction of multiplicities: x-y is defined, if it exists, as the largest d such that d+y is not larger than x
(-#) :: Uses -> Uses -> Maybe Uses
x    -# Zero = Just x
Zero -# x    = Nothing
Once  -# Once  = Just Zero
Once  -# Many = Nothing
Many -# x    = Just Many
