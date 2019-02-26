
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Simple image convolution.
-- Much material from Dave Banas's concat-learn

module Image where

import GHC.Float (float2Double)
import GHC.Generics ((:.:)(..))
import GHC.TypeLits
import Data.Maybe (fromMaybe)
import Data.Typeable (Proxy(..))

import Data.Vector.Sized (Vector, toSized, fromSized)
import qualified Data.Vector.Sized as VS
import Data.Vector.Storable (convert)

import qualified Data.Vector       as V

import Codec.Picture ( convertRGB8 )
import Codec.Picture.Types
  (DynamicImage(ImageYF), Image(..), PixelF , dynamicMap, pixelAt, promoteImage , extractLumaPlane)


-- | A 2D array represented as a composition of sized vectors.
type Arr m n = Vector m :.: Vector n

{--------------------------------------------------------------------
    Conversion between Arr m n a and DynamicImage (JuicyPixels)
--------------------------------------------------------------------}

imgToArr :: (KnownNat m, KnownNat n, Fractional a) => DynamicImage -> Arr m n a
imgToArr im = Comp1 $
  gen "the matrix" height $ \ y ->
  gen "a row"      width  $ \ x ->
  realToFrac $ pixelAt dat x y
  where
    width  = dynamicMap imageWidth  im
    height = dynamicMap imageHeight im
    dat    = (promoteImage . extractLumaPlane . convertRGB8) im :: Image PixelF

gen :: forall s a. KnownNat s => String -> Int -> (Int -> a) -> Vector s a
gen str dim = fromMaybe (error ("Failed to generate " ++ str ++ "."))
            . toSized
            . V.generate dim

arrToImg :: forall m n a. (KnownNat m, KnownNat n, Real a) => Arr m n a -> DynamicImage
arrToImg (Comp1 arr) = ImageYF $ Image
  { imageWidth  = int @n
  , imageHeight = int @m
  , imageData   = (convert . fromSized . fmap realToFrac . VS.concatMap id) arr
  }

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}

-- Move some or all elsewhere

nat :: forall n. KnownNat n => Integer
nat = natVal (Proxy @n)
{-# INLINE nat #-}

int :: forall n. KnownNat n => Int
int = fromIntegral (nat @n)
{-# INLINE int #-}
