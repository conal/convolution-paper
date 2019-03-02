{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Simple image convolution.
-- Much material from Dave Banas's concat-learn

module Image where

import Control.Applicative (liftA2)
import GHC.Float (float2Double)
import GHC.Generics ((:.:)(..))
import GHC.TypeLits (KnownNat)
import Data.Maybe (fromMaybe)
import Data.Typeable (Proxy(..))

-- import Data.Vector.Sized (Vector, toSized, fromSized)
-- import qualified Data.Vector.Sized as VS
-- import Data.Vector.Storable (convert)

import qualified Data.Vector       as V

import Codec.Picture ( convertRGB8 )
import Codec.Picture.Types
  (DynamicImage(ImageYF), Image(..), PixelF , dynamicMap, pixelAt, promoteImage , extractLumaPlane)
import Data.Vector.Storable             (convert)

import Misc
import Semi

-- Start with lists of lists.

-- | A 2D array represented as a list of lists
type Arr b = [[b]]

{--------------------------------------------------------------------
    Conversion between [[b]] and DynamicImage (JuicyPixels)
--------------------------------------------------------------------}

gen :: Int -> (Int -> a) -> [a]
gen dim f = f <$> [0 .. dim-1]

imgToArr :: Fractional b => DynamicImage -> Arr b
imgToArr im =
  gen height $ \ y ->
  gen width  $ \ x ->
  realToFrac $ pixelAt dat x y
  where
    width  = dynamicMap imageWidth  im
    height = dynamicMap imageHeight im
    dat    = (promoteImage . extractLumaPlane . convertRGB8) im :: Image PixelF

arrToImg :: Real a => Arr a -> DynamicImage
arrToImg arr = ImageYF $ Image
  { imageWidth  = length (head arr)
  , imageHeight = length arr
  , imageData   = (convert . V.fromList . map realToFrac . concat) arr
  }

-- TODO: improve efficiency.

#if 0

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

#endif
