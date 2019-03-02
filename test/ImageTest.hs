
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | 

module Main where

import qualified Data.Vector as V
import Codec.Picture (convertRGB8, readImage, savePngImage)
import Codec.Picture.Types
  (DynamicImage(ImageYF), Image(..), PixelF , dynamicMap, pixelAt, promoteImage , extractLumaPlane)
import Data.Vector.Storable (convert)

import Semi hiding ((^))

main :: IO ()
main = do convolve "original" ident "wizard"
          convolve "blur" (boxBlur 5) "wizard"
          convolve "sharpen" sharpen "wizard"
          convolve "edge-detect" edgy "wizard"

convolve :: String -> Arr Double -> FilePath -> IO ()
convolve opName kernel origName =
  do img0 <- fmap (either (error ("couldn't read " ++ file)) id) (readImage file)
     savePngImage (origName ++ "-" ++ opName ++ ".png") $
       arrToImg (imgToArr img0 <.> kernel)
 where
   file = origName ++ ".jpg"

ident :: Arr Double
ident = [[1]]

boxBlur :: Int -> Arr Double
boxBlur n = (fmap.fmap) (/ n'^(2::Int)) ((replicate n . replicate n) 1)
 where
   n' :: Double
   n' = fromIntegral n

sharpen :: Arr Double
sharpen = [[0,-1,0],[-1,5,-1],[0,-1,0]]

edgy :: Arr Double
edgy = [[-1,-1,-1],[-1,8,-1],[-1,-1,-1]]

{--------------------------------------------------------------------
    Conversion between [[b]] and DynamicImage (JuicyPixels)
--------------------------------------------------------------------}

-- | A 2D array represented as a list of lists
type Arr b = [[b]]

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
