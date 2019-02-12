-- CPP macros for generating instances of Semiring, etc

-- Instances for numeric types
#define Nums(t) \
instance Additive (t) where { (<+>) = (+) ; zero = 0 } ; \
instance DetectableZero (t) where { isZero = (== 0)} ; \
instance DetectableOne  (t) where { isOne  = (== 1)} ; \
instance Semiring (t) where { (<.>) = (*) ; one  = 1 }

#define FunctorSemimodule(f) \
instance (Semiring zz, Additive ((f) zz)) => LeftSemimodule zz ((f) zz)

#define FunctorStar(f) \
instance (Semiring ((f) qq), Ok (f) qq, StarSemiring qq) => StarSemiring ((f) qq) where \
  { star = fmapC star; plus = fmapC plus }

#define NullZero(f) \
instance Additive ((f) qq) => DetectableZero ((f) qq) where \
  { isZero = null } ; \

-- Additive, LeftSemimodule, Semiring from Applicative
#define ApplSemi(f) \
instance Additive zz => Additive ((f) zz) where \
  { (<+>) = liftA2C (<+>) ; zero = pureC zero } ; \
FunctorSemimodule(f) ; \
instance Semiring zz => Semiring ((f) zz) where \
  { (<.>) = liftA2C (<.>) ; one = pureC one } ; \
FunctorStar(f)

-- TODO: Maybe rely on Pointed and Zip instead of Applicative here, considering
-- these definitions.

-- Additive from Applicative+Monoid+Foldable
#define ApplMono(f) \
instance Monoid ((f) qq) => Additive ((f) qq) where \
  { zero = mempty ; (<+>) = (<>) } ; \
NullZero(f) ; \
instance (ApplicativeC f, Ok f qq, Monoid qq) => Semiring ((f) qq) where \
  { one = pureC mempty ; (<.>) = liftA2C (<>) } ; \
FunctorStar(f)
