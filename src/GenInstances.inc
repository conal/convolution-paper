-- CPP macros for generating instances of Semiring, etc

#define Nums(t) \
instance Additive (t) where { (<+>) = (+) ; zero = 0 } ; \
instance DetectableZero (t) where { isZero = (== 0)} ; \
instance Semiring (t) where { (<.>) = (*) ; one  = 1 }


#define FunctorSemimodule(f) \
instance Semiring zz => Semimodule zz ((f) zz)

#define FunctorStar(f) \
instance (Semiring ((f) qq), Ok (f) qq, StarSemiring qq) => StarSemiring ((f) qq) where \
  { star = fmapC star; plus = fmapC plus }

-- Additive, Semimodule, Semiring from Applicative
#define ApplSemi(f) \
instance Additive zz => Additive ((f) zz) where \
  { (<+>) = liftA2C (<+>) ; zero = pureC zero } ; \
FunctorSemimodule(f) ; \
instance Semiring zz => Semiring ((f) zz) where \
  { (<.>) = liftA2C (<.>) ; one = pureC one } ; \
FunctorStar(f)


#define FoldableZero(f) \
instance Additive ((f) qq) => DetectableZero ((f) qq) where \
  { isZero = null } ; \

-- Additive from Monoid
#define ApplMono(f) \
instance Monoid ((f) qq) => Additive ((f) qq) where \
  { zero = mempty ; (<+>) = (<>) } ; \
FoldableZero(f) ; \
instance (ApplicativeC f, Ok f qq, Monoid qq) => Semiring ((f) qq) where \
  { one = pureC mempty ; (<.>) = liftA2C (<>) } ; \
FunctorStar(f)
