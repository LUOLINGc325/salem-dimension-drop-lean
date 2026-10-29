module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

namespace Salem

/-- A rational closed interval, with transparent arithmetic for exact checking. -/
structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

end Salem

namespace Salem.RationalInterval

def add (I J : RationalInterval) : RationalInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : RationalInterval) : RationalInterval := ⟨-I.hi, -I.lo⟩

def sub (I J : RationalInterval) : RationalInterval := ⟨I.lo - J.hi, I.hi - J.lo⟩

def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

end Salem.RationalInterval

namespace Salem

/-- A rectangular complex enclosure with rational endpoints. -/
structure ComplexRationalBox where
  re : RationalInterval
  im : RationalInterval
  deriving Repr, DecidableEq

end Salem

namespace Salem.ComplexRationalBox

def mul (I J : ComplexRationalBox) : ComplexRationalBox :=
  ⟨(I.re.mul J.re).sub (I.im.mul J.im), (I.re.mul J.im).add (I.im.mul J.re)⟩

def square (I : ComplexRationalBox) : ComplexRationalBox := I.mul I

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

/-- Outward rounding to denominator `D`; the floor and ceiling are exact rationals. -/
def round (D : ℕ) (I : RationalInterval) : RationalInterval :=
  ⟨(⌊I.lo * (D : ℚ)⌋ : ℚ) / (D : ℚ), (⌈I.hi * (D : ℚ)⌉ : ℚ) / (D : ℚ)⟩

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

def one : ComplexRationalBox := ⟨⟨1, 1⟩, ⟨0, 0⟩⟩

def round (D : ℕ) (I : ComplexRationalBox) : ComplexRationalBox :=
  ⟨I.re.round D, I.im.round D⟩

/-- Binary exponentiation with exact outward rounding after each multiplication. -/
def powRounded (D : ℕ) (I : ComplexRationalBox) (n : ℕ) : ComplexRationalBox :=
  if hn : n = 0 then one else
    let B := ((powRounded D I (n / 2)).square).round D
    if n % 2 = 0 then B else (B.mul I).round D
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

def point (q : ℚ) : RationalInterval := ⟨q, q⟩

/-- Reciprocal enclosure for a positive interval. -/
def inv (I : RationalInterval) : RationalInterval := ⟨I.hi⁻¹, I.lo⁻¹⟩

/-- A fixed-grid square-root enclosure, computed using the natural square root. -/
def sqrt (D : ℕ) (I : RationalInterval) : RationalInterval :=
  ⟨(Nat.sqrt ⌊I.lo * (D : ℚ) ^ 2⌋₊ : ℚ) / (D : ℚ),
   ((Nat.sqrt ⌈I.hi * (D : ℚ) ^ 2⌉₊ + 1 : ℕ) : ℚ) / (D : ℚ)⟩

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

def add (I J : ComplexRationalBox) : ComplexRationalBox := ⟨I.re.add J.re, I.im.add J.im⟩

def neg (I : ComplexRationalBox) : ComplexRationalBox := ⟨I.re.neg, I.im.neg⟩

def sub (I J : ComplexRationalBox) : ComplexRationalBox := ⟨I.re.sub J.re, I.im.sub J.im⟩

def conj (I : ComplexRationalBox) : ComplexRationalBox := ⟨I.re, I.im.neg⟩

def ofRealInterval (I : RationalInterval) : ComplexRationalBox := ⟨I, RationalInterval.point 0⟩

def normSqInterval (I : ComplexRationalBox) : RationalInterval :=
  (I.re.mul I.re).add (I.im.mul I.im)

def inv (I : ComplexRationalBox) : ComplexRationalBox :=
  ⟨I.re.mul I.normSqInterval.inv, I.im.neg.mul I.normSqInterval.inv⟩

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

def absUpper (I : RationalInterval) : ℚ := max |I.lo| |I.hi|

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

def normSqUpper (I : ComplexRationalBox) : ℚ := I.re.absUpper ^ 2 + I.im.absUpper ^ 2

def ExcludesZero (I : ComplexRationalBox) : Prop :=
  0 < I.re.lo ∨ I.re.hi < 0 ∨ 0 < I.im.lo ∨ I.im.hi < 0

instance (I : ComplexRationalBox) : Decidable I.ExcludesZero :=
  inferInstanceAs (Decidable (0 < I.re.lo ∨ I.re.hi < 0 ∨ 0 < I.im.lo ∨ I.im.hi < 0))

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

/-- Real powers reuse the certified binary complex computation on the real axis. -/
def powRounded (D : ℕ) (I : RationalInterval) (n : ℕ) : RationalInterval :=
  ((ComplexRationalBox.ofRealInterval I).powRounded D n).re

end Salem.RationalInterval
