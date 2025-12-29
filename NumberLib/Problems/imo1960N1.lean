import Mathlib
import Mathlib.Tactic

/-- Base-10 digit extractors for a (nonnegative) natural number `n`. -/
def ones (n : Nat) : Nat := n % 10
def tens (n : Nat) : Nat := (n / 10) % 10
def hundreds (n : Nat) : Nat := n / 100

/--
A three-digit number `N` such that:
1) `11 ∣ N`, and
2) `N / 11` equals the sum of squares of the (base-10) digits of `N`.
-/
def ThreeDigit (N : Nat) : Prop := 100 ≤ N ∧ N < 1000

def ProblemProp (N : Nat) : Prop :=
  ThreeDigit N ∧ 11 ∣ N ∧
    N / 11 = (hundreds N)^2 + (tens N)^2 + (ones N)^2

instance (N : Nat) : Decidable (ThreeDigit N) := by
  unfold ThreeDigit
  infer_instance

instance (N : Nat) : Decidable (ProblemProp N) := by
  unfold ProblemProp
  infer_instance

/-- scan S = 10..90, set N = 11*S, filter by the property -/
def solsS : List Nat :=
  ((List.range 81).map (fun t => t + 10))     -- 10..90
    |>.map (fun S => 11 * S)
    |>.filter (fun N => decide (ProblemProp N))

#eval solsS  -- [363, 506, 649, 792]
