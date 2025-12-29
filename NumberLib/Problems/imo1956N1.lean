import Mathlib
import NumberLib.Divisibility.EuclideanAlgorithm
/-!
# IMO 1956 Problem 1

Prove that the fraction `(21n+4)/(14n+3)` is irreducible for every natural number `n`.
Equivalently, `Coprime (21*n+4) (14*n+3)` for all `n : ℕ`.
-/

theorem imo1956_p1 (n : ℕ) : Nat.Coprime (21 * n + 4) (14 * n + 3) := by
  refine NumberLib.coprime_of_forall_dvd (a := 21 * n + 4) (b := 14 * n + 3) (fun d hda hdb => ?_)
  let E : ℤ :=
    (-2 : ℤ) * ((21 * n + 4 : ℕ) : ℤ) + (3 : ℤ) * ((14 * n + 3 : ℕ) : ℤ)
  have hdEz : (d : ℤ) ∣ E := by
    simpa [E] using
      (NumberLib.cast_dvd_int_linear_comb
        (d := d) (a := 21 * n + 4) (b := 14 * n + 3) (x := (-2 : ℤ)) (y := (3 : ℤ)) hda hdb)
  have hE1 : E = (1 : ℤ) := by
    simp [E]
    ring
  have hd1 : (d : ℤ) ∣ (1 : ℤ) := hE1 ▸ hdEz
  exact (by exact_mod_cast hd1 : d ∣ 1)
