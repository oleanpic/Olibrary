import Mathlib

open Int

/-- If `d ∣ a` and `d ∣ b`, then `d ∣ (a - k*b)` for any integer `k`. -/
lemma Int.dvd_sub_mul {d a b k : ℤ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a - k * b := by
  have hkb : d ∣ k * b := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := k) (c := b) hb)
  exact dvd_sub ha hkb

/-- If `d` divides both `a` and `b`,
  then `d` divides any integer linear combination `x*a + y*b`. -/
lemma Int.dvd_linear_comb {d a b x y : ℤ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ x * a + y * b := by
  have hxa : d ∣ x * a := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := x) (c := a) ha)
  have hyb : d ∣ y * b := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := y) (c := b) hb)
  exact Int.dvd_add hxa hyb

/-- If `d ∣ a` and `d ∣ b` in `ℕ`, then `(d:ℤ)` divides any integer linear combination
`x*(a:ℤ) + y*(b:ℤ)`. -/
lemma Nat.cast_dvd_int_linear_comb {d a b : ℕ} {x y : ℤ}
    (ha : d ∣ a) (hb : d ∣ b) :
    (d : ℤ) ∣ x * (a : ℤ) + y * (b : ℤ) := by
  -- cast the divisibility hypotheses to ℤ
  have haZ : (d : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha
  have hbZ : (d : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  -- now use your ℤ-lemma
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Int.dvd_linear_comb (d := (d : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) (x := x) (y := y) haZ hbZ)

/-- A natural number, coerced to `ℤ`, cannot be `-1`. -/
lemma Int.ofNat_ne_neg_one (d : ℕ) : (d : ℤ) ≠ (-1 : ℤ) := by
  intro hd
  have hnonneg : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have : (0 : ℤ) ≤ (-1 : ℤ) := by simp [hd] at hnonneg
  have : ¬ ((0 : ℤ) ≤ (-1 : ℤ)) := by decide
  exact this ‹(0 : ℤ) ≤ (-1 : ℤ)›

/-- Handy criterion: if every common divisor of `a` and `b` divides `1`,
  then `a` and `b` are coprime. -/
lemma Nat.coprime_of_forall_dvd {a b : ℕ}
    (h : ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ 1) : Nat.Coprime a b := by
  have hg1 : Nat.gcd a b ∣ 1 :=
    h (Nat.gcd a b) (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
  exact Nat.coprime_iff_gcd_eq_one.2 (Nat.dvd_one.mp hg1)
