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
