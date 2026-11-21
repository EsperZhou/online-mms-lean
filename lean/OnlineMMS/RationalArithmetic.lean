import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Exact nonnegative rational arithmetic with explicit binary-size witnesses.
The witnesses are unreduced fractions; reduction can only shorten them. -/

namespace OnlineMMS.RationalArithmetic

/-- A nonnegative rational has a numerator and positive denominator using at
most `bits` binary digits each. This definition does not assume a cost model. -/
def Bounded (x : ℚ) (bits : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ x = (a : ℚ) / d ∧ a < 2 ^ bits ∧ d < 2 ^ bits

theorem Bounded.nonneg {x : ℚ} {b : ℕ} (hx : Bounded x b) : 0 ≤ x := by
  obtain ⟨a, d, _, rfl, _, _⟩ := hx
  positivity

theorem Bounded.mono {x : ℚ} {b c : ℕ} (hx : Bounded x b) (hbc : b ≤ c) :
    Bounded x c := by
  obtain ⟨a, d, hd, he, ha, hb⟩ := hx
  exact ⟨a, d, hd, he, ha.trans_le (Nat.pow_le_pow_right (by decide) hbc),
    hb.trans_le (Nat.pow_le_pow_right (by decide) hbc)⟩

theorem bounded_zero : Bounded 0 1 := ⟨0, 1, by decide, by norm_num, by decide, by decide⟩
theorem bounded_one : Bounded 1 1 := ⟨1, 1, by decide, by norm_num, by decide, by decide⟩

theorem bounded_nat (a : ℕ) : Bounded (a : ℚ) (a.size + 1) := by
  refine ⟨a, 1, by decide, by simp, ?_, ?_⟩
  · exact (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact Nat.one_lt_pow (by omega) (by decide)

private theorem mul_lt_pow {a d b c : ℕ} (ha : a < 2 ^ b) (hd : d < 2 ^ c) :
    a * d < 2 ^ (b + c) := by
  rw [pow_add]
  calc
    a * d ≤ a * 2 ^ c := Nat.mul_le_mul_left _ hd.le
    _ < 2 ^ b * 2 ^ c := Nat.mul_lt_mul_of_pos_right ha (by positivity)

theorem Bounded.mul {x y : ℚ} {b c : ℕ} (hx : Bounded x b) (hy : Bounded y c) :
    Bounded (x * y) (b + c) := by
  obtain ⟨a, d, hd, rfl, ha, hdb⟩ := hx
  obtain ⟨e, f, hf, rfl, he, hfc⟩ := hy
  refine ⟨a * e, d * f, Nat.mul_pos hd hf, ?_, mul_lt_pow ha he, mul_lt_pow hdb hfc⟩
  push_cast
  ring

theorem Bounded.add {x y : ℚ} {b c : ℕ} (hx : Bounded x b) (hy : Bounded y c) :
    Bounded (x + y) (b + c + 1) := by
  obtain ⟨a, d, hd, rfl, ha, hdb⟩ := hx
  obtain ⟨e, f, hf, rfl, he, hfc⟩ := hy
  have hdq : (d : ℚ) ≠ 0 := by positivity
  have hfq : (f : ℚ) ≠ 0 := by positivity
  refine ⟨a * f + e * d, d * f, Nat.mul_pos hd hf, ?_, ?_, ?_⟩
  · push_cast
    field_simp
  · have h₁ := mul_lt_pow ha hfc
    have h₂ := mul_lt_pow he hdb
    rw [Nat.add_comm c b] at h₂
    rw [pow_succ]
    omega
  · exact (mul_lt_pow hdb hfc).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

theorem Bounded.div {x y : ℚ} {b c : ℕ} (hx : Bounded x b) (hy : Bounded y c)
    (hypos : 0 < y) : Bounded (x / y) (b + c) := by
  obtain ⟨a, d, hd, rfl, ha, hdb⟩ := hx
  obtain ⟨e, f, hf, rfl, he, hfc⟩ := hy
  have hepos : 0 < e := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hypos
  refine ⟨a * f, d * e, Nat.mul_pos hd hepos, ?_, mul_lt_pow ha hfc,
    mul_lt_pow hdb he⟩
  push_cast
  field_simp

theorem Bounded.min {x y : ℚ} {b : ℕ} (hx : Bounded x b) (hy : Bounded y b) :
    Bounded (min x y) b := by
  rcases le_total x y with h | h
  · simpa [min_eq_left h] using hx
  · simpa [min_eq_right h] using hy

theorem bounded_sum (xs : List ℚ) (b : ℕ) (hx : ∀ x ∈ xs, Bounded x b) :
    Bounded xs.sum ((b + 1) * xs.length + 1) := by
  induction xs with
  | nil => simpa using bounded_zero
  | cons x xs ih =>
    have h := (hx x (by simp)).add (ih (fun y hy => hx y (by simp [hy])))
    simpa only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one] using
      h.mono (by omega)

theorem bounded_prod (xs : List ℚ) (b : ℕ) (hx : ∀ x ∈ xs, Bounded x b) :
    Bounded xs.prod (b * xs.length + 1) := by
  induction xs with
  | nil => simpa using bounded_one
  | cons x xs ih =>
    have h := (hx x (by simp)).mul (ih (fun y hy => hx y (by simp [hy])))
    simpa only [List.prod_cons, List.length_cons, Nat.mul_add, Nat.mul_one] using
      h.mono (by omega)

/-- The bit-size interpretation of the exact fraction witnesses. -/
theorem Bounded.encoding {x : ℚ} {b : ℕ} (hx : Bounded x b) :
    ∃ a d : ℕ, 0 < d ∧ x = (a : ℚ) / d ∧ a.size + d.size ≤ 2 * b := by
  obtain ⟨a, d, hd, he, ha, hb⟩ := hx
  exact ⟨a, d, hd, he, by have := Nat.size_le.mpr ha; have := Nat.size_le.mpr hb; omega⟩

/-- Canonical `Rat` numerator and denominator are no larger than the fraction
witnesses, so the bounds apply to the values used by executable rational code. -/
theorem Bounded.canonical_digits {x : ℚ} {b : ℕ} (hx : Bounded x b) :
    x.num.natAbs.size ≤ b ∧ x.den.size ≤ b := by
  obtain ⟨a, d, hd, he, ha, hdb⟩ := hx
  have he' : x = Rat.divInt (a : ℤ) (d : ℤ) := by simpa [Rat.divInt_eq_div] using he
  have hdd : x.den ∣ d := by
    have h := Rat.den_dvd (a : ℤ) (d : ℤ)
    rw [← he'] at h
    exact_mod_cast h
  have hden : x.den ≤ d := Nat.le_of_dvd hd hdd
  have hnum : x.num.natAbs ≤ a := by
    by_cases haz : a = 0
    · simp [haz] at he
      simp [he]
    · have h := Rat.num_dvd (a : ℤ) (show (d : ℤ) ≠ 0 by positivity)
      rw [← he'] at h
      have habs : x.num.natAbs ∣ a := by
        simpa using Int.natAbs_dvd_natAbs.mpr h
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero haz) habs
  exact ⟨Nat.size_le.mpr (hnum.trans_lt ha), Nat.size_le.mpr (hden.trans_lt hdb)⟩

/-- A fixed denominator is preserved by all integer-grid updates. -/
def OnGrid (D : ℕ) (x : ℚ) : Prop := ∃ a : ℤ, x = (a : ℚ) / D

theorem onGrid_zero (D : ℕ) : OnGrid D 0 := ⟨0, by simp⟩

theorem OnGrid.add {D : ℕ} {x y : ℚ} (hx : OnGrid D x) (hy : OnGrid D y) :
    OnGrid D (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; ring⟩

theorem OnGrid.sub {D : ℕ} {x y : ℚ} (hx : OnGrid D x) (hy : OnGrid D y) :
    OnGrid D (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; ring⟩

theorem OnGrid.max {D : ℕ} {x y : ℚ} (hx : OnGrid D x) (hy : OnGrid D y) :
    OnGrid D (max x y) := by
  rcases le_total x y with h | h
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left h] using hx

theorem onGrid_nat {D : ℕ} (hD : 0 < D) (a : ℕ) : OnGrid D (a : ℚ) := by
  refine ⟨(a : ℤ) * D, ?_⟩
  push_cast
  field_simp

theorem onGrid_sum (D : ℕ) (xs : List ℚ) (hx : ∀ x ∈ xs, OnGrid D x) :
    OnGrid D xs.sum := by
  induction xs with
  | nil => simpa using onGrid_zero D
  | cons x xs ih =>
    exact (hx x (by simp)).add (ih (fun y hy => hx y (by simp [hy])))

theorem OnGrid.div_nat {D H : ℕ} {x : ℚ} (hx : OnGrid D x) :
    OnGrid (D * H) (x / H) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, by push_cast; ring⟩

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size :=
  Nat.size_le.mpr (mul_lt_pow (Nat.lt_size_self a) (Nat.lt_size_self b))

theorem OnGrid.enlarge {D H : ℕ} {x : ℚ} (hx : OnGrid D x) (hH : 0 < H) :
    OnGrid (D * H) x := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a * H, ?_⟩
  push_cast
  exact (mul_div_mul_right (a : ℚ) (D : ℚ) (show (H : ℚ) ≠ 0 by positivity)).symm

theorem OnGrid.bounded {D : ℕ} {x : ℚ} (hD : 0 < D) (hx : OnGrid D x)
    (hlo : 0 ≤ x) (hhi : x ≤ 1) : Bounded x (D.size + 1) := by
  obtain ⟨a, rfl⟩ := hx
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have ha0 : (0 : ℤ) ≤ a := by
    have haQ := (le_div_iff₀ hDq).mp hlo
    norm_num at haQ
    exact_mod_cast haQ
  have haD : a ≤ (D : ℤ) := by
    exact_mod_cast (div_le_one hDq).mp hhi
  refine ⟨a.toNat, D, hD, ?_, ?_, ?_⟩
  · have he : (a.toNat : ℚ) = (a : ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha0
    rw [he]
  · have hle : a.toNat ≤ D := by omega
    exact hle.trans_lt ((Nat.lt_size_self D).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))
  · exact (Nat.lt_size_self D).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end OnlineMMS.RationalArithmetic
