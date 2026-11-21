import OnlineMMS.TwoTypeRationalScales
import Mathlib.Data.Nat.Size

namespace OnlineMMS.TwoType

def valuationDigits {m : ℕ} (v : Fin m → ℚ) : ℕ :=
  ∑ g, ((v g).num.natAbs.size + (v g).den.size)

def scaleScanLimit {m : ℕ} (v : Fin m → ℚ) : ℕ := 2 * valuationDigits v + m

private theorem digit_bounds {m : ℕ} (v : Fin m → ℚ) (g : Fin m) (h : 0 ≤ v g) :
    (v g : ℝ) ≤ 2 ^ valuationDigits v ∧
      (0 < v g → 1 / (2 : ℝ) ^ valuationDigits v ≤ (v g : ℝ)) := by
  have hh : (v g).num.natAbs.size + (v g).den.size ≤ valuationDigits v := by
    unfold valuationDigits
    exact Finset.single_le_sum (fun i _ => Nat.zero_le
      ((v i).num.natAbs.size + (v i).den.size)) (Finset.mem_univ g)
  have hA := Nat.size_le.mp (show (v g).num.natAbs.size ≤ valuationDigits v by omega)
  have hB := Nat.size_le.mp (show (v g).den.size ≤ valuationDigits v by omega)
  have hn : 0 ≤ (v g).num := Rat.num_nonneg.mpr h
  have he : ((v g).num.natAbs : ℤ) = (v g).num := Int.natAbs_of_nonneg hn
  have hd : (0 : ℝ) < (v g).den := by exact_mod_cast (v g).pos
  have hdn : (1 : ℝ) ≤ (v g).den := by exact_mod_cast (v g).pos
  have hAreal : ((v g).num : ℝ) < (2 : ℝ) ^ valuationDigits v := by
    rw [← he]
    exact_mod_cast hA
  have hBreal : ((v g).den : ℝ) < (2 : ℝ) ^ valuationDigits v := by exact_mod_cast hB
  rw [Rat.cast_def]
  constructor
  · exact (div_le_self (by exact_mod_cast hn) hdn).trans hAreal.le
  · intro hp
    have hnpos := Rat.num_pos.mpr hp
    have h1 : (1 : ℝ) ≤ ((v g).num : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ (v g).num by omega)
    exact (div_le_div_of_nonneg_left zero_le_one hd hBreal.le).trans
      (div_le_div_of_nonneg_right h1 hd.le)

theorem scaleScanLimit_spec {m n : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (g : Fin m) (hpos : 0 < v g) :
    ((∑ i, (v i : ℝ)) / (n : ℝ)) < (v g : ℝ) * 2 ^ scaleScanLimit v := by
  let B := valuationDigits v
  let U : ℝ := (∑ i, (v i : ℝ)) / (n : ℝ)
  have hs : (∑ i, (v i : ℝ)) ≤ (m : ℝ) * 2 ^ B := by
    calc
      _ ≤ ∑ _i : Fin m, (2 : ℝ) ^ B := Finset.sum_le_sum fun i _ => (digit_bounds v i (hv i)).1
      _ = _ := by simp [nsmul_eq_mul]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hu : U ≤ (m : ℝ) * 2 ^ B :=
    (div_le_self (Finset.sum_nonneg (fun i _ => by exact_mod_cast hv i)) hnR).trans hs
  have hm : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m))
  have hp := mul_lt_mul_of_pos_right hm (show 0 < (2 : ℝ) ^ B by positivity)
  have ha := (digit_bounds v g (hv g)).2 hpos
  have hposB : (2 : ℝ) ^ B ≠ 0 := by positivity
  have he : (2 : ℝ) ^ m * 2 ^ B = (1 / (2 : ℝ) ^ B) * 2 ^ (2 * B + m) := by
    rw [show 2 * B + m = B + (m + B) by omega, pow_add, pow_add]
    field_simp
  change U < (v g : ℝ) * 2 ^ (2 * B + m)
  exact (hu.trans_lt hp).trans_le (he ▸ mul_le_mul_of_nonneg_right ha (by positivity))

def positiveValues {m : ℕ} (v : Fin m → ℚ) : Finset ℚ :=
  (Finset.univ.image v).filter (fun a => 0 < a)

/-- Executable preprocessing, including the zero-scale case when there
are too few positive goods. -/
def rationalScale {m : ℕ} (v : Fin m → ℚ) (n : ℕ) : ℚ :=
  if hp : (positiveValues v).Nonempty then
    if n ≤ (Finset.univ.filter (fun g => 0 < v g)).card then
      rationalScaleFrom v n (scaleScanLimit v) ((positiveValues v).min' hp)
    else 0
  else 0

private theorem admissibleScale_enough_goods {m n : ℕ} {v : Fin m → ℝ} {y : ℝ}
    (ha : AdmissibleScale v n y) :
    n ≤ (Finset.univ.filter (fun g => 0 < v g)).card := by
  classical
  have hsum : bundleValue (fun g => score (v g / y)) Finset.univ ≤
      ((Finset.univ.filter (fun g => 0 < v g)).card : ℝ) := by
    unfold bundleValue
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro g _
    by_cases hp : 0 < v g
    · simp only [hp, if_true, Nat.cast_one]
      by_cases h : 1 ≤ v g / y
      · simp [score, h, zero_lt_one.trans_le h]
      · exact (score_le_value (div_nonneg hp.le ha.1.le)).trans (le_of_not_ge h)
    · have hn : ¬ 0 < v g / y := by
        exact not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) ha.1.le)
      simp [score, hp, hn]
  exact_mod_cast ha.2.trans hsum

/-- Preprocessing returns either the greatest admissible positive scale
or zero when no positive scale is possible. -/
theorem rationalScale_spec {m n : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    (rationalScale v n = 0 ∧ ∀ y, ¬ AdmissibleScale (fun g => (v g : ℝ)) n y) ∨
      IsGreatest {y : ℝ | AdmissibleScale (fun g => (v g : ℝ)) n y}
        (rationalScale v n : ℝ) := by
  classical
  let C := (Finset.univ.filter (fun g => 0 < v g)).card
  have hcounts (y : ℝ) (h : AdmissibleScale (fun g => (v g : ℝ)) n y) : n ≤ C := by
    simpa [C] using admissibleScale_enough_goods h
  by_cases hC : n ≤ C
  · obtain ⟨g, hg⟩ := Finset.card_pos.mp (hn.trans_le hC)
    have hvg : 0 < v g := (Finset.mem_filter.mp hg).2
    have hne : (positiveValues v).Nonempty :=
      ⟨v g, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hvg⟩⟩
    let a := (positiveValues v).min' hne
    have haMem := Finset.mem_filter.mp (Finset.min'_mem (positiveValues v) hne)
    have hmin (i : Fin m) (hi : 0 < v i) : a ≤ v i :=
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp haMem.1
    have hcut := scaleScanLimit_spec v hv hn j (hj ▸ haMem.2)
    rw [hj] at hcut
    right
    have he : rationalScale v n = rationalScaleFrom v n (scaleScanLimit v) a := by
      unfold rationalScale
      rw [dif_pos hne, if_pos hC]
    rw [he]
    exact rationalScaleFrom_correct v hn hv haMem.2 hmin hC hcut
  · left
    refine ⟨?_, fun y h => hC (hcounts y h)⟩
    unfold rationalScale
    split <;> simp [show ¬ n ≤ (Finset.univ.filter (fun g => 0 < v g)).card from hC]

/-- The bounded score scanner is exact at the computed scale. -/
theorem rationalScale_tag_correct {m n : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g) (hn : 0 < n)
    (g : Fin m) :
    let y := rationalScale v n
    (roundedTagRat (scaleScanLimit v) (v g / y)).elim 0 PacketLevel.weight =
      score ((v g : ℝ) / (y : ℝ)) := by
  let y := rationalScale v n
  have hs := rationalScale_spec v hv hn
  have hy : 0 ≤ y := by
    rcases hs with ⟨hzero, _⟩ | h
    · simp [y, hzero]
    · have hpos := h.1.1
      change 0 < (y : ℝ) at hpos
      exact_mod_cast hpos.le
  change (roundedTagRat (scaleScanLimit v) (v g / y)).elim 0 PacketLevel.weight =
    score ((v g : ℝ) / (y : ℝ))
  rw [← Rat.cast_div]
  apply roundedTagRat_weight _ _ (div_nonneg (hv g) hy)
  intro hpos
  obtain ⟨_, hnzero⟩ : 0 < v g ∧ 0 < y := by
    have h := (div_pos_iff (α := ℚ)).1 hpos
    rcases h with h | h
    · exact h
    · exact ((not_lt_of_ge (hv g)) h.1).elim
  rcases hs with ⟨hzero, _⟩ | hh
  · exact ((ne_of_gt hnzero) hzero).elim
  have hU := admissibleScale_le_average hn (fun i => by exact_mod_cast hv i) hh.1
  have hcut := scaleScanLimit_spec v hv hn g ((div_pos_iff_of_pos_right hnzero).mp hpos)
  rw [Rat.cast_div, dyadic]
  apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast hnzero)).mpr
  simpa only [one_mul] using hU.trans hcut.le

end OnlineMMS.TwoType
