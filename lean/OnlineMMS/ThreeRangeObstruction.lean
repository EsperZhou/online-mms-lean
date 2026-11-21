import OnlineMMS.Model
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS.ThreeRange

noncomputable def score (q η x : ℝ) : ℝ :=
  if x < q / 2 then η * x else if x < q then 1 / 2 else 1

def Initializes (q η : ℝ) : Prop :=
  ∀ m (v : Fin m → ℝ), (∀ g, 0 ≤ v g) → ∀ R : Finset (Fin m),
    1 ≤ bundleValue v R → 1 ≤ bundleValue (fun g => score q η (v g)) R

def Packs (q η : ℝ) : Prop :=
  ∀ m (v : Fin m → ℝ), (∀ g, 0 ≤ v g) → ∀ (r : ℕ) (R : Finset (Fin m)),
    (r : ℝ) ≤ bundleValue (fun g => score q η (v g)) R →
    ∃ B : Fin r → Finset (Fin m), Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∀ j, B j ⊆ R ∧ q ≤ bundleValue v (B j) ∧
        (r : ℝ) - 1 ≤ bundleValue (fun g => score q η (v g)) (R \ B j)

private theorem initializes_forces {q η : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hη : 0 ≤ η) (hi : Initializes q η) : 1 / 2 ≤ η * (1 - q) := by
  by_contra! hsmall
  let ε := min (q / 4) ((1 / 2 - η * (1 - q)) / (2 * (η + 1)))
  have he : 0 < ε := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have heq : ε ≤ q / 4 := min_le_left ..
  have hηe : η * ε < 1 / 2 - η * (1 - q) := by
    have hbound : ε ≤ (1 / 2 - η * (1 - q)) / (2 * (η + 1)) := min_le_right ..
    have hmul := (le_div_iff₀ (show 0 < (2 : ℝ) * (η + 1) by positivity)).mp hbound
    nlinarith only [hmul, he, hη, mul_nonneg he.le hη]
  let L := 1 - q + ε
  have hL : 0 < L := by dsimp [L]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (L / (q / 2))
  have hmR : 0 < (m : ℝ) := (div_pos hL (by positivity)).trans hm
  let light := L / m
  have hl : 0 < light := div_pos hL hmR
  have hlt : light < q / 2 := by
    apply (div_lt_iff₀ hmR).mpr
    have hh := (div_lt_iff₀ (show 0 < q / 2 by positivity)).mp hm
    linarith
  let v : Fin (m + 1) → ℝ := Fin.snoc (fun _ : Fin m => light) (q - ε)
  have hval : bundleValue v Finset.univ = 1 := by
    unfold bundleValue
    rw [Fin.sum_univ_castSucc]
    have he' : (m : ℝ) * light = L := by dsimp [light]; field_simp
    simp [v, nsmul_eq_mul, he', L]
  have hv : ∀ g, 0 ≤ v g := by
    intro g
    refine Fin.lastCases ?_ (fun i => ?_) g
    · simp [v]; linarith
    · simpa [v] using hl.le
  have hscore : bundleValue (fun g => score q η (v g)) Finset.univ = 1 / 2 + η * L := by
    have he' : (m : ℝ) * light = L := by dsimp [light]; field_simp
    unfold bundleValue
    rw [Fin.sum_univ_castSucc]
    simp [v, score, hlt, show ¬ (q - ε < q / 2) by linarith,
      show q - ε < q by linarith, nsmul_eq_mul]
    linear_combination η * he'
  have h := hi _ v hv Finset.univ hval.ge
  rw [hscore] at h
  dsimp [L] at h
  nlinarith only [h, hηe]

private theorem packing_fails {q η : ℝ} (hq : 0 < q) (hηq : 3 / 5 < η * q) :
    ¬ Packs q η := by
  classical
  have hη : 0 < η := by
    by_contra! hn
    have hh := mul_nonpos_of_nonpos_of_nonneg hn hq.le
    linarith
  let L := 3 / (10 * η)
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : L < q / 2 := by
    dsimp [L]
    apply (div_lt_iff₀ (show 0 < 10 * η by positivity)).mpr
    nlinarith only [hηq]
  have hlight : score q η L = 3 / 10 := by
    rw [score, if_pos hsmall]
    dsimp [L]
    field_simp
    ring
  have hmed : score q η (q / 2) = 1 / 2 := by
    simp [score, show q / 2 < q by linarith]
  let v : Fin 6 → ℝ := fun g => if g = 0 then q / 2 else L
  let w := fun g => score q η (v g)
  have hv (g : Fin 6) : 0 ≤ v g := by
    unfold v
    split
    · positivity
    · exact hL.le
  have hsum (B : Finset (Fin 6)) :
      bundleValue v B = (if (0 : Fin 6) ∈ B then q / 2 else 0) +
        ((B.erase 0).card : ℝ) * L ∧
      bundleValue w B = (if (0 : Fin 6) ∈ B then 1 / 2 else 0) +
        ((B.erase 0).card : ℝ) * (3 / 10) := by
    have hV : (∑ g ∈ B.erase 0, v g) = ((B.erase 0).card : ℝ) * L := by
      calc
        _ = ∑ _g ∈ B.erase 0, L := Finset.sum_congr rfl (fun g hg => by simp [v, (Finset.mem_erase.mp hg).1])
        _ = _ := by simp [nsmul_eq_mul]
    have hW : (∑ g ∈ B.erase 0, w g) = ((B.erase 0).card : ℝ) * (3 / 10) := by
      calc
        _ = ∑ _g ∈ B.erase 0, (3 / 10 : ℝ) := Finset.sum_congr rfl (fun g hg =>
          by simp [w, v, (Finset.mem_erase.mp hg).1, hlight])
        _ = _ := by simp [nsmul_eq_mul]
    by_cases hb : (0 : Fin 6) ∈ B
    · have hV' := Finset.sum_erase_add B v hb
      have hW' := Finset.sum_erase_add B w hb
      have hv0 : v 0 = q / 2 := by simp [v]
      have hw0 : w 0 = 1 / 2 := by simp [w, v, hmed]
      rw [hV, hv0] at hV'
      rw [hW, hw0] at hW'
      simp only [if_pos hb, bundleValue]
      exact ⟨by linarith, by linarith⟩
    · rw [Finset.erase_eq_of_not_mem hb] at hV hW ⊢
      simpa [hb, bundleValue] using And.intro hV hW
  have hall : bundleValue w (Finset.univ : Finset (Fin 6)) = 2 := by
    rw [(hsum Finset.univ).2]
    have hc : (Finset.univ.erase (0 : Fin 6)).card = 5 := by decide
    norm_num [hc]
  intro hp
  obtain ⟨B, hdis, hB⟩ := hp 6 v hv 2 Finset.univ (by simpa using hall.ge)
  have hthree (i : Fin 2) : 3 ≤ ((B i).erase 0).card := by
    obtain ⟨hsub, hpay, hleft⟩ := hB i
    have hs := Finset.sum_sdiff hsub (f := w)
    change bundleValue w (Finset.univ \ B i) + bundleValue w (B i) = bundleValue w Finset.univ at hs
    have hb : bundleValue w (B i) ≤ 1 := by rw [hall] at hs; norm_num at hleft; linarith
    obtain ⟨heV, heW⟩ := hsum (B i)
    by_cases hz : (0 : Fin 6) ∈ B i
    · rw [heW, if_pos hz] at hb
      have hc : ((B i).erase 0).card ≤ 1 := by
        by_contra! h
        have hcast : (2 : ℝ) ≤ ((B i).erase 0).card := by exact_mod_cast h
        linarith
      have hcast : (((B i).erase 0).card : ℝ) ≤ 1 := by exact_mod_cast hc
      rw [heV, if_pos hz] at hpay
      have hcost := mul_le_mul_of_nonneg_right hcast hL.le
      nlinarith only [hpay, hcost, hsmall]
    · by_contra! hc
      have hcast : (((B i).erase 0).card : ℝ) ≤ 2 := by exact_mod_cast (show ((B i).erase 0).card ≤ 2 by omega)
      rw [heV, if_neg hz] at hpay
      have hcost := mul_le_mul_of_nonneg_right hcast hL.le
      nlinarith only [hpay, hcost, hsmall]
  let X := (B 0).erase (0 : Fin 6)
  let Y := (B 1).erase (0 : Fin 6)
  have hd : Disjoint X Y := (hdis (by decide : (0 : Fin 2) ≠ 1)).mono
    (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hsub : X ∪ Y ⊆ Finset.univ.erase (0 : Fin 6) := by
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hc5 : (Finset.univ.erase (0 : Fin 6)).card = 5 := by decide
  rw [hc5] at hc
  have h0 : 3 ≤ X.card := hthree 0
  have h1 : 3 ≤ Y.card := hthree 1
  omega

/-- No choice of the slope certifies both requirements above six elevenths. -/
theorem three_range_obstruction {q η : ℝ} (hq : 6 / 11 < q) (hq1 : q < 1)
    (hη : 0 ≤ η) : ¬ (Initializes q η ∧ Packs q η) := by
  rintro ⟨hi, hp⟩
  have hq0 : 0 < q := by linarith
  have hl := initializes_forces hq0 hq1 hη hi
  have hηq : 3 / 5 < η * q := by
    by_contra! hh
    have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ q by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 - q by linarith)
    nlinarith only [hl', hh', hq]
  exact packing_fails hq0 hηq hp

end OnlineMMS.ThreeRange
