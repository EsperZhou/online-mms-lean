import OnlineMMS.TwoTypeRationalScores

namespace OnlineMMS.TwoType

def scaleBreakpointRat {m L : ℕ} (v : Fin m → ℚ)
    (i : Fin m × Fin L × Bool) : ℚ :=
  v i.1 * 2 ^ i.2.1.val * (if i.2.2 then 3 else 1)

def scaleCandidatesRat {m : ℕ} (v : Fin m → ℚ) (a U : ℚ) (L : ℕ) :
    Finset ℚ :=
  insert a (insert U ((Finset.univ.image (scaleBreakpointRat (L := L) v)).filter
    (fun z => a ≤ z ∧ z ≤ U)))

private theorem scaleBreakpointRat_cast {m L : ℕ} (v : Fin m → ℚ)
    (i : Fin m × Fin L × Bool) :
    (scaleBreakpointRat v i : ℝ) = scaleBreakpoint (fun g => (v g : ℝ)) i := by
  unfold scaleBreakpointRat scaleBreakpoint
  split <;> simp_all

private theorem scaleCandidatesRat_rep {m L : ℕ} (v : Fin m → ℚ) (a U : ℚ)
    (z : ℝ) :
    z ∈ scaleCandidates (fun g => (v g : ℝ)) a U L ↔
      ∃ q ∈ scaleCandidatesRat v a U L, (q : ℝ) = z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact ⟨a, Finset.mem_insert_self .., h.symm⟩
    rcases Finset.mem_insert.mp h with h | h
    · exact ⟨U, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), h.symm⟩
    obtain ⟨hm, hz⟩ := Finset.mem_filter.mp h
    obtain ⟨i, _, h⟩ := Finset.mem_image.mp hm
    have hq : (scaleBreakpointRat v i : ℝ) = z := (scaleBreakpointRat_cast v i).trans h
    refine ⟨scaleBreakpointRat v i, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩)), hq⟩
    rw [← hq] at hz
    exact_mod_cast hz
  · rintro ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with h | h
    · exact h ▸ Finset.mem_insert_self ..
    rcases Finset.mem_insert.mp h with h | h
    · exact h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨hm, hq⟩ := Finset.mem_filter.mp h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (scaleBreakpointRat_cast v i).symm⟩,
      by exact_mod_cast hq⟩

theorem scaleCandidatesRat_card {m : ℕ} (v : Fin m → ℚ) (a U : ℚ) (L : ℕ) :
    (scaleCandidatesRat v a U L).card ≤ 2 * m * L + 2 := by
  classical
  have h : (scaleCandidatesRat v a U L).image (fun q : ℚ => (q : ℝ)) =
      scaleCandidates (fun g => (v g : ℝ)) a U L := by
    ext z
    simpa [Finset.mem_image] using (scaleCandidatesRat_rep (L := L) v a U z).symm
  have he := Finset.card_image_of_injective (scaleCandidatesRat v a U L)
    (Rat.cast_injective (α := ℝ))
  rw [h] at he
  rw [← he]
  exact scaleCandidates_card (fun g => (v g : ℝ)) a U L

def scaleFeasibleRat {m : ℕ} (v : Fin m → ℚ) (n L : ℕ) (y : ℚ) : Prop :=
  0 < y ∧ (n : ℚ) ≤ ∑ g, roundedScoreRat L (v g / y)

instance {m : ℕ} (v : Fin m → ℚ) (n L : ℕ) (y : ℚ) :
    Decidable (scaleFeasibleRat v n L y) := by
  unfold scaleFeasibleRat
  infer_instance

/-- Scan breakpoints using rational comparisons. Zero is a fallback if the
input has too few positive goods. -/
def rationalScaleFrom {m : ℕ} (v : Fin m → ℚ) (n L : ℕ) (a : ℚ) : ℚ :=
  let U := (∑ g, v g) / (n : ℚ)
  (insert 0 ((scaleCandidatesRat v a U L).filter (scaleFeasibleRat v n L))).max'
    (Finset.insert_nonempty _ _)

private theorem scaleFeasibleRat_spec {m n L : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    {a U y : ℚ} (ha : 0 < a) (hmin : ∀ g, 0 < v g → a ≤ v g)
    (hL : (U : ℝ) < (a : ℝ) * 2 ^ L) (hay : a ≤ y) (hyU : y ≤ U) :
    scaleFeasibleRat v n L y ↔ AdmissibleScale (fun g => (v g : ℝ)) n (y : ℝ) := by
  have hy := ha.trans_le hay
  have hsum : (↑(∑ g : Fin m, roundedScoreRat L (v g / y)) : ℝ) =
      bundleValue (fun g => score ((v g : ℝ) / (y : ℝ))) Finset.univ := by
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    have hnon := div_nonneg (hv g) hy.le
    rw [roundedScoreRat_correct L _ hnon]
    · push_cast
      rfl
    · intro h
      have hp : 0 < v g := (div_pos_iff_of_pos_right hy).mp h
      have hR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
      have hle : (y : ℝ) ≤ (a : ℝ) * 2 ^ L :=
        (show (y : ℝ) ≤ (U : ℝ) by exact_mod_cast hyU).trans hL.le
      rw [Rat.cast_div, dyadic]
      apply (div_le_div_iff₀ (by positivity) hR).mpr
      simpa [mul_comm] using hle.trans
        (mul_le_mul_of_nonneg_right (show (a : ℝ) ≤ (v g : ℝ) by exact_mod_cast hmin g hp)
          (show (0 : ℝ) ≤ 2 ^ L by positivity))
  simp only [scaleFeasibleRat, AdmissibleScale, ← hsum, Rat.cast_pos, Rat.cast_natCast, Rat.cast_le]
  norm_cast

/-- The rational scan returns the greatest scale when started at the
smallest positive valuation and given the proved exponent cutoff. -/
theorem rationalScaleFrom_correct {m n L : ℕ} (v : Fin m → ℚ)
    (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) {a : ℚ} (ha : 0 < a)
    (hmin : ∀ g, 0 < v g → a ≤ v g)
    (hc : n ≤ (Finset.univ.filter (fun g => 0 < v g)).card)
    (hL : ((∑ g, (v g : ℝ)) / n) < (a : ℝ) * 2 ^ L) :
    IsGreatest {y : ℝ | AdmissibleScale (fun g => (v g : ℝ)) n y}
      (rationalScaleFrom v n L a : ℝ) := by
  classical
  let w : Fin m → ℝ := fun g => v g
  let U : ℚ := (∑ g, v g) / (n : ℚ)
  have hUR : (U : ℝ) = (∑ g, w g) / (n : ℝ) := by simp [U, w]
  have hw (g : Fin m) : 0 ≤ w g := by dsimp [w]; exact_mod_cast hv g
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hminR (g : Fin m) (hg : 0 < w g) : (a : ℝ) ≤ w g := by
    dsimp [w] at hg ⊢
    exact_mod_cast hmin g (by exact_mod_cast hg)
  have hFeas : AdmissibleScale w n (a : ℝ) := by
    apply admissibleScale_of_smallest haR hminR
    simpa [w] using hc
  have haU : a ≤ U := by
    have h := admissibleScale_le_average hn hw hFeas
    change (a : ℝ) ≤ (∑ g, w g) / ↑n at h
    rw [← hUR] at h
    exact_mod_cast h
  obtain ⟨z, hzM, hz⟩ := maximal_scale_by_breakpoints hn hw hFeas hminR
    (show bundleValue w Finset.univ / ↑n < (a : ℝ) * 2 ^ L from hL)
  change z ∈ scaleCandidates w (a : ℝ) ((∑ g, w g) / ↑n) L at hzM
  rw [← hUR] at hzM
  obtain ⟨q, hq, hqz⟩ := (scaleCandidatesRat_rep v a U z).mp hzM
  have hbetween (y : ℚ) (hm : y ∈ scaleCandidatesRat v a U L) : a ≤ y ∧ y ≤ U := by
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact ⟨le_rfl, haU⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact ⟨haU, le_rfl⟩
    · exact (Finset.mem_filter.mp hm).2
  let S := insert 0 ((scaleCandidatesRat v a U L).filter (scaleFeasibleRat v n L))
  let best := rationalScaleFrom v n L a
  have heval (y : ℚ) (hm : y ∈ scaleCandidatesRat v a U L) :
      scaleFeasibleRat v n L y ↔ AdmissibleScale w n (y : ℝ) :=
    scaleFeasibleRat_spec v hv ha hmin (hUR.symm ▸ hL) (hbetween y hm).1 (hbetween y hm).2
  have hqf : scaleFeasibleRat v n L q := (heval q hq).mpr (hqz ▸ hz.1)
  have hqle : q ≤ best := Finset.le_max' S q
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hq, hqf⟩))
  have hbest : best ∈ S := Finset.max'_mem S (Finset.insert_nonempty _ _)
  obtain hzero | hbest := Finset.mem_insert.mp hbest
  · rw [show best = 0 from hzero] at hqle
    exact False.elim ((not_le_of_gt hqf.1) hqle)
  · obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hbest
    have hadm := (heval best hm).mp hf
    exact ⟨hadm, fun y hy => (hz.2 hy).trans (hqz ▸ (show (q : ℝ) ≤ (best : ℝ) by exact_mod_cast hqle))⟩

end OnlineMMS.TwoType
