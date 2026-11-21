import OnlineMMS.ManuscriptModel

namespace OnlineMMS

theorem ObliviousAttainable.mono_failure {k : ℕ} {δ ε x : ℝ}
    (hx : ObliviousAttainable k δ x) (hle : δ ≤ ε) : ObliviousAttainable k ε x := by
  refine ⟨hx.1, fun n hn m v hv => ?_⟩
  obtain ⟨D,hD⟩ := hx.2 n hn m v hv
  exact ⟨D,fun s => (sub_le_sub_left hle 1).trans (hD s)⟩

theorem ObliviousAttainable.le_optimum {k : ℕ} {δ x : ℝ}
    (hx : ObliviousAttainable k δ x) : x ≤ alphaOblivious k δ :=
  le_csSup (show BddAbove {y | ObliviousAttainable k δ y} from ⟨1,fun _ hy => hy.1.2⟩) hx

theorem oblivious_deterministic_floor {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ) :
    (1/434:ℝ) * (1/Real.sqrt (k:ℝ)) ≤ alphaOblivious k δ := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hs : 1 ≤ Real.sqrt (k:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg k)).2 (by linarith)
  let h : ℝ := bucketMultiplier k
  have hlo : 216 ≤ h := by dsimp [h]; exact_mod_cast (bucketMultiplier_bounds hk).1
  have hhi : h ≤ Real.sqrt ((k:ℝ)/2) + 216 := (bucketMultiplier_estimate hk).2
  have hcap : 2*h ≤ 434*Real.sqrt (k:ℝ) := by
    have H := Real.sqrt_le_sqrt (show (k:ℝ)/2 ≤ k by linarith)
    linarith
  have hp : 0 < 2*h := by linarith
  have hdet : ObliviousAttainable k 0 (1/(2*h)) :=
    (oblivious_zeroFailure_attainable_iff k _).2
      ⟨⟨by positivity, (div_le_one hp).2 (by linarith)⟩,
        (explicit_fraction_le_alphaTPS hk).trans (alphaTPS_le_alphaMMS k)⟩
  calc
    _ = 1/(434*Real.sqrt (k:ℝ)) := by ring
    _ ≤ 1/(2*h) := one_div_le_one_div_of_le hp hcap
    _ ≤ _ := (hdet.mono_failure hδ).le_optimum

end OnlineMMS
