import OnlineMMS.ObliviousOrder

namespace OnlineMMS

/-- Normalizing by the deterministic square-root scale exposes the threshold
kδ. In particular δ=c/k leaves only a constant-factor change. -/
theorem scaled_oblivious_MMS_order {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1) :
    (1/434:ℝ)*max 1 (Real.sqrt ((k:ℝ)*δ)) ≤ Real.sqrt (k:ℝ)*alphaOblivious k δ ∧
    Real.sqrt (k:ℝ)*alphaOblivious k δ ≤ 5*max 1 (Real.sqrt ((k:ℝ)*δ)) := by
  have hp := Real.sqrt_pos.mpr (show (0:ℝ)<k by exact_mod_cast hk)
  have he : Real.sqrt (k:ℝ)*max (1/Real.sqrt (k:ℝ)) (Real.sqrt δ) =
      max 1 (Real.sqrt ((k:ℝ)*δ)) := by
    rw [mul_max_of_nonneg _ _ hp.le, Real.sqrt_mul (Nat.cast_nonneg k)]
    simp [hp.ne']
  obtain ⟨hl,hu⟩ := oblivious_MMS_order hk hδ hd
  have h1 := mul_le_mul_of_nonneg_left hl hp.le
  have h2 := mul_le_mul_of_nonneg_left hu hp.le
  rw [mul_left_comm,he] at h1
  rw [mul_left_comm,he] at h2
  exact ⟨h1,h2⟩

open Filter in
/-- A divergent gain in order over 1/√k occurs exactly when kδ tends to infinity.
The failure budget is allowed to depend on the number of types. -/
theorem randomization_threshold (δ : ℕ → ℝ) (hδ : ∀ k, 0 ≤ δ k ∧ δ k < 1) :
    Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)*alphaOblivious k (δ k)) atTop atTop ↔
    Tendsto (fun k : ℕ => (k:ℝ)*δ k) atTop atTop := by
  rw [tendsto_atTop_atTop,tendsto_atTop_atTop]
  constructor
  · intro h b
    let y := max 2 (b+1)
    obtain ⟨i,hi⟩ := h (5*y)
    refine ⟨max 1 i,fun k hk => ?_⟩
    have hk' : 0 < k := (le_max_left 1 i).trans hk
    have H := scaled_oblivious_MMS_order hk' (hδ k).1 (hδ k).2
    have hg := (hi k ((le_max_right 1 i).trans hk)).trans H.2
    have hy : y ≤ max 1 (Real.sqrt ((k:ℝ)*δ k)) := by linarith
    have hy2 : 2 ≤ y := le_max_left _ _
    have hb : b+1 ≤ y := le_max_right _ _
    have hroot : y ≤ Real.sqrt ((k:ℝ)*δ k) :=
      (le_max_iff.mp hy).resolve_left (by linarith)
    have hprod : 0 ≤ (k:ℝ)*δ k := mul_nonneg (Nat.cast_nonneg k) (hδ k).1
    nlinarith [Real.sq_sqrt hprod, sq_nonneg (Real.sqrt ((k:ℝ)*δ k)-1)]
  · intro h b
    let y := max 1 (434*b)
    obtain ⟨i,hi⟩ := h (y^2)
    refine ⟨max 1 i,fun k hk => ?_⟩
    have hk' : 0 < k := (le_max_left 1 i).trans hk
    have hx := hi k ((le_max_right 1 i).trans hk)
    have hp : 0 ≤ (k:ℝ)*δ k := mul_nonneg (Nat.cast_nonneg k) (hδ k).1
    have hy : 1 ≤ y := le_max_left _ _
    have hb : 434*b ≤ y := le_max_right _ _
    have hroot : y ≤ Real.sqrt ((k:ℝ)*δ k) := (Real.le_sqrt (by linarith) hp).2 hx
    have H := scaled_oblivious_MMS_order hk' (hδ k).1 (hδ k).2
    have hh := le_max_right (1:ℝ) (Real.sqrt ((k:ℝ)*δ k))
    linarith

end OnlineMMS
