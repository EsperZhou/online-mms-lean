import OnlineMMS.FinitePTASOnlineBounds

namespace OnlineMMS

/-- Executable short-horizon policy after the first type is revealed.
The horizon is one more than the number of remaining arrivals. -/
def rationalShortPTASChoice {m L : ℕ} (v : Fin 2 → Fin m → ℚ) (first : Fin 2) :
    (r : ℕ) → Option (Finset (Fin m) × Policy m 2 r)
  | 0 => none
  | 1 => match rationalTwoPTASPolicy (L := L) v with
    | .step G next => some (G first,next first)
  | 2 => some (rationalThreePTASChoice (L := L) v first)
  | r+3 => rationalLongPTASChoice (L := L) (r+3) v first

theorem rationalShortPTASChoice_correct {m r L : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hr : 1 ≤ r) (hr' : r ≤ 4) (hL : 0 < L) (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (Nat.zero_lt_succ r)
    let factor := shortHorizonFactors (r+1)
    ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      rationalShortPTASChoice (L := L) v first r = some (G,p) ∧
      (1-(1 : ℝ)/L)*μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-(1 : ℝ)/L)*orientedTarget μ factor.1 factor.2 first t)
        (Finset.univ \ G) := by
  have hrs : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hrs with h | h | h | h
  · subst r
    have hp := rationalTwoPTASPolicy_correct v hv hL
    cases hpol : rationalTwoPTASPolicy (L := L) v with
    | step G next =>
      rw [hpol] at hp
      refine ⟨G first,next first,?_,(hp first).2.1,?_⟩
      · simp [rationalShortPTASChoice,hpol]
      · simpa [shortHorizonFactors,orientedTarget] using (hp first).2.2
  · subst r
    exact ⟨_,_,rfl,(rationalThreePTASChoice_correct v hv hL first).1,
      (rationalThreePTASChoice_correct v hv hL first).2⟩
  · subst r
    simpa [rationalShortPTASChoice,shortHorizonFactors,longShortFactors,Rat.cast_div] using
      rationalLongPTASChoice_correct v hv (by decide : 3 ≤ 3) (by decide : 3 ≤ 4) hL first
  · subst r
    simpa [rationalShortPTASChoice,shortHorizonFactors,longShortFactors,Rat.cast_div] using
      rationalLongPTASChoice_correct v hv (by decide : 3 ≤ 4) (by decide : 4 ≤ 4) hL first

/-- The executable policy satisfies the short-horizon MMS guarantees
with any prescribed positive approximation tolerance. -/
theorem rationalShortPTASChoice_epsilon {m r : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hr : 1 ≤ r) (hr' : r ≤ 4) (ε : ℝ) (hε : 0 < ε)
    (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (Nat.zero_lt_succ r)
    let factor := shortHorizonFactors (r+1)
    ∃ (L : ℕ) (G : Finset (Fin m)) (p : Policy m 2 r),
      0 < L ∧ (1 : ℝ)/L ≤ ε ∧ rationalShortPTASChoice (L := L) v first r = some (G,p) ∧
      (1-ε)*μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-ε)*orientedTarget μ factor.1 factor.2 first t) (Finset.univ \ G) := by
  dsimp only
  let w : Fin 2 → Fin m → ℝ := fun t g => v t g
  let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (Nat.zero_lt_succ r)
  let factor := shortHorizonFactors (r+1)
  obtain ⟨L,hL,hacc⟩ := exists_roundedMMS_precision ε hε
  obtain ⟨G,p,he,hfirst,hrest⟩ := rationalShortPTASChoice_correct v hv hr hr' hL first
  have hva (t : Fin 2) (g : Fin m) : 0 ≤ w t g := by
    change (0 : ℝ) ≤ (v t g : ℝ)
    exact_mod_cast hv t g
  have hμ (t : Fin 2) : 0 ≤ μ t := maximinShare_nonnegative (w t) (hva t) _
  have hf : 0 ≤ factor.1 ∧ 0 ≤ factor.2 := by
    have hrs : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases hrs with h | h | h | h <;> norm_num [factor,h,shortHorizonFactors]
  have hc : 1-ε ≤ 1-(1 : ℝ)/L := sub_le_sub_left hacc 1
  refine ⟨L,G,p,hL,hacc,he,(mul_le_mul_of_nonneg_right hc (hμ first)).trans hfirst,hrest.mono ?_⟩
  intro t
  apply mul_le_mul_of_nonneg_right hc
  unfold orientedTarget
  split
  · exact mul_nonneg hf.1 (hμ t)
  · exact mul_nonneg hf.2 (hμ t)

end OnlineMMS
