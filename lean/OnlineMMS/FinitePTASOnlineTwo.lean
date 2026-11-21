import OnlineMMS.FinitePTASRational

namespace OnlineMMS

open scoped BigOperators

/-- Evaluate a bundle using executable rational arithmetic. -/
def rationalBundleValue {m : ℕ} (v : Fin m → ℚ) (S : Finset (Fin m)) : ℚ :=
  ∑ g ∈ S, v g

@[simp] theorem rationalBundleValue_cast {m : ℕ} (v : Fin m → ℚ) (S : Finset (Fin m)) :
    (rationalBundleValue v S : ℝ) = bundleValue (fun g => (v g : ℝ)) S := by
  simp [rationalBundleValue,bundleValue,Rat.cast_sum]

def otherShortType (t : Fin 2) : Fin 2 := if t = 0 then 1 else 0

theorem otherShortType_ne (t : Fin 2) : otherShortType t ≠ t := by
  fin_cases t <;> decide

theorem shortType_cases (t i : Fin 2) : i = t ∨ i = otherShortType t := by
  fin_cases t <;> fin_cases i <;> decide

def rationalPart {m n : ℕ} (R : Finset (Fin m)) (part : Fin m → Fin n)
    (j : Fin n) : Finset (Fin m) :=
  R.filter (fun g => part g = j)

def rationalPartsPay {m n : ℕ} (v : Fin m → ℚ) (R : Finset (Fin m))
    (part : Fin m → Fin n) (q : ℚ) : Prop :=
  ∀ j, q ≤ rationalBundleValue v (rationalPart R part j)

def rationalCutPays {m : ℕ} (v : Fin m → ℚ) (R G : Finset (Fin m)) (q : ℚ) : Prop :=
  G ⊆ R ∧ q ≤ rationalBundleValue v G ∧ q ≤ rationalBundleValue v (R \ G)

theorem rationalPart_subset {m n : ℕ} (R : Finset (Fin m)) (part : Fin m → Fin n)
    (j : Fin n) : rationalPart R part j ⊆ R := Finset.filter_subset _ _

theorem rationalPart_two_complement {m : ℕ} (R : Finset (Fin m)) (part : Fin m → Fin 2) :
    R \ rationalPart R part 0 = rationalPart R part 1 := by
  ext g
  rcases shortType_cases 0 (part g) with hg | hg
  · simp [rationalPart,hg]
  · simp [rationalPart,hg,otherShortType]

theorem rationalPartsPay_cut {m : ℕ} (v : Fin m → ℚ) (R : Finset (Fin m))
    (part : Fin m → Fin 2) (q : ℚ) (h : rationalPartsPay v R part q) :
    rationalCutPays v R (rationalPart R part 0) q := by
  exact ⟨rationalPart_subset _ _ _,h 0,by rw [rationalPart_two_complement]; exact h 1⟩

theorem rationalPartsPay_ptas {m n L : ℕ} (v : Fin m → ℚ) (hn : 0 < n) :
    rationalPartsPay v Finset.univ (rationalMMSAssignment (L := L) v hn)
      (rationalMMSPayment (L := L) v hn) := by
  intro j
  exact Finset.inf'_le (fun i => rationalBundleValue v
    (rationalPart Finset.univ (rationalMMSAssignment (L := L) v hn) i))
    (Finset.mem_univ j)

/-- With one arrival, give all the remaining goods. -/
def rationalOnePolicy {m : ℕ} (R : Finset (Fin m)) : Policy m 2 1 :=
  .step (fun _ => R) (fun _ => .done)

/-- The paper's two-arrival rule: offer the part of the first type's cut
that the other type values less, then allocate the complement. -/
def rationalTwoPolicy {m : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (cuts : Fin 2 → Finset (Fin m)) : Policy m 2 2 :=
  let offered := fun t =>
    let G := cuts t
    let K := R \ G
    let w := v (otherShortType t)
    if rationalBundleValue w G ≤ rationalBundleValue w K then G else K
  .step offered (fun t => rationalOnePolicy (R \ offered t))

theorem rationalTwoPolicy_correct {m : ℕ} (v : Fin 2 → Fin m → ℚ)
    (R : Finset (Fin m)) (q : Fin 2 → ℚ) (cuts : Fin 2 → Finset (Fin m))
    (h : ∀ t, rationalCutPays (v t) R (cuts t) (q t)) :
    (rationalTwoPolicy v R cuts).Guarantees (fun t g => (v t g : ℝ))
      (fun t => (q t : ℝ)) R := by
  intro t
  let u := otherShortType t
  let G := cuts t
  let K := R \ G
  obtain ⟨hG,hGv,hKv⟩ := h t
  have hK : K ⊆ R := Finset.sdiff_subset
  have hsplit : R \ (R \ cuts t) = cuts t := Finset.sdiff_sdiff_eq_self hG
  have htot : 2 * q u ≤ rationalBundleValue (v u) R := by
    have he : rationalBundleValue (v u) (R \ cuts u) + rationalBundleValue (v u) (cuts u) =
          rationalBundleValue (v u) R :=
      Finset.sum_sdiff (h u).1
    linarith [(h u).2.1,(h u).2.2]
  have hsum : rationalBundleValue (v u) K + rationalBundleValue (v u) G =
        rationalBundleValue (v u) R := Finset.sum_sdiff hG
  have cast_pay (i : Fin 2) (S : Finset (Fin m)) :
      q i ≤ rationalBundleValue (v i) S →
      (q i : ℝ) ≤ bundleValue (fun g => (v i g : ℝ)) S := by
    intro hp
    rw [← rationalBundleValue_cast]
    exact_mod_cast hp
  by_cases hc : rationalBundleValue (v (otherShortType t)) (cuts t) ≤
      rationalBundleValue (v (otherShortType t)) (R \ cuts t)
  · simp only [rationalTwoPolicy,Policy.Guarantees,if_pos hc,rationalOnePolicy]
    refine ⟨hG,cast_pay _ _ hGv,fun i => ⟨Finset.Subset.refl _,?_,trivial⟩⟩
    apply cast_pay
    rcases shortType_cases t i with hi | hi
    · rw [hi]
      exact hKv
    · rw [hi]
      change q u ≤ rationalBundleValue (v u) K
      change rationalBundleValue (v u) G ≤ rationalBundleValue (v u) K at hc
      linarith
  · simp only [rationalTwoPolicy,Policy.Guarantees,if_neg hc,rationalOnePolicy,hsplit]
    refine ⟨hK,cast_pay _ _ hKv,fun i => ⟨Finset.Subset.refl _,?_,trivial⟩⟩
    apply cast_pay
    rcases shortType_cases t i with hi | hi
    · rw [hi]
      exact hGv
    · rw [hi]
      change q u ≤ rationalBundleValue (v u) G
      change ¬ rationalBundleValue (v u) G ≤ rationalBundleValue (v u) K at hc
      linarith [le_of_not_ge hc]

/-- Full executable two-arrival policy with the rounded initial partitions. -/
def rationalTwoPTASPolicy {m L : ℕ} (v : Fin 2 → Fin m → ℚ) : Policy m 2 2 :=
  let parts := fun t => rationalMMSAssignment (L := L) (v t) (by decide : 0 < 2)
  rationalTwoPolicy v Finset.univ (fun t => rationalPart Finset.univ (parts t) 0)

theorem rationalTwoPTASPolicy_correct {m L : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hL : 0 < L) :
    (rationalTwoPTASPolicy (L := L) v).Guarantees (fun t g => (v t g : ℝ))
      (fun t => (1-(1 : ℝ)/L) * maximinShare (fun g => (v t g : ℝ)) 2 (by decide))
      Finset.univ := by
  apply (rationalTwoPolicy_correct v Finset.univ
    (fun t => rationalMMSPayment (L := L) (v t) (by decide))
    _ (fun t => rationalPartsPay_cut _ _ _ _ (rationalPartsPay_ptas _ _))).mono
  intro t
  rw [rationalMMSPayment_cast]
  apply Finset.le_inf'
  intro j _
  exact rationalMMSAssignment_guarantee (v t) (hv t) (by decide) hL j

end OnlineMMS
