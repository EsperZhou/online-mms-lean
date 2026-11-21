import OnlineMMS.Model
import OnlineMMS.Benchmarks

namespace OnlineMMS

/-- An assignment on the remaining goods. Values outside the remaining set
do not enter any part. Parts may be empty. -/
def HasPaymentPartition {m : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    (n : ℕ) (q : ℝ) : Prop :=
  ∃ p : Fin m → Fin n, ∀ j, q ≤ bundleValue v (R.filter (fun g => p g = j))

theorem paymentPartition_of_mms {m n : ℕ} (v : Fin m → ℝ) (hn : 0 < n) :
    HasPaymentPartition v Finset.univ n (maximinShare v n hn) := by
  obtain ⟨p, hp⟩ := maximinShare_attained v hn
  exact ⟨p, fun j => hp ▸ partitionMin_le_partitionValue v hn p j⟩

theorem paymentPartition_mono {m n : ℕ} {v : Fin m → ℝ} {R : Finset (Fin m)}
    {a b : ℝ} (hab : a ≤ b) (h : HasPaymentPartition v R n b) :
    HasPaymentPartition v R n a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun j => hab.trans (hp j)⟩

/-- Monotonicity of the value of a bundle under a nonnegative valuation. -/
theorem bundleValue_mono {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    {A B : Finset (Fin m)} (hAB : A ⊆ B) :
    bundleValue v A ≤ bundleValue v B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun g _ _ => hv g)

theorem bundleValue_sdiff {m : ℕ} (v : Fin m → ℝ) {A B : Finset (Fin m)}
    (h : A ⊆ B) : bundleValue v (B \ A) + bundleValue v A = bundleValue v B :=
  Finset.sum_sdiff h

theorem sum_paymentParts {m n : ℕ} (v : Fin m → ℝ) (R : Finset (Fin m))
    (p : Fin m → Fin n) :
    (∑ j, bundleValue v (R.filter (fun g => p g = j))) = bundleValue v R := by
  classical
  unfold bundleValue
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem paymentPartition_total {m n : ℕ} {v : Fin m → ℝ} {R : Finset (Fin m)}
    {q : ℝ} (h : HasPaymentPartition v R n q) :
    (n : ℝ) * q ≤ bundleValue v R := by
  obtain ⟨p, hp⟩ := h
  rw [← sum_paymentParts v R p]
  calc
    _ = ∑ _j : Fin n, q := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hp j)

theorem maximinShare_nonnegative {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) : 0 ≤ maximinShare v n hn :=
  (partitionMin_nonneg v hv hn fun _ => ⟨0, hn⟩).trans
    (partitionMin_le_maximinShare v hn _)

theorem maximinShare_le_average {m n : ℕ} (v : Fin m → ℝ) (hn : 0 < n) :
    maximinShare v n hn ≤ bundleValue v Finset.univ / (n : ℝ) := by
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hpos, mul_comm]
  exact paymentPartition_total (paymentPartition_of_mms v hn)

/-- If a part is removed, assign the remaining goods to the retained labels. -/
theorem paymentPartition_removePart {m n : ℕ} (v : Fin m → ℝ)
    (R : Finset (Fin m)) (hn : 0 < n) (p : Fin m → Fin (n + 1)) (j : Fin (n + 1))
    {q : ℝ} (hp : ∀ i, q ≤ bundleValue v (R.filter (fun g => p g = i))) :
    HasPaymentPartition v (R \ R.filter (fun g => p g = j)) n q := by
  classical
  let f : Fin m → Fin n := fun g =>
    if h : p g ≠ j then Classical.choose (Fin.exists_succAbove_eq h) else ⟨0, hn⟩
  have hf (g : Fin m) (hg : p g ≠ j) : j.succAbove (f g) = p g := by
    simp only [f, dif_pos hg]
    exact Classical.choose_spec (Fin.exists_succAbove_eq hg)
  refine ⟨f, fun i => ?_⟩
  have heq : ((R \ R.filter (fun g => p g = j)).filter (fun g => f g = i)) =
      R.filter (fun g => p g = j.succAbove i) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hg, hno⟩, hfgi⟩
      have hne : p g ≠ j := fun e => hno ⟨hg, e⟩
      refine ⟨hg, ?_⟩
      exact (hf g hne).symm.trans (congrArg j.succAbove hfgi)
    · rintro ⟨hg, hpg⟩
      refine ⟨⟨hg, fun h => ?_⟩, ?_⟩
      · exact j.succAbove_ne i (hpg.symm.trans h.2)
      · apply Fin.succAbove_right_injective
        exact (hf g (fun e => j.succAbove_ne i (hpg.symm.trans e))).trans hpg
  rw [heq]
  exact hp _

/-- View a two-part payment partition as a cut and its complement. -/
theorem paymentPartition_two_cut {m : ℕ} {v : Fin m → ℝ} {R : Finset (Fin m)}
    {q : ℝ} (h : HasPaymentPartition v R 2 q) :
    ∃ G ⊆ R, q ≤ bundleValue v G ∧ q ≤ bundleValue v (R \ G) := by
  obtain ⟨p, hp⟩ := h
  let G := R.filter (fun g => p g = 0)
  refine ⟨G, Finset.filter_subset _ _, hp 0, ?_⟩
  have hEq : R \ G = R.filter (fun g => p g = 1) := by
    ext g
    have hcases : p g = 0 ∨ p g = 1 := by
      have hpval := (p g).isLt
      rcases Nat.eq_zero_or_pos (p g).val with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by change (p g).val = 1; omega))
    simp only [G, Finset.mem_sdiff, Finset.mem_filter]
    rcases hcases with h | h <;> simp [h]
  rw [hEq]
  exact hp 1

theorem paymentPartition_two_of_cut {m : ℕ} {v : Fin m → ℝ} {R G : Finset (Fin m)}
    {q : ℝ} (hG : G ⊆ R) (hA : q ≤ bundleValue v G) (hB : q ≤ bundleValue v (R \ G)) :
    HasPaymentPartition v R 2 q := by
  let p : Fin m → Fin 2 := fun g => if g ∈ G then 0 else 1
  refine ⟨p, fun j => ?_⟩
  have h0 : R.filter (fun g => p g = 0) = G := by
    ext g
    by_cases hg : g ∈ G
    · simp [p, hg, hG hg]
    · simp [p, hg]
  have h1 : R.filter (fun g => p g = 1) = R \ G := by
    ext g
    by_cases hg : g ∈ G <;> simp [p, hg]
  fin_cases j
  · change q ≤ bundleValue v (R.filter (fun g => p g = 0))
    rwa [h0]
  · change q ≤ bundleValue v (R.filter (fun g => p g = 1))
    rwa [h1]

/-- Assemble local choices and their valid continuations into one policy. -/
theorem policy_step_of_choices {m k n : ℕ} (v : Fin k → Fin m → ℝ) (R : Finset (Fin m))
    (q : Fin k → ℝ)
    (h : ∀ t, ∃ (G : Finset (Fin m)) (p : Policy m k n), G ⊆ R ∧
      q t ≤ bundleValue (v t) G ∧ p.Guarantees v q (R \ G)) :
    ∃ p : Policy m k (n+1), p.Guarantees v q R := by
  classical
  choose G p hsub hvalue hcont using h
  exact ⟨.step G p, fun t => ⟨hsub t, hvalue t, hcont t⟩⟩

/-- With one arrival remaining, give her all the remaining goods. -/
theorem one_arrival_policy {m k : ℕ} (v : Fin k → Fin m → ℝ) (R : Finset (Fin m))
    (q : Fin k → ℝ) (h : ∀ t, q t ≤ bundleValue (v t) R) :
    ∃ p : Policy m k 1, p.Guarantees v q R :=
  ⟨.step (fun _ => R) (fun _ => .done), fun t => ⟨Finset.Subset.refl _, h t, trivial⟩⟩

private theorem fin_two_cases (t : Fin 2) : t = 0 ∨ t = 1 := by fin_cases t <;> simp

/-- The manuscript's two-arrival rule on arbitrary remaining goods and targets. -/
theorem two_arrival_policy_of_partitions {m : ℕ} (v : Fin 2 → Fin m → ℝ)
    (R : Finset (Fin m)) (q : Fin 2 → ℝ)
    (h : ∀ t, HasPaymentPartition (v t) R 2 (q t)) :
    ∃ p : Policy m 2 2, p.Guarantees v q R := by
  apply policy_step_of_choices
  intro t
  let u : Fin 2 := if t = 0 then 1 else 0
  have ht (i : Fin 2) : i = t ∨ i = u := by
    rcases fin_two_cases t with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;> simp [u]
  obtain ⟨G, hG, hleft, hright⟩ := paymentPartition_two_cut (h t)
  let K := R \ G
  have hK : K ⊆ R := Finset.sdiff_subset
  have hsplit : R \ K = G := Finset.sdiff_sdiff_eq_self hG
  have htot := paymentPartition_total (h u)
  have hsum := bundleValue_sdiff (v u) hG
  by_cases hc : bundleValue (v u) G ≤ bundleValue (v u) K
  · obtain ⟨p, hp⟩ := one_arrival_policy v K q (by
      intro i
      rcases ht i with rfl | rfl
      · exact hright
      · norm_num at htot
        linarith)
    exact ⟨G, p, hG, hleft, hp⟩
  · obtain ⟨p, hp⟩ := one_arrival_policy v G q (by
      intro i
      rcases ht i with rfl | rfl
      · exact hleft
      · norm_num at htot
        linarith)
    exact ⟨K, p, hK, hright, hsplit.symm ▸ hp⟩

/-- Exact initial MMS partitions yield full MMS against all two-arrival histories. -/
theorem two_arrival_mms_policy {m : ℕ} (v : Fin 2 → Fin m → ℝ) :
    ∃ p : Policy m 2 2, p.Guarantees v
      (fun t => maximinShare (v t) 2 (by decide)) Finset.univ :=
  two_arrival_policy_of_partitions v Finset.univ _ (fun t => paymentPartition_of_mms (v t) (by decide))

end OnlineMMS
