import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace OnlineMMS

variable {G : Type*} [DecidableEq G]

/-- Independence for a finite family of two-element edges. -/
def PairIndependent (E : Finset (Finset G)) (I : Finset G) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ({x, y} : Finset G) ∉ E

def pairNeighbors (E : Finset (Finset G)) (S : Finset G) (a : G) : Finset G :=
  S.filter fun b => a ≠ b ∧ ({a, b} : Finset G) ∈ E

def pairDegree (E : Finset (Finset G)) (S : Finset G) (a : G) : ℕ :=
  (pairNeighbors E S a).card

private theorem degree_mono (E : Finset (Finset G)) {S T : Finset G}
    (hsub : S ⊆ T) (a : G) : pairDegree E S a ≤ pairDegree E T a := by
  apply Finset.card_le_card
  intro b hb
  simp only [pairNeighbors, Finset.mem_filter] at hb ⊢
  exact ⟨hsub hb.1, hb.2⟩

/-- The residual set of vertices after selecting a vertex. -/
def pairResidual (E : Finset (Finset G)) (S : Finset G) (v : G) : Finset G :=
  S \ insert v (pairNeighbors E S v)

/-- One minimum-degree step preserves the Caro--Wei certificate. -/
theorem pair_greedy_step (E : Finset (Finset G)) (S : Finset G) (v : G)
    (hv : v ∈ S) (hmin : ∀ a ∈ S, pairDegree E S v ≤ pairDegree E S a)
    (I : Finset G) (hI : I ⊆ pairResidual E S v) (hi : PairIndependent E I)
    (hw : (∑ a ∈ pairResidual E S v, 1 / ((pairDegree E (pairResidual E S v) a : ℝ) + 1))
      ≤ (I.card : ℝ)) :
    insert v I ⊆ S ∧ PairIndependent E (insert v I) ∧
      (∑ a ∈ S, 1 / ((pairDegree E S a : ℝ) + 1)) ≤ ((insert v I).card : ℝ) := by
  classical
  let C := insert v (pairNeighbors E S v)
  let T := S \ C
  have hC : C ⊆ S := Finset.insert_subset hv (Finset.filter_subset _ _)
  have hT : T ⊆ S := Finset.sdiff_subset
  have hvin : v ∈ C := Finset.mem_insert_self _ _
  have hvnot : v ∉ T := fun h => (Finset.mem_sdiff.mp h).2 hvin
  have hvI : v ∉ I := fun h => hvnot (hI h)
  have hcardC : C.card = pairDegree E S v + 1 := by
    have hnot : v ∉ pairNeighbors E S v := by simp [pairNeighbors]
    change (insert v (pairNeighbors E S v)).card = _
    rw [Finset.card_insert_of_not_mem hnot]
    rfl
  have hsumC : (∑ a ∈ C, (1 : ℝ) / ((pairDegree E S a : ℝ) + 1)) ≤ 1 := by
    calc
      _ ≤ ∑ _a ∈ C, (1 : ℝ) / ((pairDegree E S v : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro a ha
        apply one_div_le_one_div_of_le (by positivity)
        exact add_le_add_right (by exact_mod_cast hmin a (hC ha)) _
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardC, Nat.cast_add, Nat.cast_one]
        exact mul_one_div_cancel (by positivity)
  have hsumT :
      (∑ a ∈ T, (1 : ℝ) / ((pairDegree E S a : ℝ) + 1)) ≤
        ∑ a ∈ T, (1 : ℝ) / ((pairDegree E T a : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro a _
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_right (by exact_mod_cast degree_mono E hT a) _
  refine ⟨Finset.insert_subset hv (hI.trans hT), ?_, ?_⟩
  · intro a ha b hb hab hed
    have avoid (x : G) (hx : x ∈ I) (hxd : v ≠ x) : ({v, x} : Finset G) ∉ E := by
      intro hed'
      have hmem : x ∈ pairNeighbors E S v := Finset.mem_filter.mpr ⟨hT (hI hx), hxd, hed'⟩
      exact (Finset.mem_sdiff.mp (hI hx)).2 (Finset.mem_insert_of_mem hmem)
    rcases Finset.mem_insert.mp ha with he | ha
    · subst a
      rcases Finset.mem_insert.mp hb with he | hb
      · exact hab he.symm
      · exact avoid b hb hab hed
    · rcases Finset.mem_insert.mp hb with he | hb
      · subst b
        have hs : ({v, a} : Finset G) = {a, v} := by
          ext x
          simp [or_comm]
        exact avoid a ha hab.symm (by simpa only [hs] using hed)
      · exact hi a ha b hb hab hed
  · rw [Finset.card_insert_of_not_mem hvI, Nat.cast_succ]
    have heq := Finset.sum_sdiff (f := fun a => (1 : ℝ) / ((pairDegree E S a : ℝ) + 1)) hC
    change (∑ a ∈ T, (1 : ℝ) / ((pairDegree E S a : ℝ) + 1)) +
        (∑ a ∈ C, (1 : ℝ) / ((pairDegree E S a : ℝ) + 1)) = _ at heq
    change (∑ a ∈ T, 1 / ((pairDegree E T a : ℝ) + 1)) ≤ (I.card : ℝ) at hw
    linarith [hsumT, hsumC, hw]

/-- Choosing a minimum-degree vertex and recursively deleting its closed
neighborhood yields the constructive Caro--Wei bound. -/
theorem exists_pair_weight_certificate (E : Finset (Finset G)) (S : Finset G) :
    ∃ I ⊆ S, PairIndependent E I ∧
      (∑ a ∈ S, 1 / ((pairDegree E S a : ℝ) + 1)) ≤ (I.card : ℝ) := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S (pairDegree E S) hne
    let T := pairResidual E S v
    have hT : T ⊆ S := Finset.sdiff_subset
    have hvnot : v ∉ T := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
    have hlt : T.card < S.card := Finset.card_lt_card <|
      (Finset.ssubset_iff_of_subset hT).mpr ⟨v, hv, hvnot⟩
    obtain ⟨I, hI, hi, hw⟩ := exists_pair_weight_certificate E T
    exact ⟨insert v I, pair_greedy_step E S v hv hmin I hI hi hw⟩
  · have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact ⟨∅, Finset.Subset.rfl, by simp [PairIndependent], by simp⟩
termination_by S.card

private theorem degree_le_incidence (E : Finset (Finset G)) (S : Finset G) (a : G) :
    pairDegree E S a ≤ (E.filter (a ∈ ·)).card := by
  unfold pairDegree
  apply Finset.card_le_card_of_injOn (fun b => ({a, b} : Finset G))
  · intro b hb
    simp only [pairNeighbors, Finset.mem_filter] at hb ⊢
    exact ⟨hb.2.2, Finset.mem_insert_self _ _⟩
  · intro b hb c hc hEq
    simp only [Finset.mem_coe, pairNeighbors, Finset.mem_filter] at hb hc
    change ({a, b} : Finset G) = {a, c} at hEq
    have hh : b ∈ ({a, c} : Finset G) := by rw [← hEq]; simp
    have hbc : b = a ∨ b = c := by simpa using hh
    exact hbc.resolve_left hb.2.1.symm

private theorem degree_sum_le_twice_edges (E : Finset (Finset G)) (S : Finset G)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 2) :
    ∑ a ∈ S, pairDegree E S a ≤ 2 * E.card := by
  calc
    _ ≤ ∑ a ∈ S, (E.filter (a ∈ ·)).card :=
      Finset.sum_le_sum (fun a _ => degree_le_incidence E S a)
    _ = ∑ e ∈ E, (S.filter (· ∈ e)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    _ = ∑ _e ∈ E, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have hs : S.filter (· ∈ e) = e := by
        ext a
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun ha => (hE e he).1 ha)
      rw [hs, (hE e he).2]
    _ = _ := by simp [mul_comm]

/-- The Caro--Wei and Cauchy--Schwarz bounds, combined in a form that
also makes the integer threshold for the independent set explicit. -/
theorem card_ge_of_pair_weight (E : Finset (Finset G)) (S : Finset G)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 2) {z : ℕ}
    (hstrict : (z : ℝ) * ((S.card : ℝ) + 2 * (E.card : ℝ)) < (S.card : ℝ) ^ 2)
    (I : Finset G)
    (hwei : (∑ a ∈ S, 1 / ((pairDegree E S a : ℝ) + 1)) ≤ (I.card : ℝ)) :
    z + 1 ≤ I.card := by
  classical
  have hS : 0 < (S.card : ℝ) := by
    by_contra! hb
    have hzero : (S.card : ℝ) = 0 := le_antisymm hb (Nat.cast_nonneg _)
    rw [hzero] at hstrict
    have hnon : 0 ≤ (z : ℝ) * (0 + 2 * (E.card : ℝ)) := by positivity
    norm_num at hstrict
    linarith
  have hC : (S.card : ℝ) ^ 2 / (∑ a ∈ S, ((pairDegree E S a : ℝ) + 1)) ≤
      ∑ a ∈ S, (1 : ℝ) / ((pairDegree E S a : ℝ) + 1) := by
    simpa [nsmul_eq_mul] using Finset.sq_sum_div_le_sum_sq_div S (fun _ => (1 : ℝ))
      (g := fun a => (pairDegree E S a : ℝ) + 1) (fun _ _ => by positivity)
  have hdegrees : (∑ a ∈ S, (pairDegree E S a : ℝ)) ≤ 2 * (E.card : ℝ) := by
    exact_mod_cast degree_sum_le_twice_edges E S hE
  have hSum : (∑ a ∈ S, ((pairDegree E S a : ℝ) + 1)) ≤ S.card + 2 * (E.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    simp [nsmul_eq_mul]
    linarith
  have hdpos : (0 : ℝ) < ∑ a ∈ S, ((pairDegree E S a : ℝ) + 1) := by
    rw [Finset.sum_add_distrib]
    simp
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hS
  have hZ : (z : ℝ) < (S.card : ℝ) ^ 2 / (∑ a ∈ S, ((pairDegree E S a : ℝ) + 1)) := by
    apply (lt_div_iff₀ hdpos).mpr
    exact (mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg _)).trans_lt hstrict
  have hbig : (z : ℝ) < (I.card : ℝ) := hZ.trans_le (hC.trans hwei)
  exact_mod_cast hbig

theorem exists_independent_of_average_degree (E : Finset (Finset G)) (S : Finset G)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 2) {z : ℕ}
    (hstrict : (z : ℝ) * ((S.card : ℝ) + 2 * (E.card : ℝ)) < (S.card : ℝ) ^ 2) :
    ∃ I ⊆ S, PairIndependent E I ∧ z + 1 ≤ I.card := by
  obtain ⟨I, hIS, hI, hwei⟩ := exists_pair_weight_certificate E S
  exact ⟨I, hIS, hI, card_ge_of_pair_weight E S hE hstrict I hwei⟩

end OnlineMMS
