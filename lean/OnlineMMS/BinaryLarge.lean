import OnlineMMS.BinaryGraph
import OnlineMMS.BinarySupport
import OnlineMMS.PairCount

namespace OnlineMMS

variable {G : Type*} [DecidableEq G]

private theorem disjoint_pairs (S : Finset G) (c : ℕ) (hc : 2 * c ≤ S.card) :
    ∃ E : Finset (Finset G), E.card = c ∧
      (↑E : Set (Finset G)).Pairwise Disjoint ∧
      ∀ e ∈ E, e ⊆ S ∧ e.card = 2 := by
  classical
  induction c generalizing S with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ c ih =>
    obtain ⟨e, hes, hcard⟩ := Finset.exists_subset_card_eq (s := S) (show 2 ≤ S.card by omega)
    have hm := Finset.card_sdiff_add_card_eq_card hes
    obtain ⟨E, hEc, hpair, hE⟩ := ih (S \ e) (by omega)
    have heD (f : Finset G) (hf : f ∈ E) : Disjoint e f :=
      Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp ((hE f hf).1 hb)).2 ha)
    have hne : e ∉ E := by
      intro he
      have hz := (Finset.disjoint_self_iff_empty e).mp (heD e he)
      simp [hz] at hcard
    refine ⟨insert e E, by simp [Finset.card_insert_of_not_mem hne, hEc], ?_, ?_⟩
    · intro f hf f' hf' hne'
      change f ∈ insert e E at hf
      change f' ∈ insert e E at hf'
      rcases Finset.mem_insert.mp hf with he | hf
      · subst f
        rcases Finset.mem_insert.mp hf' with he | hf'
        · exact False.elim (hne' he.symm)
        · exact heD _ hf'
      · rcases Finset.mem_insert.mp hf' with he | hf'
        · subst f'
          exact (heD _ hf).symm
        · exact hpair hf hf' hne'
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨hes, hcard⟩
      · exact ⟨((hE f hf).1.trans Finset.sdiff_subset), (hE f hf).2⟩

private theorem one_per_pair {S X : Finset G} {E : Finset (Finset G)}
    (hpair : (↑E : Set (Finset G)).Pairwise Disjoint)
    (hsub : ∀ e ∈ E, e ⊆ S)
    (hres : ∀ e ∈ E, ¬ e ⊆ X) : E.card ≤ (S \ X).card := by
  classical
  have hex (e : ↑E) : ∃ a, a ∈ e.val ∧ a ∉ X := by
    by_contra! h
    exact hres e.val e.property (fun a ha => h a ha)
  choose x hx using hex
  -- The attachment type provides exactly the domain on which each pair has a witness.
  rw [← Finset.card_attach]
  apply Finset.card_le_card_of_injOn x
  · intro e _
    exact Finset.mem_sdiff.mpr ⟨hsub e e.property (hx e).1, (hx e).2⟩
  · intro e _ f _ heq
    apply Subtype.ext
    by_cases hEq : e.val = f.val
    · exact hEq
    · have hxf : x e ∈ f.val := by rw [heq]; exact (hx f).1
      exact False.elim (Finset.disjoint_left.mp (hpair e.property f.property hEq) (hx e).1 hxf)

private theorem two_mul_demand_prev {a p : ℕ} (hp : 0 < p) (hc : 0 < binaryDemand a p) :
    2 * (p * (binaryDemand a p - 1) + 1) ≤ a := by
  have h := binaryDemand_min a hp (c := binaryDemand a p - 1) (by omega)
  omega

private theorem demand_bound {a p ℓ : ℕ} (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ)
    (hactive : a - ℓ < binaryDemand a p) :
    (binaryDemand a p : ℝ) ≤ 1 + ((ℓ : ℝ) - 2) / (2 * (p : ℝ) - 1) := by
  let c := binaryDemand a p
  have hc : 0 < c := by omega
  have ha : a ≤ ℓ + c - 1 := by omega
  have ha' : (a : ℝ) ≤ (ℓ : ℝ) + (c : ℝ) - 1 := by
    have hn : 1 ≤ ℓ + c := by omega
    have h : (a : ℝ) ≤ ((ℓ + c - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    push_cast [Nat.cast_sub hn] at h
    exact h
  have hprev := two_mul_demand_prev (a := a) (p := p) (by omega) hc
  have hprevR : (2 : ℝ) * ((p : ℝ) * ((c : ℝ) - 1) + 1) ≤ (a : ℝ) := by
    have hi : (↑(2 * (p * (c - 1) + 1) : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hprev
    push_cast [Nat.cast_sub (show 1 ≤ c by omega)] at hi
    exact hi
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : 0 < (2 * (p : ℝ) - 1) := by linarith
  change (c : ℝ) ≤ _
  have h : (c : ℝ) - 1 ≤ ((ℓ : ℝ) - 2) / (2 * (p : ℝ) - 1) :=
    (le_div_iff₀ hden).mpr (by nlinarith only [ha', hprevR])
  linarith only [h]

private theorem pair_edge_count {p k : ℕ} (hmax : ∀ q : ℕ,
    1 + (q + q).choose 2 ≤ k → q ≤ p) :
    ((k - 1 : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ 2 + 3 * (p : ℝ) := by
  have hbad : k ≤ (p + 1 + (p + 1)).choose 2 := by
    by_contra! hh
    have hz := hmax (p + 1) (by omega)
    omega
  have hformula : (p + 1 + (p + 1)).choose 2 = (p + 1) * (2 * p + 1) := by
    rw [Nat.choose_two_right]
    rw [show p + 1 + (p + 1) - 1 = 2 * p + 1 by omega]
    rw [show p + 1 + (p + 1) = 2 * (p + 1) by ring, mul_assoc,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [hformula] at hbad
  by_cases hk : 1 ≤ k
  · have hb : (k : ℝ) ≤ ((p : ℝ) + 1) * (2 * (p : ℝ) + 1) := by exact_mod_cast hbad
    rw [Nat.cast_sub hk, Nat.cast_one]
    nlinarith only [hb]
  · have hk' : k = 0 := by omega
    simp [hk']
    positivity

private theorem large_degree_inequality {p z m e : ℝ}
    (hp : 2 ≤ p) (hz : 1 ≤ z) (hm : 2 * p * z + 2 ≤ m)
    (he : e ≤ (2 * p ^ 2 + 3 * p) * (1 + (z - 1) / (2 * p - 1))) :
    z * (m + 2 * e) < m ^ 2 := by
  let J := 2 * p ^ 2 - p
  let K := 2 * p ^ 2 + 3 * p
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hden : 0 < 2 * p - 1 := by linarith
  have hscale : K / (2 * p - 1) ≤ J - 1 := by
    apply (div_le_iff₀ hden).mpr
    have heq : (J - 1) * (2 * p - 1) - K = (p - 2) * (4 * p ^ 2 + 2 * p) + 1 := by
      dsimp [J, K]
      ring
    have hh : 0 ≤ (p - 2) * (4 * p ^ 2 + 2 * p) :=
      mul_nonneg (by linarith) (by positivity)
    linarith only [heq, hh]
  have hle : e ≤ z * J + 4 * p - z + 1 := by
    have hh := mul_le_mul_of_nonneg_left hscale (sub_nonneg.mpr hz)
    have hr : K * (1 + (z - 1) / (2 * p - 1)) =
        K + (z - 1) * (K / (2 * p - 1)) := by ring
    change e ≤ K * (1 + (z - 1) / (2 * p - 1)) at he
    rw [hr] at he
    dsimp [J, K] at hh he ⊢
    linarith only [he, hh]
  let m₀ := 2 * p * z + 2
  change m₀ ≤ m at hm
  have h₀ : z ≤ m₀ := by
    have hh := mul_nonneg (show 0 ≤ 2 * p - 1 by linarith) (show 0 ≤ z by linarith)
    dsimp [m₀]
    nlinarith only [hh]
  have hmon : 0 ≤ (m - m₀) * (m + m₀ - z) :=
    mul_nonneg (sub_nonneg.mpr hm) (by linarith)
  have hloss := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * z by linarith)
  have heq : m₀ ^ 2 - z * (m₀ + 2 * (z * J + 4 * p - z + 1)) =
      2 * (z - 1) ^ 2 + 2 := by
    dsimp [m₀, J]
    ring
  nlinarith only [hmon, hloss, heq, sq_nonneg (z - 1)]

/-- The graph construction supplies enough approved goods for every possible
first and second type when the pair parameter is at least two. -/
theorem binary_large_bundle_via {m k p : ℕ} (hp : 2 ≤ p)
    (hmax : ∀ q : ℕ, 1 + (q + q).choose 2 ≤ k → q ≤ p)
    (S : Fin k → Finset (Fin m)) (first : Fin k)
    (pairs : Fin k → Finset (Finset (Fin m)))
    (hcard : ∀ t, (pairs t).card = binaryDemand (S t).card p)
    (hpair : ∀ t, (↑(pairs t) : Set (Finset (Fin m))).Pairwise Disjoint)
    (hpairs : ∀ t e, e ∈ pairs t → e ⊆ S t ∧ e.card = 2)
    (pick : Finset (Finset (Fin m)) → Finset (Fin m) → Finset (Fin m))
    (hpick : ∀ E V, (∀ e ∈ E, e ⊆ V ∧ e.card = 2) → ∀ z : ℕ,
      (z : ℝ) * ((V.card : ℝ) + 2 * (E.card : ℝ)) < (V.card : ℝ) ^ 2 →
      pick E V ⊆ V ∧ PairIndependent E (pick E V) ∧ z + 1 ≤ (pick E V).card)
    (trim : Finset (Fin m) → Finset (Fin m))
    (htrim : ∀ V, binaryDemand (S first).card p ≤ V.card →
      trim V ⊆ V ∧ (trim V).card = binaryDemand (S first).card p) :
    let ℓ := binaryDemand (S first).card p
    let active := Finset.univ.filter fun t : Fin k =>
      t ≠ first ∧ (S t).card - ℓ < binaryDemand (S t).card p
    let edges := (active.biUnion pairs).filter (· ⊆ S first)
    let X := if ℓ ≤ 1 then trim (S first) else trim (pick edges (S first))
    X ⊆ S first ∧ ℓ ≤ X.card ∧ ∀ t, binaryDemand (S t).card p ≤ (S t \ X).card := by
  classical
  let demand (t : Fin k) := binaryDemand (S t).card p
  let ℓ := demand first
  have hp0 : 0 < p := by omega
  have hhalf (t : Fin k) : demand t ≤ (S t).card / 2 :=
    binaryDemand_le_half _ hp0
  have hℓle : ℓ ≤ (S first).card := (hhalf first).trans (Nat.div_le_self _ _)
  let active := Finset.univ.filter fun t : Fin k => t ≠ first ∧ (S t).card - ℓ < demand t
  let edges := (active.biUnion pairs).filter (· ⊆ S first)
  let X := if ℓ ≤ 1 then trim (S first) else trim (pick edges (S first))
  change X ⊆ S first ∧ ℓ ≤ X.card ∧ ∀ t, demand t ≤ (S t \ X).card
  by_cases hℓsmall : ℓ ≤ 1
  · simp only [X, if_pos hℓsmall]
    obtain ⟨hX, hcard⟩ := htrim _ hℓle
    refine ⟨hX, hcard.ge, fun t => ?_⟩
    have hd := hhalf t
    have hr := Finset.le_card_sdiff (trim (S first)) (S t)
    rw [hcard] at hr
    change (S t).card - ℓ ≤ _ at hr
    by_cases hz : (S t).card = 0
    · omega
    · omega
  · have hℓ : 2 ≤ ℓ := by omega
    let z := ℓ - 1
    have hz : 1 ≤ z := by omega
    have hedge (e : Finset (Fin m)) (he : e ∈ edges) : e ⊆ S first ∧ e.card = 2 := by
      obtain ⟨hu, hs⟩ := Finset.mem_filter.mp he
      obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hu
      exact ⟨hs, (hpairs t e ht).2⟩
    have hact := Finset.card_le_card (show active ⊆ Finset.univ.erase first from by
      intro t ht
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ht).2.1, Finset.mem_univ _⟩)
    rw [Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
      at hact
    have hactR : (active.card : ℝ) ≤ 2 * (p : ℝ)^2 + 3 * (p : ℝ) :=
      (show (active.card : ℝ) ≤ ((k - 1 : ℕ) : ℝ) by exact_mod_cast hact).trans
        (pair_edge_count hmax)
    have hcountNat : edges.card ≤ ∑ t ∈ active, (pairs t).card :=
      (Finset.card_filter_le _ _).trans Finset.card_biUnion_le
    have hcountR : (edges.card : ℝ) ≤ ∑ t ∈ active, ((pairs t).card : ℝ) := by
      exact_mod_cast hcountNat
    have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hℓR : (ℓ : ℝ) = (z : ℝ) + 1 := by
      exact_mod_cast (show ℓ = z + 1 by omega)
    have hr : 0 ≤ 1 + ((z : ℝ) - 1) / (2 * (p : ℝ) - 1) := by
      have h₁ : 0 ≤ (z : ℝ) - 1 := by linarith
      have h₂ : 0 ≤ 2 * (p : ℝ) - 1 := by linarith
      positivity
    have hdeneq : (ℓ : ℝ) - 2 = (z : ℝ) - 1 := by linarith
    have hcount : (edges.card : ℝ) ≤
        (2 * (p : ℝ)^2 + 3 * (p : ℝ)) * (1 + ((z : ℝ) - 1) / (2 * (p : ℝ) - 1)) := by
      calc
        _ ≤ ∑ t ∈ active, ((pairs t).card : ℝ) := hcountR
        _ ≤ ∑ _t ∈ active, (1 + ((z : ℝ) - 1) / (2 * (p : ℝ) - 1)) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [hcard t, ← hdeneq]
          exact demand_bound hp hℓ (Finset.mem_filter.mp ht).2.2
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hactR hr
    have hmₙ : 2 * (p * z + 1) ≤ (S first).card :=
      two_mul_demand_prev hp0 (show 0 < demand first by omega)
    have hm₀ : (2 : ℝ) * ((p : ℝ) * (z : ℝ) + 1) ≤ ((S first).card : ℝ) := by
      exact_mod_cast hmₙ
    have hm : 2 * (p : ℝ) * (z : ℝ) + 2 ≤ ((S first).card : ℝ) := by
      linarith only [hm₀]
    obtain ⟨hIS, hIe, hIc⟩ := hpick edges (S first) hedge z
      (large_degree_inequality hpR hzR hm hcount)
    let I := pick edges (S first)
    change z + 1 ≤ I.card at hIc
    simp only [X, if_neg hℓsmall]
    let Y := trim I
    obtain ⟨hXI, hXc⟩ := htrim I (show ℓ ≤ I.card by omega)
    change Y ⊆ S first ∧ ℓ ≤ Y.card ∧ ∀ t, demand t ≤ (S t \ Y).card
    change Y ⊆ I at hXI
    change Y.card = ℓ at hXc
    refine ⟨hXI.trans hIS, hXc.ge, ?_⟩
    intro t
    by_cases ht : t = first
    · subst t
      have h := Finset.card_sdiff_add_card_eq_card (hXI.trans hIS)
      have hh := hhalf first
      change ℓ ≤ (S first).card / 2 at hh
      omega
    by_cases ha : t ∈ active
    · change binaryDemand (S t).card p ≤ _
      rw [← hcard t]
      apply one_per_pair (hpair t) (fun e he => (hpairs t e he).1)
      intro e he hsub
      have hE : e ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨t, ha, he⟩,
        hsub.trans (hXI.trans hIS)⟩
      obtain ⟨g, j, hne, rfl⟩ := Finset.card_eq_two.mp (hpairs t e he).2
      exact hIe g (hXI (hsub (by simp))) j (hXI (hsub (by simp))) hne hE
    · have hb : demand t ≤ (S t).card - ℓ :=
        le_of_not_gt (fun hf => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hf⟩))
      have hh := Finset.le_card_sdiff Y (S t)
      rw [hXc] at hh
      exact hb.trans hh

/-- A bundle satisfying all demands in the large-type-count branch. -/
theorem binary_large_bundle {m k p : ℕ} (hp : 2 ≤ p)
    (hmax : ∀ q : ℕ, 1 + (q + q).choose 2 ≤ k → q ≤ p)
    (S : Fin k → Finset (Fin m)) (first : Fin k) :
    ∃ X ⊆ S first, binaryDemand (S first).card p ≤ X.card ∧
      ∀ t, binaryDemand (S t).card p ≤ (S t \ X).card := by
  classical
  have hp0 : 0 < p := by omega
  have hchoose (t : Fin k) :
      ∃ P : Finset (Finset (Fin m)), P.card = binaryDemand (S t).card p ∧
        (↑P : Set (Finset (Fin m))).Pairwise Disjoint ∧
        ∀ e ∈ P, e ⊆ S t ∧ e.card = 2 :=
    disjoint_pairs _ _ (by have hh := binaryDemand_le_half (S t).card hp0; omega)
  choose pairs hcard hpair hpairs using hchoose
  let pick (E : Finset (Finset (Fin m))) (V : Finset (Fin m)) :=
    (exists_pair_weight_certificate E V).choose
  have hpick E V (hE : ∀ e ∈ E, e ⊆ V ∧ e.card = 2) (z : ℕ)
      (hz : (z : ℝ) * ((V.card : ℝ) + 2 * (E.card : ℝ)) < (V.card : ℝ) ^ 2) :
      pick E V ⊆ V ∧ PairIndependent E (pick E V) ∧ z + 1 ≤ (pick E V).card := by
    obtain ⟨hs, hi, hw⟩ := (exists_pair_weight_certificate E V).choose_spec
    exact ⟨hs, hi, card_ge_of_pair_weight E V hE hz _ hw⟩
  let ℓ := binaryDemand (S first).card p
  let trim (V : Finset (Fin m)) :=
    if h : ℓ ≤ V.card then (Finset.exists_subset_card_eq h).choose else ∅
  have htrim V (hV : ℓ ≤ V.card) : trim V ⊆ V ∧ (trim V).card = ℓ := by
    simpa only [trim, dif_pos hV] using (Finset.exists_subset_card_eq hV).choose_spec
  exact ⟨_, binary_large_bundle_via hp hmax S first pairs hcard hpair hpairs
    pick hpick trim htrim⟩

/-- The large-type-count branch of the binary online guarantee. -/
theorem binary_large_guarantee {m k : ℕ} (hk : 7 ≤ k)
    (S : Fin k → Finset (Fin m)) :
    ∃ policy : Policy m k 2, policy.Guarantees (fun t => approvalValue (S t))
      (fun t => (1 / (pairParameter k : ℝ)) *
        maximinShare (approvalValue (S t)) 2 (by decide)) Finset.univ := by
  obtain ⟨hp, _, hmax⟩ := pairParameter_spec hk
  exact binary_policy_of_demands (by omega) S (binary_large_bundle hp hmax S)

end OnlineMMS
