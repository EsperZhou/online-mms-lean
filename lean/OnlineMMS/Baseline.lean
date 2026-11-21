import OnlineMMS.Benchmarks
import OnlineMMS.BaselineBag
import OnlineMMS.BaselineOneType
import OnlineMMS.BaselinePool
import OnlineMMS.BaselinePreprocess
import OnlineMMS.BaselineServe
import OnlineMMS.MainTheorem

/-! The deterministic one-over-k baseline using shared tentative bundles. -/

namespace OnlineMMS

private abbrev Reserves (m k : ℕ) := Fin k → Finset (Finset (Fin m))

private noncomputable abbrev fraction (k : ℕ) : ℝ := 1 / (k : ℝ)

private def Active {m k : ℕ} (d : Fin k → ℝ) (r : ℕ)
    (F : Reserves m k) (t : Fin k) : Prop :=
  0 < d t ∧ (F t).card < r

private structure BaselineValid {m k : ℕ} (w : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (remaining : Finset (Fin m)) (F : Reserves m k) : Prop where
  cap : ∀ t, (F t).card ≤ r
  pays : ∀ t, ∀ B ∈ F t, fraction k ≤ bundleValue (w t) B
  singletons : ∀ t, Active d r F t → ∀ g ∈ remaining, fraction k ≤ w t g → {g} ∈ F t
  legal : ∀ B ∈ reserveBank F, B.Nonempty ∧ B ⊆ remaining
  disjoint : (↑(reserveBank F) : Set (Finset (Fin m))).Pairwise Disjoint
  mass : ∀ t, Active d r F t → (r : ℝ) ≤ bundleValue (w t) remaining
  small : ∀ t, Active d r F t → ∀ B ∈ reserveBank F, bundleValue (w t) B ≤ 1
  coverage : ∀ t, Active d r F t → ∀ B ∈ reserveBank F,
    fraction k ≤ bundleValue (w t) B → B ∈ F t

private noncomputable def addBag {m k : ℕ} (w : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (F : Reserves m k) (B : Finset (Fin m)) :
    Reserves m k := by
  classical
  exact fun t => if Active d r F t ∧ fraction k ≤ bundleValue (w t) B
                 then insert B (F t) else F t

private theorem addBag_extends {m k : ℕ} (w : Fin k → Fin m → ℝ)
    (d : Fin k → ℝ) (r : ℕ) (F : Reserves m k) (B : Finset (Fin m)) (t : Fin k) :
    F t ⊆ addBag w d r F B t := by
  classical
  unfold addBag
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

private theorem add_bag {m k r : ℕ} {w : Fin k → Fin m → ℝ} {d : Fin k → ℝ}
    {R : Finset (Fin m)} {F : Reserves m k} (hF : BaselineValid w d r R F)
    {B : Finset (Fin m)} (hB : B ⊆ freePool R F) (hBne : B.Nonempty)
    (hhits : ∃ t, Active d r F t ∧ fraction k ≤ bundleValue (w t) B)
    (hsmall : ∀ t, Active d r F t → bundleValue (w t) B ≤ 1) :
    BaselineValid w d r R (addBag w d r F B) ∧
      (freePool R (addBag w d r F B)).card < (freePool R F).card := by
  classical
  let F' := addBag w d r F B
  have hsub (t : Fin k) : F t ⊆ F' t := addBag_extends w d r F B t
  have hbank : reserveBank F' = insert B (reserveBank F) := by
    ext C
    rw [Finset.mem_insert, mem_reserveBank, mem_reserveBank]
    constructor
    · rintro ⟨t, ht⟩
      dsimp [F', addBag] at ht
      split at ht
      · rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr ⟨t, ht⟩
      · exact Or.inr ⟨t, ht⟩
    · rintro (h | ⟨t, ht⟩)
      · subst C
        obtain ⟨t, ht⟩ := hhits
        refine ⟨t, ?_⟩
        change B ∈ addBag w d r F B t
        rw [addBag, if_pos ht]
        exact Finset.mem_insert_self _ _
      · exact ⟨t, hsub t ht⟩
  have hactive (t : Fin k) (ht : Active d r F' t) : Active d r F t :=
    ⟨ht.1, (Finset.card_le_card (hsub t)).trans_lt ht.2⟩
  have hR : B ⊆ R := hB.trans (freePool_subset R F)
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun t ht => hF.mass t (hactive t ht), ?_, ?_⟩
    · intro t
      dsimp [F', addBag]
      split
      · rename_i ht
        exact (Finset.card_insert_le _ _).trans (by have := ht.1.2; omega)
      · exact hF.cap t
    · intro t C hC
      dsimp [F', addBag] at hC
      split at hC
      · rename_i ht
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact ht.2
        · exact hF.pays t C hC
      · exact hF.pays t C hC
    · intro t ht g hg hpay
      exact hsub t (hF.singletons t (hactive t ht) g hg hpay)
    · intro C hC
      rw [hbank, Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact ⟨hBne, hR⟩
      · exact hF.legal C hC
    · intro C hC D hD hne
      change C ∈ reserveBank F' at hC
      change D ∈ reserveBank F' at hD
      rw [hbank, Finset.mem_insert] at hC hD
      rcases hC with rfl | hC
      · rcases hD with rfl | hD
        · exact False.elim (hne rfl)
        · exact disjoint_of_subset_freePool hB hD
      · rcases hD with rfl | hD
        · exact (disjoint_of_subset_freePool hB hC).symm
        · exact hF.disjoint hC hD hne
    · intro t ht C hC
      rw [hbank, Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact hsmall t (hactive t ht)
      · exact hF.small t (hactive t ht) C hC
    · intro t ht C hC hpay
      rw [hbank, Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · unfold addBag
        rw [if_pos ⟨hactive t ht, hpay⟩]
        exact Finset.mem_insert_self _ _
      · exact hsub t (hF.coverage t (hactive t ht) C hC hpay)
  · apply Finset.card_lt_card
    have hp : freePool R F' ⊆ freePool R F := by
      intro g hg
      simp only [freePool, hbank, Finset.mem_sdiff, Finset.mem_biUnion] at hg ⊢
      refine ⟨hg.1, fun ⟨C, hC, hgc⟩ => hg.2 ⟨C, Finset.mem_insert_of_mem hC, hgc⟩⟩
    refine (Finset.ssubset_iff_of_subset hp).mpr ?_
    obtain ⟨g, hg⟩ := hBne
    refine ⟨g, hB hg, fun h => ?_⟩
    simp only [freePool, hbank, Finset.mem_sdiff, Finset.mem_biUnion] at h
    exact h.2 ⟨B, Finset.mem_insert_self _ _, hg⟩

private theorem find_qualified_bag {m k r : ℕ} {w : Fin k → Fin m → ℝ}
    {d : Fin k → ℝ} {R : Finset (Fin m)}
    (hk : 2 ≤ k) (hr : 0 < r) (hw : ∀ t g, 0 ≤ w t g ∧ w t g ≤ 1)
    (t : Fin k) (ht : 0 < d t) (F : Reserves m k)
    (hF : BaselineValid w d r R F) :
    ∃ F' : Reserves m k, BaselineValid w d r R F' ∧ (F' t).Nonempty := by
  classical
  by_cases hex : (F t).Nonempty
  · exact ⟨F, hF, hex⟩
  have hempty : F t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hex
  have htactive : Active d r F t := ⟨ht, by simpa [hempty] using hr⟩
  have hpool : fraction k ≤ bundleValue (w t) (freePool R F) := by
    apply threshold_le_freePool (w t) R F r t hr (fun g => (hw t g).1) hF.cap hempty
    · intro C hC
      by_contra! h
      have : C ∈ F t := hF.coverage t htactive C hC h.le
      simp [hempty] at this
    · exact hF.mass t htactive
  let A : Finset (Fin k) := Finset.univ.filter (Active d r F)
  have hA (i : Fin k) : i ∈ A ↔ Active d r F i := by simp [A]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have hβ : 0 < fraction k := by positivity
  have hβ2 : 2 * fraction k ≤ 1 := by
    unfold fraction
    rw [mul_one_div]
    exact (div_le_one₀ hkp).2 hkR
  have hitems (i : Fin k) (hi : i ∈ A) (g : Fin m) (hg : g ∈ freePool R F) :
      w i g < fraction k := by
    apply lt_of_not_ge
    intro hge
    obtain ⟨hgR, hn⟩ := Finset.mem_sdiff.mp hg
    have hmem := hF.singletons i ((hA i).1 hi) g hgR hge
    exact hn (Finset.mem_biUnion.mpr
      ⟨{g}, mem_reserveBank.mpr ⟨i, hmem⟩, Finset.mem_singleton_self g⟩)
  obtain ⟨B, hB, hne, hreach, hsmall, _⟩ := exists_crossing_bag w (freePool R F) A hβ
    hitems ⟨t, (hA t).2 htactive, hpool⟩
  have hreach' : ∃ i, Active d r F i ∧ fraction k ≤ bundleValue (w i) B := by
    obtain ⟨i, hi, hpay⟩ := hreach
    exact ⟨i, (hA i).1 hi, hpay⟩
  have hsmall' (i : Fin k) (hi : Active d r F i) : bundleValue (w i) B ≤ 1 :=
    (hsmall i ((hA i).2 hi)).trans hβ2
  obtain ⟨hvalid, hdecrease⟩ := add_bag hF hB hne hreach' hsmall'
  exact find_qualified_bag hk hr hw t ht (addBag w d r F B) hvalid
termination_by (freePool R F).card
decreasing_by exact hdecrease

private theorem serve_bag {m k r : ℕ} {w : Fin k → Fin m → ℝ} {d : Fin k → ℝ}
    {R B : Finset (Fin m)} {F : Reserves m k} (hF : BaselineValid w d (r + 1) R F)
    (hB : B ∈ reserveBank F ∨ B = ∅) :
    ∃ F' : Reserves m k, BaselineValid w d r (R \ B) F' := by
  classical
  obtain ⟨F', hsub, hcap, htrim⟩ := exists_trim_reserves (r := r) F B
  have hbefore (i : Fin k) (hi : Active d r F' i) : Active d (r + 1) F i :=
    ⟨hi.1, (htrim i hi.2).1⟩
  have hleft (C : Finset (Fin m)) (hC : C ∈ reserveBank F') :
      C ∈ reserveBank F ∧ C ≠ B := by
    obtain ⟨i, hi⟩ := mem_reserveBank.mp hC
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (hsub i hi)
    exact ⟨mem_reserveBank.mpr ⟨i, hmem⟩, hne⟩
  have hBsub : B ⊆ R := by
    rcases hB with hB | rfl
    · exact (hF.legal B hB).2
    · exact Finset.empty_subset _
  refine ⟨F', ⟨hcap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i C hC => hF.pays i C (Finset.mem_erase.mp (hsub i hC)).2
  · intro t ht g hg hpay
    obtain ⟨hgR, hgB⟩ := Finset.mem_sdiff.mp hg
    rw [(htrim t ht.2).2]
    refine Finset.mem_erase.mpr ⟨?_, hF.singletons t (hbefore t ht) g hgR hpay⟩
    rintro h
    exact hgB (h ▸ Finset.mem_singleton_self g)
  · intro C hC
    obtain ⟨i, hi⟩ := mem_reserveBank.mp hC
    refine ⟨(hF.legal C (hleft C hC).1).1, trimmed_reserve_subset_remaining hsub ?_ ?_ i C hi⟩
    · exact fun j D hD => (hF.legal D (mem_reserveBank.mpr ⟨j, hD⟩)).2
    · intro j D hD hne
      rcases hB with hB | rfl
      · exact hF.disjoint (mem_reserveBank.mpr ⟨j, hD⟩) hB hne
      · simp

  · exact fun C hC D hD hne => hF.disjoint (hleft C hC).1 (hleft D hD).1 hne
  · intro i hi
    have hmass := hF.mass i (hbefore i hi)
    have hloss : bundleValue (w i) B ≤ 1 := by
      rcases hB with hB | rfl
      · exact hF.small i (hbefore i hi) B hB
      · simp [bundleValue]
    have hsum := Finset.sum_sdiff hBsub (f := w i)
    unfold bundleValue at *
    push_cast at hmass
    linarith
  · exact fun i hi C hC => hF.small i (hbefore i hi) C (hleft C hC).1
  · intro i hi C hC hpay
    rw [(htrim i hi.2).2]
    exact Finset.mem_erase.mpr ⟨(hleft C hC).2,
      hF.coverage i (hbefore i hi) C (hleft C hC).1 hpay⟩

/-- The shared-reservation argument yields a one-over-k share of original TPS
    when there are at least two listed types. -/
theorem one_over_k_tps_policy {m n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => truncatedShare (v t) n / (k : ℝ)) Finset.univ := by
  classical
  let d : Fin k → ℝ := fun t => truncatedShare (v t) n
  let w : Fin k → Fin m → ℝ := fun t => normalizedWeight (v t) n
  have hd (t : Fin k) : 0 ≤ d t := (truncatedShare_spec (v t) (hv t) hn).1.1
  have wzero (t : Fin k) (ht : ¬0 < d t) (g : Fin m) : w t g = 0 := by
    have he : truncatedShare (v t) n = 0 := le_antisymm (le_of_not_gt ht) (hd t)
    simp [w, normalizedWeight, he]
  have hw (t : Fin k) (g : Fin m) : 0 ≤ w t g ∧ w t g ≤ 1 := by
    by_cases ht : 0 < d t
    · exact ⟨normalizedWeight_nonneg (v t) (hv t) ht g, normalizedWeight_le_one (v t) ht g⟩
    · rw [wzero t ht g]
      norm_num
  obtain ⟨F, hcap, hsingle, hcomplete⟩ := exists_initial_reserves w n (fraction k)
  let initial : Finset (Fin m) × Reserves m k := (Finset.univ, F)
  have hbank (B : Finset (Fin m)) (hB : B ∈ reserveBank F) :
      ∃ g : Fin m, B = {g} := by
    obtain ⟨t, ht⟩ := mem_reserveBank.mp hB
    obtain ⟨g, hg, _⟩ := hsingle t B ht
    exact ⟨g, hg⟩
  have hinit : BaselineValid w d n initial.1 initial.2 := by
    refine ⟨hcap, ?_, fun t ht g _ => hcomplete t ht.2 g, ?_, ?_, ?_, ?_, ?_⟩
    · intro t B hB
      obtain ⟨g, rfl, hpay⟩ := hsingle t B hB
      simpa [bundleValue] using hpay
    · intro B hB
      obtain ⟨g, rfl⟩ := hbank B hB
      exact ⟨Finset.singleton_nonempty g, Finset.subset_univ _⟩
    · intro B hB C hC hne
      obtain ⟨g, rfl⟩ := hbank B hB
      obtain ⟨j, rfl⟩ := hbank C hC
      exact Finset.disjoint_singleton.mpr (fun h => hne (congrArg (fun x => ({x} : Finset (Fin m))) h))
    · intro t ht
      exact (sum_normalizedWeight (v t) (hv t) hn ht.1).ge
    · intro t _ B hB
      obtain ⟨g, rfl⟩ := hbank B hB
      simpa [bundleValue] using (hw t g).2
    · intro t ht B hB hpay
      obtain ⟨g, rfl⟩ := hbank B hB
      exact hcomplete t ht.2 g (by simpa [bundleValue] using hpay)
  have hstep (r : ℕ) (x : Finset (Fin m) × Reserves m k)
      (hx : BaselineValid w d (r + 1) x.1 x.2) (t : Fin k) :
      ∃ B y, B ⊆ x.1 ∧ d t / (k : ℝ) ≤ bundleValue (v t) B ∧
        (y : Finset (Fin m) × Reserves m k).1 = x.1 \ B ∧ BaselineValid w d r y.1 y.2 := by
    by_cases ht : 0 < d t
    · obtain ⟨F', hF', hready⟩ := find_qualified_bag hk (by omega) hw t ht x.2 hx
      obtain ⟨B, hB⟩ := hready
      have hbank : B ∈ reserveBank F' := mem_reserveBank.mpr ⟨t, hB⟩
      obtain ⟨next, hnext⟩ := serve_bag hF' (Or.inl hbank)
      refine ⟨B, (x.1 \ B, next), (hF'.legal B hbank).2, ?_, rfl, hnext⟩
      calc
        d t / (k : ℝ) = d t * fraction k := by simp [fraction, div_eq_mul_inv]
        _ ≤ d t * bundleValue (w t) B :=
          mul_le_mul_of_nonneg_left (hF'.pays t B hB) ht.le
        _ = ∑ g ∈ B, d t * w t g := Finset.mul_sum ..
        _ ≤ bundleValue (v t) B :=
          Finset.sum_le_sum (fun g _ => truncatedShare_mul_normalizedWeight_le (v t) ht g)
    · obtain ⟨next, hnext⟩ := serve_bag hx (B := ∅) (Or.inr rfl)
      have hz : d t = 0 := le_antisymm (le_of_not_gt ht) (hd t)
      exact ⟨∅, (x.1 \ ∅, next), Finset.empty_subset _, by simp [hz, bundleValue], rfl, hnext⟩
  exact policy_of_steps Prod.fst (fun r x => BaselineValid w d r x.1 x.2)
    v (fun t => d t / (k : ℝ)) hstep n initial hinit

/-- The general deterministic one-over-k MMS guarantee for every positive
    horizon and number of listed types. -/
theorem one_over_k_mms_policy {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℝ) (hv : ∀ t g, 0 ≤ v t g) :
    ∃ policy : Policy m k n,
      policy.Guarantees v (fun t => maximinShare (v t) n hn / (k : ℝ)) Finset.univ := by
  by_cases h : k = 1
  · subst k
    simpa using exists_one_type_mms_policy hn v
  · obtain ⟨policy, hp⟩ := one_over_k_tps_policy hn (by omega) v hv
    exact ⟨policy, hp.mono (fun t =>
      div_le_div_of_nonneg_right (maximinShare_le_truncatedShare (v t) (hv t) hn)
        (Nat.cast_nonneg k))⟩

/-- The one-over-k guarantee remains valid after taking the worst case over all
    valuation lists, goods counts and positive horizons. -/
theorem one_over_k_le_alphaMMS {k : ℕ} (hk : 0 < k) :
    1 / (k : ℝ) ≤ alphaMMS k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hOne : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  apply le_uniformFactor
  · exact ⟨by positivity, (div_le_one₀ hkR).mpr hOne⟩
  · intro n hn m v hv
    obtain ⟨policy, hp⟩ := one_over_k_mms_policy hn hk v hv
    exact ⟨policy, by simpa [div_eq_mul_inv, mul_comm] using hp⟩

end OnlineMMS
