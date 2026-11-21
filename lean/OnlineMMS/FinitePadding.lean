import OnlineMMS.FiniteHorizon
import Mathlib.Algebra.BigOperators.Fin

namespace OnlineMMS

private def padded {m : ℕ} (q : ℝ) (v : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.lastCases q v

private def oldGoods {m : ℕ} (R : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun g => g.castSucc ∈ R)

@[simp] private theorem mem_oldGoods {m : ℕ} {R : Finset (Fin (m + 1))} {g : Fin m} :
    g ∈ oldGoods R ↔ g.castSucc ∈ R := by simp [oldGoods]

private theorem oldGoods_sdiff {m : ℕ} (R G : Finset (Fin (m + 1))) :
    oldGoods (R \ G) = oldGoods R \ oldGoods G := by
  ext g
  simp [Finset.mem_sdiff]

private theorem oldGoods_subset {m : ℕ} {R G : Finset (Fin (m + 1))}
    (h : R ⊆ G) : oldGoods R ⊆ oldGoods G := by
  intro g hg
  exact mem_oldGoods.mpr (h (mem_oldGoods.mp hg))

private theorem padded_bundleValue {m : ℕ} (q : ℝ) (v : Fin m → ℝ)
    (R : Finset (Fin (m + 1))) :
    bundleValue (padded q v) R =
      bundleValue v (oldGoods R) + (if Fin.last m ∈ R then q else 0) := by
  classical
  unfold bundleValue oldGoods
  rw [Finset.sum_filter]
  calc
    _ = ∑ g : Fin (m + 1), if g ∈ R then padded q v g else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by rw [Fin.sum_univ_castSucc]; simp [padded]

private theorem padded_nonneg {m : ℕ} {q : ℝ} {v : Fin m → ℝ}
    (hq : 0 ≤ q) (hv : ∀ g, 0 ≤ v g) : ∀ g, 0 ≤ padded q v g := by
  intro g
  refine Fin.lastCases ?_ (fun j => ?_) g
  · simpa [padded] using hq
  · simpa [padded] using hv j

/-- Adding a good worth the old MMS preserves MMS when the horizon rises by one. -/
theorem padding_preserves_mms {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) :
    maximinShare (padded (maximinShare v n hn) v) (n + 1) (by omega) = maximinShare v n hn := by
  classical
  let q := maximinShare v n hn
  let w := padded q v
  apply le_antisymm
  · obtain ⟨p,hp⟩ := paymentPartition_of_mms w (show 0 < n+1 by omega)
    let z := Fin.last m
    let U := (Finset.univ : Finset (Fin (m + 1))) \ Finset.univ.filter (fun g => p g = p z)
    have hz : z ∉ U := by simp [U]
    obtain ⟨r,hr⟩ := paymentPartition_removePart w Finset.univ hn p (p z) hp
    let f : Fin m → Fin n := fun g => r g.castSucc
    apply le_trans _ (partitionMin_le_maximinShare v hn f)
    apply Finset.le_inf'
    intro j _
    let T := U.filter (fun g => r g = j)
    have hzT : z ∉ T := fun h => hz ((Finset.mem_filter.mp h).1)
    have hsub : oldGoods T ⊆ Finset.univ.filter (fun g => f g = j) := by
      intro g hg
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (mem_oldGoods.mp hg)).2⟩
    have hvalue := hr j
    change maximinShare w (n + 1) (by omega) ≤ bundleValue w T at hvalue
    rw [show bundleValue w T = bundleValue v (oldGoods T) by
      simpa [w, z, hzT] using padded_bundleValue q v T] at hvalue
    exact hvalue.trans (bundleValue_mono v hv hsub)
  · obtain ⟨p,hp⟩ := paymentPartition_of_mms v hn
    let r : Fin (m + 1) → Fin (n + 1) := Fin.lastCases (Fin.last n) (fun g => (p g).castSucc)
    apply le_trans _ (partitionMin_le_maximinShare w (by omega) r)
    apply Finset.le_inf'
    intro j _
    refine Fin.lastCases
      (motive := fun j => q ≤ bundleValue w (Finset.univ.filter (fun g => r g = j)))
      ?_ (fun i => ?_) j
    · change q ≤ bundleValue w (Finset.univ.filter (fun g => r g = Fin.last n))
      rw [show bundleValue w (Finset.univ.filter (fun g => r g = Fin.last n)) = _
          from padded_bundleValue q v _]
      have he : oldGoods (Finset.univ.filter (fun g => r g = Fin.last n)) = ∅ := by
        ext g
        simp [r, Fin.castSucc_ne_last]
      rw [he]
      simp [r,bundleValue]
    · change q ≤ bundleValue w (Finset.univ.filter (fun g => r g = i.castSucc))
      rw [show bundleValue w (Finset.univ.filter (fun g => r g = i.castSucc)) = _
          from padded_bundleValue q v _]
      have he : oldGoods (Finset.univ.filter (fun g => r g = i.castSucc)) =
          Finset.univ.filter (fun g => p g = i) := by
        ext g
        simp [r]
      rw [he]
      simpa [r,(Fin.castSucc_ne_last i).symm] using hp i

/-- Adding one good worth the old TPS preserves TPS when the horizon rises by one. -/
theorem padding_preserves_tps {m n : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) :
    truncatedShare (padded (truncatedShare v n) v) (n + 1) = truncatedShare v n := by
  let d := truncatedShare v n
  let w := padded d v
  have hspec := truncatedShare_spec v hv hn
  have haug := truncatedShare_spec w (padded_nonneg hspec.1.1 hv) (show 0 < n + 1 by omega)
  have hsum (y : ℝ) : (∑ g, min (w g) y) = (∑ g, min (v g) y) + min d y := by
    rw [Fin.sum_univ_castSucc]
    simp [w,padded]
  apply le_antisymm
  · apply hspec.2
    refine ⟨haug.1.1, ?_⟩
    have h := haug.1.2
    rw [hsum] at h
    push_cast at h
    linarith [min_le_right d (truncatedShare w (n + 1))]
  · apply haug.2
    refine ⟨hspec.1.1, ?_⟩
    rw [hsum, min_self]
    push_cast
    linarith [hspec.1.2]

private theorem guarantees_expand {m k n : ℕ} (p : Policy m k n)
    (v : Fin k → Fin m → ℝ) (q : Fin k → ℝ) {R S : Finset (Fin m)}
    (hRS : R ⊆ S) (hp : p.Guarantees v q R) : p.Guarantees v q S := by
  induction p generalizing R S with
  | done => trivial
  | step bundles next ih =>
    intro t
    obtain ⟨hsub,hpay,hcont⟩ := hp t
    refine ⟨hsub.trans hRS,hpay,ih t ?_ hcont⟩
    intro g hg
    exact Finset.mem_sdiff.mpr
      ⟨hRS (Finset.mem_sdiff.mp hg).1,(Finset.mem_sdiff.mp hg).2⟩

private theorem simulate_when_absent {m k n : ℕ} (v : Fin k → Fin m → ℝ)
    (zval target : Fin k → ℝ) (p : Policy (m + 1) k n) (R : Finset (Fin (m + 1)))
    (hz : Fin.last m ∉ R) (hp : p.Guarantees (fun t => padded (zval t) (v t)) target R) :
    ∃ actual : Policy m k n, actual.Guarantees v target (oldGoods R) := by
  induction p generalizing R with
  | done => exact ⟨.done,trivial⟩
  | step bundles next ih =>
    apply policy_step_of_choices
    intro t
    obtain ⟨hsub,hpay,hcont⟩ := hp t
    have hzB : Fin.last m ∉ bundles t := fun h => hz (hsub h)
    have hzR : Fin.last m ∉ R \ bundles t := fun h => hz ((Finset.mem_sdiff.mp h).1)
    obtain ⟨pr,hpr⟩ := ih t (R \ bundles t) hzR hcont
    refine ⟨oldGoods (bundles t),pr,oldGoods_subset hsub,?_,?_⟩
    · simpa [padded_bundleValue,hzB] using hpay
    · simpa [oldGoods_sdiff] using hpr

/-- Simulating the virtual policy and skipping the allocation of the padding good
preserves all targets on the original instance. -/
theorem simulate_padding_policy {m k n : ℕ} (v : Fin k → Fin m → ℝ)
    (zval target : Fin k → ℝ) (p : Policy (m + 1) k (n + 1)) (R : Finset (Fin (m + 1)))
    (hp : p.Guarantees (fun t => padded (zval t) (v t)) target R) :
    ∃ actual : Policy m k n, actual.Guarantees v target (oldGoods R) := by
  induction n generalizing R with
  | zero => exact ⟨.done,trivial⟩
  | succ n ih =>
    cases p with
    | step bundles next =>
      apply policy_step_of_choices
      intro t
      obtain ⟨hsub,hpay,hcont⟩ := hp t
      let V := R \ bundles t
      by_cases hz : Fin.last m ∈ bundles t
      · have hfree : Fin.last m ∉ V := fun h => (Finset.mem_sdiff.mp h).2 hz
        cases hnext : next t with
        | step later after =>
          rw [hnext] at hcont
          obtain ⟨hsub₂,hpay₂,hcont₂⟩ := hcont t
          have hfree₂ : Fin.last m ∉ later t := fun h => hfree (hsub₂ h)
          have hfree₃ : Fin.last m ∉ V \ later t := fun h => hfree ((Finset.mem_sdiff.mp h).1)
          obtain ⟨pr,hpr⟩ := simulate_when_absent v zval target (after t) (V \ later t)
            hfree₃ hcont₂
          refine ⟨oldGoods (later t),pr,oldGoods_subset (hsub₂.trans Finset.sdiff_subset),?_,?_⟩
          · simpa [padded_bundleValue,hfree₂] using hpay₂
          · apply guarantees_expand pr v target _ hpr
            rw [oldGoods_sdiff]
            intro g hg
            obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hg
            exact Finset.mem_sdiff.mpr ⟨oldGoods_subset Finset.sdiff_subset h₁,h₂⟩
      · obtain ⟨pr,hpr⟩ := ih (next t) V hcont
        refine ⟨oldGoods (bundles t),pr,oldGoods_subset hsub,?_,?_⟩
        · simpa [padded_bundleValue,hz] using hpay
        · simpa [V,oldGoods_sdiff] using hpr

private theorem horizon_padding {k n : ℕ} (b : Benchmark) (hn : 0 < n)
    (hb : ∀ (m : ℕ) (v : Fin m → ℝ), (∀ g, 0 ≤ v g) →
      0 ≤ b n hn m v ∧ b (n + 1) (by omega) (m + 1) (padded (b n hn m v) v) = b n hn m v) :
    horizonFactor b k (n + 1) (by omega) ≤ horizonFactor b k n hn := by
  apply le_horizonFactor b hn
  intro m v hv
  let w : Fin k → Fin (m+1) → ℝ := fun t => padded (b n hn m (v t)) (v t)
  have hw (t : Fin k) : ∀ g, 0 ≤ w t g := padded_nonneg (hb m _ (hv t)).1 (hv t)
  have heq (t : Fin k) : b (n+1) (by omega) (m+1) (w t) = b n hn m (v t) :=
    (hb m _ (hv t)).2
  let z := instanceFactor w (fun t => b (n+1) (by omega) (m+1) (w t)) (n+1)
  have hz := horizonFactor_le_instance b (show 0 < n+1 by omega) w hw
  refine hz.trans ?_
  obtain ⟨hzrange,p,hp⟩ := (instanceFactor_attained w _ (n+1)).1
  change p.Guarantees w (fun t => z * b (n+1) (by omega) (m+1) (w t)) Finset.univ at hp
  simp_rw [heq] at hp
  obtain ⟨actual,hactual⟩ := simulate_padding_policy v (fun t => b n hn m (v t))
    (fun t => z * b n hn m (v t)) p Finset.univ hp
  apply (instanceFactor_attained v _ n).2
  exact ⟨hzrange, actual, by simpa [oldGoods] using hactual⟩

theorem alpha_horizon_mms_padding {k n : ℕ} (hn : 0 < n) :
    alphaHorizonMMS k (n+1) (by omega) ≤ alphaHorizonMMS k n hn :=
  horizon_padding _ hn fun _ v hv => ⟨maximinShare_nonnegative v hv hn, padding_preserves_mms v hv hn⟩

theorem alpha_horizon_tps_padding {k n : ℕ} (hn : 0 < n) :
    alphaHorizonTPS k (n+1) (by omega) ≤ alphaHorizonTPS k n hn :=
  horizon_padding _ hn fun _ v hv => ⟨(truncatedShare_spec v hv hn).1.1, padding_preserves_tps v hv hn⟩

end OnlineMMS
