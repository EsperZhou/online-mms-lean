import OnlineMMS.MainTheorem
import OnlineMMS.PairShares
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Option

namespace OnlineMMS

/-- The supports for pair types are the unordered two-element subsets of the goods. -/
private abbrev PairTypes (m : ℕ) :=
  ↥((Finset.univ : Finset (Fin m)).powersetCard 2)

private theorem pair_labels_card (m : ℕ) :
    Fintype.card (Option (PairTypes m)) = 1 + m.choose 2 := by
  simp [PairTypes, Finset.card_powersetCard, Nat.add_comm]

private def labelValue {m : ℕ} : Option (PairTypes m) → Fin m → ℝ
  | none => fun _ => 1
  | some pair => fun g => if g ∈ pair.val then 1 else 0

/-- For a single fixed binary instance, sending its all-goods type first forces
a choice. A first bundle of size at most one pays at most one against MMS p.
Every larger first bundle leaves some pair type, whose MMS is one, with no
value in the entire remainder. -/
theorem pair_adversary_instance {p k : ℕ} (hcount : 1 + (p + p).choose 2 ≤ k) :
    ∃ (v : Fin k → Fin (p + p) → ℝ) (first : Fin k),
      (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      maximinShare (v first) 2 (by decide) = (p : ℝ) ∧
      ∀ bundle : Finset (Fin (p + p)),
        bundleValue (v first) bundle ≤ 1 ∨
        ∃ next : Fin k, maximinShare (v next) 2 (by decide) = 1 ∧
          ∀ G ⊆ Finset.univ \ bundle, bundleValue (v next) G = 0 := by
  classical
  let m := p + p
  let label := Option (PairTypes m)
  have hcard : Fintype.card label ≤ k := (pair_labels_card m).trans_le hcount
  let encode : label → Fin k := fun a => Fin.castLE hcard (Fintype.equivFin label a)
  have hinj : Function.Injective encode :=
    (Fin.castLE_injective hcard).comp (Fintype.equivFin label).injective
  let zero : Fin k → Fin m → ℝ := fun _ _ => 0
  let v := Function.extend encode labelValue zero
  have hval (a : label) : v (encode a) = labelValue a :=
    hinj.extend_apply labelValue zero a
  refine ⟨v, encode none, ?_, ?_, ?_⟩
  · intro t g
    by_cases ht : ∃ a, encode a = t
    · obtain ⟨a, rfl⟩ := ht
      rw [hval]
      cases a with
      | none => exact Or.inr rfl
      | some pair =>
        by_cases h : g ∈ pair.val
        · right; simp [labelValue, h]
        · left; simp [labelValue, h]
    · show v t g = 0 ∨ v t g = 1
      exact Or.inl (congrFun (Function.extend_apply' labelValue zero t ht) g)
  · rw [hval]
    exact two_agent_unit_mms p
  · intro bundle
    by_cases hsize : bundle.card ≤ 1
    · left
      rw [hval]
      have hs : (bundle.card : ℝ) ≤ 1 := by exact_mod_cast hsize
      simpa [labelValue, bundleValue, nsmul_eq_mul] using hs
    · have htwo : 2 ≤ bundle.card := by omega
      obtain ⟨S, hS, hcardS⟩ := Finset.exists_subset_card_eq htwo
      let pair : PairTypes m :=
        ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcardS⟩⟩
      right
      refine ⟨encode (some pair), ?_, ?_⟩
      · rw [hval]
        exact two_agent_pair_mms S hcardS
      · intro G hG
        rw [hval]
        apply Finset.sum_eq_zero
        intro g hg
        have hnot : g ∉ S := fun h => (Finset.mem_sdiff.mp (hG hg)).2 (hS h)
        simp [labelValue, pair, hnot]

/-- On the same binary instance, every deterministic two-arrival policy
fails to guarantee any MMS fraction strictly larger than 1/p. -/
theorem pair_adversary_defeats_every_policy {p k : ℕ} (hp : 0 < p)
    (hcount : 1 + (p + p).choose 2 ≤ k) :
    ∃ v : Fin k → Fin (p + p) → ℝ,
      (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      ∀ (a : ℝ), 1 / (p : ℝ) < a → ∀ policy : Policy (p + p) k 2,
        ¬ policy.Guarantees v (fun t => a * maximinShare (v t) 2 (by decide)) Finset.univ := by
  obtain ⟨v, first, hbinary, hfirst, hbranch⟩ := pair_adversary_instance hcount
  refine ⟨v, hbinary, ?_⟩
  intro a ha policy hguarantee
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  cases policy with
  | step bundle next =>
    obtain ⟨_, hpaid, hchild⟩ := hguarantee first
    rcases hbranch (bundle first) with hlow | ⟨t, hshare, hzero⟩
    · change a * maximinShare (v first) 2 (by decide) ≤ _ at hpaid
      rw [hfirst] at hpaid
      have hlarge := (div_lt_iff₀ hpR).mp ha
      linarith
    · cases hnext : next first with
      | step second stop =>
        rw [hnext] at hchild
        obtain ⟨hsub, hpay, _⟩ := hchild t
        change a * maximinShare (v t) 2 (by decide) ≤ _ at hpay
        rw [hshare, mul_one, hzero (second t) hsub] at hpay
        exact (not_le_of_gt (ha.trans_le hpay)) (by positivity)

/-- The binary instance bounds its best attainable fraction, even if the
policy can be optimized for that instance. -/
theorem pair_adversary_best_instance {p k : ℕ} (hp : 0 < p)
    (hcount : 1 + (p + p).choose 2 ≤ k) :
    ∃ v : Fin k → Fin (p + p) → ℝ,
      (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      instanceFactor v (fun t => maximinShare (v t) 2 (by decide)) 2 ≤ 1 / (p : ℝ) := by
  obtain ⟨v, hbinary, hdefeats⟩ := pair_adversary_defeats_every_policy hp hcount
  refine ⟨v, hbinary, ?_⟩
  let b : Fin k → ℝ := fun t => maximinShare (v t) 2 (by decide)
  change instanceFactor v b 2 ≤ 1 / (p : ℝ)
  by_contra! hgt
  obtain ⟨_, policy, hpay⟩ := (instanceFactor_attained v b 2).1
  exact hdefeats (instanceFactor v b 2) hgt policy hpay

private theorem binary_nonneg {m k : ℕ} {v : Fin k → Fin m → ℝ}
    (hv : ∀ t g, v t g = 0 ∨ v t g = 1) (t : Fin k) (g : Fin m) : 0 ≤ v t g := by
  rcases hv t g with h | h <;> norm_num [h]

/-- The pair obstruction at horizon two bounds the uniform MMS optimum,
which takes its infimum over all horizons and instances. -/
theorem alphaMMS_le_pair_fraction {p k : ℕ} (hp : 0 < p)
    (hcount : 1 + (p + p).choose 2 ≤ k) :
    alphaMMS k ≤ 1 / (p : ℝ) := by
  obtain ⟨v, hbinary, hbest⟩ := pair_adversary_best_instance hp hcount
  exact (uniformFactor_le_instance (fun n hn _ v => maximinShare v n hn)
    (show 0 < 2 by decide) v (binary_nonneg hbinary)).trans hbest

private def twoArrivalFactors (b : Benchmark) (k : ℕ)
    (accept : (m : ℕ) → (Fin k → Fin m → ℝ) → Prop) : Set ℝ :=
  {a | ∃ (m : ℕ) (v : Fin k → Fin m → ℝ),
    (∀ t g, 0 ≤ v t g) ∧ accept m v ∧
    a = instanceFactor v (fun t => b 2 (by decide) m (v t)) 2}

private theorem twoArrivalFactors_bounded (b : Benchmark) (k : ℕ)
    (accept : (m : ℕ) → (Fin k → Fin m → ℝ) → Prop) :
    BddBelow (twoArrivalFactors b k accept) := by
  refine ⟨0, ?_⟩
  rintro a ⟨m, v, _, _, rfl⟩
  exact instanceFactor_nonneg v _ 2

noncomputable def alphaTwoArrivalTPS (k : ℕ) : ℝ :=
  sInf (twoArrivalFactors (fun n _ _ v => truncatedShare v n) k (fun _ _ => True))

noncomputable def alphaTwoArrivalMMS (k : ℕ) : ℝ :=
  sInf (twoArrivalFactors (fun n hn _ v => maximinShare v n hn) k (fun _ _ => True))

noncomputable def alphaTwoArrivalBinaryMMS (k : ℕ) : ℝ :=
  sInf (twoArrivalFactors (fun n hn _ v => maximinShare v n hn) k
    (fun _ v => ∀ t g, v t g = 0 ∨ v t g = 1))

/-- The finite horizon bounds in the pair-obstruction proposition. -/
theorem pair_twoArrival_bounds {p k : ℕ} (hp : 0 < p)
    (hcount : 1 + (p + p).choose 2 ≤ k) :
    alphaTwoArrivalTPS k ≤ alphaTwoArrivalMMS k ∧
      alphaTwoArrivalMMS k ≤ alphaTwoArrivalBinaryMMS k ∧
      alphaTwoArrivalBinaryMMS k ≤ 1 / (p : ℝ) := by
  obtain ⟨v, hv, hbest⟩ := pair_adversary_best_instance hp hcount
  have hm : (twoArrivalFactors (fun n hn _ v => maximinShare v n hn) k (fun _ _ => True)).Nonempty :=
    ⟨_, p + p, v, binary_nonneg hv, trivial, rfl⟩
  have hb : (twoArrivalFactors (fun n hn _ v => maximinShare v n hn) k
      (fun _ v => ∀ t g, v t g = 0 ∨ v t g = 1)).Nonempty :=
    ⟨_, p + p, v, binary_nonneg hv, hv, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · apply le_csInf hm
    rintro a ⟨m, w, hw, _, rfl⟩
    exact (csInf_le (twoArrivalFactors_bounded _ _ _) ⟨m, w, hw, trivial, rfl⟩).trans
      (instanceFactor_antitone_benchmark w (fun t =>
        maximinShare_le_truncatedShare (w t) (hw t) (by decide)))
  · apply le_csInf hb
    rintro a ⟨m, w, hw, _, rfl⟩
    exact csInf_le (twoArrivalFactors_bounded _ _ _) ⟨m, w, hw, trivial, rfl⟩
  · exact (csInf_le (twoArrivalFactors_bounded _ _ _)
      ⟨p + p, v, binary_nonneg hv, hv, rfl⟩).trans hbest

end OnlineMMS
