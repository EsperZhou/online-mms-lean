import OnlineMMS.PairObstruction
import OnlineMMS.PairCount
import OnlineMMS.RandomTape

namespace OnlineMMS.ObliviousPair

open scoped Classical

open private PairTypes pair_labels_card labelValue from OnlineMMS.PairObstruction

private abbrev supports (m : ℕ) := (Finset.univ : Finset (Fin m)).powersetCard 2

/-- The pair instance keeps a single type label for every unordered pair. -/
private theorem labelledInstance {p k : ℕ} (fit : 1 + (p+p).choose 2 ≤ k) :
    ∃ (v : Fin k → Fin (p+p) → ℝ) (first : Fin k)
      (second : Finset (Fin (p+p)) → Fin k),
      (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      v first = (fun _ => 1) ∧
      ∀ S ∈ supports (p+p), v (second S) = fun g => if g ∈ S then 1 else 0 := by
  classical
  let m := p+p
  let L := Option (PairTypes m)
  have hcard : Fintype.card L ≤ k := (pair_labels_card m).trans_le fit
  let en : L → Fin k := fun a => Fin.castLE hcard (Fintype.equivFin L a)
  have hinj : Function.Injective en :=
    (Fin.castLE_injective hcard).comp (Fintype.equivFin L).injective
  let pad : Fin k → Fin m → ℝ := fun _ _ => 0
  let v := Function.extend en labelValue pad
  have hv (a : L) : v (en a) = labelValue a := hinj.extend_apply labelValue pad a
  let second (S : Finset (Fin m)) := if h : S ∈ supports m then en (some ⟨S,h⟩) else en none
  refine ⟨v, en none, second, ?_, hv none, ?_⟩
  · intro t g
    by_cases h : ∃ a, en a = t
    · obtain ⟨a, rfl⟩ := h
      rw [hv]
      cases a with
      | none => exact Or.inr rfl
      | some pair =>
        by_cases hg : g ∈ pair.val
        · right; simp [labelValue, hg]
        · left; simp [labelValue, hg]
    · exact Or.inl (congrFun (Function.extend_apply' labelValue pad t h) g)
  · intro S hS
    simpa only [second, dif_pos hS] using hv (some ⟨S,hS⟩)

def pairSeq {k : ℕ} (f s : Fin k) : Fin 2 → Fin k :=
  Fin.cons f (fun _ => s)

private def firstBundle {m k : ℕ} (pi : Policy m k 2) (first : Fin k) : Finset (Fin m) :=
  match pi with
  | .step bundle _ => bundle first

private noncomputable abbrev target {m k : ℕ} (v : Fin k → Fin m → ℝ) (x : ℝ) (t : Fin k) :=
  x * maximinShare (v t) 2 (by decide)

private theorem short_fails {p k : ℕ} {v : Fin k → Fin (p+p) → ℝ} {first s : Fin k}
    (allGoods : v first = fun _ => 1) (pi : Policy (p+p) k 2) {x : ℝ}
    (short : (firstBundle pi first).card < ⌈x * p⌉₊) :
    ¬pi.GuaranteesSequence v (target v x) Finset.univ (pairSeq first s) := by
  cases pi with
  | step b next =>
    intro success
    have pay : target v x first ≤ bundleValue (v first) (b first) := success.2.1
    have low : ((b first).card : ℝ) < x * p :=
      lt_of_not_ge (fun h => (not_le_of_gt short) (Nat.ceil_le.mpr h))
    unfold target at pay
    rw [allGoods, two_agent_unit_mms] at pay
    exact (not_le_of_gt low) (by simpa [bundleValue] using pay)

private theorem trapped_fails {p k : ℕ} {v : Fin k → Fin (p+p) → ℝ} {first s : Fin k}
    {S : Finset (Fin (p+p))} (hS : S.card = 2)
    (hs : v s = fun g => if g ∈ S then 1 else 0)
    (pi : Policy (p+p) k 2) (trapped : S ⊆ firstBundle pi first) {x : ℝ} (hx : 0 < x) :
    ¬pi.GuaranteesSequence v (target v x) Finset.univ (pairSeq first s) := by
  cases pi with
  | step b cont =>
    intro success
    have child : (cont first).GuaranteesSequence v (target v x) (Finset.univ \ b first)
        (fun _ => s) := by simpa [pairSeq] using success.2.2
    cases e : cont first with
    | step b₂ stop =>
      rw [e] at child
      have sub : b₂ s ⊆ Finset.univ \ b first := child.1
      have pay : target v x s ≤ bundleValue (v s) (b₂ s) := child.2.1
      have zero : bundleValue (v s) (b₂ s) = 0 := by
        apply Finset.sum_eq_zero
        intro g hg
        have hnot : g ∉ S := fun h => (Finset.mem_sdiff.mp (sub hg)).2 (trapped h)
        simp [hs, hnot]
      unfold target at pay
      rw [zero, hs, two_agent_pair_mms S hS, mul_one] at pay
      exact (not_le_of_gt hx) pay

private theorem failing_count {p k : ℕ} {x : ℝ} {first : Fin k}
    {v : Fin k → Fin (p+p) → ℝ} {second : Finset (Fin (p+p)) → Fin k}
    (allGoods : v first = fun _ => 1)
    (hsecond : ∀ S ∈ supports (p+p), v (second S) = fun g => if g ∈ S then 1 else 0)
    (pi : Policy (p+p) k 2) (hx : 0 < x) (hx1 : x ≤ 1) :
    (⌈x * p⌉₊).choose 2 ≤ ((supports (p+p)).filter (fun S =>
      ¬pi.GuaranteesSequence v (target v x) Finset.univ (pairSeq first (second S)))).card := by
  classical
  by_cases small : (firstBundle pi first).card < ⌈x * p⌉₊
  · have h := Finset.filter_true_of_mem (s := supports (p+p))
        (p := fun S => ¬pi.GuaranteesSequence v (target v x) Finset.univ (pairSeq first (second S)))
        (fun _ _ => short_fails allGoods pi small)
    rw [h]
    simp only [supports, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    apply Nat.choose_le_choose
    apply Nat.ceil_le.mpr
    push_cast
    have := mul_le_mul_of_nonneg_right hx1 (Nat.cast_nonneg p : (0:ℝ) ≤ p)
    linarith
  · refine (Nat.choose_le_choose 2 (le_of_not_gt small)).trans ?_
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card
    intro S hS
    obtain ⟨hsub, htwo⟩ := Finset.mem_powersetCard.mp hS
    have hAll : S ∈ supports (p+p) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, htwo⟩
    exact Finset.mem_filter.mpr ⟨hAll, trapped_fails htwo (hsecond S hAll) pi hsub hx⟩

/-- Exchange the sum over random tapes and the sum over unordered pairs.
Every tape destroys at least the stated number of pair continuations. -/
private theorem total_failure_mass {p k : ℕ} (fit : 1 + (p+p).choose 2 ≤ k) :
    ∃ (v : Fin k → Fin (p+p) → ℝ) (first : Fin k) (second : Finset (Fin (p+p)) → Fin k),
      (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      v first = (fun _ => 1) ∧
      (∀ S ∈ supports (p+p), v (second S) = fun g => if g ∈ S then 1 else 0) ∧
      ∀ {x : ℝ}, 0 < x → x ≤ 1 →
      ∀ {T : Type} [Fintype T] (mass : T → ℝ),
        (∀ a, 0 ≤ mass a) → (∑ a, mass a) = 1 → ∀ (policy : T → Policy (p+p) k 2),
        ((⌈x * p⌉₊).choose 2 : ℝ) ≤ ∑ S ∈ supports (p+p), ∑ a,
          if (policy a).GuaranteesSequence v (target v x) Finset.univ (pairSeq first (second S))
          then 0 else mass a := by
  classical
  obtain ⟨v, first, second, hbin, hall, hs⟩ := labelledInstance fit
  refine ⟨v, first, second, hbin, hall, hs, ?_⟩
  intro x hx hx1 T inst mass hpos hmass policy
  let good (a : T) (S : Finset (Fin (p+p))) :=
    (policy a).GuaranteesSequence v (target v x) Finset.univ (pairSeq first (second S))
  have hrow (a : T) : ((⌈x * p⌉₊).choose 2 : ℝ) ≤
      ∑ S ∈ supports (p+p), (if good a S then (0:ℝ) else 1) := by
    have heq : (∑ S ∈ supports (p+p), if good a S then (0:ℝ) else 1) =
        (((supports (p+p)).filter (fun S => ¬good a S)).card : ℝ) := by
      simpa only [ite_not] using Finset.sum_boole (α := ℝ) (fun S => ¬good a S) (supports (p+p))
    rw [heq]
    exact_mod_cast failing_count hall hs (policy a) hx hx1
  calc
    ((⌈x * p⌉₊).choose 2 : ℝ) = ∑ a, mass a * ((⌈x * p⌉₊).choose 2 : ℝ) := by
      rw [← Finset.sum_mul, hmass, one_mul]
    _ ≤ ∑ a, mass a * ∑ S ∈ supports (p+p), (if good a S then (0:ℝ) else 1) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) (hpos a)
    _ = ∑ S ∈ supports (p+p), ∑ a, if good a S then (0:ℝ) else mass a := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero, mul_one]
      exact Finset.sum_comm


/-- A failure bound applying separately to each fixed pair continuation must
cover the average number of failed continuations. -/
theorem failure_count_bound {p k : ℕ} (fit : 1 + (p+p).choose 2 ≤ k) :
    ∃ (v : Fin k → Fin (p+p) → ℝ) (first : Fin k), (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      ∀ {x δ : ℝ}, 0 < x → x ≤ 1 →
      ∀ {T : Type} [Fintype T] (mass : T → ℝ),
        (∀ a, 0 ≤ mass a) → (∑ a, mass a) = 1 → ∀ (policy : T → Policy (p+p) k 2),
        (∀ s : Fin k, (∑ a, if (policy a).GuaranteesSequence v (target v x) Finset.univ
             (pairSeq first s) then 0 else mass a) ≤ δ) →
        ((⌈x * p⌉₊).choose 2 : ℝ) ≤ ((p+p).choose 2 : ℝ) * δ := by
  classical
  obtain ⟨v, first, second, binary, _, _, lower⟩ := total_failure_mass fit
  refine ⟨v, first, binary, ?_⟩
  intro x δ hx hx1 T inst mass hpos htotal policy bySequence
  refine (lower hx hx1 mass hpos htotal policy).trans ?_
  calc
    _ ≤ ∑ _S ∈ supports (p+p), δ := Finset.sum_le_sum fun S _ => bySequence (second S)
    _ = _ := by simp [supports, Finset.card_powersetCard]

/-- A worst continuation can be fixed using the lottery alone, without seeing
its sampled tape or the first agent's bundle. -/
theorem exists_fixed_failing_sequence {p k : ℕ} (hp : 0 < p)
    (fit : 1 + (p+p).choose 2 ≤ k) :
    ∃ (v : Fin k → Fin (p+p) → ℝ) (first : Fin k), (∀ t g, v t g = 0 ∨ v t g = 1) ∧
      v first = (fun _ => 1) ∧
      ∀ {x : ℝ}, 0 < x → x ≤ 1 →
      ∀ {T : Type} [Fintype T] (mass : T → ℝ),
        (∀ a, 0 ≤ mass a) → (∑ a, mass a) = 1 → ∀ (policy : T → Policy (p+p) k 2),
        ∃ s : Fin k, (∃ S : Finset (Fin (p+p)), S.card = 2 ∧
          v s = fun g => if g ∈ S then 1 else 0) ∧
          (((⌈x * p⌉₊).choose 2 : ℝ) / ((p+p).choose 2 : ℝ) ≤
            ∑ a, if (policy a).GuaranteesSequence v (target v x) Finset.univ (pairSeq first s)
              then 0 else mass a) := by
  classical
  obtain ⟨v, first, second, binary, allGoods, values, lower⟩ := total_failure_mass fit
  refine ⟨v, first, binary, allGoods, ?_⟩
  intro x hx hx1 T inst mass hmass htotal policy
  let fail (s : Fin k) := ∑ a, if (policy a).GuaranteesSequence
    v (target v x) Finset.univ (pairSeq first s) then 0 else mass a
  have hcard : (supports (p+p)).card = (p+p).choose 2 := by
    simp [supports, Finset.card_powersetCard]
  have hpos : 0 < (p+p).choose 2 := Nat.choose_pos (by omega)
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (supports (p+p)) (fun S => fail (second S))
    (Finset.card_pos.mp (hcard.symm ▸ hpos))
  refine ⟨second S, ⟨S, (Finset.mem_powersetCard.mp hS).2, values S hS⟩, ?_⟩
  apply (div_le_iff₀ (show (0:ℝ) < ((p+p).choose 2 : ℝ) by exact_mod_cast hpos)).mpr
  calc
    _ ≤ ∑ B ∈ supports (p+p), fail (second B) := lower hx hx1 mass hmass htotal policy
    _ ≤ ∑ _B ∈ supports (p+p), fail (second S) := Finset.sum_le_sum hmax
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]; apply mul_comm

private theorem twice_choose_cast {a : ℕ} (ha : 1 ≤ a) :
    (a.choose 2 : ℝ) * 2 = (a : ℝ) * (a - 1 : ℝ) := by
  have h := Nat.choose_succ_right_eq a 1
  simp only [Nat.choose_one_right, one_add_one_eq_two] at h
  have hr := congrArg (fun z : ℕ => (z : ℝ)) h
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub ha, Nat.cast_one] using hr

/-- The counting inequality yields the explicit upper bound in Proposition 2.3. -/
theorem fraction_le_of_count {p : ℕ} {x δ : ℝ} (hp : 0 < p) (hx : 0 < x) (hd : 0 ≤ δ)
    (count : ((⌈x * p⌉₊).choose 2 : ℝ) ≤ ((p+p).choose 2 : ℝ) * δ) :
    x ≤ 1/(p:ℝ) + 2 * Real.sqrt δ := by
  let q := ⌈x * p⌉₊
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : 1 ≤ q := Nat.one_le_ceil_iff.mpr (mul_pos hx hpR)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hchoice := twice_choose_cast hq
  have hdbl := twice_choose_cast (a:=p+p) (by omega)
  push_cast at hdbl
  have hcount : (q:ℝ) * (q - 1 : ℝ) ≤ (2*(p:ℝ)) * (2*(p:ℝ)-1) * δ := by
    change (q.choose 2 : ℝ) ≤ _ at count
    calc
      _ = (q.choose 2 : ℝ) * 2 := hchoice.symm
      _ ≤ (((p+p).choose 2 : ℝ) * 2) * δ := by linarith only [count]
      _ = _ := by rw [hdbl]; ring
  have hsq : ((q:ℝ)-1)^2 ≤ (2*(p:ℝ)*Real.sqrt δ)^2 := by
    rw [mul_pow, Real.sq_sqrt hd]
    nlinarith only [hcount, hqR, mul_nonneg hpR.le hd]
  have ho := (sq_le_sq₀ (by linarith : 0 ≤ (q:ℝ)-1) (by positivity : 0 ≤ 2*(p:ℝ)*Real.sqrt δ)).mp hsq
  have hxq : x * p ≤ (q:ℝ) := Nat.le_ceil _
  calc
    x ≤ (1 + 2 * Real.sqrt δ * p) / p := (le_div_iff₀ hpR).mpr (by linarith only [ho,hxq])
    _ = _ := by field_simp

end OnlineMMS.ObliviousPair
