import OnlineMMS.FinitePTASCellSearch
import Mathlib.Logic.Equiv.Fin.Basic

namespace OnlineMMS

open scoped BigOperators

/-- Replace each intersection of the two supplied partitions by a representative cell. -/
def partitionCellTag {m n : ℕ} (part : Fin 2 → Fin m → Fin n) (g : Fin m) : Fin (n*n) :=
  finProdFinEquiv (part 0 g,part 1 g)

def partitionCellLabel {n : ℕ} (t : Fin 2) (c : Fin (n*n)) : Fin n :=
  let labels := (finProdFinEquiv (m := n) (n := n)).symm c
  if t = 0 then labels.1 else labels.2

@[simp] theorem partitionCellLabel_tag {m n : ℕ} (part : Fin 2 → Fin m → Fin n)
    (t : Fin 2) (g : Fin m) : partitionCellLabel t (partitionCellTag part g) = part t g := by
  fin_cases t <;> simp [partitionCellLabel,partitionCellTag]

def expandCellBundle {m c : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin c)
    (C : Finset (Fin c)) : Finset (Fin m) := R.filter (fun g => tag g ∈ C)

theorem expandCellBundle_mono {m c : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin c)
    {A B : Finset (Fin c)} (h : A ⊆ B) : expandCellBundle R tag A ⊆ expandCellBundle R tag B := by
  intro g hg
  obtain ⟨hR,hA⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hR,h hA⟩

@[simp] theorem expandCellBundle_univ {m c : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin c) :
    expandCellBundle R tag Finset.univ = R := by simp [expandCellBundle]

@[simp] theorem expandCellBundle_diff {m c : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin c)
    (A B : Finset (Fin c)) :
    expandCellBundle R tag (A \ B) = expandCellBundle R tag A \ expandCellBundle R tag B := by
  ext g
  simp only [expandCellBundle,Finset.mem_filter,Finset.mem_sdiff]
  tauto

def cellValuations {m c : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (tag : Fin m → Fin c) (t : Fin 2) (i : Fin c) : ℚ :=
  rationalBundleValue (v t) (R.filter (fun g => tag g = i))

theorem cellValuations_nonneg {m c : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (tag : Fin m → Fin c) :
    ∀ t i, 0 ≤ cellValuations v R tag t i := by
  intro t i
  exact Finset.sum_nonneg (fun g _ => hv t g)

theorem cellValuations_bundleValue {m c : ℕ} (v : Fin 2 → Fin m → ℚ)
    (R : Finset (Fin m)) (tag : Fin m → Fin c) (C : Finset (Fin c)) (t : Fin 2) :
    bundleValue (fun i => (cellValuations v R tag t i : ℝ)) C =
      bundleValue (fun g => (v t g : ℝ)) (expandCellBundle R tag C) := by
  simp only [cellValuations,rationalBundleValue_cast]
  exact Finset.sum_fiberwise_eq_sum_filter R C tag (fun g => (v t g : ℝ))

theorem cellValuations_preserve_parts {m n : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (part : Fin 2 → Fin m → Fin n) (q : Fin 2 → ℚ)
    (h : ∀ t, rationalPartsPay (v t) R (part t) (q t)) :
    ∀ t, HasPaymentPartition (fun i => (cellValuations v R (partitionCellTag part) t i : ℝ))
      Finset.univ n (q t : ℝ) := by
  intro t
  refine ⟨partitionCellLabel t,fun j => ?_⟩
  rw [cellValuations_bundleValue]
  have he : expandCellBundle R (partitionCellTag part)
      (Finset.univ.filter (fun g => partitionCellLabel t g = j)) = rationalPart R (part t) j := by
    ext g
    simp [expandCellBundle,rationalPart]
  rw [he,← rationalBundleValue_cast]
  exact_mod_cast h t j

def expandCellPolicy {m c : ℕ} (R : Finset (Fin m)) (tag : Fin m → Fin c) :
    {r : ℕ} → Policy c 2 r → Policy m 2 r
  | 0,.done => .done
  | _+1,.step G next =>
    .step (fun t => expandCellBundle R tag (G t)) (fun t => expandCellPolicy R tag (next t))

theorem expandCellPolicy_correct {m c r : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (tag : Fin m → Fin c) (C : Finset (Fin c)) (q : Fin 2 → ℝ) (p : Policy c 2 r)
    (h : p.Guarantees (fun t g => (cellValuations v R tag t g : ℝ)) q C) :
    (expandCellPolicy R tag p).Guarantees (fun t g => (v t g : ℝ)) q (expandCellBundle R tag C) := by
  induction r generalizing C with
  | zero => cases p; trivial
  | succ r ih =>
    cases p with
    | step G next =>
      intro t
      obtain ⟨hsub,hpay,hcont⟩ := h t
      refine ⟨expandCellBundle_mono R tag hsub,?_,?_⟩
      · rw [← cellValuations_bundleValue]
        exact hpay
      · rw [← expandCellBundle_diff]
        exact ih _ _ hcont

/-- The guaranteed continuation factors for the long end of the short-horizon analysis. -/
def longShortFactors (r : ℕ) : ℚ × ℚ :=
  if r = 3 then (9/10,3/4) else (3/4,27/40)

def rationalOrientedTarget (q : Fin 2 → ℚ) (a b : ℚ) (first t : Fin 2) : ℚ :=
  (if t = first then a else b)*q t

@[simp] theorem rationalOrientedTarget_cast (q : Fin 2 → ℚ) (a b : ℚ) (first t : Fin 2) :
    (rationalOrientedTarget q a b first t : ℝ) =
      orientedTarget (fun i => (q i : ℝ)) (a : ℝ) (b : ℝ) first t := by
  by_cases h : t = first <;> simp [rationalOrientedTarget,orientedTarget,h,Rat.cast_mul]

private def tabulateTypes {α : Type} (f : Fin 2 → α) : α × α :=
  (f 0,f 1)

private def readType {α : Type} (table : α × α) (t : Fin 2) : α :=
  if t = 0 then table.1 else table.2

@[simp] private theorem readType_tabulateTypes {α : Type} (f : Fin 2 → α) :
    readType (tabulateTypes f) = f := by
  funext t
  fin_cases t <;> rfl

private def tabulateRows {α : Type} {c : ℕ} (w : Fin 2 → Fin c → α) :
    Vector α c × Vector α c :=
  tabulateTypes (fun t => Vector.ofFn (w t))

private def readRows {α : Type} {c : ℕ} (table : Vector α c × Vector α c)
    (t : Fin 2) (i : Fin c) : α :=
  (readType table t)[i]

@[simp] private theorem readRows_tabulateRows {α : Type} {c : ℕ} (w : Fin 2 → Fin c → α) :
    readRows (tabulateRows w) = w := by
  funext t i
  simp [readRows,tabulateRows]

private def rationalPartitionPayment {m n : ℕ} (v : Fin m → ℚ) (hn : 0 < n)
    (part : Fin m → Fin n) : ℚ :=
  Finset.univ.inf' ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    (fun j => rationalBundleValue v (rationalPart Finset.univ part j))

@[simp] private theorem rationalPartitionPayment_eq {m n L : ℕ} (v : Fin m → ℚ) (hn : 0 < n) :
    rationalPartitionPayment v hn (rationalMMSAssignment (L := L) v hn) =
      rationalMMSPayment (L := L) v hn := rfl

/-- Run exact continuation search only on the constant number of representative cells. -/
def rationalCompressedChoice {m r : ℕ} (v : Fin 2 → Fin m → ℚ) (R : Finset (Fin m))
    (part : Fin 2 → Fin m → Fin (r+1)) (q : Fin 2 → ℚ) (first : Fin 2) :
    Option (Finset (Fin m) × Policy m 2 r) :=
  let tag := partitionCellTag part
  let values := tabulateRows (cellValuations v R tag)
  let w := readRows values
  let factor := longShortFactors r
  let target := rationalOrientedTarget q factor.1 factor.2 first
  (searchCellBundle (w first) (q first) Finset.univ (searchCellPolicy w target r)).map
    (fun (G,p) => (expandCellBundle R tag G,expandCellPolicy R tag p))

theorem rationalCompressedChoice_correct {m r : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (R : Finset (Fin m)) (part : Fin 2 → Fin m → Fin (r+1))
    (q : Fin 2 → ℚ) (hq : ∀ t, 0 ≤ q t) (hp : ∀ t, rationalPartsPay (v t) R (part t) (q t))
    (hr : 3 ≤ r) (hr' : r ≤ 4) (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let factors := longShortFactors r
    ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      rationalCompressedChoice v R part q first = some (G,p) ∧ G ⊆ R ∧
      (q first : ℝ) ≤ bundleValue (w first) G ∧
      p.Guarantees w (orientedTarget (fun t => (q t : ℝ)) (factors.1 : ℝ)
        (factors.2 : ℝ) first) (R \ G) := by
  dsimp only
  let tag := partitionCellTag part
  let w := cellValuations v R tag
  let wr : Fin 2 → Fin ((r+1)*(r+1)) → ℝ := fun t i => w t i
  let qr : Fin 2 → ℝ := fun t => q t
  let factor := longShortFactors r
  let target := rationalOrientedTarget q factor.1 factor.2 first
  have hqR (t : Fin 2) : 0 ≤ qr t := by
    dsimp [qr]
    exact_mod_cast hq t
  have hwR (t) (i) : 0 ≤ wr t i := by
    have hh := cellValuations_nonneg v hv R tag t i
    dsimp [wr,w]
    exact_mod_cast hh
  have hparts := cellValuations_preserve_parts v R part q hp
  have htgt : (fun t => (target t : ℝ)) =
      orientedTarget qr (factor.1 : ℝ) (factor.2 : ℝ) first := by
    funext t
    exact rationalOrientedTarget_cast _ _ _ _ _
  have hcompressed :
    ∃ (G : Finset (Fin ((r+1)*(r+1)))) (p : Policy ((r+1)*(r+1)) 2 r),
      G ⊆ Finset.univ ∧ qr first ≤ bundleValue (wr first) G ∧
      p.Guarantees wr (fun t => (target t : ℝ)) (Finset.univ \ G) := by
    rw [htgt]
    have hrs : r = 3 ∨ r = 4 := by omega
    rcases hrs with hh | hh
    · subst r
      simpa [factor,longShortFactors,Rat.cast_div] using
        four_arrival_first_choice wr hwR Finset.univ qr hqR hparts first
    · subst r
      simpa [factor,longShortFactors,Rat.cast_div] using
        five_arrival_first_choice wr hwR Finset.univ qr hqR hparts first
  obtain ⟨G,p,hG,hpay,hrest⟩ := hcompressed
  obtain ⟨p',hp'⟩ := searchCellPolicy_complete w target (Finset.univ \ G) p hrest
  obtain ⟨⟨G',p''⟩,hchoice⟩ := searchCellBundle_complete (w first) (q first) Finset.univ G
    (searchCellPolicy w target r) p' hG hpay hp'
  obtain ⟨hsub,hfirst,hfound⟩ := searchCellBundle_sound (w first) (q first) Finset.univ G'
    (searchCellPolicy w target r) p'' hchoice
  have hpolicy := searchCellPolicy_sound w target (Finset.univ \ G') p'' hfound
  have hexpand := expandCellPolicy_correct v R tag (Finset.univ \ G') _ p'' hpolicy
  rw [expandCellBundle_diff,expandCellBundle_univ,htgt] at hexpand
  refine ⟨expandCellBundle R tag G',expandCellPolicy R tag p'',?_,
    Finset.filter_subset _ _,?_,hexpand⟩
  · simp only [rationalCompressedChoice,readRows_tabulateRows]
    change (searchCellBundle (w first) (q first) Finset.univ (searchCellPolicy w target r)).map _ = _
    rw [hchoice]
    rfl
  · rw [← cellValuations_bundleValue]
    exact hfirst

/-- Start compressed continuation search using the executable approximate partitions. -/
def rationalLongPTASChoice {m L : ℕ} (r : ℕ) (v : Fin 2 → Fin m → ℚ)
    (first : Fin 2) : Option (Finset (Fin m) × Policy m 2 r) :=
  let parts := tabulateRows (fun t => rationalMMSAssignment (L := L) (v t) (Nat.zero_lt_succ r))
  let payments := tabulateTypes (fun t => rationalPartitionPayment (v t)
    (Nat.zero_lt_succ r) (readRows parts t))
  rationalCompressedChoice v Finset.univ (readRows parts) (readType payments) first

theorem rationalLongPTASChoice_correct {m r L : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hr : 3 ≤ r) (hr' : r ≤ 4) (hL : 0 < L) (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (Nat.zero_lt_succ r)
    let factor := longShortFactors r
    ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      rationalLongPTASChoice (L := L) r v first = some (G,p) ∧
      (1-(1 : ℝ)/L)*μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-(1 : ℝ)/L)*orientedTarget μ (factor.1 : ℝ)
        (factor.2 : ℝ) first t) (Finset.univ \ G) := by
  dsimp only
  let q := fun t => rationalMMSPayment (L := L) (v t) (Nat.zero_lt_succ r)
  have hq (t : Fin 2) : 0 ≤ q t := by
    change 0 ≤ rationalMMSPayment (L := L) (v t) (Nat.zero_lt_succ r)
    unfold rationalMMSPayment
    apply Finset.le_inf'
    intro i _
    exact Finset.sum_nonneg (fun g _ => hv t g)
  have hp (t : Fin 2) := rationalPartsPay_ptas (L := L) (v t) (Nat.zero_lt_succ r)
  obtain ⟨G,p,he,_,hfirst,hrest⟩ := rationalCompressedChoice_correct v hv Finset.univ _ q hq hp
    hr hr' first
  have ha (t : Fin 2) : (1-(1 : ℝ)/L)*maximinShare (fun g => (v t g : ℝ))
      (r+1) (Nat.zero_lt_succ r) ≤ (q t : ℝ) := by
    change _ ≤ (rationalMMSPayment (L := L) (v t) (Nat.zero_lt_succ r) : ℝ)
    rw [rationalMMSPayment_cast]
    apply Finset.le_inf'
    intro i _
    exact rationalMMSAssignment_guarantee (v t) (hv t) _ hL i
  refine ⟨G,p,?_,(ha first).trans hfirst,
    oriented_approximate_partition_transfer first
      (by unfold longShortFactors; split <;> norm_num)
      (by unfold longShortFactors; split <;> norm_num) ha hrest⟩
  simpa [rationalLongPTASChoice,q] using he

/-- No more than 25 cells reach the continuation search for four or five arrivals. -/
theorem rationalLongPTASChoice_search_bound {r : ℕ} (hr : r ≤ 4) :
    cellPolicySearchCalls ((r+1)*(r+1)) (r+1) ≤ cellPolicySearchCalls 25 5 := by
  apply cellPolicySearchCalls_short _ (by omega)
  exact Nat.mul_le_mul (show r+1 ≤ 5 by omega) (show r+1 ≤ 5 by omega)

end OnlineMMS
