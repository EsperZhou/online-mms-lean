import OnlineMMS.FinitePartitions
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Max

namespace OnlineMMS

/-- The natural load of each part under an assignment. -/
def roundedLoads {m n : ℕ} (w : Fin m → ℕ) (p : Fin m → Fin n) : Fin n → ℕ :=
  fun j => ∑ g, if p g = j then w g else 0

private def addLoad {n : ℕ} (s : Fin n → ℕ) (j : Fin n) (a : ℕ) : Fin n → ℕ :=
  fun i => if j = i then a + s i else s i

private theorem roundedLoads_succ {m n : ℕ} (w : Fin (m+1) → ℕ) (p : Fin (m+1) → Fin n) :
    roundedLoads w p = addLoad (roundedLoads (fun g => w g.succ) (fun g => p g.succ))
      (p 0) (w 0) := by
  funext i
  unfold roundedLoads addLoad
  rw [Fin.sum_univ_succ]
  split <;> simp_all

/-- Keep a single assignment for each load vector. -/
private def dedupLoads {m n : ℕ} :
    List ((Fin n → ℕ) × (Fin m → Fin n)) → List ((Fin n → ℕ) × (Fin m → Fin n))
  | [] => []
  | x :: xs =>
      let kept := dedupLoads xs
      if kept.any (fun y => decide (y.1 = x.1)) then kept else x :: kept

private theorem dedupLoads_sublist {m n : ℕ} (xs : List ((Fin n → ℕ) × (Fin m → Fin n))) :
    List.Sublist (dedupLoads xs) xs := by
  induction xs with
  | nil => simp [dedupLoads]
  | cons x xs ih =>
    simp only [dedupLoads]
    split
    · exact ih.cons _
    · exact ih.cons₂ _

private theorem dedupLoads_has_load {m n : ℕ} (s : Fin n → ℕ)
    (xs : List ((Fin n → ℕ) × (Fin m → Fin n))) :
    (∃ x ∈ dedupLoads xs, x.1 = s) ↔ (∃ x ∈ xs, x.1 = s) := by
  constructor
  · rintro ⟨x,hx,hs⟩
    exact ⟨x,(dedupLoads_sublist xs).subset hx,hs⟩
  · induction xs with
    | nil => simp
    | cons x xs ih =>
      rintro ⟨y,hy,hs⟩
      simp only [List.mem_cons] at hy
      simp only [dedupLoads]
      split
      · rename_i hm
        rw [List.any_eq_true] at hm
        obtain ⟨z,hz,hzx⟩ := hm
        simp only [decide_eq_true_eq] at hzx
        rcases hy with rfl | hy
        · exact ⟨z,hz,hzx.trans hs⟩
        · exact ih ⟨y,hy,hs⟩
      · rcases hy with rfl | hy
        · exact ⟨y,by simp,hs⟩
        · obtain ⟨z,hz,hzs⟩ := ih ⟨y,hy,hs⟩
          exact ⟨z,by simp [hz],hzs⟩

private theorem dedupLoads_nodup {m n : ℕ} (xs : List ((Fin n → ℕ) × (Fin m → Fin n))) :
    (List.map Prod.fst (dedupLoads xs)).Nodup := by
  induction xs with
  | nil => simp [dedupLoads]
  | cons x xs ih =>
    simp only [dedupLoads]
    split
    · exact ih
    · rename_i hm
      simp only [List.map_cons,List.nodup_cons,ih,and_true,List.mem_map]
      rintro ⟨y,hy,he⟩
      apply hm
      exact List.any_eq_true.mpr ⟨y,hy,by simp [he]⟩

private def extendFrontier {m n : ℕ} (a : ℕ)
    (xs : List ((Fin n → ℕ) × (Fin m → Fin n))) :
    List ((Fin n → ℕ) × (Fin (m+1) → Fin n)) :=
  xs.flatMap (fun x => (List.finRange n).map
    (fun j => (addLoad x.1 j a, Fin.cases j x.2)))

/-- Dynamic programming frontier, carrying a witness with each distinct load vector. -/
def roundedFrontier (n : ℕ) : {m : ℕ} → (Fin m → ℕ) →
    List ((Fin n → ℕ) × (Fin m → Fin n))
  | 0, _ => [(fun _ => 0, Fin.elim0)]
  | _+1, w => dedupLoads (extendFrontier (w 0)
      (roundedFrontier n (fun g => w g.succ)))

theorem roundedFrontier_sound {m n : ℕ} (w : Fin m → ℕ)
    (x : (Fin n → ℕ) × (Fin m → Fin n)) (hx : x ∈ roundedFrontier n w) :
    x.1 = roundedLoads w x.2 := by
  induction m with
  | zero =>
    simp [roundedFrontier] at hx
    subst x
    funext i
    simp [roundedLoads]
  | succ m ih =>
    rw [roundedFrontier] at hx
    have hm := (dedupLoads_sublist _).subset hx
    simp only [extendFrontier,List.mem_flatMap,List.mem_map] at hm
    obtain ⟨y,hy,j,_,rfl⟩ := hm
    rw [roundedLoads_succ]
    simp only [Fin.cases_zero,Fin.cases_succ]
    rw [ih _ _ hy]

theorem roundedFrontier_complete {m n : ℕ} (w : Fin m → ℕ) (p : Fin m → Fin n) :
    ∃ x ∈ roundedFrontier n w, x.1 = roundedLoads w p := by
  induction m with
  | zero =>
    refine ⟨(fun _ => 0, Fin.elim0),by simp [roundedFrontier],?_⟩
    funext j
    simp [roundedLoads]
  | succ m ih =>
    obtain ⟨y,hy,he⟩ := ih (fun g => w g.succ) (fun g => p g.succ)
    rw [roundedFrontier,dedupLoads_has_load]
    refine ⟨(addLoad y.1 (p 0) (w 0),Fin.cases (p 0) y.2),?_,?_⟩
    · exact List.mem_flatMap.mpr ⟨y,hy,List.mem_map.mpr ⟨p 0,List.mem_finRange _,rfl⟩⟩
    · rw [roundedLoads_succ,he]

theorem roundedFrontier_nodup {m n : ℕ} (w : Fin m → ℕ) :
    (List.map Prod.fst (roundedFrontier n w)).Nodup := by
  cases m with
  | zero => simp [roundedFrontier]
  | succ m => exact dedupLoads_nodup _

theorem roundedFrontier_length_le {m n W : ℕ} (w : Fin m → ℕ) (hw : ∀ g, w g ≤ W) :
    (roundedFrontier n w).length ≤ (m*W+1)^n := by
  let xs := (roundedFrontier n w).map Prod.fst
  have hxs : xs.Nodup := roundedFrontier_nodup w
  have hb (s : {s // s ∈ xs.toFinset}) (j : Fin n) : s.1 j < m*W+1 := by
    have hs := List.mem_toFinset.mp s.2
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hs
    rw [← he,roundedFrontier_sound w x hx]
    apply Nat.lt_succ_of_le
    calc
      roundedLoads w x.2 j ≤ ∑ _ : Fin m, W := by
        apply Finset.sum_le_sum
        intro g _
        split
        · exact hw g
        · exact Nat.zero_le _
      _ = m*W := by simp
  let embed (s : {s // s ∈ xs.toFinset}) (j : Fin n) : Fin (m*W+1) := ⟨s.1 j,hb s j⟩
  have hi : Function.Injective embed := by
    intro x y h
    apply Subtype.ext
    funext j
    exact congrArg Fin.val (congrFun h j)
  have hc := Fintype.card_le_of_injective embed hi
  simpa [Fintype.card_fun,List.toFinset_card_of_nodup hxs,xs] using hc

private theorem extendFrontier_length {m n : ℕ} (a : ℕ)
    (xs : List ((Fin n → ℕ) × (Fin m → Fin n))) :
    (extendFrontier a xs).length = n * xs.length := by
  induction xs with
  | nil => simp [extendFrontier]
  | cons x xs ih =>
    simp only [extendFrontier,List.flatMap_cons,List.length_append,List.length_map,List.length_finRange]
    rw [← extendFrontier,ih,List.length_cons,Nat.mul_succ]
    omega

/-- Each layer generates at most n times the preceding frontier bound. -/
theorem roundedFrontier_layer_candidates {m n W : ℕ} (w : Fin m → ℕ)
    (hw : ∀ g, w g ≤ W) (a : ℕ) :
    (extendFrontier a (roundedFrontier n w)).length ≤ n * (m*W+1)^n := by
  rw [extendFrontier_length]
  exact Nat.mul_le_mul_left _ (roundedFrontier_length_le w hw)

/-- Score a load vector by its smallest coordinate. -/
def roundedLoadScore {n : ℕ} (hn : 0 < n) (s : Fin n → ℕ) : ℕ :=
  Finset.univ.inf' ⟨⟨0,hn⟩,Finset.mem_univ _⟩ s

theorem roundedLoadScore_le {n : ℕ} (hn : 0 < n) (s : Fin n → ℕ) (j : Fin n) :
    roundedLoadScore hn s ≤ s j := Finset.inf'_le _ (Finset.mem_univ _)

theorem le_roundedLoadScore {n : ℕ} (hn : 0 < n) (s : Fin n → ℕ)
    {q : ℕ} (h : ∀ j, q ≤ s j) : q ≤ roundedLoadScore hn s :=
  Finset.le_inf' _ _ (fun j _ => h j)

private def bestWitness {α : Type} (score : α → ℕ) (x : α) : List α → α
  | [] => x
  | y :: ys => bestWitness score (if score x ≤ score y then y else x) ys

private theorem bestWitness_mem {α : Type} (score : α → ℕ) (x : α) (xs : List α) :
    bestWitness score x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [bestWitness]
  | cons y ys ih =>
    simp only [bestWitness]
    split
    · simpa using List.mem_cons_of_mem x (ih y)
    · have h := ih x
      simp only [List.mem_cons] at h ⊢
      tauto

private theorem bestWitness_max {α : Type} (score : α → ℕ) (x : α) (xs : List α)
    (y : α) (hy : y ∈ x :: xs) : score y ≤ score (bestWitness score x xs) := by
  induction xs generalizing x y with
  | nil =>
    have : y = x := by simpa using hy
    subst y
    simp [bestWitness]
  | cons z zs ih =>
    simp only [bestWitness]
    split
    · rename_i h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.trans (ih z z (by simp))
      · exact ih z y hy
    · rename_i h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ih y y (by simp)
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact (Nat.le_of_not_ge h).trans (ih x x (by simp))
        · exact ih x y (List.mem_cons_of_mem _ hy)

/-- Return an optimal assignment of the rounded jobs, using only the rounded frontiers. -/
def roundedOptimalAssignment {m n : ℕ} (hn : 0 < n) (w : Fin m → ℕ) :
    Fin m → Fin n :=
  match roundedFrontier n w with
  | [] => fun _ => ⟨0,hn⟩
  | x :: xs => (bestWitness (fun y => roundedLoadScore hn y.1) x xs).2

theorem roundedOptimalAssignment_max {m n : ℕ} (hn : 0 < n) (w : Fin m → ℕ)
    (p : Fin m → Fin n) :
    roundedLoadScore hn (roundedLoads w p) ≤
      roundedLoadScore hn (roundedLoads w (roundedOptimalAssignment hn w)) := by
  obtain ⟨y,hy,he⟩ := roundedFrontier_complete w p
  unfold roundedOptimalAssignment
  split
  · rename_i h
    rw [h] at hy
    simp at hy
  · rename_i x xs h
    let score (z : (Fin n → ℕ) × (Fin m → Fin n)) := roundedLoadScore hn z.1
    rw [h] at hy
    have hb := roundedFrontier_sound w (bestWitness score x xs)
      (by rw [h]; exact bestWitness_mem score x xs)
    change _ ≤ roundedLoadScore hn (roundedLoads w (bestWitness score x xs).2)
    rw [← hb,← he]
    exact bestWitness_max score x xs y hy

end OnlineMMS
