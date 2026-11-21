import OnlineMMS.Sampling

namespace OnlineMMS

open private GreedyForSlots from OnlineMMS.Sampling

namespace ConditionalSelection

variable {T G : Type*}

def InCube (z : T → ℝ) : Prop := ∀ t, z t ∈ Set.Icc (0:ℝ) 1

/-- Affinity in each entire bucket column, on the cube of exactly q columns. -/
def MultiAffine [Fintype T] (q : ℕ) (F : List (T → ℝ) → ℝ) : Prop :=
  ∀ left right : List (T → ℝ), left.length + 1 + right.length = q →
    (∀ z ∈ left, InCube z) → (∀ z ∈ right, InCube z) →
    ∃ (a : ℝ) (c : T → ℝ), ∀ z, InCube z →
      F (left ++ z :: right) = a + ∑ t, z t * c t

private theorem mean_mem (w : T → G → ℝ) (hw : ∀ g, InCube (fun t => w t g))
    (B : Finset G) (hb : B.Nonempty) : InCube (slotMean w B) := by
  intro t
  have hc : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hb
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun g _ => (hw g t).1)) hc.le
  · apply (div_le_iff₀ hc).2
    simpa using Finset.sum_le_sum (s := B) (fun g _ => (hw g t).2)

private theorem means_mem (w : T → G → ℝ) (hw : ∀ g, InCube (fun t => w t g))
    (bs : List (Finset G)) (hb : ∀ B ∈ bs, B.Nonempty) :
    ∀ z ∈ slotMeans w bs, InCube z := by
  intro z hz
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hz
  exact mean_mem w hw B (hb B hB)

private theorem fix_mem (w : T → G → ℝ) (hw : ∀ g, InCube (fun t => w t g))
    {left : List (T → ℝ)} (hl : ∀ z ∈ left, InCube z) (g : G) :
    ∀ z ∈ left ++ [fun t => w t g], InCube z := by
  intro z hz
  rcases List.mem_append.mp hz with h|h
  · exact hl z h
  · rcases List.mem_singleton.mp h with rfl
    exact hw g

variable [Fintype T]

theorem mean_column {q : ℕ} {F : List (T → ℝ) → ℝ} (hf : MultiAffine q F)
    (w : T → G → ℝ) (hw : ∀ g, InCube (fun t => w t g)) (B : Finset G) (hb : B.Nonempty)
    (left right : List (T → ℝ)) (hlen : left.length+1+right.length=q)
    (hl : ∀ z ∈ left, InCube z) (hr : ∀ z ∈ right, InCube z) :
    F (left ++ slotMean w B :: right) =
      (∑ g ∈ B, F (left ++ (fun t => w t g) :: right)) / B.card := by
  classical
  obtain ⟨a,c,h⟩ := hf left right hlen hl hr
  rw [h _ (mean_mem w hw B hb)]
  have he : (∑ g ∈ B, F (left ++ (fun t => w t g) :: right)) =
      ∑ g ∈ B, (a + ∑ t, w t g * c t) :=
    Finset.sum_congr rfl (fun g _ => h _ (hw g))
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hb).ne'
  have hs : (∑ g ∈ B, ∑ t, w t g * c t) / B.card = ∑ t, slotMean w B t * c t := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [← Finset.sum_mul, slotMean]
    ring
  rw [he, Finset.sum_add_distrib, add_div, hs]
  simp [nsmul_eq_mul, hc]

/-- An explicit expectation for independent, uniformly drawn bucket entries. -/
noncomputable def drawAverage (w : T → G → ℝ) (F : List (T → ℝ) → ℝ) :
    List (Finset G) → List (T → ℝ) → ℝ
  | [], left => F left
  | B :: bs, left =>
      (∑ g ∈ B, drawAverage w F bs (left ++ [fun t => w t g])) / B.card

private theorem draw_eq {q : ℕ} {F : List (T → ℝ) → ℝ} (hf : MultiAffine q F)
    (w : T → G → ℝ) (hw : ∀ g, InCube (fun t => w t g)) (bs : List (Finset G))
    (hb : ∀ B ∈ bs, B.Nonempty) (left : List (T → ℝ))
    (hlen : left.length+bs.length=q) (hl : ∀ z ∈ left, InCube z) :
    drawAverage w F bs left = F (left ++ slotMeans w bs) := by
  classical
  induction bs generalizing left with
  | nil => simp [drawAverage, slotMeans]
  | cons B bs ih =>
    have hb' : ∀ C ∈ bs, C.Nonempty := fun C h => hb C (List.mem_cons_of_mem B h)
    have hB := hb B List.mem_cons_self
    rw [drawAverage]
    change _ = F (left ++ slotMean w B :: slotMeans w bs)
    rw [mean_column hf w hw B hB left (slotMeans w bs) (by simpa [slotMeans, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlen) hl (means_mem w hw bs hb')]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa only [List.append_assoc, List.singleton_append] using
      ih hb' (left ++ [fun t => w t g]) (by simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
        (fix_mem w hw hl g)

/-- Lemma 3.4 for every objective affine in each bucket column on its stated domain. -/
theorem select_le_expectation {F : List (T → ℝ) → ℝ} (w : T → G → ℝ)
    (hw : ∀ g, InCube (fun t => w t g)) (bs : List (Finset G)) (hf : MultiAffine bs.length F)
    (hb : ∀ B ∈ bs, B.Nonempty) (selected : List G) (hg : GreedyForSlots w F [] bs selected) :
    List.Forall₂ (fun B g => g ∈ B) bs selected ∧
      F (selected.map fun g t => w t g) ≤ drawAverage w F bs [] := by
  classical
  let q := bs.length
  have aux (tail : List (Finset G)) (left : List (T → ℝ)) (sel : List G)
      (hne : ∀ B ∈ tail, B.Nonempty) (hl : ∀ z ∈ left, InCube z)
      (hlen : left.length+tail.length=q) (hmin : GreedyForSlots w F left tail sel) :
      List.Forall₂ (fun B g => g ∈ B) tail sel ∧
        F (left ++ sel.map fun g t => w t g) ≤ F (left ++ slotMeans w tail) := by
    induction tail generalizing left sel with
    | nil =>
      cases sel with
      | nil => exact ⟨.nil, le_rfl⟩
      | cons g s => exact False.elim hmin
    | cons B tail ih =>
      cases sel with
      | nil => exact False.elim hmin
      | cons g s =>
        obtain ⟨hgB,hbest,hrest⟩ := hmin
        have hb' : ∀ C ∈ tail, C.Nonempty := fun C h => hne C (List.mem_cons_of_mem B h)
        obtain ⟨hsel,hval⟩ := ih (left ++ [fun t => w t g]) s hb' (fix_mem w hw hl g)
          (by simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]) hrest
        refine ⟨.cons hgB hsel, ?_⟩
        have hnext : F (left ++ (g :: s).map (fun a t => w t a)) ≤
            F (left ++ (fun t => w t g) :: slotMeans w tail) := by
          simpa only [List.append_assoc, List.singleton_append, List.map_cons] using hval
        apply hnext.trans
        change _ ≤ F (left ++ slotMean w B :: slotMeans w tail)
        rw [mean_column hf w hw B ⟨g,hgB⟩ left (slotMeans w tail)
          (by simpa [slotMeans, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen)
          hl (means_mem w hw tail hb')]
        have hc : (0:ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨g,hgB⟩
        apply (le_div_iff₀ hc).2
        simpa [nsmul_eq_mul, mul_comm] using Finset.sum_le_sum hbest
  rw [draw_eq hf w hw bs hb [] (by simp) (by simp)]
  simpa only [List.nil_append] using aux bs [] selected hb (by simp) (by simp [q]) hg

/-- This certifies both the pair-plus-product and the product-only objectives,
for an arbitrary subset of protected types. -/
theorem protected_multiAffine (q : ℕ) (h a b : ℝ) (P : T → ℝ) (K : Finset T) :
    MultiAffine q (protectedSampleObjective h a b P K) := by
  classical
  intro left right _ _ _
  let c (t : T) := slotCoefficient h a b (P t) (left.map (fun x => x t)) (right.map (fun x => x t))
  refine ⟨protectedSampleObjective h a b P K (left ++ (fun _ => 0) :: right),
    (fun t => if t ∈ K then c t else 0), ?_⟩
  intro z _
  simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  unfold protectedSampleObjective
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by
    simpa only [List.map_append, List.map_cons, c] using
      rowObjective_slot h a b (P t) (left.map (fun x => x t)) (right.map (fun x => x t)) (z t)

end ConditionalSelection
end OnlineMMS
