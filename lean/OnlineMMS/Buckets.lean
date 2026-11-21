import OnlineMMS.Model
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Linarith

namespace OnlineMMS

/-- Consecutive blocks of a nonincreasing ordering. The last, short block is
    represented by the terminal constructor and does not enter the sample. -/
inductive SortedBuckets {G : Type*} [DecidableEq G] (w : G → ℝ) (width : ℕ) :
    Finset G → List (Finset G) → Prop
  | tail {remaining} (hsize : remaining.card < width) :
      SortedBuckets w width remaining []
  | full {bucket remaining buckets}
      (hsize : bucket.card = width) (hdisj : Disjoint bucket remaining)
      (horder : ∀ g ∈ bucket, ∀ x ∈ remaining, w x ≤ w g)
      (rest : SortedBuckets w width remaining buckets) :
      SortedBuckets w width (bucket ∪ remaining) (bucket :: buckets)

namespace SortedBuckets
variable {G : Type*} [DecidableEq G] {w : G → ℝ} {width : ℕ}

private theorem of_sorted_list (hwidth : 0 < width) (goods : List G)
    (hnd : goods.Nodup) (hsorted : goods.Pairwise (fun g x => w x ≤ w g)) :
    ∃ buckets, SortedBuckets w width goods.toFinset buckets := by
  by_cases hshort : goods.length < width
  · exact ⟨[], .tail (by simpa [List.toFinset_card_of_nodup hnd] using hshort)⟩
  · let head := goods.take width
    let tail := goods.drop width
    have happ : head ++ tail = goods := List.take_append_drop _ _
    have hnd' : (head ++ tail).Nodup := happ ▸ hnd
    have hs' : (head ++ tail).Pairwise (fun g x => w x ≤ w g) := happ ▸ hsorted
    have hsplit := List.pairwise_append.mp hs'
    have hdisj : Disjoint head.toFinset tail.toFinset := by
      refine Finset.disjoint_left.mpr (fun x hx hy => ?_)
      exact List.disjoint_left.mp (List.nodup_append.mp hnd').2.2 (by simpa using hx) (by simpa using hy)
    obtain ⟨buckets, hrest⟩ := of_sorted_list hwidth tail
      (List.nodup_append.mp hnd').2.1 hsplit.2.1
    have hunion : head.toFinset ∪ tail.toFinset = goods.toFinset := by
      rw [← List.toFinset_append, happ]
    refine ⟨head.toFinset :: buckets, hunion ▸ .full ?_ hdisj ?_ hrest⟩
    · rw [List.toFinset_card_of_nodup (List.nodup_append.mp hnd').1]
      exact List.length_take_of_le (Nat.le_of_not_gt hshort)
    · intro g hg x hx
      exact hsplit.2.2 g (by simpa using hg) x (by simpa using hx)
termination_by goods.length
decreasing_by
  simp [tail]
  omega

theorem exists_buckets (hwidth : 0 < width) (remaining : Finset G) :
    ∃ buckets, SortedBuckets w width remaining buckets := by
  let rel : G → G → Prop := fun g x => w x ≤ w g
  letI : DecidableRel rel := fun g x => inferInstanceAs (Decidable (w x ≤ w g))
  letI : IsTotal G rel := ⟨fun g x => le_total (w x) (w g)⟩
  letI : IsTrans G rel := ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩
  let goods := remaining.toList.mergeSort (rel · ·)
  have hperm : goods.Perm remaining.toList := List.mergeSort_perm _ _
  have hnd : goods.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hs : goods.Pairwise rel := List.sorted_mergeSort' rel _
  have heq : goods.toFinset = remaining := by
    ext g
    simpa using hperm.mem_iff (a := g)
  rw [← heq]
  exact of_sorted_list hwidth goods hnd hs

theorem bucket_size {remaining : Finset G} {buckets : List (Finset G)}
    (h : SortedBuckets w width remaining buckets) :
    ∀ bucket ∈ buckets, bucket.card = width := by
  induction h with
  | tail => simp
  | @full bucket remaining buckets hsize hdisj horder rest ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hsize
    · exact ih _ hB

theorem bucket_subsets {remaining : Finset G} {buckets : List (Finset G)}
    (h : SortedBuckets w width remaining buckets) :
    ∀ bucket ∈ buckets, bucket ⊆ remaining := by
  induction h with
  | tail => simp
  | @full bucket remaining buckets hsize hdisj horder rest ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact Finset.subset_union_left
    · exact (ih _ hB).trans Finset.subset_union_right

theorem pairwise_disjoint {remaining : Finset G} {buckets : List (Finset G)}
    (h : SortedBuckets w width remaining buckets) : buckets.Pairwise Disjoint := by
  induction h with
  | tail => simp
  | @full bucket remaining buckets hsize hdisj horder rest ih =>
    exact List.pairwise_cons.mpr
      ⟨fun B hB => hdisj.mono_right (rest.bucket_subsets B hB), ih⟩

theorem selected_valid {remaining : Finset G} {buckets : List (Finset G)}
    (h : SortedBuckets w width remaining buckets) {goods : List G}
    (hchoose : List.Forall₂ (fun B g => g ∈ B) buckets goods) :
    goods.toFinset ⊆ remaining ∧ goods.Nodup := by
  induction h generalizing goods with
  | tail =>
    cases hchoose
    simp
  | @full bucket remaining buckets hsize hdisj horder rest ih =>
    cases hchoose with
    | cons hg hgs =>
      rename_i g gs
      obtain ⟨hsub, hnd⟩ := ih hgs
      have hnot : g ∉ gs := fun hmem =>
        Finset.disjoint_left.mp hdisj hg (hsub (by simpa using hmem))
      constructor
      · rw [List.toFinset_cons]
        exact Finset.insert_subset_iff.mpr
          ⟨Finset.mem_union_left _ hg, hsub.trans Finset.subset_union_right⟩
      · exact List.nodup_cons.mpr ⟨hnot, hnd⟩

/-- Paper's sorted-list payment lemma in the form before dividing by width. -/
theorem payment {remaining : Finset G} {buckets : List (Finset G)}
    (h : SortedBuckets w width remaining buckets) {goods : List G}
    (hchoose : List.Forall₂ (fun B g => g ∈ B) buckets goods)
    (hnonneg : ∀ g, 0 ≤ w g) {a : ℝ} (ha : 0 ≤ a) (hweight : ∀ g ∈ remaining, w g ≤ a) :
    (∑ g ∈ remaining, w g) ≤ (width : ℝ) * (a + (goods.map w).sum) := by
  induction h generalizing goods a with
  | @tail remaining hsize =>
    cases hchoose
    simp only [List.map_nil, List.sum_nil, add_zero]
    calc
      (∑ g ∈ remaining, w g) ≤ ∑ _g ∈ remaining, a :=
        Finset.sum_le_sum hweight
      _ = (remaining.card : ℝ) * a := by simp [nsmul_eq_mul]
      _ ≤ (width : ℝ) * a :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hsize) ha
  | @full bucket remaining buckets hsize hdisj horder rest ih =>
    cases hchoose with
    | cons hg hgs =>
      rename_i g gs
      have hfirst : (∑ x ∈ bucket, w x) ≤ (width : ℝ) * a := by
        calc
          (∑ x ∈ bucket, w x) ≤ ∑ _x ∈ bucket, a :=
            Finset.sum_le_sum (fun x hx => hweight x (Finset.mem_union_left _ hx))
          _ = _ := by simp [hsize, nsmul_eq_mul]
      have htail := ih hgs (hnonneg g) (fun x hx => horder g hg x hx)
      rw [Finset.sum_union hdisj, List.map_cons, List.sum_cons]
      linarith

end SortedBuckets

end OnlineMMS
