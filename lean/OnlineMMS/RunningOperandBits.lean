import OnlineMMS.BucketRunningScores
import OnlineMMS.RationalAlgorithm1FastWork

namespace OnlineMMS.BucketBitComplexity

open RationalArithmetic
open private coefficientFromStats summarizeQ from OnlineMMS.BucketRunningScores

/-- All the per-type arithmetic in a conditional comparison has a linear
digit budget in the number of goods. The coefficient budget covers the
historical product and both constants of the active objective. -/
def runningRowBits (h m b C : ℕ) : ℕ := 5*((h.size+b+3)*(m+1)+C+2)

theorem conditional_operands_bounded {h m b C : ℕ} (hh : 1 ≤ h) (q c p u x : ℚ)
    (left right : List ℚ) (hlen : left.length+1+right.length ≤ m)
    (hq : Bounded q C) (hc : Bounded c C) (hp : Bounded p C)
    (hu : Bounded u b) (hx : Bounded x b)
    (hl : ∀ a ∈ left, Bounded a b) (hr : ∀ a ∈ right, Bounded a b) :
    let ys := left ++ u :: right
    let f := fun y : ℚ => 1+((h:ℚ)-1)*y
    let A := ys.sum
    let V := sampleProductQ h ys
    let budget := runningRowBits h m b C
    ∀ y ∈ [A, V, f u, f x, A-u, A-u+x, V/f u, V/f u*f x, p*V, p*V/f u,
      2*q, 2*q*(A-u), c*(p*V/f u), c*(p*V/f u)*((h:ℚ)-1),
      2*q*(A-u)+c*(p*V/f u)*((h:ℚ)-1)], Bounded y budget := by
  let ys := left ++ u :: right
  let L := h.size+b+3
  let U := L*(m+1)
  have hDm : Bounded ((h:ℚ)-1) (h.size+1) := by
    rw [← Nat.cast_one (R := ℚ), ← Nat.cast_sub hh]
    exact (bounded_nat (h-1)).mono (Nat.add_le_add_right (Nat.size_le_size (Nat.sub_le ..)) 1)
  have hfac (a : ℚ) (ha : Bounded a b) : Bounded (1+((h:ℚ)-1)*a) L :=
    (bounded_one.add (hDm.mul ha)).mono (by dsimp [L]; omega)
  have hlist : ∀ a ∈ ys, Bounded a b := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hl a ha
    · rcases List.mem_cons.mp ha with rfl|ha
      · exact hu
      · exact hr a ha
  have hy : ys.length ≤ m := by simpa [ys, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
  have hs : Bounded ys.sum U := (bounded_sum ys b hlist).mono (by
    have H := Nat.mul_le_mul (show b+1 ≤ L by dsimp [L]; omega) hy
    dsimp [U]; rw [Nat.mul_add, Nat.mul_one]; dsimp [L] at *; omega)
  have hv : Bounded (sampleProductQ h ys) U := (bounded_sampleProductQ h ys b hh hlist).mono (by
    have H := Nat.mul_le_mul_left L hy
    dsimp [U]; rw [Nat.mul_add,Nat.mul_one]; dsimp [L] at *; omega)
  have hs' : Bounded (ys.sum-u) U := by
    have hlen' : (left++right).length ≤ m := by simpa using (show left.length+right.length ≤ m by omega)
    have ht := bounded_sum (left++right) b (fun a ha =>
      (List.mem_append.mp ha).elim (hl a) (hr a))
    have H := Nat.mul_le_mul (show b+1 ≤ L by dsimp [L]; omega) hlen'
    rw [show ys.sum-u=(left++right).sum by simp [ys]; ring]
    apply ht.mono
    dsimp [U]; rw [Nat.mul_add,Nat.mul_one]; dsimp [L] at *; omega
  have hfpos : 0 < 1 + ((h:ℚ)-1)*u := by
    have := mul_nonneg hDm.nonneg hu.nonneg
    linarith
  have h2 : Bounded (2:ℚ) 2 := ⟨2,1,by decide,by norm_num,by decide,by decide⟩
  have hsmall : L ≤ U := (Nat.le_mul_of_pos_right L (by omega : 0 < m+1))
  have huL : b ≤ L := by dsimp [L]; omega
  have hhm : h.size+1 ≤ L := by dsimp [L]; omega
  change ∀ y ∈ [ys.sum, _, _, _, _, _, _, _, _, _, _, _, _, _, _], Bounded y _
  intro y hy'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy'
  rcases hy' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | apply hs.mono
    | apply hv.mono
    | apply (hfac u hu).mono
    | apply (hfac x hx).mono
    | apply hs'.mono
    | apply (hs'.add hx).mono
    | apply (hv.div (hfac u hu) hfpos).mono
    | apply ((hv.div (hfac u hu) hfpos).mul (hfac x hx)).mono
    | apply (hp.mul hv).mono
    | apply ((hp.mul hv).div (hfac u hu) hfpos).mono
    | apply (h2.mul hq).mono
    | apply ((h2.mul hq).mul hs').mono
    | apply (hc.mul ((hp.mul hv).div (hfac u hu) hfpos)).mono
    | apply ((hc.mul ((hp.mul hv).div (hfac u hu) hfpos)).mul hDm).mono
    | apply (((h2.mul hq).mul hs').add ((hc.mul ((hp.mul hv).div (hfac u hu) hfpos)).mul hDm)).mono
  all_goals change _ ≤ 5*(U+C+2)
  all_goals omega

/-- This is the dot product compared by runningChoice, including an arbitrary
subset of summands for its live accumulator. -/
theorem running_score_bits {k m h b C : ℕ} (hh : 1 ≤ h) (q c : ℚ) (P u z : Fin k → ℚ)
    (left right : List (Fin k → ℚ)) (hlen : left.length+1+right.length ≤ m)
    (hq : Bounded q C) (hc : Bounded c C) (hp : ∀ t, Bounded (P t) C)
    (hu : ∀ t, Bounded (u t) b) (hz : ∀ t, Bounded (z t) b)
    (hl : ∀ a ∈ left, ∀ t, Bounded (a t) b) (hr : ∀ a ∈ right, ∀ t, Bounded (a t) b)
    (K : Finset (Fin k)) :
    Bounded (∑ t ∈ K, z t * coefficientFromStats h q c P u (summarizeQ h (left++u::right)) t)
      ((runningRowBits h m b C+b+1)*k+1) := by
  classical
  let f (t : Fin k) := z t * coefficientFromStats h q c P u (summarizeQ h (left++u::right)) t
  have hrow (t : Fin k) : Bounded (f t) (runningRowBits h m b C+b) := by
    have hop := conditional_operands_bounded hh q c (P t) (u t) (z t)
      (left.map (fun a => a t)) (right.map (fun a => a t)) (by simpa using hlen)
      hq hc (hp t) (hu t) (hz t)
      (fun a ha => by obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha; exact hl s hs t)
      (fun a ha => by obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha; exact hr s hs t)
    have hc' : Bounded (coefficientFromStats h q c P u (summarizeQ h (left++u::right)) t)
        (runningRowBits h m b C) := by
      apply hop
      simp [coefficientFromStats,summarizeQ, List.map_append, List.map_cons]
    exact ((hz t).mul hc').mono (by omega)
  have part (S : Finset (Fin k)) : Bounded (∑ t ∈ S, f t) ((runningRowBits h m b C+b+1)*S.card+1) := by
    induction S using Finset.induction_on with
    | empty => simpa using bounded_zero
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_not_mem hi, Nat.mul_succ]
      exact ((hrow i).add ih).mono (by omega)
  exact (part K).mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by simpa using K.card_le_univ : K.card ≤ k)) 1)

end OnlineMMS.BucketBitComplexity
