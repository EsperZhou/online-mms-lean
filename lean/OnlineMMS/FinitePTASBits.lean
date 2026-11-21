import OnlineMMS.FinitePTASRational
import OnlineMMS.RationalArithmetic

namespace OnlineMMS

open scoped BigOperators
open RationalArithmetic

private theorem bounded_finite_sum {ι : Type*} (S : Finset ι) (v : ι → ℚ) (b : ℕ)
    (hv : ∀ g ∈ S, Bounded (v g) b) :
    Bounded (∑ g ∈ S, v g) ((b+1)*S.card+1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using bounded_zero
  | insert g S hg ih =>
    rw [Finset.sum_insert hg,Finset.card_insert_of_not_mem hg]
    have h := (hv g (Finset.mem_insert_self ..)).add (ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)))
    exact h.mono (by rw [Nat.mul_succ]; omega)

/-- Numerators and denominators of TPS scan candidates have polynomial size. -/
def tpsCandidateBits (m n b : ℕ) : ℕ :=
  (b+1)*m+n.size+2

theorem rationalTPSIntersection_bounded {m : ℕ} (v : Fin m → ℚ) (n b : ℕ)
    (hv : ∀ g, Bounded (v g) b) (c : ℚ) :
    Bounded (rationalTPSIntersection v n c) (tpsCandidateBits m n b) := by
  let S := Finset.univ.filter (fun g => v g ≤ c)
  let h := n - (Finset.univ.filter (fun g => c < v g)).card
  have hcard : S.card ≤ m := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
  have hsum : Bounded (∑ g ∈ S, v g) ((b+1)*m+1) :=
    (bounded_finite_sum S v b (fun g _ => hv g)).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hcard) _)
  change Bounded ((∑ g ∈ S, v g) / (h : ℚ)) _
  by_cases hh : 0 < h
  · have hbits : h.size ≤ n.size := Nat.size_le_size (Nat.sub_le _ _)
    have hd : Bounded (h : ℚ) (n.size+1) :=
      (bounded_nat h).mono (Nat.add_le_add_right hbits _)
    exact (hsum.div hd (by exact_mod_cast hh)).mono (by unfold tpsCandidateBits; omega)
  · simp only [Nat.eq_zero_of_not_pos hh, Nat.cast_zero, div_zero]
    exact bounded_zero.mono (by unfold tpsCandidateBits; omega)

theorem rationalTPSCandidate_bounded {m : ℕ} (v : Fin m → ℚ) (n b : ℕ)
    (hv : ∀ g, Bounded (v g) b) (c : ℚ) (hc : c ∈ rationalTPSCandidates v n) :
    Bounded c (tpsCandidateBits m n b) := by
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact bounded_zero.mono (by unfold tpsCandidateBits; omega)
  · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hc
    exact rationalTPSIntersection_bounded v n b hv d

theorem rationalTPS_bounded {m : ℕ} (v : Fin m → ℚ) (n b : ℕ) (hv : ∀ g, Bounded (v g) b) :
    Bounded (rationalTPS v n) (tpsCandidateBits m n b) := by
  have h : rationalTPS v n ∈
      insert 0 ((rationalTPSCandidates v n).filter (rationalTPSFeasible v n)) :=
    Finset.max'_mem _ _
  rcases Finset.mem_insert.mp h with hz | hm
  · rw [hz]
    exact bounded_zero.mono (by unfold tpsCandidateBits; omega)
  · exact rationalTPSCandidate_bounded v n b hv _ (Finset.mem_filter.mp hm).1

/-- The capped-sum feasibility tests also have a polynomial bound on both exact operands. -/
theorem rationalTPSFeasibility_operands_bounded {m : ℕ} (v : Fin m → ℚ) (n b : ℕ)
    (hv : ∀ g, Bounded (v g) b) (q : ℚ) (hq : q ∈ rationalTPSCandidates v n) :
    let c := max b (tpsCandidateBits m n b)
    Bounded ((n : ℚ)*q) (n.size+1+c) ∧
    Bounded (∑ g, min (v g) q) ((c+1)*m+1) := by
  dsimp only
  let c := max b (tpsCandidateBits m n b)
  have hq' : Bounded q c :=
    (rationalTPSCandidate_bounded v n b hv q hq).mono (le_max_right _ _)
  refine ⟨(bounded_nat n).mul hq',?_⟩
  simpa using bounded_finite_sum Finset.univ _ c
    (fun g _ => ((hv g).mono (le_max_left _ _)).min hq')

/-- Before taking its floor, each scaled item weight is a bounded-size exact fraction. -/
theorem rationalMMSScaledWeight_bounded {m n L b : ℕ} (v : Fin m → ℚ)
    (hv : ∀ g, Bounded (v g) b) (g : Fin m) :
    let d := rationalTPS v n
    let c := max b (tpsCandidateBits m n b)
    Bounded ((2*m*L : ℕ) * (min (v g) d / d)) ((2*m*L).size+1 + c + c) := by
  dsimp only
  let d := rationalTPS v n
  let c := max b (tpsCandidateBits m n b)
  have hq : Bounded d c := (rationalTPS_bounded v n b hv).mono (le_max_right _ _)
  change Bounded ((2*m*L : ℕ) * (min (v g) d / d)) _
  by_cases hd : 0 < d
  · have hmin := ((hv g).mono (le_max_left _ _)).min hq
    exact ((bounded_nat _).mul (hmin.div hq hd)).mono (by omega)
  · have hz : d = 0 := le_antisymm (le_of_not_gt hd) hq.nonneg
    rw [hz,div_zero,mul_zero]
    exact bounded_zero.mono (by omega)

/-- Computing the exact payment of a rounded partition uses bounded-size bundle sums. -/
theorem rationalMMSPayment_bounded {m n L b : ℕ} (v : Fin m → ℚ)
    (hv : ∀ g, Bounded (v g) b) (hn : 0 < n) :
    Bounded (rationalMMSPayment (L := L) v hn) ((b+1)*m+1) := by
  let p := rationalMMSAssignment (L := L) v hn
  let f := fun j : Fin n => ∑ g ∈ Finset.univ.filter (fun g => p g = j), v g
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' hne f
  change Bounded (Finset.univ.inf' hne f) _
  rw [hi]
  let S := Finset.univ.filter (fun g => p g = i)
  have hcard : S.card ≤ m := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
  exact (bounded_finite_sum S v b (fun g _ => hv g)).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hcard) _)

end OnlineMMS
