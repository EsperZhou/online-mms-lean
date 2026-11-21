import OnlineMMS.BinaryLarge
import OnlineMMS.BinaryRuntimeGraph

namespace OnlineMMS

open private large_degree_inequality from OnlineMMS.BinaryLarge

/-- Lemma 4.4, with the manuscript's edge bound. The algorithm returns an
independent set with at least the required cardinality and a cubic scan bound. -/
theorem independent_first_bundle {G : Type*} [DecidableEq G] (E : Finset (Finset G))
    (adj : G → G → Bool) (hadj : ∀ a b, adj a b = true ↔ a ≠ b ∧ ({a,b} : Finset G) ∈ E)
    (L : List G) (hL : L.Nodup) (hE : ∀ e ∈ E, e ⊆ L.toFinset ∧ e.card = 2)
    {p ν : ℕ} (hp : 2 ≤ p) (hν : 2 ≤ ν) (hm : 2*p*(ν-1)+2 ≤ L.toFinset.card)
    (he : (E.card : ℝ) ≤ (((2*p+2).choose 2 : ℝ) - 1) *
      (1 + ((ν : ℝ)-2)/(2*(p : ℝ)-1))) :
    let out := BinaryRuntime.graphGreedy adj L.length L
    out.1.toFinset ⊆ L.toFinset ∧ PairIndependent E out.1.toFinset ∧
      ν ≤ out.1.toFinset.card ∧ out.2 ≤ (L.length+1)^3 ∧
      ∃ T ⊆ out.1.toFinset, T.card = ν ∧ PairIndependent E T := by
  have hchoose : (2*p+2).choose 2 = (p+1)*(2*p+1) := by
    rw [Nat.choose_two_right, show 2*p+2-1 = 2*p+1 by omega,
      show 2*p+2 = 2*(p+1) by ring, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have heq : (((2*p+2).choose 2 : ℝ) - 1) = 2*(p:ℝ)^2+3*p := by
    rw [hchoose]; push_cast; ring
  rw [heq] at he
  have hz : ((ν-1 : ℕ) : ℝ) = (ν:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hmr : 2*(p:ℝ)*((ν-1:ℕ):ℝ)+2 ≤ (L.toFinset.card : ℝ) := by exact_mod_cast hm
  have hzr : (1 : ℝ) ≤ ((ν-1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ ν-1 by omega)
  have hsr := large_degree_inequality (p := (p:ℝ)) (z := ((ν-1:ℕ):ℝ)) (e := (E.card:ℝ))
    (by exact_mod_cast hp) hzr hmr (by simpa only [hz, show (ν:ℝ)-1-1 = ν-2 by ring] using he)
  obtain ⟨hsub,hind,hcard,hwork⟩ := BinaryRuntime.graphGreedy_threshold E adj hadj L hL hE hsr
  rw [show ν-1+1 = ν by omega] at hcard
  obtain ⟨T,hT,hsize⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨hsub,hind,hcard,hwork,T,hT,hsize,fun a ha b hb => hind a (hT ha) b (hT hb)⟩

end OnlineMMS
