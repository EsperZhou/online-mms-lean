import OnlineMMS.RunningOperandBits

namespace OnlineMMS.RationalAlgorithm1

open RationalArithmetic BucketBitComplexity
open private qCoeff cCoeff widthQ from OnlineMMS.RationalAlgorithm1
open private widthQ_pos from OnlineMMS.RationalAlgorithm1Cost
open private coefficientFromStats summarizeQ from OnlineMMS.BucketRunningScores

/-- Binary digit count of the three integer dimensions and the explicitly
listed rational valuations, with one unit for an empty encoding. -/
def encodingLength {m k : ℕ} (n : ℕ) (v : Fin k → Fin m → ℚ) : ℕ :=
  inputDigits v + n.size + k.size + m.size + 1

private theorem goods_le_digits {m k : ℕ} (hk : 0 < k) (v : Fin k → Fin m → ℚ) :
    m ≤ inputDigits v := by
  let t : Fin k := ⟨0,hk⟩
  have H : m ≤ valuationInputDigits (v t) := by
    unfold valuationInputDigits
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun g _ => show 1 ≤ (v t g).num.natAbs.size + (v t g).den.size from
        (show 1 ≤ (v t g).den.size from Nat.size_pos.mpr (v t g).pos).trans (Nat.le_add_left _ _))
  exact H.trans (Finset.single_le_sum (fun i _ => Nat.zero_le (valuationInputDigits (v i)))
    (Finset.mem_univ t))

private theorem parameter_digits (k : ℕ) : (parameterQ k).size ≤ k.size+9 := by
  have hle : parameterQ k ≤ 220*(k+1) := by
    unfold parameterQ
    split
    · omega
    · have H := Nat.findGreatest_le (P := fun j => 32*j^2 < k) k
      omega
  have hw : (k+1).size ≤ k.size+1 := Nat.size_le.mpr (by
    have H := Nat.lt_size_self k
    rw [pow_succ]; omega)
  have H := (Nat.size_le_size hle).trans (size_mul_le 220 (k+1))
  have H' : (220:ℕ).size≤8 := Nat.size_le.mpr (by decide)
  omega

private theorem budget_le {m k n : ℕ} (hk : 0 < k) (v : Fin k → Fin m → ℚ) :
    let h := parameterQ k
    let d := 2*inputDigits v + m + 2
    let b := d+m.size
    let C := productCoefficientBits h m d
    (runningRowBits h m b C+b+1)*k+1 ≤ 2048*(k+1)*(m+1)*encodingLength n v := by
  let L := encodingLength n v
  let h := parameterQ k
  let d := 2*inputDigits v+m+2
  let b := d+m.size
  let a := h.size+b+3
  let U := a*(m+1)
  let C := productCoefficientBits h m d
  have hg := goods_le_digits hk v
  have hh := parameter_digits k
  have hb : a ≤ 20*L := by dsimp [a,h,b,d,L,encodingLength]; omega
  have ha : 3 ≤ a := by dsimp [a]; omega
  have hU : a ≤ U := Nat.le_mul_of_pos_right a (by omega)
  have hm : (h.size+d+3)*m ≤ U :=
    Nat.mul_le_mul (by dsimp [a,b]; omega) (by omega)
  have hsmall : h.size+1 ≤ a := by dsimp [a]; omega
  have hC : C ≤ 8*U := by dsimp [C,productCoefficientBits]; omega
  have hrel : runningRowBits h m b C+b+1 ≤ 64*U := by
    have hba : b ≤ a := by dsimp [a]; omega
    change 5*(U+C+2)+b+1 ≤ _
    omega
  have hRU : U ≤ 20*L*(m+1) := Nat.mul_le_mul_right _ hb
  have hB : runningRowBits h m b C+b+1 ≤ 1280*L*(m+1) := calc
    _ ≤ 64*(20*L*(m+1)) := hrel.trans (Nat.mul_le_mul_left _ hRU)
    _ = _ := by ring
  have H := Nat.mul_le_mul_right k hB
  have hL : 1 ≤ L := by dsimp [L,encodingLength]; omega
  change (runningRowBits h m b C+b+1)*k+1 ≤ 2048*(k+1)*(m+1)*L
  nlinarith [Nat.zero_le (L*m*k),Nat.zero_le (L*m),Nat.zero_le (L*k)]

/-- Every partial dot product compared by optimized Algorithm 1 at every
prefix has O(k(m+1)L) numerator and denominator digits. The statement even
allows arbitrary goods to have been fixed in the preceding bucket columns. -/
theorem policy_sampling_digits {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (v : Fin k → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g) (ts : List (Fin k))
    (r : ℕ) (i : Fin k) (before after : List (Finset (Fin m))) (B : Finset (Fin m))
    (chosen : List (Fin m)) (hc : chosen.length=before.length) (g : Fin m) (K : Finset (Fin k)) :
    let h := parameterQ k
    let x := policyState v n ts
    let bs := rationalBuckets (x.weight i) (widthQ h (h/4) r x) x.remaining
    let u := slotMeanQ x.weight B
    let left := chosen.map (fun a t => x.weight t a)
    let right := after.map (slotMeanQ x.weight)
    bs=before++B::after →
      Bounded (∑ t ∈ K, x.weight t g *
        coefficientFromStats h (qCoeff x) (cCoeff h x) x.products u (summarizeQ h (left++u::right)) t)
        (2048*(k+1)*(m+1)*encodingLength n v) := by
  dsimp only
  let h := parameterQ k
  let x := policyState v n ts
  let H := widthQ h (h/4) r x
  let bs := rationalBuckets (x.weight i) H x.remaining
  let d := 2*inputDigits v+m+2
  let b := d+m.size
  let C := productCoefficientBits h m d
  change bs = before++B::after → _
  intro he
  obtain ⟨D,hD,hist⟩ := policyState_gridHistory hn hk v hv
  have hs : GridHistory h D x := hist ts
  have h216 : 216 ≤ h := by dsimp [h]; rw [parameterQ_eq]; exact (bucketMultiplier_bounds hk).1
  have hh : 0 < h := by omega
  have hH : 0 < H := widthQ_pos hh (by omega)
  have spec := rationalBuckets_spec (x.weight i) hH x.remaining
  have hne (S : Finset (Fin m)) (hm : S ∈ bs) : S.Nonempty :=
    Finset.card_pos.mp (spec.bucket_size S hm ▸ hH)
  have hcount : bs.length ≤ m := (length_le_candidateCount hne).trans
    (candidateCount_le_goods bs spec.pairwise_disjoint)
  have hval (t : Fin k) (g : Fin m) : Bounded (x.weight t g) b := by
    obtain ⟨ha,h0,h1⟩ := hs.weights t g
    exact (ha.bounded (hD t).1 h0 h1).mono (by dsimp [b,d]; have := (hD t).2; omega)
  have hmean (S : Finset (Fin m)) (hS : S ∈ bs) (t : Fin k) : Bounded (slotMeanQ x.weight S t) b := by
    have hw := spec.bucket_size S hS
    have hs' : H ≤ m := by rw [← hw]; simpa using S.card_le_univ
    exact (slotMeanQ_bounded (hD t).1 hH x.weight S hw t (fun g => (hs.weights t g).1)
      (fun g => (hs.weights t g).2)).mono (by dsimp [b,d]; have := (hD t).2; have := Nat.size_le_size hs'; omega)
  have hC : 1 ≤ C := by dsimp [C,productCoefficientBits]; omega
  have hq : Bounded (qCoeff x) C := by unfold qCoeff; split <;> first | exact bounded_one.mono hC | exact bounded_zero.mono hC
  have hc' : Bounded (cCoeff h x) C := by
    unfold cCoeff; split
    · exact (bounded_firstCoefficient hh).mono (by dsimp [C,productCoefficientBits]; omega)
    · exact bounded_one.mono hC
  apply Bounded.mono _ (budget_le (n := n) hk v)
  apply running_score_bits (m := m) (b := b) (C := C) hh _ _ _ _ _
  · simp [he, hc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hcount ⊢
    exact hcount
  · exact hq
  · exact hc'
  · exact hs.products_bounded hh hD
  · exact hmean B (by simp [he])
  · exact fun t => hval t g
  · intro a ha t
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp ha
    exact hval t z
  · intro a ha t
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp ha
    exact hmean S (by simp [he,hS]) t

end OnlineMMS.RationalAlgorithm1
