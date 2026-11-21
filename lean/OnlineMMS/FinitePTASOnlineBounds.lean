import OnlineMMS.FinitePTASBits
import OnlineMMS.FinitePTASOnlineThree
import OnlineMMS.FinitePTASCompressed

namespace OnlineMMS

open RationalArithmetic
open private bounded_finite_sum from OnlineMMS.FinitePTASBits

/-- Every partial sum needed for a real bundle comparison has polynomial binary size. -/
theorem rationalOnlineBundle_bounded {m b : ℕ} (v : Fin m → ℚ)
    (hv : ∀ g, Bounded (v g) b) (S : Finset (Fin m)) :
    Bounded (rationalBundleValue v S) ((b+1)*m+1) := by
  have hc : S.card ≤ m := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
  exact (bounded_finite_sum S v b (fun g _ => hv g)).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _)

/-- Comparing compressed bundles keeps the bit-size coefficient bounded
by the constant number of cells at horizons four and five. -/
theorem rationalCompressedBundle_bounded {m n b : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, Bounded (v t g) b) (nmax : n ≤ 5) (part : Fin 2 → Fin m → Fin n)
    (R : Finset (Fin m)) (t : Fin 2) (S : Finset (Fin (n*n))) :
    Bounded (rationalBundleValue (cellValuations v R (partitionCellTag part) t) S)
      (((b+1)*m+2)*25+1) := by
  have hcell (i : Fin (n*n)) :
      Bounded (cellValuations v R (partitionCellTag part) t i) ((b+1)*m+1) :=
    rationalOnlineBundle_bounded (v t) (hv t) _
  have hc := Nat.mul_le_mul nmax nmax
  have h := rationalOnlineBundle_bounded _ hcell S
  exact h.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _)

theorem longShortFactor_bounded (r : ℕ) :
    Bounded (longShortFactors r).1 6 ∧ Bounded (longShortFactors r).2 6 := by
  unfold longShortFactors
  split
  · exact ⟨⟨9,10,by decide,rfl,by decide,by decide⟩,⟨3,4,by decide,rfl,by decide,by decide⟩⟩
  · exact ⟨⟨3,4,by decide,rfl,by decide,by decide⟩,⟨27,40,by decide,rfl,by decide,by decide⟩⟩

theorem longRationalOrientedTarget_bounded {b : ℕ} (q : Fin 2 → ℚ)
    (hq : ∀ t, Bounded (q t) b) (r : ℕ) (first t : Fin 2) :
    Bounded (rationalOrientedTarget q (longShortFactors r).1 (longShortFactors r).2 first t)
      (6+b) := by
  unfold rationalOrientedTarget
  split
  · exact (longShortFactor_bounded r).1.mul (hq t)
  · exact (longShortFactor_bounded r).2.mul (hq t)

theorem shortThreeTarget_bounded {b : ℕ} (q : ℚ) (hq : Bounded q b) :
    Bounded ((9/10)*q) (4+b) :=
  (show Bounded (9/10) 4 from ⟨9,10,by decide,rfl,by decide,by decide⟩).mul hq

/-- Four bundle scans cover both possible next revelations in the two-arrival rule. -/
def rationalTwoBundleScanWork (m : ℕ) : ℕ := 4*(m+1)

theorem rationalThreeThenTwoScanWork_le (m : ℕ) :
    2*(rationalThreeCutScanWork m+rationalTwoBundleScanWork m) ≤ 3080*(m+1) := by
  unfold rationalTwoBundleScanWork
  have h := rationalThreeCutScanWork_le m
  omega

/-- The aggregation of two input types has at most 50 scans of the original goods. -/
theorem compressedAggregationScans_le {n : ℕ} (hn : n ≤ 5) (m : ℕ) :
    2*(n*n)*m ≤ 50*m := by
  exact Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn hn))

end OnlineMMS
