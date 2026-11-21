import OnlineMMS.FinitePTAS
import OnlineMMS.RationalTPS
import Mathlib.Data.Rat.Floor

open scoped BigOperators

namespace OnlineMMS

/-- Round the capped rational values to natural weights. -/
def rationalMMSWeights {m : ℕ} (v : Fin m → ℚ) (n L : ℕ) : Fin m → ℕ :=
  let d := rationalTPS v n
  fun g => (Rat.floor ((2*m*L : ℕ) * (min (v g) d / d))).toNat

theorem rationalMMSWeights_eq {m n L : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) :
    rationalMMSWeights v n L = roundedMMSWeights (fun g => (v g : ℝ)) n L := by
  funext g
  simp only [rationalMMSWeights, roundedMMSWeights, normalizedWeight,
    ← rationalTPS_correct hn v hv, ← Int.floor_toNat]
  congr 1
  change ⌊(_ : ℚ)⌋ = _
  rw [← Rat.floor_cast (α := ℝ)]
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div, Rat.cast_min]

/-- Executable rational preprocessing, followed by the integer dynamic program. -/
def rationalMMSAssignment {m n L : ℕ} (v : Fin m → ℚ) (hn : 0 < n) : Fin m → Fin n :=
  roundedOptimalAssignment hn (rationalMMSWeights v n L)

theorem rationalMMSAssignment_guarantee {m n L : ℕ} (v : Fin m → ℚ) (hv : ∀ g, 0 ≤ v g)
    (hn : 0 < n) (hL : 0 < L) (j : Fin n) :
    (1 - (1 : ℝ)/L) * maximinShare (fun g => (v g : ℝ)) n hn ≤
      partitionValue (fun g => (v g : ℝ)) (rationalMMSAssignment (L := L) v hn) j := by
  have hvR : ∀ g, (0 : ℝ) ≤ (v g : ℝ) := fun g => by exact_mod_cast hv g
  rw [rationalMMSAssignment, rationalMMSWeights_eq v hv hn]
  exact roundedMMSAssignment_guarantee _ hvR hn hL j

/-- Compute the exact minimum of the returned rational partition. -/
def rationalMMSPayment {m n L : ℕ} (v : Fin m → ℚ) (hn : 0 < n) : ℚ :=
  let p := rationalMMSAssignment (L := L) v hn
  Finset.univ.inf' ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    (fun j => ∑ g ∈ Finset.univ.filter (fun g => p g = j), v g)

theorem rationalMMSPayment_cast {m n L : ℕ} (v : Fin m → ℚ) (hn : 0 < n) :
    (rationalMMSPayment (L := L) v hn : ℝ) =
      partitionMin (fun g => (v g : ℝ)) hn (rationalMMSAssignment (L := L) v hn) := by
  simp only [rationalMMSPayment, partitionMin, partitionValue]
  rw [Finset.comp_inf'_eq_inf'_comp _ (fun x : ℚ => (x : ℝ))
    (fun x y => Rat.cast_min x y)]
  simp only [Function.comp_def, Rat.cast_sum]

/-- Choose an integer precision that realizes any prescribed positive error. -/
theorem exists_roundedMMS_precision (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ (1 : ℝ)/L ≤ ε := by
  let L := ⌈ε⁻¹⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hceil : ε⁻¹ ≤ (L : ℝ) := Nat.le_ceil _
  refine ⟨L,hL,(div_le_iff₀ hLR).2 ?_⟩
  have h := mul_le_mul_of_nonneg_left hceil hε.le
  rwa [mul_inv_cancel₀ hε.ne'] at h

/-- The short-horizon factors, with the first type named first. -/
noncomputable def shortHorizonFactors : ℕ → ℝ × ℝ
  | 2 => (1,1)
  | 3 => (1,9/10)
  | 4 => (9/10,3/4)
  | 5 => (3/4,27/40)
  | _ => (0,0)

/-- The computed rational partitions support the manuscript's type-specific
guarantees, with one approximation loss from preprocessing. -/
theorem rational_short_horizon_oriented_policy {m r L : ℕ}
    (v : Fin 2 → Fin m → ℚ) (hv : ∀ t g, 0 ≤ v t g)
    (hr : 1 ≤ r) (hr' : r ≤ 4) (hL : 0 < L) (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (by omega)
    let ab := shortHorizonFactors (r+1)
    ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      (1-(1 : ℝ)/L) * μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-(1 : ℝ)/L) * orientedTarget μ ab.1 ab.2 first t)
        (Finset.univ \ G) := by
  dsimp only
  let w : Fin 2 → Fin m → ℝ := fun t g => v t g
  let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (by omega)
  let q : Fin 2 → ℝ := fun t => rationalMMSPayment (L := L) (v t) (by omega : 0 < r+1)
  have hw (t : Fin 2) (g : Fin m) : 0 ≤ w t g := by
    dsimp [w]
    exact_mod_cast hv t g
  have hqpart (t : Fin 2) :
      q t = partitionMin (w t) (by omega : 0 < r+1)
        (rationalMMSAssignment (L := L) (v t) (by omega)) :=
    rationalMMSPayment_cast (v t) (by omega)
  have hpart (t : Fin 2) : HasPaymentPartition (w t) Finset.univ (r+1) (q t) := by
    rw [hqpart]
    exact ⟨rationalMMSAssignment (L := L) (v t) (by omega),
      partitionMin_le_partitionValue _ (by omega) _⟩
  have hq (t : Fin 2) : 0 ≤ q t := by
    rw [hqpart]
    exact partitionMin_nonneg _ (hw t) _ _
  have hqapprox (t : Fin 2) : (1-(1 : ℝ)/L) * μ t ≤ q t := by
    rw [hqpart]
    apply Finset.le_inf'
    intro j _
    exact rationalMMSAssignment_guarantee (v t) (hv t) (by omega) hL j
  change ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      (1-(1 : ℝ)/L) * μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-(1 : ℝ)/L) *
        orientedTarget μ (shortHorizonFactors (r+1)).1 (shortHorizonFactors (r+1)).2 first t)
        (Finset.univ \ G)
  have hrs : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hrs with h | h | h | h
  · subst r
    obtain ⟨p,hp⟩ := two_arrival_policy_of_partitions w Finset.univ q hpart
    cases p with
    | step G next =>
      refine ⟨G first,next first,(hqapprox first).trans (hp first).2.1,(hp first).2.2.mono ?_⟩
      intro t
      simpa [shortHorizonFactors,orientedTarget] using hqapprox t
  · subst r
    obtain ⟨G,p,_,hp,hc⟩ := three_arrival_first_choice w hw Finset.univ q hpart first
    exact ⟨G,p,(hqapprox first).trans hp,
      oriented_approximate_partition_transfer first (by norm_num [shortHorizonFactors])
        (by norm_num [shortHorizonFactors]) hqapprox hc⟩
  · subst r
    obtain ⟨G,p,_,hp,hc⟩ := four_arrival_first_choice w hw Finset.univ q hq hpart first
    exact ⟨G,p,(hqapprox first).trans hp,
      oriented_approximate_partition_transfer first (by norm_num [shortHorizonFactors])
        (by norm_num [shortHorizonFactors]) hqapprox hc⟩
  · subst r
    obtain ⟨G,p,_,hp,hc⟩ := five_arrival_first_choice w hw Finset.univ q hq hpart first
    exact ⟨G,p,(hqapprox first).trans hp,
      oriented_approximate_partition_transfer first (by norm_num [shortHorizonFactors])
        (by norm_num [shortHorizonFactors]) hqapprox hc⟩

/-- Any positive approximation tolerance supports all four type-specific guarantees. -/
theorem rational_short_horizon_ptas {m r : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hr : 1 ≤ r) (hr' : r ≤ 4) (ε : ℝ) (hε : 0 < ε)
    (first : Fin 2) :
    let w : Fin 2 → Fin m → ℝ := fun t g => v t g
    let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (by omega)
    let ab := shortHorizonFactors (r+1)
    ∃ (G : Finset (Fin m)) (p : Policy m 2 r),
      (1-ε) * μ first ≤ bundleValue (w first) G ∧
      p.Guarantees w (fun t => (1-ε) * orientedTarget μ ab.1 ab.2 first t)
        (Finset.univ \ G) := by
  dsimp only
  let w : Fin 2 → Fin m → ℝ := fun t g => v t g
  let μ : Fin 2 → ℝ := fun t => maximinShare (w t) (r+1) (by omega)
  let ab := shortHorizonFactors (r+1)
  obtain ⟨L,hL,hacc⟩ := exists_roundedMMS_precision ε hε
  obtain ⟨G,p,hG,hp⟩ := rational_short_horizon_oriented_policy v hv hr hr' hL first
  have hμ (t : Fin 2) : 0 ≤ μ t :=
    maximinShare_nonnegative _ (fun g => by
      change (0 : ℝ) ≤ (v t g : ℝ)
      exact_mod_cast hv t g) (by omega)
  have hab : 0 ≤ ab.1 ∧ 0 ≤ ab.2 := by
    have hrs : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases hrs with h | h | h | h <;> norm_num [ab, h, shortHorizonFactors]
  have hcoef : 1-ε ≤ 1-(1 : ℝ)/L := sub_le_sub_left hacc 1
  refine ⟨G,p,(mul_le_mul_of_nonneg_right hcoef (hμ first)).trans hG,hp.mono ?_⟩
  intro t
  apply mul_le_mul_of_nonneg_right hcoef
  unfold orientedTarget
  split
  · exact mul_nonneg hab.1 (hμ t)
  · exact mul_nonneg hab.2 (hμ t)

end OnlineMMS
