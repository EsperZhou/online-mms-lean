import OnlineMMS.TwoTypeRealScales
import OnlineMMS.TwoTypeSharpness
import OnlineMMS.PolicyPaths

/-! Proposition 5.2 for the same maximal-scale packet rule on every real
input, including the instances used by the rational implementation. -/

namespace OnlineMMS.TwoType

private noncomputable def active (y : ℝ) : ℚ := if 0 < y then 1 else 0

open private admissibleScale_enough_goods from OnlineMMS.TwoTypeScalePreparation

theorem realScale_zero_iff_fewer_positive_goods {m n : ℕ} (v : Fin m → ℝ)
    (hv : ∀ g, 0 ≤ v g) (hn : 0 < n) :
    realScale v n = 0 ↔ (Finset.univ.filter (fun g => 0 < v g)).card < n := by
  classical
  let S := Finset.univ.filter (fun g => 0 < v g)
  rcases realScale_spec v hv hn with ⟨hz,hno⟩ | h
  · refine ⟨fun _ => ?_, fun _ => hz⟩
    by_contra! hc
    obtain ⟨g,hg,hmin⟩ := S.exists_min_image v (Finset.card_pos.mp (hn.trans_le hc))
    have ha : 0 < v g := (Finset.mem_filter.mp hg).2
    exact hno _ (admissibleScale_of_smallest ha
      (fun i hi => hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)) hc)
  · exact ⟨fun hz => (h.1.1.ne' hz).elim,
      fun hc => (not_le_of_gt hc (admissibleScale_enough_goods h.1)).elim⟩

/-- The packet rule only tests whether a scale is positive. Its packet
weights and tie order are the same on real and rational inputs. -/
noncomputable def realPacketPolicy {m : ℕ} (v : Fin 2 → Fin m → ℝ) (n : ℕ) : Policy m 2 n :=
  let y (t : Fin 2) := realScale (v t) n
  packetPolicy (fun t => active (y t)) (fun t g => realTag (v t g / y t)) n Finset.univ

private theorem packetPolicy_congr_active {m : ℕ} {a b : Fin 2 → ℚ}
    (h : ∀ t, a t ≤ 0 ↔ b t ≤ 0) (tag : Fin 2 → Fin m → Option PacketLevel) (n : ℕ)
    (R : Finset (Fin m)) : packetPolicy a tag n R = packetPolicy b tag n R := by
  have same (r : ℕ) (S : Finset (Fin m)) : packetChoice a tag r S = packetChoice b tag r S := by
    funext t
    simp only [packetChoice, h t]
  induction n generalizing R with
  | zero => rfl
  | succ n ih => simp only [packetPolicy, same, ih]

theorem realPacketPolicy_eq_rational {m n : ℕ} (v : Fin 2 → Fin m → ℚ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    realPacketPolicy (fun t g => (v t g : ℝ)) n = rationalPacketPolicy v n := by
  unfold realPacketPolicy rationalPacketPolicy
  have ht (t : Fin 2) (g : Fin m) := realTag_eq_roundedTagRat (v t) (hv t) hn g
  simp only [ht]
  simp only [realScale_eq_rationalScale _ (hv _) hn]
  apply packetPolicy_congr_active
  intro t
  by_cases ht : 0 < rationalScale (v t) n
  · have ht' : (0:ℝ) < (rationalScale (v t) n : ℝ) := by exact_mod_cast ht
    simp [active,ht',not_le_of_gt ht]
  · have ht' : ¬(0:ℝ) < (rationalScale (v t) n : ℝ) := by exact_mod_cast ht
    simp [active,ht',le_of_not_gt ht]

private theorem transfer_payments {m k n : ℕ} (p : Policy m k n)
    {u v : Fin k → Fin m → ℝ} {a b : Fin k → ℝ} (R : Finset (Fin m))
    (h : ∀ t G, a t ≤ bundleValue (u t) G → b t ≤ bundleValue (v t) G)
    (hp : p.Guarantees u a R) : p.Guarantees v b R := by
  induction p generalizing R with
  | done => trivial
  | step bundles q ih => intro t; exact ⟨(hp t).1,h t _ (hp t).2.1,ih t _ (hp t).2.2⟩

/-- On every real nonnegative input, this specific maximal-scale policy
pays the scale of every arriving type. -/
theorem realPacketPolicy_pays_scale {m n : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    (realPacketPolicy v n).Guarantees v (fun t => realScale (v t) n) Finset.univ := by
  let y (t : Fin 2) := realScale (v t) n
  let f (t : Fin 2) := active (y t)
  let u (t : Fin 2) (g : Fin m) := v t g / y t
  let tag (t : Fin 2) (g : Fin m) := realTag (u t g)
  have hy (t : Fin 2) : 0 ≤ y t := by
    rcases realScale_spec (v t) (hv t) hn with ⟨h,_⟩ | h
    · simp [y,h]
    · exact h.1.1.le
  have hu (t : Fin 2) (g : Fin m) : 0 ≤ u t g := div_nonneg (hv t g) (hy t)
  have hflag (t : Fin 2) : 0 ≤ f t := by dsimp [f,active]; split <;> norm_num
  have hnorm (t : Fin 2) (g : Fin m) : u t g / (f t : ℝ) = u t g := by
    by_cases hp : 0 < y t
    · simp [f,active,hp]
    · have hz := le_antisymm (le_of_not_gt hp) (hy t)
      simp [f,active,u,hz]
  have htag (t : Fin 2) (g : Fin m) :
      score (u t g / (f t : ℝ)) = (tag t g).elim 0 PacketLevel.weight := by
    rw [hnorm]
    exact (realTag_weight (hu t g)).symm
  have hinit (t : Fin 2) (ht : 0 < f t) :
      (n : ℝ) ≤ bundleValue (fun g => score (u t g / (f t : ℝ))) Finset.univ := by
    have hpos : 0 < y t := by by_contra hh; simp [f,active,hh] at ht
    rcases realScale_spec (v t) (hv t) hn with h | h
    · exact ((show (0:ℝ) < 0 from h.1 ▸ hpos)).false.elim
    · simp only [hnorm]
      exact h.1.2
  have hp := packetPolicy_guarantees u hu f hflag tag htag n Finset.univ hinit
  refine transfer_payments (realPacketPolicy v n) Finset.univ (fun t G hpay => ?_) hp
  by_cases ht : 0 < y t
  · change (f t : ℝ) ≤ ∑ g ∈ G, v t g / y t at hpay
    rw [← Finset.sum_div] at hpay
    have hh := (le_div_iff₀ ht).mp hpay
    simpa [f,active,ht,y,bundleValue] using hh
  · have hz := le_antisymm (le_of_not_gt ht) (hy t)
    change y t ≤ _
    rw [hz]
    exact Finset.sum_nonneg fun g _ => hv t g

theorem realPacketPolicy_guarantees {m n : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    (realPacketPolicy v n).Guarantees v (fun t => 4/7 * maximinShare (v t) n hn) Finset.univ :=
  (realPacketPolicy_pays_scale v hv hn).mono fun t => realScale_ge_four_sevenths (v t) (hv t) hn

private theorem packetPolicy_full {m n : ℕ} (hn : 0 < n) (a : Fin 2 → ℚ)
    (tag : Fin 2 → Fin m → Option PacketLevel) (R : Finset (Fin m))
    (v : Fin 2 → Fin m → ℝ) (b : Fin 2 → ℝ)
    (hp : (packetPolicy a tag n R).Guarantees v b R) :
    (packetPolicy a tag n R).FullAllocation R := by
  induction n generalizing R with
  | zero => omega
  | succ n ih =>
    intro t
    refine ⟨(hp t).1,?_⟩
    cases n with
    | zero => simp [packetPolicy, packetChoice, Policy.FullAllocation]
    | succ n => exact ih (by omega) _ (hp t).2.2

theorem realPacketPolicy_full {m n : ℕ} (v : Fin 2 → Fin m → ℝ)
    (hv : ∀ t g, 0 ≤ v t g) (hn : 0 < n) :
    (realPacketPolicy v n).FullAllocation Finset.univ :=
  packetPolicy_full hn _ _ _ _ _ (realPacketPolicy_pays_scale v hv hn)

theorem realPacketPolicy_exact_guarantee :
    IsGreatest {ρ : ℝ | ∀ m n (hn : 0 < n) (v : Fin 2 → Fin m → ℝ), (∀ t g, 0 ≤ v t g) →
      (realPacketPolicy v n).Guarantees v (fun t => ρ * maximinShare (v t) n hn) Finset.univ} (4/7) := by
  refine ⟨fun _ _ hn v hv => realPacketPolicy_guarantees v hv hn, fun ρ hρ => ?_⟩
  apply rationalPacketPolicy_exact_guarantee.2
  intro m n hn v hv
  simpa [realPacketPolicy_eq_rational v hv hn] using
    hρ m n hn (fun t g => (v t g : ℝ)) (fun t g => by change 0 ≤ (v t g : ℝ); exact_mod_cast hv t g)

/-- All realized worst-sequence scores of the specified policy, one per
original instance, with the manuscript's cap at one. -/
def realPacketFactors : Set ℝ :=
  {z | ∃ (m n : ℕ) (hn : 0 < n) (v : Fin 2 → Fin m → ℝ), (∀ t g, 0 ≤ v t g) ∧
    z = (realPacketPolicy v n).worstScore (by decide) v (fun t => maximinShare (v t) n hn)}

/-- The infimum over all real two-type instances and all positive numbers
of agents is exactly four sevenths, as in Proposition 5.2. -/
theorem realPacketPolicy_infimum : sInf realPacketFactors = 4/7 := by
  classical
  apply IsGLB.csInf_eq
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨m,n,hn,v,hv,rfl⟩
      apply Finset.le_inf'
      intro s _
      exact ((realPacketPolicy v n).score_iff_guaranteesSequence v hv _
        (fun t => maximinShare_nonnegative _ (hv t) hn) _ (by norm_num) _
        (realPacketPolicy_full v hv hn) s).2
        ((Policy.guarantees_iff_sequences _ _ _ _).1 (realPacketPolicy_guarantees v hv hn) s)
    · intro ρ hρ
      apply realPacketPolicy_exact_guarantee.2
      intro m n hn v hv
      let p := realPacketPolicy v n
      let b (t : Fin 2) := maximinShare (v t) n hn
      have h : ρ ≤ p.worstScore (by decide) v b := hρ ⟨m,n,hn,v,hv,rfl⟩
      apply (Policy.guarantees_iff_sequences _ _ _ _).2
      intro s
      have hs : ρ ≤ cappedHistoryScore v b (p.playHistory s) :=
        h.trans (Finset.inf'_le _ (Finset.mem_univ s))
      have hone := ((le_cappedHistoryScore_iff v b _ _).1 hs).1
      exact (p.score_iff_guaranteesSequence v hv b (fun t => maximinShare_nonnegative _ (hv t) hn)
        ρ hone _ (realPacketPolicy_full v hv hn) s).1 hs
  · let v : Fin 2 → Fin 0 → ℝ := fun _ _ => 0
    exact ⟨(realPacketPolicy v 1).worstScore (by decide) v (fun t => maximinShare (v t) 1 (by decide)),
      0,1,by decide,v,fun _ _ => le_rfl,rfl⟩

end OnlineMMS.TwoType
