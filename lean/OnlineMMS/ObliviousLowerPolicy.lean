import OnlineMMS.ObliviousLowerLottery

namespace OnlineMMS.ObliviousFixed
noncomputable section
open Law

/-- One allocation and its admissible successor, including the goods identity used at
every recursive policy node. -/
structure Move {m : ℕ} {S : Type} (goods : S → Finset (Fin m)) (valid : ℕ → S → Prop)
    (r : ℕ) (x : S) where
  bundle : Finset (Fin m)
  next : S
  subset : bundle ⊆ goods x
  remaining : goods next = goods x \ bundle
  ok : valid r next

def miss (floor amount : ℝ) : ℝ := if floor ≤ amount then 0 else 1

private def branchFailure {m k r} (v : Fin k → Fin m → ℝ) (floor : Fin k → ℝ)
    (R : Finset (Fin m)) (t : Fin k) (tail : Fin r → Fin k)
    (a : Finset (Fin m) × Policy m k r) : ℝ :=
  @ite _ (a.1 ⊆ R ∧ floor t ≤ bundleValue (v t) a.1 ∧
    a.2.GuaranteesSequence v floor (R \ a.1) tail) (Classical.propDecidable _) 0 1

private theorem branchFailure_le {m k r} (v : Fin k → Fin m → ℝ) (floor : Fin k → ℝ)
    (R : Finset (Fin m)) (t : Fin k) (tail : Fin r → Fin k)
    (B : Finset (Fin m)) (p : Policy m k r) (hB : B ⊆ R) :
    branchFailure v floor R t tail (B,p) ≤
      miss (floor t) (bundleValue (v t) B) + Law.failure p v floor (R \ B) tail := by
  classical
  unfold branchFailure miss Law.failure
  by_cases hp : floor t ≤ bundleValue (v t) B <;>
    by_cases hw : p.GuaranteesSequence v floor (R \ B) tail <;> simp [hB, hp, hw]

/-- A finite behavioral allocation rule defines one lottery on complete legal trees.
The supermartingale estimate is required separately for each fixed type, while the
bound sums only the types on the sequence fixed before the draw. -/
theorem policy_law_of_steps {m k : ℕ} {S : Type}
    (goods : S → Finset (Fin m)) (valid : ℕ → S → Prop)
    (empty : ∀ x, valid 0 x → goods x = ∅)
    (v : Fin k → Fin m → ℝ) (floor : Fin k → ℝ)
    (q : ℕ → ℝ) (hq : ∀ r, 0 ≤ q r) (potential : ℕ → S → Fin k → ℝ)
    (step : ∀ r x, valid (r+1) x → ∀ t : Fin k,
      ∃ D : Law (Move goods valid r x),
        D.All (fun a => miss (floor t) (bundleValue (v t) a.bundle) ≤
          q (r+1) * potential (r+1) x t) ∧
        (r ≠ 0 → ∀ u, D.mean (fun a => potential r a.next u) ≤ potential (r+1) x u)) :
    ∀ n x, valid n x → ∃ D : Law (Policy m k n),
      D.All (fun p => p.FullAllocation (goods x)) ∧ ∀ seq,
      D.mean (fun p => Law.failure p v floor (goods x) seq) ≤
        ∑ j : Fin n, q (n - j.val) * potential n x (seq j) := by
  classical
  intro n
  induction n with
  | zero =>
    intro x hx
    refine ⟨Law.pure .done, fun _ => empty x hx, fun seq => ?_⟩
    simp [Law.failure, Policy.GuaranteesSequence]
  | succ r ih =>
    intro x hx
    choose transitions immediate budget using step r x hx
    have ht (t : Fin k) (a : Move goods valid r x) := ih a.next a.ok
    choose children childLegal childBound using ht
    let branches (t : Fin k) : Law (Finset (Fin m) × Policy m k r) :=
      (transitions t).bind fun a => (children t a).map (fun p => (a.bundle, p))
    let D := (Law.joint k branches).map (fun a =>
      Policy.step (fun t => (a t).1) (fun t => (a t).2))
    refine ⟨D, ?_, ?_⟩
    · have leg (t : Fin k) : (branches t).All (fun a =>
          a.1 ⊆ goods x ∧ a.2.FullAllocation (goods x \ a.1)) := by
        apply Law.all_bind
        intro i j
        let z := (transitions t).val i
        exact ⟨z.subset, z.remaining ▸ childLegal t z j⟩
      exact Law.joint_all branches _ leg
    · intro seq
      let t := seq 0
      let tail := Fin.tail seq
      let current := q (r+1) * potential (r+1) x t
      let future := ∑ j : Fin r, q (r-j.val) * potential (r+1) x (tail j)
      have hshape : (∑ j : Fin (r+1), q (r+1-j.val) * potential (r+1) x (seq j)) =
          current + future := by
        rw [Fin.sum_univ_succ]
        simp [current, future, t, tail, Fin.tail]
      rw [hshape]
      change ((Law.joint k branches).mean (fun a => branchFailure v floor (goods x) t tail (a t))) ≤ _
      rw [Law.joint_marginal]
      dsimp only [branches]
      rw [Law.mean_bind]
      simp only [Law.mean_map]
      let tailcost (a : Move goods valid r x) :=
        ∑ j : Fin r, q (r-j.val) * potential r a.next (tail j)
      have hchild (i : (transitions t).Atom) :
          let a := (transitions t).val i
          (children t a).mean (fun p => branchFailure v floor (goods x) t tail (a.bundle,p))
            ≤ current + tailcost a := by
        let a := (transitions t).val i
        let missNow := miss (floor t) (bundleValue (v t) a.bundle)
        calc
          _ ≤ (children t a).mean (fun p => missNow + Law.failure p v floor (goods a.next) tail) := by
            apply Law.mean_mono
            intro j
            rw [a.remaining]
            exact branchFailure_le v floor (goods x) t tail a.bundle _ a.subset
          _ = missNow + (children t a).mean (fun p => Law.failure p v floor (goods a.next) tail) := by
            rw [Law.mean_add, Law.mean_const]
          _ ≤ current + tailcost a := add_le_add (immediate t i) (childBound t a tail)
      refine (Law.mean_mono (D := transitions t)
        (f := fun a => (children t a).mean (fun p => branchFailure v floor (goods x) t tail (a.bundle,p)))
        (g := fun a => current + tailcost a) hchild).trans ?_
      rw [Law.mean_add, Law.mean_const]
      apply add_le_add_left
      dsimp only [tailcost, future]
      rw [Law.mean_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [Law.mean_smul]
      exact mul_le_mul_of_nonneg_left (budget t (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)) _) (hq _)

end
end OnlineMMS.ObliviousFixed
