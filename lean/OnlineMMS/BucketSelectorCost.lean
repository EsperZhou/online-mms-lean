import OnlineMMS.BucketBitComplexity

namespace OnlineMMS.BucketBitComplexity

/-- The tail means require one sum and one division for each type and bucket. -/
def meansOps {m : ℕ} (k : ℕ) (bs : List (Finset (Fin m))) : ℕ :=
  k * (candidateCount bs + bs.length)

theorem bucketCount_le_candidates {m : ℕ} (bs : List (Finset (Fin m)))
    (hne : ∀ B ∈ bs, B.Nonempty) : bs.length ≤ candidateCount bs := by
  induction bs with
  | nil => simp [candidateCount]
  | cons B bs ih =>
    have hB := Finset.card_pos.mpr (hne B (by simp))
    have ht := ih (fun A hA => hne A (by simp [hA]))
    simp only [List.length_cons, candidateCount, List.map_cons, List.sum_cons] at *
    omega

/-- The exact selector, carrying a conservative arithmetic counter through
the same recursive calls. A list minimum performs at most two objective
evaluations and one comparison per candidate. Means are charged afresh for
every objective evaluation, so no caching assumption is needed. -/
def selectCosted {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ) :
    List (Fin k → ℚ) → List (Finset (Fin m)) → List (Fin m) × ℕ
  | _, [] => ([], 0)
  | left, B :: bs =>
      let score (g : Fin m) := objectiveCosted h q c P
        (left ++ (fun t => w t g) :: slotMeansQ w bs)
      let work := 2 * B.card *
        (objectiveOps k (left.length + 1 + bs.length) + meansOps k bs + 1)
      match (B.sort (· ≤ ·)).argmin (fun g => (score g).1) with
      | none =>
          let tail := selectCosted w h q c P left bs
          (tail.1, work + tail.2)
      | some g =>
          let tail := selectCosted w h q c P (left ++ [fun t => w t g]) bs
          (g :: tail.1, work + tail.2)

theorem selectCosted_value {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ)) :
    (selectCosted w h q c P left bs).1 = selectQ w h q c P left bs := by
  induction bs generalizing left with
  | nil => rfl
  | cons B bs ih =>
    simp only [selectCosted, objectiveCosted_spec, selectQ]
    split <;> simp_all only [ih]

theorem objectiveOps_mono {k a b : ℕ} (hab : a ≤ b) : objectiveOps k a ≤ objectiveOps k b := by
  have hp : Monotone pairOps := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [pairOps]
    omega
  unfold objectiveOps
  exact Nat.mul_le_mul_left k (by have := hp hab; omega)

theorem selectCosted_bound {m k M : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ))
    (hslots : left.length + bs.length ≤ M) (hcandidates : candidateCount bs ≤ M) :
    (selectCosted w h q c P left bs).2 ≤ selectionOps k M (candidateCount bs) := by
  induction bs generalizing left with
  | nil => simp [selectCosted, candidateCount, selectionOps]
  | cons B bs ih =>
    have hcard : candidateCount (B :: bs) = B.card + candidateCount bs := by
      simp [candidateCount]
    have htail : candidateCount bs ≤ M := by rw [hcard] at hcandidates; omega
    have hsize : left.length + 1 + bs.length ≤ M := by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hslots
    have hmeans : meansOps k bs ≤ 2 * k * (M + 1) := by
      unfold meansOps
      have hlen : bs.length ≤ M := by omega
      have hm := Nat.mul_le_mul_left k (show candidateCount bs + bs.length ≤ 2 * (M + 1) by omega)
      nlinarith only [hm]
    have hlocal : 2 * B.card *
        (objectiveOps k (left.length + 1 + bs.length) + meansOps k bs + 1) ≤
        2 * B.card * (objectiveOps k M + 2 * k * (M + 1) + 1) :=
      Nat.mul_le_mul_left _ (by have := objectiveOps_mono (k := k) hsize; omega)
    simp only [selectCosted]
    split
    · have hi := ih left (by simp only [List.length_cons] at hslots; omega) htail
      change _ + (selectCosted w h q c P left bs).2 ≤ _
      unfold selectionOps at hi ⊢
      rw [hcard]
      nlinarith only [hlocal, hi]
    · rename_i g he
      have hi := ih (left ++ [fun t => w t g]) (by simpa using hsize) htail
      change _ + (selectCosted w h q c P (left ++ [fun t => w t g]) bs).2 ≤ _
      unfold selectionOps at hi ⊢
      rw [hcard]
      nlinarith only [hlocal, hi]

/-- End-to-end selection: the returned goods obey the paper's conditional
minimization rule, and the counter is polynomial in types and available
goods. The premise also permits the fixed prefix of the quadratic estimator. -/
theorem selectCosted_certified {m k M : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ)
    (P : Fin k → ℚ) (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ))
    (hne : ∀ B ∈ bs, B.Nonempty) (hslots : left.length + bs.length ≤ M)
    (hcandidates : candidateCount bs ≤ M) :
    IsGreedySample (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ) (c : ℝ)
      (fun t => (P t : ℝ)) (realProfiles left) bs (selectCosted w h q c P left bs).1 ∧
      (selectCosted w h q c P left bs).2 ≤ 30 * (k + 1) * (M + 1)^3 := by
  constructor
  · rw [selectCosted_value]
    exact selectQ_greedy w h q c P bs hne left
  · exact (selectCosted_bound w h q c P bs left hslots hcandidates).trans
      (selectionOps_le hcandidates)

theorem objectiveBits_mono_length {h k a b bits C : ℕ} (hab : a ≤ b) :
    objectiveBits h k a bits C ≤ objectiveBits h k b bits C := by
  unfold objectiveBits rowBits
  gcongr

/-- Every candidate score actually visited by the selector has the given
numerator/denominator bound; recursion follows its chosen minimizers. -/
def ScoresBounded {m k : ℕ} (w : Fin k → Fin m → ℚ) (h q c : ℚ) (P : Fin k → ℚ)
    (bits : ℕ) : List (Fin k → ℚ) → List (Finset (Fin m)) → Prop
  | _, [] => True
  | left, B :: bs =>
      (∀ g ∈ B, RationalArithmetic.Bounded
        (objectiveQ h q c P (left ++ (fun t => w t g) :: slotMeansQ w bs)) bits) ∧
      match (B.sort (· ≤ ·)).argmin (fun g =>
        objectiveQ h q c P (left ++ (fun t => w t g) :: slotMeansQ w bs)) with
      | none => ScoresBounded w h q c P bits left bs
      | some g => ScoresBounded w h q c P bits (left ++ [fun t => w t g]) bs

theorem scoresBounded_of_inputs {m k M : ℕ} (w : Fin k → Fin m → ℚ)
    (h b C : ℕ) (q c : ℚ) (P : Fin k → ℚ) (hh : 1 ≤ h)
    (hq : RationalArithmetic.Bounded q C) (hc : RationalArithmetic.Bounded c C)
    (hp : ∀ t, RationalArithmetic.Bounded (P t) C)
    (hw : ∀ t g, RationalArithmetic.Bounded (w t g) b)
    (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ))
    (hleft : ∀ z ∈ left, ∀ t, RationalArithmetic.Bounded (z t) b)
    (hmean : ∀ B ∈ bs, ∀ t, RationalArithmetic.Bounded (slotMeanQ w B t) b)
    (hslots : left.length + bs.length ≤ M) :
    ScoresBounded w h q c P (objectiveBits h k M b C) left bs := by
  induction bs generalizing left with
  | nil => trivial
  | cons B bs ih =>
    have hm : ∀ A ∈ bs, ∀ t, RationalArithmetic.Bounded (slotMeanQ w A t) b :=
      fun A hA => hmean A (by simp [hA])
    have hlen : left.length + 1 + bs.length ≤ M := by
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hslots
    change (∀ g ∈ B, _) ∧ _
    refine ⟨?_, ?_⟩
    · intro g _
      apply (bounded_objectiveQ h q c P _ b C hh hq hc hp ?_).mono
        (objectiveBits_mono_length (by simpa [slotMeansQ, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hlen))
      intro z hz t
      rcases List.mem_append.mp hz with hz | hz
      · exact hleft z hz t
      · rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact hw t g
        · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hz
          exact hm A hA t
    · split
      · exact ih left hleft hm (by simp only [List.length_cons] at hslots; omega)
      · rename_i g he
        apply ih (left ++ [fun t => w t g]) ?_ hm (by simpa using hlen)
        intro z hz t
        rcases List.mem_append.mp hz with hz | hz
        · exact hleft z hz t
        · have hz' : z = fun t => w t g := by simpa using hz
          rw [hz']; exact hw t g

/-- Combined certificate in the declared rational-arithmetic cost model.
The last conjunct bounds every possible objective evaluation on profiles of
the prescribed size, so it applies throughout selection when normalized
weights and bucket means satisfy the common-denominator bounds. -/
theorem selectCosted_bit_certified {m k M : ℕ} (w : Fin k → Fin m → ℚ)
    (h b C : ℕ) (q c : ℚ) (P : Fin k → ℚ) (hh : 1 ≤ h)
    (hq : RationalArithmetic.Bounded q C) (hc : RationalArithmetic.Bounded c C)
    (hp : ∀ t, RationalArithmetic.Bounded (P t) C)
    (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ))
    (hne : ∀ B ∈ bs, B.Nonempty) (hslots : left.length + bs.length ≤ M)
    (hcandidates : candidateCount bs ≤ M) :
    IsGreedySample (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ) (c : ℝ)
      (fun t => (P t : ℝ)) (realProfiles left) bs (selectCosted w h q c P left bs).1 ∧
    bitCostEnvelope (selectCosted w h q c P left bs).2 (objectiveBits h k M b C) ≤
      30 * (k + 1) * (M + 1)^3 * (objectiveBits h k M b C + 1)^3 ∧
    ∀ slots : List (Fin k → ℚ), slots.length ≤ M →
      (∀ z ∈ slots, ∀ t, RationalArithmetic.Bounded (z t) b) →
      (objectiveQ h q c P slots).num.natAbs.size ≤ objectiveBits h k M b C ∧
      (objectiveQ h q c P slots).den.size ≤ objectiveBits h k M b C := by
  obtain ⟨hg, hcost⟩ := selectCosted_certified w h q c P bs left hne hslots hcandidates
  refine ⟨?_, Nat.mul_le_mul_right _ hcost, ?_⟩
  · simpa using hg
  · intro slots hlen hvalues
    exact ((bounded_objectiveQ h q c P slots b C hh hq hc hp hvalues).mono
      (objectiveBits_mono_length hlen)).canonical_digits

/-- A single certificate connects actual selector output, all visited score
sizes, its counted recurrence, and the modeled polynomial bit-cost envelope. -/
theorem selectCosted_complete_certificate {m k M : ℕ} (w : Fin k → Fin m → ℚ)
    (h b C : ℕ) (q c : ℚ) (P : Fin k → ℚ) (hh : 1 ≤ h)
    (hq : RationalArithmetic.Bounded q C) (hc : RationalArithmetic.Bounded c C)
    (hp : ∀ t, RationalArithmetic.Bounded (P t) C)
    (hw : ∀ t g, RationalArithmetic.Bounded (w t g) b)
    (bs : List (Finset (Fin m))) (left : List (Fin k → ℚ))
    (hleft : ∀ z ∈ left, ∀ t, RationalArithmetic.Bounded (z t) b)
    (hmean : ∀ B ∈ bs, ∀ t, RationalArithmetic.Bounded (slotMeanQ w B t) b)
    (hne : ∀ B ∈ bs, B.Nonempty) (hslots : left.length + bs.length ≤ M)
    (hcandidates : candidateCount bs ≤ M) :
    IsGreedySample (fun t g => (w t g : ℝ)) (h : ℝ) (q : ℝ) (c : ℝ)
      (fun t => (P t : ℝ)) (realProfiles left) bs (selectCosted w h q c P left bs).1 ∧
    ScoresBounded w h q c P (objectiveBits h k M b C) left bs ∧
    bitCostEnvelope (selectCosted w h q c P left bs).2 (objectiveBits h k M b C) ≤
      30 * (k + 1) * (M + 1)^3 * (objectiveBits h k M b C + 1)^3 := by
  obtain ⟨hg, hcost, _⟩ :=
    selectCosted_bit_certified w h b C q c P hh hq hc hp bs left hne hslots hcandidates
  exact ⟨hg, scoresBounded_of_inputs w h b C q c P hh hq hc hp hw bs left hleft hmean hslots,
    hcost⟩

end OnlineMMS.BucketBitComplexity
