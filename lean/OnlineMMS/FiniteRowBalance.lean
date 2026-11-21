import OnlineMMS.FinitePartitions

namespace OnlineMMS

def listWeight {G : Type*} (w : G → ℝ) (goods : List G) : ℝ :=
  (goods.map w).sum

def greedyDifference (start : ℝ) (values : List ℝ) : ℝ :=
  values.foldl (fun diff value => |diff - value|) start

theorem listWeight_append {G : Type*} (w : G → ℝ) (X Y : List G) :
    listWeight w (X ++ Y) = listWeight w X + listWeight w Y := by
  simp [listWeight]

theorem greedyDifference_nonneg (d : ℝ) (hd : 0 ≤ d) (vals : List ℝ) :
    0 ≤ greedyDifference d vals := by
  induction vals generalizing d with
  | nil => exact hd
  | cons x xs ih => exact ih _ (abs_nonneg _)

/-- Construct the two actual bundles by placing each cell into a lighter bundle. -/
theorem greedy_balancing_split {G : Type*} (w : G → ℝ) (cells X Y : List G) :
    ∃ A B : List G, (A ++ B).Perm (X ++ Y ++ cells) ∧
      |listWeight w A - listWeight w B| =
        greedyDifference |listWeight w X - listWeight w Y| (cells.map w) := by
  induction cells generalizing X Y with
  | nil => exact ⟨X, Y, by simp, rfl⟩
  | cons g cells ih =>
    by_cases h : listWeight w X ≤ listWeight w Y
    · obtain ⟨A, B, hp, habs⟩ := ih (g :: X) Y
      refine ⟨A, B, hp.trans ?_, ?_⟩
      · simpa only [List.cons_append] using
          (List.perm_middle : ((X ++ Y) ++ g :: cells).Perm (g :: ((X ++ Y) ++ cells))).symm
      · rw [habs]
        simp only [greedyDifference, List.map_cons, List.foldl_cons]
        congr 1
        rw [abs_of_nonpos (sub_nonpos.mpr h)]
        unfold listWeight
        simp only [List.map_cons, List.sum_cons]
        rw [← abs_neg (w g + (List.map w X).sum - (List.map w Y).sum)]
        congr 1
        ring
    · obtain ⟨A, B, hp, habs⟩ := ih X (g :: Y)
      refine ⟨A, B, hp.trans ?_, ?_⟩
      · simpa only [List.append_assoc] using
          ((List.perm_middle : (Y ++ g :: cells).Perm (g :: (Y ++ cells))).symm.append_left X)
      · rw [habs]
        simp only [greedyDifference, List.map_cons, List.foldl_cons]
        congr 1
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
        unfold listWeight
        simp only [List.map_cons, List.sum_cons]
        congr 1
        ring

/-- When every nonnegative next value is less than D, a difference less
than D remains below D. -/
theorem greedyDifference_lt_of_bounded {d D : ℝ} (hd : 0 ≤ d) (hD : d < D)
    (vals : List ℝ) (hv : ∀ x ∈ vals, 0 ≤ x ∧ x < D) :
    greedyDifference d vals < D := by
  induction vals generalizing d with
  | nil => exact hD
  | cons x xs ih =>
    have hx := hv x (by simp)
    change greedyDifference (abs (d - x)) xs < D
    apply ih (abs_nonneg (d - x))
    · exact abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro y hy
      exact hv y (List.mem_cons_of_mem _ hy)

theorem greedyDifference_three_lt {d x y z D : ℝ} (hd : 0 ≤ d)
    (h₀ : d - x - y - z < D) (h₁ : x - y - z < D) (h₂ : y - z < D) (h₃ : z < D) :
    greedyDifference d [x,y,z] < D := by
  change abs (abs (abs (d-x) - y) - z) < D
  have hdx : |d-x| < D + z + y := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdy : abs (abs (d-x) - y) < D + z :=
    abs_lt.mpr ⟨by linarith [abs_nonneg (d-x)], by linarith⟩
  exact abs_lt.mpr ⟨by linarith [abs_nonneg (abs (d-x)-y)], by linarith⟩

theorem greedyDifference_two_lt {d x y D : ℝ} (hd : 0 ≤ d)
    (h₀ : d - x - y < D) (h₁ : x - y < D) (h₂ : y < D) :
    greedyDifference d [x,y] < D := by
  change abs (abs (d-x) - y) < D
  have hdx : |d-x| < D + y := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact abs_lt.mpr ⟨by linarith [abs_nonneg (d-x)], by linarith⟩

end OnlineMMS
