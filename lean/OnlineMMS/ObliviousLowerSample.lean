import OnlineMMS.ObliviousLowerLottery
import OnlineMMS.FixedWidthKernel

namespace OnlineMMS.ObliviousFixed
noncomputable section

def draw {G : Type} (B : Finset G) (hB : B.Nonempty) : Law G where
  Atom := ↥B
  finite := inferInstance
  mass _ := 1 / B.card
  nonneg _ := by positivity
  total := by
    have hb : (0:ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
    simp [Finset.card_univ, nsmul_eq_mul, hb.ne']
  val g := g.1

theorem mean_draw {G : Type} (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) :
    (draw B hB).mean f = (∑ g ∈ B, f g) / B.card := by
  unfold Law.mean
  change (∑ g : B, (1 / (B.card:ℝ)) * f g) = _
  rw [← Finset.mul_sum, Finset.sum_coe_sort]
  ring

/-- Independent uniform representatives, one for each full bucket. -/
def drawBuckets {G : Type} : ∀ B : List (Finset G), (∀ C ∈ B, C.Nonempty) → Law (List G)
  | [], _ => Law.pure []
  | C :: rest, hc => (draw C (hc _ (by simp))).bind fun g =>
      (drawBuckets rest (fun x hx => hc x (by simp [hx]))).map (g :: ·)

theorem drawBuckets_selection {G : Type} (B : List (Finset G)) (hB : ∀ C ∈ B, C.Nonempty) :
    (drawBuckets B hB).All (fun xs => List.Forall₂ (fun C g => g ∈ C) B xs) := by
  induction B with
  | nil => exact fun _ => .nil
  | cons C rest ih =>
    apply Law.all_bind
    intro g j
    exact .cons g.2 (ih _ j)

theorem mean_drawBuckets_product {k : ℕ} {G : Type} (w : Fin k → G → ℝ)
    (t : Fin k) (h : ℝ) (B : List (Finset G)) (hB : ∀ C ∈ B, C.Nonempty) :
    (drawBuckets B hB).mean (fun gs => sampleProduct h (gs.map (w t))) =
      sampleProduct h ((slotMeans w B).map (fun f => f t)) := by
  induction B with
  | nil => simp [drawBuckets, slotMeans, sampleProduct]
  | cons C rest ih =>
    let M := sampleProduct h ((slotMeans w rest).map (fun f => f t))
    simp only [drawBuckets, Law.mean_bind, Law.mean_map, List.map_cons, sampleProduct]
    change (draw C _).mean (fun g => (drawBuckets rest _).mean
      (fun xs => (1+(h-1)*w t g) * sampleProduct h (xs.map (w t)))) =
      (1+(h-1)*(slotMean w C t)) * M
    simp_rw [Law.mean_smul, ih]
    change (draw C _).mean (fun a => (1+(h-1)*w t a) * M) = _
    calc
      _ = (draw C _).mean (fun a => M * (1+(h-1)*w t a)) := by
        apply Law.mean_congr
        intro _
        ring
      _ = M * (1 + (h-1)*slotMean w C t) := by
        rw [Law.mean_smul, Law.mean_add, Law.mean_const, Law.mean_smul, mean_draw]
        rfl
      _ = _ := mul_comm _ _

/-- A single sample multiplies the fixed target type's expected exponential
loss by at most three regardless of the number of remaining goods. -/
theorem sample_exp_mean_bound {m k r h : ℕ} (hh : 16 ≤ h)
    {v : Fin k → Fin m → ℝ} {d : Fin k → ℝ} {x : FixedWidth.State m k Unit}
    (hx : FixedWidth.Valid v d (r+1) x)
    (t u : Fin k) (b : List (Finset (Fin m)))
    (hb : SortedBuckets (x.weight t) (h*(r+1+x.samples)) x.remaining b)
    (nonempty : ∀ C ∈ b, C.Nonempty) :
    (drawBuckets b nonempty).mean (fun gs => sampleProduct (h:ℝ) (gs.map (x.weight u))) ≤ 3 := by
  let H := h * (r+1+x.samples)
  let N : ℝ := ((r+1 : ℕ):ℝ)+x.samples
  have hH : 0 < H := Nat.mul_pos (by omega) (by omega)
  have hR : 0 < (h:ℝ) := by exact_mod_cast (show 0<h by omega)
  have hone : 1 ≤ (h:ℝ) := by exact_mod_cast (show 1≤h by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  let row := (slotMeans x.weight b).map (fun f => f u)
  have hmass : row.sum ≤ 1/(h:ℝ) := by
    have hmean := slotMeans_sum_le_of_width x.weight b x.remaining H hb.pairwise_disjoint
      hb.bucket_size hb.bucket_subsets u (fun g => (hx.weights u g).1)
    refine hmean.trans ((div_le_div_of_nonneg_right (hx.cap u) (Nat.cast_nonneg H)).trans ?_)
    have he : (H:ℝ) = (h:ℝ)*N := by dsimp [H,N]; push_cast; ring
    change N/(H:ℝ) ≤ 1/(h:ℝ)
    rw [he]
    exact le_of_eq (by field_simp; ring)
  have hz := slotMeans_nonneg x.weight b u (fun g => (hx.weights u g).1)
  have hZ : 0 ≤ row.sum := List.sum_nonneg hz
  have hex : ((h:ℝ)-1) * row.sum ≤ 1 := by
    calc
      _ ≤ (h:ℝ) * row.sum := by nlinarith
      _ ≤ (h:ℝ) * (1/(h:ℝ)) := mul_le_mul_of_nonneg_left hmass hR.le
      _ = 1 := by field_simp
  rw [mean_drawBuckets_product]
  exact (sampleProduct_le_exp hone row hz).trans ((Real.exp_le_exp.mpr hex).trans
    (Real.exp_one_lt_d9.trans (by norm_num)).le)

end
end OnlineMMS.ObliviousFixed
