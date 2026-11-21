import OnlineMMS.FiniteRowMatrix

namespace OnlineMMS

/-- Appendix B.2 for the two supplied partitions. Every term in A or B is a
whole row-column intersection. This also preserves the column labels when
the column lower bound is smaller than MMS or is nonpositive. -/
theorem group_six_supplied_cells {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (R : Finset (Fin m)) (rows cols : Fin m → Fin 3) (q : ℝ)
    (hcol : ∀ j, q ≤ bundleValue v (R.filter (fun g => cols g=j))) :
    let w := fun c : Fin 3 × Fin 3 => bundleValue v (R.filter (fun g => (rows g,cols g)=c))
    ∃ i j : Fin 3, i ≠ j ∧ ∃ A B : List (Fin 3 × Fin 3),
      (A++B).Perm [(i,0),(i,1),(i,2),(j,0),(j,1),(j,2)] ∧
      9*q/10 ≤ (A.map w).sum ∧ 9*q/10 ≤ (B.map w).sum := by
  classical
  let w := fun c : Fin 3 × Fin 3 => bundleValue v (R.filter (fun g => (rows g,cols g)=c))
  let col := fun j : Fin 3 => bundleValue v (R.filter (fun g => cols g=j))
  have hw (c) : 0 ≤ w c := Finset.sum_nonneg (fun g _ => hv g)
  by_cases hq : 0 < q
  · let v' := fun c : Fin 3 × Fin 3 => (10/col c.2)*w c
    have hc (j) : 0 < col j := hq.trans_le (hcol j)
    have h0 (c) : 0 ≤ v' c := mul_nonneg (div_nonneg (by norm_num) (hc _).le) (hw c)
    have hg (j : Fin 3) : (∑ i : Fin 3, w (i,j)) = col j := by
      have he (i : Fin 3) : R.filter (fun g => (rows g,cols g)=(i,j)) =
          (R.filter (fun g => cols g=j)).filter (fun g => rows g=i) := by
        ext g; simp only [Finset.mem_filter,Prod.mk.injEq]; tauto
      simpa only [w,he,col] using sum_paymentParts v (R.filter (fun g => cols g=j)) rows
    have htot (j : Fin 3) : (∑ i : Fin 3, v' (i,j))=10 := by
      change (∑ i : Fin 3, (10/col j)*w (i,j)) = 10
      rw [← Finset.mul_sum,hg,div_mul_cancel₀ _ (hc j).ne']
    obtain ⟨i,j,hij,A,B,hab,ha,hb⟩ := normalized_matrix_split v' h0 htot
    have hscale (c : Fin 3 × Fin 3) : q/10*v' c ≤ w c := by
      change q/10*((10/col c.2)*w c) ≤ w c
      rw [show q/10*((10/col c.2)*w c) = (q/col c.2)*w c by ring]
      exact mul_le_of_le_one_left (hw _) ((div_le_one (hc _)).2 (hcol _))
    have hlist (l : List (Fin 3 × Fin 3)) : q/10*(l.map v').sum ≤ (l.map w).sum := by
      induction l with
      | nil => simp
      | cons c l ih => simpa [mul_add] using add_le_add (hscale c) ih
    have H (l : List (Fin 3 × Fin 3)) (hn : 9 ≤ (l.map v').sum) : 9*q/10 ≤ (l.map w).sum := by
      exact (show 9*q/10 = (q/10)*9 by ring) ▸
        (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ q/10)).trans (hlist l)
    exact ⟨i,j,hij,A,B,hab,H A ha,H B hb⟩
  · refine ⟨0,1,by decide,[(0,0),(0,1),(0,2)],[(1,0),(1,1),(1,2)],List.Perm.refl _,?_,?_⟩
    all_goals change _ ≤ (_ + (_ + (_ + 0)))
    all_goals
      apply (show 9*q/10 ≤ 0 by linarith).trans
      exact add_nonneg (hw _) (add_nonneg (hw _) (add_nonneg (hw _) le_rfl))

end OnlineMMS
