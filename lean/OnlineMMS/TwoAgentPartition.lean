import OnlineMMS.FinitePartitions

namespace OnlineMMS

/-- The decision test in Section 2 is precisely the equal-sum partition
problem on the same goods. It therefore applies to every integer input. -/
theorem two_MMS_half_iff_partition {m : ℕ} (v : Fin m → ℝ) :
    maximinShare v 2 (by decide) = bundleValue v Finset.univ / 2 ↔
    ∃ S : Finset (Fin m), bundleValue v S = bundleValue v Sᶜ := by
  classical
  have H (S : Finset (Fin m)) : bundleValue v S + bundleValue v Sᶜ = bundleValue v Finset.univ :=
    Finset.sum_add_sum_compl S v
  constructor
  · intro heq
    obtain ⟨p,hp⟩ := paymentPartition_of_mms v (by decide : 0 < 2)
    let S := Finset.univ.filter (fun g => p g=0)
    have hc : Sᶜ = Finset.univ.filter (fun g => p g=1) := by
      ext g
      simp only [S, Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
      generalize p g = a
      fin_cases a <;> decide
    have h0 := hp 0
    have h1 := hp 1
    rw [heq] at h0 h1
    change _ ≤ bundleValue v S at h0
    rw [← hc] at h1
    exact ⟨S, by linarith only [H S,h0,h1]⟩
  · rintro ⟨S,hs⟩
    apply le_antisymm (by simpa using maximinShare_le_average v (by decide : 0<2))
    let p : Fin m → Fin 2 := fun g => if g ∈ S then 0 else 1
    apply le_trans _ (partitionMin_le_maximinShare v (by decide) p)
    apply Finset.le_inf'
    intro j _
    fin_cases j
    · have he : Finset.univ.filter (fun g => p g=0)=S := by ext g; by_cases hm : g∈S <;> simp [p,hm]
      change _ ≤ ∑ g ∈ Finset.univ.filter (fun g => p g=0), v g
      rw [he]
      change _ ≤ bundleValue v S
      linarith only [H S,hs]
    · have he : Finset.univ.filter (fun g => p g=1)=Sᶜ := by ext g; by_cases hm : g∈S <;> simp [p,hm]
      change _ ≤ ∑ g ∈ Finset.univ.filter (fun g => p g=1), v g
      rw [he]
      change _ ≤ bundleValue v Sᶜ
      linarith only [H S,hs]

end OnlineMMS
