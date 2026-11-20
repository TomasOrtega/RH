import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Take `⟨w, hw⟩` from `a`. Take `⟨w', hw'⟩` from `b`. Simplify using `only at hab`. Substitute `hab` using the available equality. Both sides reduce to the same expression.
-/
theorem dominant_weight_ext {N : ℕ} (a b : DomWeight N) (hab : a.w = b.w) : a = b := by
  obtain ⟨w, hw⟩ := a
  obtain ⟨w', hw'⟩ := b
  simp only at hab
  subst hab
  rfl

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))`.
-/
theorem extremal_mem_nablaSq' (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))

/- English proof (translation)
Substitute `h` using the available equality. Establish `hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i)` using `fun i => (hmu i).1`. Establish `hsum` using `Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)`. Establish `hl : lam.detShift = lam.w (Fin.last n)`. Unfold `DomWeight.detShift`.

Rewrite using `[dif_pos (by omega)]`. Use `congr 1`. Unfold `degZ wsum`. Rewrite using `[hl, Fin.sum_univ_castSucc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degree_sub_det_shift_nonneg {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu) : 0 ≤ degZ lam mu - lam.detShift := by
  subst h
  have hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i) := fun i => (hmu i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dif_pos (by omega)]
    congr 1
  unfold degZ wsum
  rw [hl, Fin.sum_univ_castSucc]
  linarith

/- English proof (translation)
Establish `h1` using `degree_sub_det_shift_nonneg h lam mu hmu`. Establish `h2` using `degree_sub_det_shift_nonneg h lam sg hsg`. Unfold `dLast at hd`. Establish `h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift`. Rewrite using `[← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]`.

Unfold `degZ at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_sum_eq_of_last_gap {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith

/- English proof (translation)
Introduce `n N h lam sg hsg io0 hio hne f hf hfw`. Set `T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)` to `(nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg`. Establish `key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg))`. Rewrite using `[(h4 n N h lam).2]`. Use `iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `s hs`. Rewrite using `[Submodule.mem_comap, Submodule.mem_comap]`. Establish `hφ' : IsEqv h mu lam φ` using `hφ`. Establish `hhom` using `hL n N h lam mu hmu φ hφ' s hs`.

Distinguish the cases in `hd : dLast lam mu = dLast lam sg`. Rewrite `hhom` using `[hd]`. Rewrite using `[hhom.weightedHomogeneousComponent_same]`. Establish `hw : wsum mu = wsum sg` using `weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd`. Distinguish the cases in `hmw : mu.w = sg.w`.

Establish `hms : mu = sg` using `dominant_weight_ext mu sg hmw`. Substitute `hms` using the available equality. Establish `hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)), (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧ ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s)`. Introduce `ψ hψ`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ`.

Break down `hψ with rfl | rfl` into its components or cases. Conclude with `hφ'`. Conclude with `hio`. Take `⟨_, c, hc⟩` from `(h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩`. Use `Submodule.mem_sup_left ?_` and prove the remaining obligations.

Rewrite using `[hc s hs, ← map_smul]`. Conclude with `Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)`. Use `Submodule.mem_sup_right ?_` and prove the remaining obligations. Unfold `OtherPart`. Conclude with `Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ' (Submodule.mem_map_of_mem hs))))))`.

Rewrite using `[hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]`. Conclude with `zero_mem _`. Establish `hfT` using `key hf`. Rewrite `hfT` using `[Submodule.mem_comap, hfw.weightedHomogeneousComponent_same]`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hfT`.

Take `⟨u, hu, rfl⟩` from `Submodule.mem_map.1 hy`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz, add_sub_cancel_left]`. Conclude with `hz`.
-/
theorem decomp_of (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end PI.WGL
