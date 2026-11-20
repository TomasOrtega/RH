import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ExistsNearSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SigLamSmoothOfGenSub

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Unfold `nuJ`. Apply `List.sum_nonneg` to reduce the goal to its premises. Introduce `a ha`. Take `⟨w, -, rfl⟩` from `List.mem_map.1 ha`. Conclude with `norm_nonneg _`.
-/
theorem nuJ_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : 0 ≤ nuJ σ Ws v := by
  unfold nuJ
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

/- English proof (translation)
Simplify using `[nuJ, dSW]`.
-/
theorem nuJ_cons_nil (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : nuJ σ ([] :: Ws) v = ‖v‖ + nuJ σ Ws v := by
  simp [nuJ, dSW]

/- English proof (translation)
The claim follows from `| [], _ => by simp [nuJ] | w :: Ws, h => by have h1 := h w List.mem_cons_self have h2 := nuJ_le_add_of σ a b c Ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) simp only [nuJ, List.map_cons, List.sum_cons] at h2 ⊢ linarith`.
-/
theorem nuJ_le_add_of (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a b c : H) :
    ∀ Ws : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ w ∈ Ws, ‖dSW σ w a‖ ≤ ‖dSW σ w b‖ + ‖dSW σ w c‖) → nuJ σ Ws a ≤ nuJ σ Ws b + nuJ σ Ws c
  | [], _ => by simp [nuJ]
  | w :: Ws, h => by
    have h1 := h w List.mem_cons_self
    have h2 := nuJ_le_add_of σ a b c Ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [nuJ, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.
-/
theorem NE_nonneg' {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

end Gen

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

/- English proof (translation)
Unfold `dS`. Use `set f : ℝ → Hlam ε Ψ v₀ := fun t => sigLam ε Ψ v₀ (NormedSpace.exp ((t : ℂ) • X)) y with hfdef`. Establish `hf : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (y : L2 ε)) = fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)`. Use function extensionality and compare the values at `t`. Rewrite using `[hfdef, sigLam_coe hgap hP hv₀ (exp_smul_mem_UJset hX t)]`.

Rewrite using `[hf]`. Set `Ir : Hlam ε Ψ v₀ →L[ℝ] L2 ε` to `((Hlam ε Ψ v₀).subtypeL).restrictScalars ℝ`. Set `Pr : L2 ε →L[ℝ] Hlam ε Ψ v₀` to `((Hlam ε Ψ v₀).orthogonalProjectionOnto).restrictScalars ℝ`. Distinguish the cases in `hd : DifferentiableAt ℝ f 0`. Conclude with `((Ir.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd.hasDerivAt).deriv).symm`.

Establish `hd' : ¬ DifferentiableAt ℝ (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0`. Introduce `h`. Apply `hd` to reduce the goal to its premises. Establish `h2` using `Pr.differentiableAt.comp (0 : ℝ) h`. Establish `e : (Pr ∘ fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) = f`.

Use function extensionality and compare the values at `t`. Conclude with `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f t)`. Rewrite `h2` using `[e]`. Conclude with `h2`. Establish `h0 : deriv f 0 = 0` using `deriv_zero_of_not_differentiableAt hd`.

Establish `h1 : deriv (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 = 0` using `deriv_zero_of_not_differentiableAt hd'`. Conclude with `(congrArg Subtype.val h0).trans h1.symm`.
-/
theorem dS_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : Hlam ε Ψ v₀) :
    ((dS (sigLam ε Ψ v₀) X y : Hlam ε Ψ v₀) : L2 ε) = dS (rreg ε) X (y : L2 ε) := by
  unfold dS
  set f : ℝ → Hlam ε Ψ v₀ := fun t => sigLam ε Ψ v₀ (NormedSpace.exp ((t : ℂ) • X)) y with hfdef
  have hf : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (y : L2 ε)) = fun t => ((f t : Hlam ε Ψ v₀) : L2 ε) := by
    funext t
    rw [hfdef, sigLam_coe hgap hP hv₀ (exp_smul_mem_UJset hX t)]
  rw [hf]
  let Ir : Hlam ε Ψ v₀ →L[ℝ] L2 ε := ((Hlam ε Ψ v₀).subtypeL).restrictScalars ℝ
  let Pr : L2 ε →L[ℝ] Hlam ε Ψ v₀ := ((Hlam ε Ψ v₀).orthogonalProjectionOnto).restrictScalars ℝ
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((Ir.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd.hasDerivAt).deriv).symm
  · have hd' : ¬ DifferentiableAt ℝ (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 := by
      intro h
      apply hd
      have h2 := Pr.differentiableAt.comp (0 : ℝ) h
      have e : (Pr ∘ fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) = f := by
        funext t
        exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f t)
      rw [e] at h2
      exact h2
    have h0 : deriv f 0 = 0 := deriv_zero_of_not_differentiableAt hd
    have h1 : deriv (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 = 0 := deriv_zero_of_not_differentiableAt hd'
    exact (congrArg Subtype.val h0).trans h1.symm

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | X :: w, hw, y => by simp only [dSW] rw [dS_sigLam_coe hgap hP hv₀ (hw X List.mem_cons_self), dSW_sigLam_coe hgap hP hv₀ w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) y]`.
-/
theorem dSW_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ y : Hlam ε Ψ v₀,
      ((dSW (sigLam ε Ψ v₀) w y : Hlam ε Ψ v₀) : L2 ε) = dSW (rreg ε) w (y : L2 ε)
  | [], _, _ => rfl
  | X :: w, hw, y => by
    simp only [dSW]
    rw [dS_sigLam_coe hgap hP hv₀ (hw X List.mem_cons_self),
      dSW_sigLam_coe hgap hP hv₀ w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) y]

/- English proof (translation)
Unfold `nuJ`. Use `congr 1`. Use `List.map_congr_left fun w hw => ?_` and prove the remaining obligations. Rewrite using `[← dSW_sigLam_coe hgap hP hv₀ w (hWs w hw) y, Submodule.coe_norm]`.
-/
theorem nuJ_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (y : Hlam ε Ψ v₀) :
    nuJ (rreg ε) Ws (y : L2 ε) = nuJ (sigLam ε Ψ v₀) Ws y := by
  unfold nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [← dSW_sigLam_coe hgap hP hv₀ w (hWs w hw) y, Submodule.coe_norm]

end ReciprocityTheory.ChartRestriction.DS.DecInf
