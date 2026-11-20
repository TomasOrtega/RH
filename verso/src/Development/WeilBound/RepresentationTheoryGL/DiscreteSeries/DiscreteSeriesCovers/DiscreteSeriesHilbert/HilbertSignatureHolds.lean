import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε lam T Ψ hP hst`. Establish `hσ` using `rreg_isURepOn ε`. Establish `hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x`. Introduce `g hg x`. Establish `hx : rreg ε g x ∈ Hlam ε Ψ T.w` using `hst g hg x x.2`.

Use `show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _`. Conclude with `congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `by show inUJ ε 1`. Simplify using `[inUJ]`. Use `⟨hcoe, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `ContinuousLinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hcoe 1 h1 x, hσ.1.1]`. Both sides reduce to the same expression. Introduce `a ha b hb`. Use `ContinuousLinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.comp_apply, hcoe _ (mul_mem_unitaryJ ha hb) x, hcoe a ha, hcoe b hb, hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]`. Introduce `g hg x`. Establish `h` using `hσ.2.1 g hg (x : L2 ε)`. Rewrite `h` using `[← hcoe g hg x]`. Simplify using `using h`.

Introduce `v`. Conclude with `(Hlam ε Ψ T.w).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : L2 ε))`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (datumV_ne_bot hP (HW.KType.w_ne_zero T))`. Use `nontrivial_of_ne (⟨(x : L2 ε), UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) _ x hx⟩ : Hlam ε Ψ T.w) 0 ?_` and prove the remaining obligations. Introduce `h`.

Apply `hx0` to reduce the goal to its premises. Establish `h2 : (x : L2 ε) = 0` using `congrArg Subtype.val h`. Conclude with `Subtype.ext h2`.
-/
theorem hilbert_signature_holds : StepSig := by
  intro n ε lam T Ψ hP hst
  have hσ := rreg_isURepOn ε
  have hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
    intro g hg x
    have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hst g hg x x.2
    show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  refine ⟨hcoe, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [hcoe 1 h1 x, hσ.1.1]
    rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [ContinuousLinearMap.comp_apply, hcoe _ (mul_mem_unitaryJ ha hb) x,
      hcoe a ha, hcoe b hb, hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]
  · intro g hg x
    have h := hσ.2.1 g hg (x : L2 ε)
    rw [← hcoe g hg x] at h
    simpa using h
  · intro v
    exact (Hlam ε Ψ T.w).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : L2 ε))
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (datumV_ne_bot hP (HW.KType.w_ne_zero T))
    refine nontrivial_of_ne (⟨(x : L2 ε), UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) _ x hx⟩ : Hlam ε Ψ T.w) 0 ?_
    intro h
    apply hx0
    have h2 : (x : L2 ε) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2

end PositivityTheory.RgDs.Hilb
