import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquivStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotientStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

/- English proof (translation)
Introduce `K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g hL' hSE`. Take `⟨hf, hfg, hg, hL, hL''⟩` from `hSE`. Establish `hsub` using `GlobalTheory.T.sub_and_quotient_bundles K C V' L' (LinearMap.range f) hL'`. Take `⟨e1, he1⟩ : ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ x, (e x : V') = f x` from `⟨LinearEquiv.ofInjective f hf, fun x => by simp⟩`. Establish `hker : LinearMap.range f = LinearMap.ker g` using `(LinearMap.exact_iff.mp hfg).symm`.

Take `⟨e2, he2⟩ : ∃ e : (V' ⧸ LinearMap.range f) ≃ₗ[K] V'', ∀ y, e (Submodule.Quotient.mk y) = g y` from `⟨(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective g hg), fun y => by simp [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]⟩`. Establish `hc1 : ∀ (i : C.I) (x : LinearMap.range f), x ∈ GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f) i ↔ e1.symm x ∈ L i`. Introduce `i x`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.Crv.sub, AddSubgroup.mem_comap]`. Rewrite using `[hL i, ← he1, LinearEquiv.apply_symm_apply]`.

Conclude with `Iff.rfl`. Establish `hc2 : ∀ (i : C.I) (z : V' ⧸ LinearMap.range f), z ∈ GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f) i ↔ e2 z ∈ L'' i`. Introduce `i z`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.Crv.quot]`. Rewrite using `[AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `h2 : e2 (Submodule.Quotient.mk y) ∈ L'' i`. Rewrite using `[he2]`. Conclude with `(hL'' i (g y)).2 ⟨y, hy, rfl⟩`.

Conclude with `h2`. Introduce `hz`. Take `⟨y, hy, hyz⟩` from `(hL'' i _).1 hz`. Use `⟨y, hy, e2.injective ?_⟩` and prove the remaining obligations. Establish `h3 : e2 (Submodule.Quotient.mk y) = e2 z` using `by rw [he2, hyz]`.

Conclude with `h3`. Take `⟨hLb, hdL⟩` from `GlobalTheory.T.degree_invariant_linear_equiv K C (LinearMap.range f) V (GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f)) L e1.symm hsub.1 hc1`. Take `⟨hL''b, hdL''⟩` from `GlobalTheory.T.degree_invariant_linear_equiv K C (V' ⧸ LinearMap.range f) V'' (GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f)) L'' e2 hsub.2 hc2`. Use `⟨hLb, hL''b, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.degree_additive_sub_quotient K C V' L' (LinearMap.range f) hL']`.

Unfold `GlobalTheory.CompanionTheory.Ar.Crv.subDeg`. Rewrite using `[hdL, hdL'']`.
-/
theorem deg_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g hL' hSE
  obtain ⟨hf, hfg, hg, hL, hL''⟩ := hSE
  have hsub := GlobalTheory.T.sub_and_quotient_bundles K C V' L' (LinearMap.range f) hL'
  obtain ⟨e1, he1⟩ : ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ x, (e x : V') = f x :=
    ⟨LinearEquiv.ofInjective f hf, fun x => by simp⟩
  have hker : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  obtain ⟨e2, he2⟩ : ∃ e : (V' ⧸ LinearMap.range f) ≃ₗ[K] V'',
      ∀ y, e (Submodule.Quotient.mk y) = g y :=
    ⟨(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective g hg),
      fun y => by simp [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]⟩
  have hc1 : ∀ (i : C.I) (x : LinearMap.range f),
      x ∈ GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f) i ↔ e1.symm x ∈ L i := by
    intro i x
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.sub, AddSubgroup.mem_comap]
    rw [hL i, ← he1, LinearEquiv.apply_symm_apply]
    exact Iff.rfl
  have hc2 : ∀ (i : C.I) (z : V' ⧸ LinearMap.range f),
      z ∈ GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f) i ↔ e2 z ∈ L'' i := by
    intro i z
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.quot]
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h2 : e2 (Submodule.Quotient.mk y) ∈ L'' i := by
        rw [he2]
        exact (hL'' i (g y)).2 ⟨y, hy, rfl⟩
      exact h2
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hL'' i _).1 hz
      refine ⟨y, hy, e2.injective ?_⟩
      have h3 : e2 (Submodule.Quotient.mk y) = e2 z := by rw [he2, hyz]
      exact h3
  obtain ⟨hLb, hdL⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (LinearMap.range f) V
    (GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f)) L e1.symm hsub.1 hc1
  obtain ⟨hL''b, hdL''⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (V' ⧸ LinearMap.range f) V''
    (GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f)) L'' e2 hsub.2 hc2
  refine ⟨hLb, hL''b, ?_⟩
  rw [GlobalTheory.T.degree_additive_sub_quotient K C V' L' (LinearMap.range f) hL']
  unfold GlobalTheory.CompanionTheory.Ar.Crv.subDeg
  rw [hdL, hdL'']

end GlobalTheory.CompanionTheory.Ar.Crv
