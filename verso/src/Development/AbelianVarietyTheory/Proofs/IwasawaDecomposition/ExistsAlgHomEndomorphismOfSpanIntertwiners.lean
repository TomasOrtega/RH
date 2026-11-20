import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

/- English proof (translation)
Introduce `H W V _ _ _ _ _ _ σ ρ hirr hspan`. Establish `hsurj : Function.Surjective σ.asAlgebraHom`. Establish `hB` using `GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr`. Establish `hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩`. Introduce `A`. Establish `: A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range` using `hle (hB ▸ Submodule.mem_top)`. Conclude with `this`.

Establish `hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W), ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w)`. Introduce `f a w`. Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add]`.

Consider the case `single g c`. Simplify using `only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]`. Use `congr 1`. Conclude with `(Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm`. Establish `hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom`.

Introduce `a ha`. Rewrite `ha`, the goal using `[RingHom.mem_ker]`. Establish `hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤ LinearMap.ker (ρ.asAlgebraHom a)`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`.

Rewrite using `[LinearMap.mem_ker, hint, ha]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[hspan, top_le_iff]`. Conclude with `LinearMap.ker_eq_top.1 hle`. Set `Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V` to `(Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom`.

Establish `hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a`. Introduce `a`. Establish `: (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) = Ideal.Quotient.mk _ a`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨Φ, fun h => ?_, fun T hT A => ?_⟩` and prove the remaining obligations. Use `hΦ (MonoidAlgebra.single h 1)` as an intermediate fact.

Simplify `this` using `[Representation.asAlgebraHom_single]`. Take `⟨a, rfl⟩` from `hsurj A`. Rewrite using `[hΦ]`. Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `hx.add_right hy`. Consider the case `single g c`. Rewrite using `[Representation.asAlgebraHom_single]`. Conclude with `(hT g).smul_right c`.
-/
theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
