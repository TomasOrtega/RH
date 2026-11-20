import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S A _ m hA hm`. Take `⟨⟩` from `hA`. Establish `hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => rw [pow_zero, Hom.one_def]`. Use `infer_instance`. Consider the case `succ n ih => rw [pow_succ, Hom.mul_def]`. Use `infer_instance`. Establish `hfin : IsFinite ((𝟙 A) ^ m).left` using `GrpTangent.isFinite_id_pow A hm`.

Establish `het : Etale ((𝟙 A) ^ m).left` using `GrpTangent.etale_id_pow A hm`. Use `⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩` and prove the remaining obligations. Use `set f := ((𝟙 A) ^ m).left with hf`. Establish `hcl : IsClopen (Set.range f)` using `⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩`. Establish `hw : A.hom (f x) = A.hom x`.

Rewrite using `[← Scheme.Hom.comp_apply, hf, Over.w]`. Establish `hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f` using `(A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl ⟨f x, by simp [hw], Set.mem_range_self x⟩`. Conclude with `hsub rfl`.
-/
theorem abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by
  intro S A _ m hA hm
  obtain ⟨⟩ := hA
  have hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance
  have hfin : IsFinite ((𝟙 A) ^ m).left := GrpTangent.isFinite_id_pow A hm
  have het : Etale ((𝟙 A) ^ m).left := GrpTangent.etale_id_pow A hm
  refine ⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩
  set f := ((𝟙 A) ^ m).left with hf

  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩

  have hw : A.hom (f x) = A.hom x := by
    rw [← Scheme.Hom.comp_apply, hf, Over.w]

  have hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f :=
    (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl
      ⟨f x, by simp [hw], Set.mem_range_self x⟩
  exact hsub rfl

end GlobalTheory
