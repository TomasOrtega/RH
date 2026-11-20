import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

/- English proof (translation)
Introduce `Y Z π _ _ hK`. Use `letI := fieldK π hK`. Use `letI := algKL π`. Take `⟨U, hU, hζU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := genPt π) trivial`. Establish `hηU : genericPoint Y ∈ π ⁻¹ᵁ U` using `hζU`.

Establish `hV : IsAffineOpen (π ⁻¹ᵁ U)` using `hU.preimage π`. Use `haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩`. Set `f : Γ(Z, U) →+* Z.presheaf.stalk (genPt π)` to `(Z.presheaf.germ U (genPt π) hζU).hom`. Set `φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField` to `(Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hηU).hom`. Set `g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U)` to `(π.app U).hom`.

Establish `hsq : ∀ a, algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) = φ (g a)` using `fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a`. Establish `hfin : g.Finite` using `IsFinite.finite_app π U hU`. Use `letI : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra`. Use `haveI : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := hfin`. Use `letI : Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField := φ.toAlgebra`.

Use `haveI : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y _ hV`. Establish `hint : ∀ b, IsIntegral (Z.presheaf.stalk (genPt π)) (φ b)`. Introduce `b`. Take `⟨p, hp, hpb⟩` from `Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b`. Use `⟨p.map f, hp.map f, ?_⟩` and prove the remaining obligations.

Establish `e : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp f = φ.comp g` using `RingHom.ext hsq`. Establish `hpb' : p.eval₂ g b = 0` using `hpb`. Rewrite using `[Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))`. Use `haveI : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype`.

Establish `hF : FiniteDimensional (Z.presheaf.stalk (genPt π)) (IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))))` using `IntermediateField.finiteDimensional_adjoin (by`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `hint b)`. Establish `hmem : ∀ b, φ b ∈ IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))`. Introduce `b`.

Establish `hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U))` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `e : φ (a • x) = algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) * φ x`. Rewrite using `[hsq, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) hx`. Establish `htop : IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) = ⊤`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations.

Take `⟨b, c, hc, rfl⟩` from `IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x`. Conclude with `div_mem (hmem b) (hmem c)`. Establish `h2 : FiniteDimensional (Z.presheaf.stalk (genPt π)) (⊤ : IntermediateField (Z.presheaf.stalk (genPt π)) Y.functionField)` using `htop ▸ hF`. Conclude with `LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv`.
-/
theorem finiteDimensional_functionField : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  letI := fieldK π hK
  letI := algKL π
  obtain ⟨U, hU, hζU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := genPt π) trivial
  have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
  let f : Γ(Z, U) →+* Z.presheaf.stalk (genPt π) := (Z.presheaf.germ U (genPt π) hζU).hom
  let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField :=
    (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hηU).hom
  let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
  have hsq : ∀ a, algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) = φ (g a) :=
    fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
  have hfin : g.Finite := IsFinite.finite_app π U hU
  letI : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
  haveI : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  letI : Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField := φ.toAlgebra
  haveI : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hV
  have hint : ∀ b, IsIntegral (Z.presheaf.stalk (genPt π)) (φ b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
    refine ⟨p.map f, hp.map f, ?_⟩
    have e : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp f = φ.comp g :=
      RingHom.ext hsq
    have hpb' : p.eval₂ g b = 0 := hpb
    rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
  haveI : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
  have hF : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
  have hmem : ∀ b, φ b ∈ IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := by
    intro b
    have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have e : φ (a • x) = algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) * φ x := by
        rw [hsq, Algebra.smul_def, map_mul]; rfl
      rw [e]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
  have htop : IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
    exact div_mem (hmem b) (hmem c)
  have h2 : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (⊤ : IntermediateField (Z.presheaf.stalk (genPt π)) Y.functionField) := htop ▸ hF
  exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv

end GlobalTheory.NormSheafDescent
