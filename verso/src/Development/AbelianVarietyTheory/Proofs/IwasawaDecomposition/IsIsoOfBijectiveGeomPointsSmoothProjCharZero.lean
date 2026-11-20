import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

namespace GlobalTheory.BijPointsIso

universe u

variable {X Y : Scheme.{u}}

/- English proof (translation)
Rewrite using `[UniversallyInjective.iff_diagonal, surjective_iff]`. Introduce `z`. Set `K` to `AlgebraicClosure ((pullback f f).residueField z)`. Set `φ : Spec (.of K) ⟶ pullback f f` to `Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫ (pullback f f).fromSpecResidueField z`. Establish `hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f` using `h K (by simp only [Category.assoc, pullback.condition])`.

Establish `hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f`. Apply the tactic sequence `apply pullback.hom_ext <;> simp [hφ₁]`. Set `pt : Spec (.of K)` to `IsLocalRing.closedPoint (CommRingCat.of K)`. Use `⟨(φ ≫ pullback.fst f f) pt, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`.
-/
theorem universallyInjective_of_injective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro z
  let K := AlgebraicClosure ((pullback f f).residueField z)
  let φ : Spec (.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫
      (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
    h K (by simp only [Category.assoc, pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hφ₁]
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨(φ ≫ pullback.fst f f) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/- English proof (translation)
Introduce `y`. Set `K` to `AlgebraicClosure (Y.residueField y)`. Take `⟨g, hg⟩` from `h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y)`. Set `pt : Spec (.of K)` to `IsLocalRing.closedPoint (CommRingCat.of K)`. Use `⟨g pt, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply]`. Simplify using `only at hg`. Rewrite using `[hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`.
-/
theorem surjective_of_surjective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Surjective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    Function.Surjective f := by
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨g, hg⟩ := h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
    Y.fromSpecResidueField y)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨g pt, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  simp only at hg
  rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/- English proof (translation)
Use `⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e`. Rewrite `e` using `[Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot, sub_eq_zero]`. Conclude with `e`.
-/
theorem bijective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (hR : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩
  change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e
  rw [Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot,
    sub_eq_zero] at e
  exact e

/- English proof (translation)
Use `set x := genericPoint X`. Establish `h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable` using `((tfae_universallyInjective.{u} f).out 0 2).mp ‹_›`. Establish `hpi` using `h3.2 x`. Establish `hr : Function.Bijective (f.residueFieldMap x)` using `by algebraize [(f.residueFieldMap x).hom]`. Establish `: IsPurelyInseparable (Y.residueField (f x)) (X.residueField x)` using `hpi`.

Conclude with `IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _`. Establish `hX : IsField (X.presheaf.stalk x)` using `Field.toIsField X.functionField`. Establish `hY : IsField (Y.presheaf.stalk (f x))`. Rewrite using `[GlobalTheory.apply_genericPoint_of_isDominant f]`. Conclude with `Field.toIsField Y.functionField`.

Establish `hsq` using `Scheme.residue_residueFieldMap f x`. Establish `hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a)` using `fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm`. Establish `bX` using `bijective_residue_of_isField hX`. Establish `bY` using `bijective_residue_of_isField hY`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`.

Establish `: Function.Bijective (X.residue x ∘ f.stalkMap x)`. Establish `e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x))` using `funext hsq'`. Rewrite using `[e]`. Conclude with `hr.comp bY`. Conclude with `(Function.Bijective.of_comp_iff' bX _).mp this`.
-/
theorem isIso_stalkMap_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [UniversallyInjective f] [IsDominant f]
    (hc : CharZero (Y.residueField (f (genericPoint X)))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  set x := genericPoint X
  have h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective.{u} f).out 0 2).mp ‹_›
  have hpi := h3.2 x
  have hr : Function.Bijective (f.residueFieldMap x) := by
    algebraize [(f.residueFieldMap x).hom]
    have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hpi
    exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _
  have hX : IsField (X.presheaf.stalk x) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f x)) := by
    rw [GlobalTheory.apply_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  have hsq := Scheme.residue_residueFieldMap f x
  have hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm
  have bX := bijective_residue_of_isField hX
  have bY := bijective_residue_of_isField hY
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (X.residue x ∘ f.stalkMap x) := by
    have e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x)) := funext hsq'
    rw [e]; exact hr.comp bY
  exact (Function.Bijective.of_comp_iff' bX _).mp this

end GlobalTheory.BijPointsIso

namespace GlobalTheory.BijPointsIso

/- English proof (translation)
Set `ψ : F →+* Y.X.residueField y` to `(Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))`. Conclude with `charZero_of_injective_ringHom ψ.injective`.
-/
theorem charZero_residueField {F : Type} [Field F] [CharZero F] (Y : Var F) (y : Y.X) :
    CharZero (Y.X.residueField y) := by
  let ψ : F →+* Y.X.residueField y :=
    (Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))
  exact charZero_of_injective_ringHom ψ.injective

/- English proof (translation)
Introduce `F _ _ Y₁ Y₂ h hc hb`. Establish `: UniversallyInjective h` using `universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1`. Establish `: IsProper (h ≫ Y₂.str)` using `hc ▸ inferInstance`. Establish `: IsProper h` using `IsProper.of_comp h Y₂.str`. Establish `hs : Function.Surjective h` using `surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2`.

Establish `: IsDominant h` using `⟨hs.denseRange⟩`. Use `isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)` as an intermediate fact. Establish `hN` using `Y₂.isNormalScheme`. Conclude with `GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk`.
-/
theorem isIso_of_bijective_points : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F)
    (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str →
      (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) →
        IsIso h := by
  intro F _ _ Y₁ Y₂ h hc hb
  have : UniversallyInjective h :=
    universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1
  have : IsProper (h ≫ Y₂.str) := hc ▸ inferInstance
  have : IsProper h := IsProper.of_comp h Y₂.str
  have hs : Function.Surjective h := surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2
  have : IsDominant h := ⟨hs.denseRange⟩
  have := isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)
  have hN := Y₂.isNormalScheme
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk

end GlobalTheory.BijPointsIso
