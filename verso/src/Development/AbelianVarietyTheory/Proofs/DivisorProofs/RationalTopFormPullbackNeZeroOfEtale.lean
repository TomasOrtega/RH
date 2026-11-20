import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

/- English proof (translation)
Use `letI := e.hom.toAlgebra`. Set `E : R ≃ₐ[R] S` to `{ (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }`. Use `show Algebra.FormallyEtale R S`. Conclude with `Algebra.FormallyEtale.of_equiv E`.
-/
theorem formallyEtale_of_isIso {R S : CommRingCat.{0}} (e : R ⟶ S) [IsIso e] :
    e.hom.FormallyEtale := by
  letI := e.hom.toAlgebra
  let E : R ≃ₐ[R] S := { (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  show Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv E

/- English proof (translation)
The claim follows from `((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)`.
-/
theorem genericPoint_mem_of_nonempty {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

/- English proof (translation)
Use `(genericPoint_spec X).image f.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, f.denseRange.closure_range]`. Conclude with `this.eq (genericPoint_spec Y)`.
-/
theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

/- English proof (translation)
Establish `hξ` using `genericPoint_mem_of_nonempty U hU`. Set `u : (U : Scheme.{0})` to `⟨genericPoint M, hξ⟩`. Establish `h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale`. Establish `hu` using `FormallyUnramified.stalkMap (U.ι ≫ f) u`. Establish `hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth` using `Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))`.

Use `algebraize [((U.ι ≫ f).stalkMap u).hom]`. Conclude with `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩`. Rewrite `h1` using `[Scheme.Hom.stalkMap_comp]`. Establish `h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale`. Establish `e : f.stalkMap (genericPoint M) = (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u)` using `by simp; rfl`.

Rewrite using `[e]`. Conclude with `RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)`. Establish `hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W → IsIso (W.presheaf.stalkSpecializes h)`. Introduce and unpack `x h rfl`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`.

Use `infer_instance`. Establish `key : ∀ h : f (genericPoint M) ⤳ genericPoint W, (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale`. Introduce `h`. Use `haveI := hiso h (map_genericPoint f)`. Conclude with `RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2`.

Conclude with `key _`.
-/
theorem formallyEtale_functionFieldMap {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens) (hf : Etale (U.ι ≫ f))
    (hU : (U : Set M).Nonempty) : (functionFieldMap f).FormallyEtale := by
  have hξ := genericPoint_mem_of_nonempty U hU
  let u : (U : Scheme.{0}) := ⟨genericPoint M, hξ⟩
  have h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale := by
    have hu := FormallyUnramified.stalkMap (U.ι ≫ f) u
    have hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))
    algebraize [((U.ι ≫ f).stalkMap u).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    have e : f.stalkMap (genericPoint M) =
        (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u) := by simp; rfl
    rw [e]
    exact RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)
  have hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      IsIso (W.presheaf.stalkSpecializes h) := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have key : ∀ h : f (genericPoint M) ⤳ genericPoint W,
      (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    intro h
    haveI := hiso h (map_genericPoint f)
    exact RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2
  exact key _

/- English proof (translation)
Establish `e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘ (TensorProduct.lid A M).symm`. Use function extensionality and compare the values at `m`. Simplify using `[hφ.equiv_tmul]`. Rewrite using `[e]`. Use `hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)` and prove the remaining obligations.
-/
theorem injective_of_isBaseChange_field {A B M N : Type*} [Field A] [CommRing B] [Nontrivial B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) : Function.Injective φ := by
  have e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘
      (TensorProduct.lid A M).symm := by
    funext m
    simp [hφ.equiv_tmul]
  rw [e]
  refine hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)

/- English proof (translation)
Introduce `M W _ _ _ _ p f _ n _ _ U hf hU η hη h0`. Establish `hE` using `formallyEtale_functionFieldMap f U hf hU`. Use `letI := (Cartier.constFn p).toAlgebra`. Use `letI := (Cartier.constFn (f ≫ p)).toAlgebra`. Use `letI := (functionFieldMap f).toAlgebra`.

Use `haveI : IsScalarTower ℂ W.functionField M.functionField := IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm`. Use `haveI : Algebra.FormallyEtale W.functionField M.functionField := hE`. Establish `hb` using `isBaseChange_exteriorPower (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n`. Conclude with `hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))`.
-/
theorem ratPull_ne_zero : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M]
    [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ)
    [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 →
      GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  intro M W _ _ _ _ p f _ n _ _ U hf hU η hη h0
  have hE := formallyEtale_functionFieldMap f U hf hU
  letI := (Cartier.constFn p).toAlgebra
  letI := (Cartier.constFn (f ≫ p)).toAlgebra
  letI := (functionFieldMap f).toAlgebra
  haveI : IsScalarTower ℂ W.functionField M.functionField :=
    IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm
  haveI : Algebra.FormallyEtale W.functionField M.functionField := hE
  have hb := isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n
  exact hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))

end GlobalTheory.EtaleKlt
