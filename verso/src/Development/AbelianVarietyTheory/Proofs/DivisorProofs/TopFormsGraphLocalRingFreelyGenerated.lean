import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

/- English proof (translation)
Use `letI := c.toAlgebra`. Establish `hτ' : IsTranscendenceBasis ℂ τ` using `hτ`. Establish `hv` using `hτ'.1`. Set `P` to `MvPolynomial (Fin r) ℂ`. Set `A` to `Algebra.adjoin ℂ (Set.range τ)`.

Set `Lf` to `IntermediateField.adjoin ℂ (Set.range τ)`. Use `haveI := hτ'.isAlgebraic_field`. Use `haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Set `f1 : P →+* A` to `hv.aevalEquiv.toAlgHom.toRingHom`. Establish `h1 : f1.FormallyEtale`.

Use `letI : Algebra P A := f1.toAlgebra`. Use `show Algebra.FormallyEtale P A`. Conclude with `.of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)`. Use `open scoped IntermediateField.algebraAdjoinAdjoin in`. Establish `h2 : (algebraMap A Lf).FormallyEtale` using `RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))`.

Establish `h3 : (algebraMap Lf F).FormallyEtale` using `RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)`. Establish `hc` using `RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3`. Use `hc using 1` and compare the differences between its conclusion and the goal. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))`. Establish `hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y` using `fun y => rfl`. Rewrite using `[hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]`. Both sides reduce to the same expression.

Introduce `i`. Simplify using `only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))`. Use `hv.algebraMap_aevalEquiv (MvPolynomial.X i)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.aeval_X]`.

Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

/- English proof (translation)
Use `letI := c.toAlgebra`. Establish `hx' : IsTranscendenceBasis ℂ x` using `hx`. Use `haveI := hx'.isAlgebraic_field`. Use `haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Conclude with `exists_basis_kaehler_of_algebraicIndependent hx'.1`.
-/
theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

/- English proof (translation)
Introduce `K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ`. Set `β` to `(algebraMap ℂ L).codRestrict (loc L σ) hc`. Set `ρ : K →+* loc L σ` to `(toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom`. Establish `hρ : ρ.comp (algebraMap ℂ K) = β`. Use extensionality with `a`.

Express the relevant statement in the definitionally equal form `algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a`. Rewrite using `[← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Take `⟨b, hb⟩` from `exists_basis_omega_of_trBasis (algebraMap ℂ K) hx`. Establish `hg` using `formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ' (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)`. Establish `hl : (toLoc L σ).FormallyEtale` using `RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)`.

Establish `hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale`. Use `RingHom.FormallyEtale.comp hg hl using 1` and compare the differences between its conclusion and the goal. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[ρ]`.

Introduce `i`. Simplify using the standard rewrite rules. Conclude with `GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ`.
-/
theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
