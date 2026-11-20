import Mathlib

set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential

namespace GlobalTheory.BertiniAlg

/- English proof (translation)
Set `P` to `MvPolynomial σ k`. Set `φ : P →ₐ[k] κ` to `MvPolynomial.aeval t`. Establish `hφ : Function.Injective φ` using `ht`. Use `algebraize [φ.toRingHom]`. Establish `: IsScalarTower k P κ` using `IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm`.

Set `K` to `FractionRing P`. Establish `hinj : Function.Injective (algebraMap P κ)` using `hφ`. Set `: Algebra K κ` to `(IsFractionRing.lift (K := K) hinj).toAlgebra`. Establish `: IsScalarTower P K κ` using `IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap (K := K) hinj a).symm`. Establish `: IsScalarTower k K κ` using `IsScalarTower.of_algebraMap_eq fun a => by`.

Rewrite using `[IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ, ← IsScalarTower.algebraMap_apply]`. Establish `: Algebra.EssFiniteType K κ` using `.of_comp k K κ`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap k K).injective`. Establish `: Algebra.FormallySmooth K κ` using `Algebra.FormallySmooth.of_perfectField`. Establish `: Algebra.FormallyEtale P K` using `.of_isLocalization (nonZeroDivisors P)`.

Establish `: Algebra.FormallySmooth P κ` using `.comp P K κ`. Establish `hH : Subsingleton (Algebra.H1Cotangent P κ)` using `Algebra.FormallySmooth.subsingleton_h1Cotangent`. Establish `hinjm : Function.Injective (mapBaseChange k P κ)`. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx`.

Rewrite using `[Subsingleton.elim y 0, map_zero]`. Set `b` to `(mvPolynomialBasis k σ).baseChange κ`. Establish `h` using `b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)`. Establish `hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s` using `MvPolynomial.aeval_X t s`. Establish `e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b`.

Use function extensionality and compare the values at `s`. Simplify using `only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]`. Use `erw [mapBaseChange_tmul, one_smul, map_D, hX]`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem linearIndependent_D_of_algebraicIndependent (k κ : Type) [Field k] [CharZero k] [Field κ]
    [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ)
    (ht : AlgebraicIndependent k t) :
    LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  let P := MvPolynomial σ k
  let φ : P →ₐ[k] κ := MvPolynomial.aeval t
  have hφ : Function.Injective φ := ht
  algebraize [φ.toRingHom]
  have : IsScalarTower k P κ := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let K := FractionRing P
  have hinj : Function.Injective (algebraMap P κ) := hφ
  let : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower P K κ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : IsScalarTower k K κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType K κ := .of_comp k K κ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallySmooth K κ := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale P K := .of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth P κ := .comp P K κ
  have hH : Subsingleton (Algebra.H1Cotangent P κ) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinjm : Function.Injective (mapBaseChange k P κ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  let b := (mvPolynomialBasis k σ).baseChange κ
  have h := b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)
  have hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s := MvPolynomial.aeval_X t s
  have e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b := by
    funext s
    simp only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
    erw [mapBaseChange_tmul, one_smul, map_D, hX]
  rw [e]
  exact h

end GlobalTheory.BertiniAlg
