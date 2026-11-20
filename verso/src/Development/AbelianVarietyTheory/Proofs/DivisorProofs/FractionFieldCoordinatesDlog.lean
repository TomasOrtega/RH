import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtCoordBasis

open KaehlerDifferential

/- English proof (translation)
Use `⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (algebraMap ℤ (ZMod p))`. Introduce `x`. Take `⟨m, rfl⟩` from `ZMod.intCast_surjective x`. Conclude with `⟨m, by simp⟩`.

Establish `hs : Subsingleton Ω[ZMod p⁄ℤ]` using `KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj`. Establish `hex` using `KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(hex x).1 hx`.

Use `clear hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Subsingleton.elim b 0]`. Consider the case `add y z hy hz => rw [map_add, hy, hz, add_zero]`.
-/
theorem kaehler_map_bijective (p : ℕ) (L : Type) [CommRing L] [Algebra (ZMod p) L] :
    Function.Bijective (KaehlerDifferential.map ℤ (ZMod p) L L) := by
  refine ⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    intro x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨m, by simp⟩
  have hs : Subsingleton Ω[ZMod p⁄ℤ] := KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hex := KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Subsingleton.elim b 0]
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

/- English proof (translation)
Introduce `p _ A _ _ _ n t het L _ _ _ ht`. Set `P` to `MvPolynomial (Fin n) (ZMod p)`. Use `letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra`. Use `haveI : IsScalarTower (ZMod p) P A := .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm`. Use `haveI : Algebra.Etale P A := het`.

Use `letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra`. Use `haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)`. Set `bA : Module.Basis (Fin n) A Ω[A⁄ZMod p]` to `((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)`. Establish `hbA : ∀ j, bA j = D (ZMod p) A (t j)`.

Introduce `j`. Simplify using `only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]`. Establish `h : algebraMap P A (MvPolynomial.X j) = t j`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval t (MvPolynomial.X j) = t j`. Conclude with `MvPolynomial.aeval_X t j`.

Rewrite using `[← h, ← map_D (ZMod p) (ZMod p) P A]`. Conclude with `(mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)`. Set `bL : Module.Basis (Fin n) L Ω[L⁄ZMod p]` to `(bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)`. Establish `hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j))`. Introduce `j`.

Simplify using `only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]`. Set `e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p]` to `LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)`. Establish `he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x`. Introduce `x`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Conclude with `(KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm`. Set `b : Module.Basis (Fin n) L Ω[L⁄ℤ]` to `bL.map e.symm`. Establish `hb : ∀ j, b j = D ℤ L (algebraMap A L (t j))`. Introduce `j`. Simplify using `only [b, Module.Basis.map_apply, hbL, he]`.

Establish `hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b`. Use function extensionality and compare the values at `i`. Simplify using `[hb, dK]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`.

Conclude with `b.linearIndependent`. Rewrite using `[hfun]`. Conclude with `b.span_eq`. Introduce `f`. Use `⟨bA.repr (D (ZMod p) A f), ?_⟩` and prove the remaining obligations.

Establish `h1` using `bA.sum_repr (D (ZMod p) A f)`. Rewrite using `[← he, ← map_D (ZMod p) (ZMod p) A L]`. Use `conv_lhs => rw [← h1]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]`.
-/
theorem etale_coords_basis : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  intro p _ A _ _ _ n t het L _ _ _ ht
  classical
  let P := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod p) P A :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm
  haveI : Algebra.Etale P A := het
  letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra
  haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  let bA : Module.Basis (Fin n) A Ω[A⁄ZMod p] :=
    ((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)
  have hbA : ∀ j, bA j = D (ZMod p) A (t j) := by
    intro j
    simp only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have h : algebraMap P A (MvPolynomial.X j) = t j := by
      change MvPolynomial.aeval t (MvPolynomial.X j) = t j
      exact MvPolynomial.aeval_X t j
    rw [← h, ← map_D (ZMod p) (ZMod p) P A]
    exact (mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)
  let bL : Module.Basis (Fin n) L Ω[L⁄ZMod p] :=
    (bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)
  have hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j)) := by
    intro j
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]
  let e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)
  have he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    exact (KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm
  let b : Module.Basis (Fin n) L Ω[L⁄ℤ] := bL.map e.symm
  have hb : ∀ j, b j = D ℤ L (algebraMap A L (t j)) := by
    intro j
    simp only [b, Module.Basis.map_apply, hbL, he]
  have hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b := by
    funext i
    simp [hb, dK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hfun]; exact b.linearIndependent
  · rw [hfun]; exact b.span_eq
  · intro f
    refine ⟨bA.repr (D (ZMod p) A f), ?_⟩
    have h1 := bA.sum_repr (D (ZMod p) A f)
    rw [← he, ← map_D (ZMod p) (ZMod p) A L]
    conv_lhs => rw [← h1]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]

end GlobalTheory.EtCoordBasis
