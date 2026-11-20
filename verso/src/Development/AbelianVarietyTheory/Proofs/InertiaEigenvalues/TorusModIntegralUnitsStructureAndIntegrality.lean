import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieRegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonnegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIffForallMaximalSpectrumResidueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitPrescribedResidueReducedFiniteAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralResidueComapInvolutionIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallIntegerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusEqOneIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusInvMulPowValuationNonnegIffStatement

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Introduce `K B hL a ha`. Establish `hred : IsReduced B.A` using `GlobalTheory.T.isReduced_of_lieReg' K B hL`. Use `haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A`. Establish `hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ, IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x)`. Introduce `m`.

Use `haveI := m.isMaximal`. Use `letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal`. Use `haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)`. Conclude with `GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)`. Use `choose v hvs hvi using hv`.

Set `w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ` to `fun m => (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))`. Establish `hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔ 0 ≤ Multiplicative.toAdd (w m x)` using `fun m x => hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)`. Establish `hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x)`. Introduce `x`. Rewrite using `[GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]`.

Conclude with `forall_congr' fun m => hw m x`. Set `τ : B.Aˣ →* B.Aˣ` to `Units.map (B.σ : B.A →* B.A)`. Establish `hτ : ∀ x, τ (τ x) = x` using `fun x => Units.ext (B.σ_σ _)`. Establish `hT : ∀ t, t ∈ B.T ↔ t * τ t = 1`. Introduce `t`.

Rewrite using `[Units.ext_iff]`. Both sides reduce to the same expression. Set `s : MaximalSpectrum B.A → MaximalSpectrum B.A` to `fun m => ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩`. Establish `hs : ∀ m, s (s m) = m`. Introduce `m`.

Use extensionality with `y`. Use `show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal`. Rewrite using `[B.σ_σ]`. Establish `hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x))`. Introduce `m x`.

Rewrite using `[← hw, ← hw]`. Conclude with `GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x`. Establish `hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1`. Introduce `m n`. Take `⟨z, hz⟩` from `hvs m (Multiplicative.ofAdd n)`.

Take `⟨y, hy1, hy2⟩` from `GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero`. Use `⟨y, ?_, fun j hj => ?_⟩` and prove the remaining obligations. Establish `: Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z` using `Units.ext hy1 show v m _ = _`. Rewrite using `[this, hz]`. Establish `: Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1` using `Units.ext (hy2 j hj) show v j _ = _`.

Rewrite using `[this, map_one]`. Establish `hne : algebraMap K.O K.E a ≠ 0`. Introduce `h`. Conclude with `ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))`. Set `α : B.Aˣ` to `Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)`.

Establish `hαv : (α : B.A) = algebraMap K.O B.A a` using `(IsScalarTower.algebraMap_apply K.O K.E B.A a).symm`. Establish `hτα : τ α = α`. Apply `Units.ext` to reduce the goal to its premises. Use `show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)`. Rewrite using `[B.σ_alg, ha.2.2]`.

Establish `hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α)`. Introduce `m`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹)`.

Rewrite using `[map_inv, toAdd_inv]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[← hw]`. Apply `GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m` to reduce the goal to its premises. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use `show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)`. Rewrite using `[Ideal.Quotient.mk_algebraMap]`. Take `⟨r, e, he1, he2, he3⟩` from `GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs`. Use `⟨r, (valsAt w e).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat, GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3] show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)`.

Rewrite using `[hP, hP]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩`. Introduce and unpack `⟨ha1, ha2⟩ m`.

Use `ha2 m` as an intermediate fact. Rewrite `this` using `[map_inv, toAdd_inv]`. Combine the linear relations using `[ha1 m]`. Conclude with `Int.lt_toNat.mpr (hαpos (e j))`. Rewrite using `[← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]`.

Use `congr 2`. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val, hαv]`.
-/
theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := GlobalTheory.T.isReduced_of_lieReg' K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs
  refine ⟨r, (valsAt w e).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
