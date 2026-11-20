import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QuotTower

open scoped TensorProduct

variable {p : ℕ} {R : Type} [CommRing R]

def mulPN (G : PDivGroup p R) (n : ℕ) (k : ℕ) : G.A n →ₐc[R] G.A (n + k) :=
  Nat.rec (motive := fun k => G.A n →ₐc[R] G.A (n + k)) (BialgHom.id R _)
    (fun k f => (G.mulP (n + k)).comp f) k

def resLE (G : PDivGroup p R) {m : ℕ} : ∀ {m' : ℕ}, m ≤ m' → (G.A m' →ₐc[R] G.A m) :=
  @Nat.leRec m (fun m' _ => G.A m' →ₐc[R] G.A m) (BialgHom.id R _) (fun k _ f => f.comp (G.res k))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]`.
-/
theorem comp_pow {A X Y : Over (Sp R)} [GrpObj A] (f : X ⟶ Y) (g : Y ⟶ A) (k : ℕ) :
    f ≫ g ^ k = (f ≫ g) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]

variable {G H : PDivGroup p R} {A : Over (Sp R)} [GrpObj A]

/- English proof (translation)
Use `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨mulP_flat p R G n, fun P => ?_⟩` and prove the remaining obligations. Use `letI : Algebra (G.A n) (G.A (n + 1)) := ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra`. Use `haveI : IsScalarTower R (G.A n) (G.A (n + 1)) := IsScalarTower.of_algebraMap_eq fun r => ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)).commutes r).symm`. Use `haveI : Module.Finite (G.A n) (G.A (n + 1)) := Module.Finite.of_restrictScalars_finite R _ _`. Take `⟨Q, -, hQ, e⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := G.A (n + 1)) P.asIdeal ⊥ (by`.

Rewrite using `[← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot (algebraMap (G.A n) (G.A (n + 1)))).1 (Test.mulP_injective G n)]`. Conclude with `bot_le)`. Conclude with `⟨⟨Q, hQ⟩, PrimeSpectrum.ext e⟩`.
-/
theorem mulP_faithfullyFlat (G : PDivGroup p R) (n : ℕ) :
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)).FaithfullyFlat := by
  refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨mulP_flat p R G n, fun P => ?_⟩
  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower R (G.A n) (G.A (n + 1)) := IsScalarTower.of_algebraMap_eq fun r =>
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)).commutes r).symm
  haveI : Module.Finite (G.A n) (G.A (n + 1)) := Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨Q, -, hQ, e⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := G.A (n + 1)) P.asIdeal ⊥ (by
    rw [← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot (algebraMap (G.A n) (G.A (n + 1)))).1 (Test.mulP_injective G n)]
    exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext e⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id`. Consider the case `succ k ih => exact RingHom.FaithfullyFlat.stableUnderComposition _ _ ih (mulP_faithfullyFlat G (n + k))`.
-/
theorem mulPN_faithfullyFlat (G : PDivGroup p R) (n k : ℕ) :
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)) : G.A n →+* G.A (n + k)).FaithfullyFlat := by
  induction k with
  | zero => exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  | succ k ih => exact RingHom.FaithfullyFlat.stableUnderComposition _ _ ih (mulP_faithfullyFlat G (n + k))

/- English proof (translation)
Use `letI : Algebra (G.A n) B := (φ : G.A n →+* B).toAlgebra`. Use `letI : Algebra (G.A n) (G.A (n + k)) := ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)) : G.A n →+* G.A (n + k)).toAlgebra`. Use `haveI : IsScalarTower R (G.A n) B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm`. Use `haveI : IsScalarTower R (G.A n) (G.A (n + k)) := IsScalarTower.of_algebraMap_eq fun r => ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)).commutes r).symm`. Use `haveI : Module.FaithfullyFlat (G.A n) (G.A (n + k)) := RingHom.faithfullyFlat_algebraMap_iff.1 (mulPN_faithfullyFlat G n k)`.

Use `⟨B ⊗[G.A n] G.A (n + k), inferInstance, inferInstance, Algebra.TensorProduct.includeLeft, (Algebra.TensorProduct.includeRight : G.A (n + k) →ₐ[G.A n] _).restrictScalars R, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance`. Use `AlgHom.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : B) ⊗ₜ[G.A n] (algebraMap (G.A n) (G.A (n + k)) a) = (algebraMap (G.A n) B a) ⊗ₜ[G.A n] 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.
-/
theorem exists_lift (G : PDivGroup p R) (n k : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (φ : G.A n →ₐ[R] B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (j : B →ₐ[R] B') (φ' : G.A (n + k) →ₐ[R] B'),
      (j : B →+* B').FaithfullyFlat ∧ φ'.comp (mulPN G n k : G.A n →ₐ[R] G.A (n + k)) = j.comp φ := by
  letI : Algebra (G.A n) B := (φ : G.A n →+* B).toAlgebra
  letI : Algebra (G.A n) (G.A (n + k)) :=
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)) : G.A n →+* G.A (n + k)).toAlgebra
  haveI : IsScalarTower R (G.A n) B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : IsScalarTower R (G.A n) (G.A (n + k)) := IsScalarTower.of_algebraMap_eq fun r =>
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)).commutes r).symm
  haveI : Module.FaithfullyFlat (G.A n) (G.A (n + k)) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 (mulPN_faithfullyFlat G n k)
  refine ⟨B ⊗[G.A n] G.A (n + k), inferInstance, inferInstance, Algebra.TensorProduct.includeLeft,
    (Algebra.TensorProduct.includeRight : G.A (n + k) →ₐ[G.A n] _).restrictScalars R, ?_, ?_⟩
  · exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  · refine AlgHom.ext fun a => ?_
    change (1 : B) ⊗ₜ[G.A n] (algebraMap (G.A n) (G.A (n + k)) a) = (algebraMap (G.A n) B a) ⊗ₜ[G.A n] 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

end GlobalTheory.QuotTower
