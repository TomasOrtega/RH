import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableCpowDiscr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.GlueSign

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Use extensionality with `a`. Use `h2 a` as an intermediate fact. Simplify using `only [MonoidHom.inv_apply]`. Rewrite using `[inv_eq_of_mul_eq_one_left this]`.
-/
theorem inv_eq_self_of_sq {η : Fˣ →* ℂˣ} (h2 : ∀ a, η a * η a = 1) : η⁻¹ = η := by
  ext a
  have := h2 a
  simp only [MonoidHom.inv_apply]
  rw [inv_eq_of_mul_eq_one_left this]

/- English proof (translation)
Rewrite using `[isUnramifiedChar_iff]`. Introduce `u _`. Both sides reduce to the same expression.
-/
theorem isUnramifiedChar_one : IsUnramifiedChar (1 : Fˣ →* ℂˣ) := by
  rw [isUnramifiedChar_iff]; intro u _; rfl

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Rewrite using `[localEpsilon_of_isUnramified isUnramifiedChar_one]`. Simplify using the standard rewrite rules.
-/
theorem localEpsilon_one_half (ψ : AddChar F Circle) : localEpsilon (1 : Fˣ →* ℂˣ) ψ (1 / 2) = 1 := by
  rw [localEpsilon_of_isUnramified isUnramifiedChar_one]
  simp

/- English proof (translation)
Establish `h : localLFactor η (1 / 2) ≠ 0`. Use `localLFactor_ne_zero hc ?_` and prove the remaining obligations. Simplify using `[quasiCharExponent, hn]`. Rewrite using `[gam, inv_eq_self_of_sq h2, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]`. Clear the denominators using the available nonvanishing facts.
-/
theorem gam_half {η : Fˣ →* ℂˣ} (hc : Continuous η) (hn : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1) (h2 : ∀ a, η a * η a = 1)
    (ψ : AddChar F Circle) : gam ψ η (1 / 2) = localEpsilon η ψ (1 / 2) := by
  have h : localLFactor η (1 / 2) ≠ 0 := by
    refine localLFactor_ne_zero hc ?_
    simp [quasiCharExponent, hn]
  rw [gam, inv_eq_self_of_sq h2, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  field_simp

/- English proof (translation)
Rewrite using `[gam_half continuous_const (by simp) (by simp), localEpsilon_one_half]`.
-/
theorem gam_one_half (ψ : AddChar F Circle) : gam ψ (1 : Fˣ →* ℂˣ) (1 / 2) = 1 := by
  rw [gam_half continuous_const (by simp) (by simp), localEpsilon_one_half]

end Local

section Local2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

/- English proof (translation)
Rewrite using `[GL2LocalData.lamE, gam_one_half, gam_one_half, gam_half hc hn h2]`. Simplify using the standard rewrite rules.
-/
theorem lamE_eq {η : Fˣ →* ℂˣ} (hc : Continuous η) (hn : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1) (h2 : ∀ a, η a * η a = 1)
    (ψ : AddChar F Circle) : GL2LocalData.lamE E ψ η = localEpsilon η ψ (1 / 2) := by
  rw [GL2LocalData.lamE, gam_one_half, gam_one_half, gam_half hc hn h2]
  simp

end Local2

section Sym

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

instance isAbelianGalois_quadratic : IsAbelianGalois ℚ K := {}

/- English proof (translation)
Rewrite using `[Quadratic.heckeChar, heckeCharacterOfChar_apply, reciprocityMap_intermediateField, ← charBar_restrictNormalHom (Quadratic.galChar K) (reciprocityMap ℚ K c)]`. Both sides reduce to the same expression.
-/
theorem heckeChar_apply (c : IdeleClassGroup ℚ) :
    ((Quadratic.heckeChar K c : Circle) : ℂ) = Quadratic.galChar K (reciprocityMap ℚ K c) := by
  rw [Quadratic.heckeChar, heckeCharacterOfChar_apply, reciprocityMap_intermediateField,
    ← charBar_restrictNormalHom (Quadratic.galChar K) (reciprocityMap ℚ K c)]
  rfl

/- English proof (translation)
Rewrite using `[GroundTheory.Automorphic.GodementSection.coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply, heckeChar_apply, reciprocityMap_mk, ideleSymbol_finiteEmbedding]`.
-/
theorem localChar_apply (v : Pl) (a : (Qv v)ˣ) :
    ((localChar (Quadratic.heckeChar K) v a : ℂˣ) : ℂ) = Quadratic.galChar K (localSymbol K v a) := by
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply,
    heckeChar_apply, reciprocityMap_mk, ideleSymbol_finiteEmbedding]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(((Quadratic.heckeChar K) (IdeleClassGroup.mk ℚ (IdeleGroup.infiniteEmbedding w a)) : Circle) : ℂ) = _`. Rewrite using `[heckeChar_apply, reciprocityMap_mk, ideleSymbol_infiniteEmbedding]`.
-/
theorem infiniteComponent_apply (w : InfinitePlace ℚ) (a : (w.Completion)ˣ) :
    (((Quadratic.heckeChar K).infiniteComponent w a : Circle) : ℂ) = Quadratic.galChar K (infiniteLocalSymbol K w a) := by
  change (((Quadratic.heckeChar K) (IdeleClassGroup.mk ℚ (IdeleGroup.infiniteEmbedding w a)) : Circle) : ℂ) = _
  rw [heckeChar_apply, reciprocityMap_mk, ideleSymbol_infiniteEmbedding]

end Sym

section Sym2

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

open Classical in
/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[h, Quadratic.galChar_one_apply]`. Both sides reduce to the same expression. Rewrite using `[Quadratic.galChar_apply_of_ne_one K h]`. Simplify using the standard rewrite rules.
-/
theorem galChar_val (σ : Gal(K/ℚ)) : ((Quadratic.galChar K σ : ℂˣ) : ℂ) = if σ = 1 then 1 else -1 := by
  split_ifs with h
  · rw [h, Quadratic.galChar_one_apply]; rfl
  · rw [Quadratic.galChar_apply_of_ne_one K h]; simp

end Sym2

section Inf

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

/- English proof (translation)
Establish `hv : w.IsReal` using `IsTotallyReal.isReal w`. Take `⟨u⟩` from `IdeleNorm.nonempty_infinitePlacesOver K w`. Rewrite using `[infiniteLocalSymbol_apply K w hv u, if_pos (by simp)]`. Use `conjAt_ne_one (InfinitePlace.isRamified_iff.2 ⟨IsTotallyComplex.isComplex _, ?_⟩)` and prove the remaining obligations. Conclude with `IsTotallyReal.isReal _`.
-/
theorem infiniteLocalSymbol_neg_one [IsTotallyComplex K] (w : InfinitePlace ℚ) :
    infiniteLocalSymbol K w (-1) ≠ 1 := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver K w
  rw [infiniteLocalSymbol_apply K w hv u, if_pos (by simp)]
  refine conjAt_ne_one (InfinitePlace.isRamified_iff.2 ⟨IsTotallyComplex.isComplex _, ?_⟩)
  exact IsTotallyReal.isReal _

/- English proof (translation)
Rewrite using `[infiniteComponent_apply, galChar_val, if_neg (infiniteLocalSymbol_neg_one K w)]`.
-/
theorem infiniteComponent_neg_one [IsTotallyComplex K] (w : InfinitePlace ℚ) :
    (((Quadratic.heckeChar K).infiniteComponent w (-1) : Circle) : ℂ) = -1 := by
  rw [infiniteComponent_apply, galChar_val, if_neg (infiniteLocalSymbol_neg_one K w)]

end Inf

section Prod

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

attribute [local instance] galCommGroup

end Prod

section Root

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
/- English proof (translation)
Use extensionality with `c`. Establish `h` using `heckeChar_apply K c`. Rewrite `h` using `[galChar_val]`. Express the relevant statement in the definitionally equal form `(((Quadratic.heckeChar K c)⁻¹ : Circle) : ℂ) = _`. Rewrite using `[Circle.coe_inv, h]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem heckeChar_inv : (Quadratic.heckeChar K)⁻¹ = Quadratic.heckeChar K := by
  ext c
  have h := heckeChar_apply K c
  rw [galChar_val] at h
  change (((Quadratic.heckeChar K c)⁻¹ : Circle) : ℂ) = _
  rw [Circle.coe_inv, h]
  split_ifs <;> simp

end Root

section Root2

open Complex

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] [IsTotallyComplex K]

end Root2

section Main

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

end Main

end GlobalTheory.CompanionTheory.GlueSign
