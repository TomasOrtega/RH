import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
open IsLocalRing Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `T E _ _ _ _ _ Q hQp hQ`. Use `set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef`. Use `set f := algebraMap T[X] E with hfdef`. Take `⟨y, hy, hQy⟩` from `Ideal.exists_le_maximal Q hQp.ne_top`. Establish `hPy : P ≤ y.comap f` using `hQ ▸ Ideal.comap_mono hQy`.

Use `letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _`. Establish `eP` using `Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)`. Use `haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩`. Establish `hPnf : ¬ P.IsMaximal`. Introduce `hm`.

Establish `hf : IsField (T[X] ⧸ P)` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm`. Conclude with `Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)`. Set `φ : T[X] ⧸ P →+* E ⧸ y` to `Ideal.quotientMap y f hPy`. Establish `hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f` using `Ideal.quotientMap_comp_mk hPy`. Establish `hft : φ.FiniteType`.

Apply `RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)` to reduce the goal to its premises. Rewrite using `[hcomp]`. Conclude with `RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) (RingHom.finiteType_algebraMap.mpr inferInstance)`. Use `letI : Field (E ⧸ y) := Ideal.Quotient.field y`. Use `letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra`.

Use `haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft`. Use `haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _`. Establish `hker : (RingHom.ker φ).IsMaximal`. Use `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))` as an intermediate fact. Rewrite `this` using `[← RingHom.ker_eq_comap_bot]`. Then use the resulting hypothesis.

Establish `hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P)`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hymax : (y.comap f).IsMaximal`. Rewrite using `[hyc]`.

Conclude with `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Use `⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩` and prove the remaining obligations. Establish `hle : maximalIdeal T ≤ (y.comap f).comap C`. Introduce `a ha`. Conclude with `hPy (Ideal.mem_map_of_mem _ ha)`.

Establish `hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤` using `(Ideal.comap_isPrime C (y.comap f)).ne_top`. Conclude with `((maximalIdeal.isMaximal T).eq_of_le hne hle).symm`.
-/
theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q hQp hQ
  set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef
  set f := algebraMap T[X] E with hfdef
  obtain ⟨y, hy, hQy⟩ := Ideal.exists_le_maximal Q hQp.ne_top
  have hPy : P ≤ y.comap f := hQ ▸ Ideal.comap_mono hQy

  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  have eP := Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩
  have hPnf : ¬ P.IsMaximal := by
    intro hm
    have hf : IsField (T[X] ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm
    exact Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)

  let φ : T[X] ⧸ P →+* E ⧸ y := Ideal.quotientMap y f hPy
  have hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f := Ideal.quotientMap_comp_mk hPy
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)
    rw [hcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Field (E ⧸ y) := Ideal.Quotient.field y
  letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra
  haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft
  haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _
  have hker : (RingHom.ker φ).IsMaximal := by
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))
    rwa [← RingHom.ker_eq_comap_bot] at this
  have hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hymax : (y.comap f).IsMaximal := by
    rw [hyc]; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩
  have hle : maximalIdeal T ≤ (y.comap f).comap C := by
    intro a ha
    exact hPy (Ideal.mem_map_of_mem _ ha)
  have hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤ := (Ideal.comap_isPrime C (y.comap f)).ne_top
  exact ((maximalIdeal.isMaximal T).eq_of_le hne hle).symm

end GlobalTheory
