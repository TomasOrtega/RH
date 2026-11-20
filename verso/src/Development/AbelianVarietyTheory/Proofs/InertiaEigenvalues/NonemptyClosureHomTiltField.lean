import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiltRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisAlt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ProofStatement.main`. Consider the case `exact _root_.GlobalTheory.ProofStatement.main`. Consider the case `(apply _root_.GlobalTheory.ProofStatement.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ProofStatement.main ..)`.
-/
theorem exists_pow_eq_one_of_algClosure_zmod (l : ℕ) [hl : Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  first
  | exact @_root_.GlobalTheory.ProofStatement.main
  | exact _root_.GlobalTheory.ProofStatement.main
  | (apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProofStatement.main ..)

/- English proof (translation)
Use `haveI : NeZero m := ⟨hm.ne'⟩`. Take `⟨x, hx⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m`. Take `⟨e, he, hex⟩` from `exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one`. Use `⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩` and prove the remaining obligations. Establish `h1 : e.untilt ^ d = 1` using `by rw [← map_pow, hd, map_one]`.

Establish `h2 : (x : ℂ_[l]) ^ d = 1`. Rewrite using `[← hex]`. Conclude with `congrArg Subtype.val h1` after adjusting the coercions. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[map_pow, map_one]`.

Conclude with `h2`.
-/
theorem exists_isPrimitiveRoot_tilt (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ e : Per.Fl l, IsPrimitiveRoot e m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  obtain ⟨e, he, hex⟩ := exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one
  refine ⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩
  have h1 : e.untilt ^ d = 1 := by rw [← map_pow, hd, map_one]
  have h2 : (x : ℂ_[l]) ^ d = 1 := by
    rw [← hex]
    exact_mod_cast congrArg Subtype.val h1
  apply (algebraMap (Om l) ℂ_[l]).injective
  rw [map_pow, map_one]
  exact h2

/- English proof (translation)
Introduce `l hl`. Use `haveI : IsDomain (Per.Fl l) := inferInstance`. Use `haveI : CharP (Per.Fl l) l := inferInstance`. Set `Ω` to `AlgebraicClosure (FractionRing (Per.Fl l))`. Set `j : Per.Fl l →+* Ω` to `(algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))`.

Establish `hj : Function.Injective j` using `(algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)`. Use `haveI : CharP Ω l := charP_of_injective_ringHom hj l`. Use `letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l`. Set `f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω` to `IsAlgClosed.lift`. Establish `hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range`.

Introduce `a`. Distinguish the cases in `ha : a = 0`. Rewrite using `[ha, map_zero]`. Conclude with `zero_mem _`. Take `⟨m, hm, hlm, ham⟩` from `exists_pow_eq_one_of_algClosure_zmod l a ha`.

Take `⟨e, he⟩` from `exists_isPrimitiveRoot_tilt l m hm hlm`. Use `haveI : NeZero m := ⟨hm.ne'⟩`. Take `⟨i, -, hi⟩` from `(he.map_of_injective hj).eq_pow_of_pow_eq_one (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])`. Conclude with `⟨e ^ i, by rw [map_pow, hi]⟩`. Set `E : Per.Fl l ≃+* j.range` to `RingEquiv.ofBijective j.rangeRestrict ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩`.

Conclude with `⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩`.
-/
theorem nonempty_algClosure_zmod_to_tilt :
    ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  intro l hl
  haveI : IsDomain (Per.Fl l) := inferInstance
  haveI : CharP (Per.Fl l) l := inferInstance
  let Ω := AlgebraicClosure (FractionRing (Per.Fl l))
  let j : Per.Fl l →+* Ω :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω l := charP_of_injective_ringHom hj l
  letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l
  let f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω := IsAlgClosed.lift
  have hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    obtain ⟨m, hm, hlm, ham⟩ := exists_pow_eq_one_of_algClosure_zmod l a ha
    obtain ⟨e, he⟩ := exists_isPrimitiveRoot_tilt l m hm hlm
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := (he.map_of_injective hj).eq_pow_of_pow_eq_one
      (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])
    exact ⟨e ^ i, by rw [map_pow, hi]⟩
  let E : Per.Fl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  exact ⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩

end GlobalTheory.Per
