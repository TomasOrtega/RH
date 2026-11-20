import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af

namespace GlobalTheory.ConjElOverReal

/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, map_inv₀, Complex.inv_eq_conj]`. Apply `Complex.norm_eq_one_of_pow_eq_one (n := m) _ hm` to reduce the goal to its premises. Rewrite using `[← map_pow, hx, map_one]`.
-/
private theorem exists_ne_zero_smul_mem_of_mem_span' (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (c : G E Ω) (hc : IsConjEl c)
    (x : Ω) (m : ℕ) (hm : m ≠ 0) (hx : x ^ m = 1) : c x = x⁻¹ := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  rw [hj, map_inv₀, Complex.inv_eq_conj]
  apply Complex.norm_eq_one_of_pow_eq_one (n := m) _ hm
  rw [← map_pow, hx, map_one]

/- English proof (translation)
Establish `hZ : cycZ E Ω l c = -1`. Unfold `cycZ`. Apply `Units.ext` to reduce the goal to its premises. Use `PadicInt.ext_of_toZModPow.mp fun n => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, cyclotomicCharacter.toZModPow, Units.val_neg, Units.val_one, map_neg, map_one]`.

Use `symm`. Apply `modularCyclotomicCharacter.unique` to reduce the goal to its premises. Introduce `t ht`. Establish `hm : l ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`. Use `haveI : NeZero (l ^ n) := ⟨hm⟩`.

Establish `ht' : (t : Ω) ^ (l ^ n) = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]`. Establish `hd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Use `push_cast`.

Rewrite using `[ZMod.natCast_zmod_val, neg_add_cancel]`. Take `⟨q, hq⟩` from `hd`. Establish `h1 : (t : Ω) ^ (-1 : ZMod (l ^ n)).val * t = 1`. Rewrite using `[← pow_succ, hq, pow_mul, ht', one_pow]`. Use `show c (t : Ω) = _`.

Rewrite using `[exists_ne_zero_smul_mem_of_mem_span' E Ω c hc _ _ hm ht']`. Conclude with `(eq_inv_of_mul_eq_one_left h1).symm`. Unfold `cycBar`. Rewrite using `[MonoidHom.comp_apply, hZ]`. Use `ext`.

Simplify using the standard rewrite rules.
-/
private theorem main_lemma_2 (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosed Ω]
    (l : ℕ) [Fact l.Prime] (c : G E Ω) (hc : IsConjEl c) : cycBar E Ω l c = -1 := by
  have hZ : cycZ E Ω l c = -1 := by
    unfold cycZ
    apply Units.ext
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [MonoidHom.comp_apply, cyclotomicCharacter.toZModPow, Units.val_neg, Units.val_one, map_neg,
      map_one]
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    have hm : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    haveI : NeZero (l ^ n) := ⟨hm⟩
    have ht' : (t : Ω) ^ (l ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    have hd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, neg_add_cancel]
    obtain ⟨q, hq⟩ := hd
    have h1 : (t : Ω) ^ (-1 : ZMod (l ^ n)).val * t = 1 := by
      rw [← pow_succ, hq, pow_mul, ht', one_pow]
    show c (t : Ω) = _
    rw [exists_ne_zero_smul_mem_of_mem_span' E Ω c hc _ _ hm ht']
    exact (eq_inv_of_mul_eq_one_left h1).symm
  unfold cycBar
  rw [MonoidHom.comp_apply, hZ]
  ext
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed K, haveI := IsAlgClosure.isAlgebraic (R := K) (K := Ω); Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩; cycBar (maximalRealSubfield K) Ω l c = -1 := by intro K Ω _ _ _ _ _ haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).in …`.
-/
theorem main : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∃ c : G (maximalRealSubfield K) Ω, IsConjEl c) ∧ ∀ (l : ℕ) [Fact l.Prime] (c : G (maximalRealSubfield K) Ω), IsConjEl c → haveI : IsAlgClosure (maximalRealSubfield K) Ω := ⟨IsAlgClosure.isAlgClosed K, haveI := IsAlgClosure.isAlgebraic (R := K) (K := Ω); Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩; cycBar (maximalRealSubfield K) Ω l c = -1 := by
  intro K Ω _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  refine ⟨?_, fun l _ c hc => main_lemma_2 _ Ω l c hc⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  let cq : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  let σ : Ω ≃ₐ[ℚ] Ω := cq.restrictNormal Ω
  have hσ : ∀ x, j (σ x) = starRingEnd ℂ (j x) := fun x => AlgEquiv.restrictNormal_commutes cq Ω x
  have hfix : ∀ x : maximalRealSubfield K,
      σ (algebraMap (maximalRealSubfield K) Ω x) = algebraMap (maximalRealSubfield K) Ω x := by
    intro x
    apply j.injective
    show j _ = j _
    rw [hσ]
    have hx := (mem_maximalRealSubfield_iff (x : K)).1 x.2 (j.toRingHom.comp (algebraMap K Ω))
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield K) K Ω]
    exact hx
  exact ⟨{ σ.toRingEquiv with commutes' := hfix }, j.toRingHom, fun x => hσ x⟩

end GlobalTheory.ConjElOverReal
