import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ c hc`. Take `⟨j, hj⟩` from `hc`. Use `haveI : CharZero Ω := j.charZero`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩`.

Establish `hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹`. Introduce `x m hm hx`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, map_inv₀]`. Establish `hn : ‖j x‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm`.

Establish `hs : Complex.normSq (j x) = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, hn]`. Evaluate the numerical expressions. Rewrite using `[Complex.inv_def, hs]`. Simplify using the standard rewrite rules.

Use `set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg`. Establish `hcyc : cyclotomicCharacter Ω l g = -1` using `by ext1`. Use `PadicInt.ext_of_toZModPow.mp fun n => ?_` and prove the remaining obligations. Rewrite using `[cyclotomicCharacter.toZModPow]`. Establish `hk : NeZero (l ^ n)` using `⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩`.

Rewrite using `[← modularCyclotomicCharacter.unique Ω _ g (c := -1)]`. Simplify using the standard rewrite rules. Introduce `t ht`. Establish `ht' : (t : Ω) ^ (l ^ n) = 1`. Rewrite `ht` using `[mem_rootsOfUnity]`.

Simplify using `using congrArg Units.val ht`. Establish `hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Use `push_cast`. Simplify using the standard rewrite rules.

Take `⟨m, hm⟩` from `hdvd`. Establish `hne : (t : Ω) ≠ 0` using `t.ne_zero`. Establish `key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, hm, pow_mul, ht', one_pow]`.

Rewrite using `[key]`. Conclude with `hinv _ (l ^ n) (NeZero.ne _) ht'`. Use `show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1`. Establish `: ReciprocityTheory.Gal.cycZ F Ω l c = -1` using `hcyc`. Rewrite using `[this]`.

Use `ext`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.cyclotomic_char_conj_invariant :
    UpperTheory.V.Af.Sol.CycConj := by
  intro F Ω _ _ _ _ _ l _ c hc
  obtain ⟨j, hj⟩ := hc
  haveI : CharZero Ω := j.charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩
  have hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹ := by
    intro x m hm hx
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm
    have hs : Complex.normSq (j x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]; norm_num
    rw [Complex.inv_def, hs]; simp
  set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg
  have hcyc : cyclotomicCharacter Ω l g = -1 := by
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow]
    have hk : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
    rw [← modularCyclotomicCharacter.unique Ω _ g (c := -1)]
    · simp
    · intro t ht
      have ht' : (t : Ω) ^ (l ^ n) = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      have hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
      obtain ⟨m, hm⟩ := hdvd
      have hne : (t : Ω) ≠ 0 := t.ne_zero
      have key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, hm, pow_mul, ht', one_pow]
      rw [key]
      exact hinv _ (l ^ n) (NeZero.ne _) ht'
  show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1
  have : ReciprocityTheory.Gal.cycZ F Ω l c = -1 := hcyc
  rw [this]
  ext; simp
