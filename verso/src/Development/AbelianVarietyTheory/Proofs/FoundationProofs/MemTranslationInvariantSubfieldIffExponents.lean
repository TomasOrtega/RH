import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.KTExp

/- English proof (translation)
Use `haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')`. Conclude with `⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩`.
-/
theorem exists_prim_root_of_isAlgClosed (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n : ℕ) (hn : 0 < n) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hε : Function.Injective ε` using `ε.injective`. Unfold `eOm`. Apply `Function.invFun_eq` to reduce the goal to its premises.

Take `⟨ζ, hζ⟩` from `exists_prim_root_of_isAlgClosed Ω x.den x.den_pos`. Establish `hζ' : IsPrimitiveRoot (ε ζ) x.den` using `hζ.map_of_injective hε`. Use `haveI : NeZero x.den := ⟨x.den_nz⟩`. Establish `hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1`. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`.

Use `⟨x.num, ?_⟩` and prove the remaining obligations. Establish `hx : (x : ℂ) * x.den = x.num` using `by exact_mod_cast Rat.mul_den_eq_num x`. Combine the equalities or inequalities in the displayed calculation. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hpow`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem map_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  obtain ⟨ζ, hζ⟩ := exists_prim_root_of_isAlgClosed Ω x.den x.den_pos
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
Establish `hε : Function.Injective ε` using `ε.injective`. Rewrite using `[← hε.eq_iff, map_one, map_eOm, Complex.exp_eq_one_iff]`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Establish `h3 : ((x : ℚ) : ℂ) = ((n : ℚ) : ℂ)`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `: x = n` using `by exact_mod_cast h3`. Rewrite using `[this]`. Both sides reduce to the same expression. Introduce `h`. Use `⟨x.num, ?_⟩` and prove the remaining obligations.

Establish `: x = (x.num : ℚ)`. Conclude with `((Rat.den_eq_one_iff x).1 h).symm`. Rewrite using `[this]`. Use `push_cast`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eOm_eq_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x = 1 ↔ x.den = 1 := by
  have hε : Function.Injective ε := ε.injective
  rw [← hε.eq_iff, map_one, map_eOm, Complex.exp_eq_one_iff]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    have h3 : ((x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ hne
      push_cast
      rw [hn]; ring
    have : x = n := by exact_mod_cast h3
    rw [this]; rfl
  · intro h
    refine ⟨x.num, ?_⟩
    have : x = (x.num : ℚ) := by
      exact ((Rat.den_eq_one_iff x).1 h).symm
    rw [this]; push_cast; simp; ring

/- English proof (translation)
Establish `h : ((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (L : ℤ); 0, 1]`. Rewrite using `[← zpow_natCast, ModularGroup.coe_T_zpow]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Express the relevant statement in the definitionally equal form `(((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) _ _ = _`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem ent_T_pow (L : ℕ) :
    ent (ofSL (ModularGroup.T ^ L)) 0 0 = 1 ∧ ent (ofSL (ModularGroup.T ^ L)) 0 1 = L ∧
    ent (ofSL (ModularGroup.T ^ L)) 1 0 = 0 ∧ ent (ofSL (ModularGroup.T ^ L)) 1 1 = 1 := by
  have h : ((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (L : ℤ); 0, 1] := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · change (((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) _ _ = _
    rw [h]; simp

end GlobalTheory.Glue.KTExp

namespace GlobalTheory.Glue.KTExp

/- English proof (translation)
Introduce `Ω _ _ _ ε X L _ f`. Take `⟨h00, h01, h10, h11⟩` from `ent_T_pow L`. Establish `key : ∀ r : ℚ, (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = eOm ε (r * L) * (X.exp f).coeff r`. Introduce `r`. Use `X.exp_upper (ofSL (ModularGroup.T ^ L)) h10 f r` as an intermediate fact.

Rewrite `this` using `[h00, h01, h11, mul_one, div_one, div_one]`. Then use the resulting hypothesis. Establish `hmem : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f`. Unfold `KT`. Rewrite using `[RingHom.mem_eqLocusField]`. Both sides reduce to the same expression.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `h r hr`. Establish `k` using `key r`. Rewrite `k` using `[h]`.

Establish `h1 : eOm ε (r * L) = 1`. Establish `: (1 - eOm ε (r * L)) * (X.exp f).coeff r = 0` using `by rw [sub_mul, one_mul, ← k, sub_self]`. Conclude with `(sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)).symm`. Conclude with `(eOm_eq_one_iff ε _).1 h1`. Introduce `h`.

Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = (X.exp f).coeff r`. Rewrite using `[key r]`. Distinguish the cases in `hr : (X.exp f).coeff r = 0`.

Rewrite using `[hr, mul_zero]`. Rewrite using `[(eOm_eq_one_iff ε _).2 (h r hr), one_mul]`.
-/
theorem mem_KT_iff : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  intro Ω _ _ _ ε X L _ f
  obtain ⟨h00, h01, h10, h11⟩ := ent_T_pow L
  have key : ∀ r : ℚ, (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = eOm ε (r * L) * (X.exp f).coeff r := by
    intro r
    have := X.exp_upper (ofSL (ModularGroup.T ^ L)) h10 f r
    rwa [h00, h01, h11, mul_one, div_one, div_one] at this
  have hmem : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := by
    unfold KT
    rw [RingHom.mem_eqLocusField]
    rfl
  rw [hmem]
  constructor
  · intro h r hr
    have k := key r
    rw [h] at k
    have h1 : eOm ε (r * L) = 1 := by
      have : (1 - eOm ε (r * L)) * (X.exp f).coeff r = 0 := by rw [sub_mul, one_mul, ← k, sub_self]
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)).symm
    exact (eOm_eq_one_iff ε _).1 h1
  · intro h
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    ext r
    change (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = (X.exp f).coeff r
    rw [key r]
    by_cases hr : (X.exp f).coeff r = 0
    · rw [hr, mul_zero]
    · rw [(eOm_eq_one_iff ε _).2 (h r hr), one_mul]

end GlobalTheory.Glue.KTExp
