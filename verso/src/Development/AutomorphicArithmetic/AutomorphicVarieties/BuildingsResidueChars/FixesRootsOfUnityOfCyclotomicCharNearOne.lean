import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ p _ b s h ζ hζ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (p ^ i) := fun i => inferInstance`. Break down `Nat.eq_zero_or_pos b with rfl | hb` into its components or cases.

Rewrite `hζ` using `[pow_zero, pow_one]`. Rewrite using `[hζ, map_one]`. Use `set j : ℤ_[p] := ((cycZ F Ω p s : ℤ_[p]ˣ) : ℤ_[p]) with hj`. Establish `hn : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖ = ‖x‖` using `fun x => PadicAlgCl.norm_extends p x`. Establish `e1 : ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1 = algebraMap ℚ_[p] (PadicAlgCl p) (((j - 1 : ℤ_[p])) : ℚ_[p])`.

Rewrite using `[show ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (j : ℚ_[p]) from rfl]`. Simplify using the standard rewrite rules. Establish `e2 : ((p ^ b : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) ((((p : ℤ_[p]) ^ b : ℤ_[p])) : ℚ_[p])`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1, e2, hn, hn]`.

Establish `h' : ‖j - 1‖ ≤ (p : ℝ) ^ (-(b : ℤ))`. Rewrite using `[← PadicInt.norm_p_pow]`. Conclude with `h`. Establish `hmem` using `(PadicInt.norm_le_pow_iff_mem_span_pow (j - 1) b).mp h'`. Rewrite `hmem` using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`.

Establish `hspec` using `cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G F Ω) Ω s) ζ hζ`. Establish `hone : (p ^ b : ℕ) ≠ 1`. Use `Nat.one_lt_pow hb.ne' (Fact.out : p.Prime).one_lt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hval : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val.toZModPow b).val = 1`.

Establish `hj' : (cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val = j` using `rfl`. Rewrite using `[hj', hmem]`. Conclude with `ZMod.val_one'' hone`. Rewrite `hspec` using `[hval, pow_one]`. Conclude with `hspec`.
-/
theorem UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (b : ℕ) (s : G F Ω),
    ‖((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1‖ ≤ ‖((p ^ b : ℕ) : Qbar p)‖ → ∀ ζ : Ω, ζ ^ p ^ b = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ p _ b s h ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (p ^ i) := fun i => inferInstance
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [pow_zero, pow_one] at hζ
    rw [hζ, map_one]
  set j : ℤ_[p] := ((cycZ F Ω p s : ℤ_[p]ˣ) : ℤ_[p]) with hj
  have hn : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖ = ‖x‖ := fun x => PadicAlgCl.norm_extends p x
  have e1 : ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1 = algebraMap ℚ_[p] (PadicAlgCl p) (((j - 1 : ℤ_[p])) : ℚ_[p]) := by
    rw [show ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (j : ℚ_[p]) from rfl]
    simp
  have e2 : ((p ^ b : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) ((((p : ℤ_[p]) ^ b : ℤ_[p])) : ℚ_[p]) := by
    simp
  rw [e1, e2, hn, hn] at h
  have h' : ‖j - 1‖ ≤ (p : ℝ) ^ (-(b : ℤ)) := by
    rw [← PadicInt.norm_p_pow]
    exact h
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (j - 1) b).mp h'
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hspec := cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G F Ω) Ω s) ζ hζ
  have hone : (p ^ b : ℕ) ≠ 1 := by
    have := Nat.one_lt_pow hb.ne' (Fact.out : p.Prime).one_lt
    omega
  have hval : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val.toZModPow b).val = 1 := by
    have hj' : (cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val = j := rfl
    rw [hj', hmem]
    exact ZMod.val_one'' hone
  rw [hval, pow_one] at hspec
  exact hspec
