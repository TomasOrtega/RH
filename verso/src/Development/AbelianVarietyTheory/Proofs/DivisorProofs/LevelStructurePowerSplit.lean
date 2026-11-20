import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.LevelPow

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `h0 : X.rm.act 0 = 1`. Establish `h` using `X.rm.add 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `(mul_eq_left.1 h.symm)`. Rewrite using `[Nat.cast_zero, zero_mul, h0, pow_zero, MonObj.comp_one]`. Consider the case `succ k ih`. Rewrite using `[Nat.cast_succ, add_mul, _root_.one_mul, X.rm.add, MonObj.comp_mul, ih, pow_succ]`.
-/
theorem comp_act_natCast_mul (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    x ≫ X.rm.act ((k : 𝓞 F) * a) = (x ≫ X.rm.act a) ^ k := by
  induction k with
  | zero =>
    have h0 : X.rm.act 0 = 1 := by
      have h := X.rm.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.1 h.symm)
    rw [Nat.cast_zero, zero_mul, h0, pow_zero, MonObj.comp_one]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, _root_.one_mul, X.rm.add, MonObj.comp_mul, ih, pow_succ]

/- English proof (translation)
Use `haveI := X.rm.hom a`. Rewrite using `[MonObj.pow_comp, comp_act_natCast_mul]`.
-/
theorem pow_comp_act (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    (x ^ k) ≫ X.rm.act a = x ≫ X.rm.act ((k : 𝓞 F) * a) := by
  haveI := X.rm.hom a
  rw [MonObj.pow_comp, comp_act_natCast_mul]

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 hn`.
-/
theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hn

/- English proof (translation)
Rewrite `h` using `[Nat.cast_mul, mul_comm]`. Conclude with `(mul_dvd_mul_iff_left (natCast_ne_zero hM')).1 h`.
-/
theorem dvd_of_mul_dvd_mul {M M' : ℕ} (hM' : M' ≠ 0) {a : 𝓞 F}
    (h : ((M * M' : ℕ) : 𝓞 F) ∣ (M' : 𝓞 F) * a) : (M : 𝓞 F) ∣ a := by
  rw [Nat.cast_mul, mul_comm] at h
  exact (mul_dvd_mul_iff_left (natCast_ne_zero hM')).1 h

/- English proof (translation)
Substitute `hL` using the available equality. Use `⟨{ pt := fun i ↦ ξ.pt i ^ M', tors := ?_, inj := ?_, surj := ?_ }, fun _ ↦ rfl⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[← pow_mul, mul_comm M' M, ξ.tors i]`. Introduce `Ω _ _ t a b h`.

Simplify using `only [pow_comp_act] at h`. Take `⟨ha, hb⟩` from `ξ.inj Ω t _ _ h`. Conclude with `⟨dvd_of_mul_dvd_mul hM' ha, dvd_of_mul_dvd_mul hM' hb⟩`. Introduce `Ω _ _ t y hy`. Establish `hy' : y ^ (M * M') = 1` using `by rw [pow_mul, hy, one_pow]`.

Take `⟨a, b, hab⟩` from `ξ.surj Ω t y hy'`. Establish `hN : (toUnit (Over.mk t) ≫ ξ.pt 0 ≫ X.rm.act ((M : 𝓞 F) * a)) * (toUnit (Over.mk t) ≫ ξ.pt 1 ≫ X.rm.act ((M : 𝓞 F) * b)) = 1`. Rewrite using `[← hy, hab, mul_pow]`. Simplify using `only [← Category.assoc, comp_act_natCast_mul, MonObj.comp_pow]`. Take `⟨ha, hb⟩` from `ξ.inj Ω t _ _ hN`.

Rewrite `ha`, `hb` using `[mul_comm M M']`. Take `⟨a', rfl⟩` from `dvd_of_mul_dvd_mul hM ha`. Take `⟨b', rfl⟩` from `dvd_of_mul_dvd_mul hM hb`. Use `⟨a', b', ?_⟩` and prove the remaining obligations. Rewrite using `[hab, pow_comp_act, pow_comp_act]`.
-/
theorem exists_level_pow {X : Obj F 𝔠 S} {L M M' : ℕ} (hL : L = M * M') (hM : M ≠ 0) (hM' : M' ≠ 0)
    (ξ : X.Level L) : ∃ β : X.Level M, ∀ i, β.pt i = ξ.pt i ^ M' := by
  subst hL
  refine ⟨{ pt := fun i ↦ ξ.pt i ^ M', tors := ?_, inj := ?_, surj := ?_ }, fun _ ↦ rfl⟩
  · intro i
    rw [← pow_mul, mul_comm M' M, ξ.tors i]
  · intro Ω _ _ t a b h
    simp only [pow_comp_act] at h
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ h
    exact ⟨dvd_of_mul_dvd_mul hM' ha, dvd_of_mul_dvd_mul hM' hb⟩
  · intro Ω _ _ t y hy
    have hy' : y ^ (M * M') = 1 := by rw [pow_mul, hy, one_pow]
    obtain ⟨a, b, hab⟩ := ξ.surj Ω t y hy'
    have hN : (toUnit (Over.mk t) ≫ ξ.pt 0 ≫ X.rm.act ((M : 𝓞 F) * a)) *
        (toUnit (Over.mk t) ≫ ξ.pt 1 ≫ X.rm.act ((M : 𝓞 F) * b)) = 1 := by
      rw [← hy, hab, mul_pow]
      simp only [← Category.assoc, comp_act_natCast_mul, MonObj.comp_pow]
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ hN
    rw [mul_comm M M'] at ha hb
    obtain ⟨a', rfl⟩ := dvd_of_mul_dvd_mul hM ha
    obtain ⟨b', rfl⟩ := dvd_of_mul_dvd_mul hM hb
    refine ⟨a', b', ?_⟩
    rw [hab, pow_comp_act, pow_comp_act]

end GlobalTheory.RealMult.LevelPow

open GlobalTheory.RealMult.LevelPow in

/- English proof (translation)
Introduce `F _ _ 𝔠 S X N N' hN hN' ξ`. Conclude with `⟨exists_level_pow rfl hN hN' ξ, exists_level_pow (mul_comm N N') hN' hN ξ⟩`.
-/
theorem GlobalTheory.RealMult.Obj.Level.exists_pow_levels : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  intro F _ _ 𝔠 S X N N' hN hN' ξ
  exact ⟨exists_level_pow rfl hN hN' ξ, exists_level_pow (mul_comm N N') hN' hN ξ⟩
