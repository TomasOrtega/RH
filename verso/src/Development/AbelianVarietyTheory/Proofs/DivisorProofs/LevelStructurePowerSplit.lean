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
Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_comp_act (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    (x ^ k) ≫ X.rm.act a = x ≫ X.rm.act ((k : 𝓞 F) * a) := by
  haveI := X.rm.hom a
  rw [MonObj.pow_comp, comp_act_natCast_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hn

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem dvd_of_mul_dvd_mul {M M' : ℕ} (hM' : M' ≠ 0) {a : 𝓞 F}
    (h : ((M * M' : ℕ) : 𝓞 F) ∣ (M' : 𝓞 F) * a) : (M : 𝓞 F) ∣ a := by
  rw [Nat.cast_mul, mul_comm] at h
  exact (mul_dvd_mul_iff_left (natCast_ne_zero hM')).1 h

/- English proof (translation)
Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem GlobalTheory.RealMult.Obj.Level.exists_pow_levels : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  intro F _ _ 𝔠 S X N N' hN hN' ξ
  exact ⟨exists_level_pow rfl hN hN' ξ, exists_level_pow (mul_comm N N') hN' hN ξ⟩
