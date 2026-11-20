import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp mat rat mem_Sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
Introduce `E _ _ _ A n p _ S F c hc`. Establish `hcE : (c : E) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Establish `hcQ : (c : ℚ) ^ 2 ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')`. Set `u : GL (Fin n) E` to `⟨(c : E) • 1, (c : E)⁻¹ • 1, by simp [smul_smul, hcE], by simp [smul_smul, hcE]⟩`. Set `s : ℚˣ` to `Units.mk0 ((c : ℚ) ^ 2) hcQ`.

Establish `hm : (u, s) ∈ Gam0 E n`. Use `⟨mem_Sim.2 ?_, ?_⟩` and prove the remaining obligations. Use `show (((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * ((c : E) • (1 : Matrix (Fin n) (Fin n) E)) = algebraMap ℚ E ((c : ℚ) ^ 2) • 1`. Use extensionality with `i k`. Distinguish the cases in `hik : i = k`.

Simplify using `[hik, Matrix.one_apply, Matrix.mul_apply, pow_two]`. Simplify using `[hik, Ne.symm hik, Matrix.one_apply, Matrix.mul_apply]`. Use `show (0 : ℚ) < (c : ℚ) ^ 2`. Check the signs of the components of the expression. Set `y : Gam0 E n` to `⟨(u, s), hm⟩`.

Establish `hmat : (mat (rat y)).val = ((c : FiniteAdeleRing (𝓞 E) E)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))` using `by show ((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) = _`. Use extensionality with `i k`. Apply the tactic sequence `by_cases hik : i = k <;> simp [hik, Matrix.one_apply]`. Establish `hcomp : ∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Introduce `w`.

Use `show ((mat (rat y)).val).map (pLoc E w) = _`. Rewrite using `[hmat]`. Use extensionality with `i k`. Apply the tactic sequence `by_cases hik : i = k <;> simp [hik, Matrix.one_apply]`. Establish `hcen : ∀ g : GUf E n, rat y * g = g * rat y`.

Introduce `g`. Use `Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))` and prove the remaining obligations. Use `show (mat (rat y)).val * (mat g).val = (mat g).val * (mat (rat y)).val`. Rewrite using `[hmat]`. Simplify using the standard rewrite rules.

Use `⟨y, rfl, rfl, hcomp, hcen, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Take `⟨g, rfl⟩` from `F.surj h`. Rewrite using `[← map_mul, ← map_mul, hcen]`. Introduce `v`.

Use `sub_eq_zero.1 (F.vec_inj _ fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_nsmul, F.vec_act w hw, sub_eq_zero]`. Establish `e : (F.a w * comp w (rat y) * (F.a w)⁻¹).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Rewrite using `[Units.val_mul, Units.val_mul, hcomp w]`. Simplify using the standard rewrite rules.

Rewrite using `[e, Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]`.
-/
theorem UpperTheory.exists_levelSubgroup_central_scalar_of_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (c : ℕ), 0 < c →
      ∃ y : Gam0 E n, y.1.1.val = (c : E) • (1 : Matrix (Fin n) (Fin n) E) ∧ ((y.1.2 : ℚˣ) : ℚ) = (c : ℚ) ^ 2 ∧
        (∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
        (∀ g : GUf E n, rat y * g = g * rat y) ∧
        (∀ h : S.G.GAf, F.j (rat y) * h = h * F.j (rat y)) ∧
        ∀ v, S.L.actG (F.j (rat y)) v = c • v := by
  intro E _ _ _ A n p _ S F c hc
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcQ : (c : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
  let u : GL (Fin n) E := ⟨(c : E) • 1, (c : E)⁻¹ • 1, by simp [smul_smul, hcE], by simp [smul_smul, hcE]⟩
  let s : ℚˣ := Units.mk0 ((c : ℚ) ^ 2) hcQ
  have hm : (u, s) ∈ Gam0 E n := by
    refine ⟨mem_Sim.2 ?_, ?_⟩
    · show (((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * ((c : E) • (1 : Matrix (Fin n) (Fin n) E)) = algebraMap ℚ E ((c : ℚ) ^ 2) • 1
      ext i k
      by_cases hik : i = k
      · simp [hik, Matrix.one_apply, Matrix.mul_apply, pow_two]
      · simp [hik, Ne.symm hik, Matrix.one_apply, Matrix.mul_apply]
    · show (0 : ℚ) < (c : ℚ) ^ 2
      positivity
  let y : Gam0 E n := ⟨(u, s), hm⟩
  have hmat : (mat (rat y)).val = ((c : FiniteAdeleRing (𝓞 E) E)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) := by
    show ((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) = _
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcomp : ∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro w
    show ((mat (rat y)).val).map (pLoc E w) = _
    rw [hmat]
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcen : ∀ g : GUf E n, rat y * g = g * rat y := by
    intro g
    refine Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))
    show (mat (rat y)).val * (mat g).val = (mat g).val * (mat (rat y)).val
    rw [hmat]
    simp
  refine ⟨y, rfl, rfl, hcomp, hcen, ?_, ?_⟩
  · intro h
    obtain ⟨g, rfl⟩ := F.surj h
    rw [← map_mul, ← map_mul, hcen]
  · intro v
    refine sub_eq_zero.1 (F.vec_inj _ fun w hw => ?_)
    rw [map_sub, map_nsmul, F.vec_act w hw, sub_eq_zero]
    have e : (F.a w * comp w (rat y) * (F.a w)⁻¹).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      rw [Units.val_mul, Units.val_mul, hcomp w]
      simp
    rw [e, Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]
