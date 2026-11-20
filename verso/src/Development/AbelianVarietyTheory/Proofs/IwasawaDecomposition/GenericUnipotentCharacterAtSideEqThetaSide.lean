import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem star_mul_self_of_pow (D : D7) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    star ((ζ : ↥D.LL0) : D.what₂.LL) * ((ζ : ↥D.LL0) : D.what₂.LL) = 1 := by
  apply D.what₂.embLL.injective
  rw [map_mul, map_one, D.starLL_cx]
  have hp : ((ζ : ↥D.LL0) : D.what₂.LL) ^ n = 1 := by
    have e := congrArg (fun u : (↥D.LL0)ˣ => ((u : ↥D.LL0) : D.what₂.LL)) h
    simpa using e
  have hz : (D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)) ^ n = 1 := by
    rw [← map_pow, hp, map_one]
  have hn1 : ‖D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
  simp

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem readT_false_eq (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (x : ↥D.LL0) : readT D T i false x = readT D T i true ⟨star (x : D.what₂.LL), hstar x⟩ := by
  simp only [readT, RingHom.comp_apply, Bool.false_eq_true, if_false, if_true]
  rw [T.restX_coefficientEmbedding_conj i x ⟨star (x : D.what₂.LL), hstar x⟩ rfl]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem readT_false_mul_true (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    readT D T i false (ζ : ↥D.LL0) * readT D T i true (ζ : ↥D.LL0) = 1 := by
  rw [readT_false_eq D T hstar, ← map_mul]
  have e : (⟨star ((ζ : ↥D.LL0) : D.what₂.LL), hstar _⟩ : ↥D.LL0) * (ζ : ↥D.LL0) = 1 :=
    Subtype.ext (star_mul_self_of_pow D ζ n hn h)
  rw [e, map_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mul_pow_g_eq_one (g : ℕ) (m : Multiplicative (ZMod g)) : m ^ g = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem psiUT_eq_thSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  intro D S In T hstar
  refine ⟨fun i b u => ?_, fun _ i k h => ?_⟩
  · simp only [psiUT, MonoidHom.comp_apply, psiUOf_apply, map_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    cases b
    · simp only [thSide, Bool.false_eq_true, if_false, MonoidHom.inv_apply, MonoidHom.comp_apply]
      apply Units.ext
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.coe_map]
      refine eq_inv_of_mul_eq_one_left ?_
      exact readT_false_mul_true D T hstar i _ (D.host.g kv.1) (D.host.g_prime kv.1).ne_zero
        (by rw [← map_pow, mul_pow_g_eq_one, map_one])
    · rfl
  · apply In.θ_ne k
    refine MonoidHom.ext fun x => Units.ext ?_
    apply (readT D T i true).injective
    have e := congrArg (fun u : (FractionRing (T.O i))ˣ => (u : FractionRing (T.O i))) (DFunLike.congr_fun h x)
    simpa using e

end GlobalTheory.HeightCounting.FormsStep
