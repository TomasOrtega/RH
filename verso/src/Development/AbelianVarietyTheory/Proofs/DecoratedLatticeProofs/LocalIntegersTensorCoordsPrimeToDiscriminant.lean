import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm.Coords

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isIntegral_of_trace_norm (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) : IsIntegral ℤ w := by
  have hE : IsIntegral (𝓞 E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) (𝓞 E) t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) (𝓞 E) n), by monicity!, ?_⟩
    have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E t := rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) n) = algebraMap F E n := rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2, ← ht, ← hn]
    ring
  exact isIntegral_trans (R := ℤ) w hE

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_coords (h : IsCMExt F E σ) (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) (x : 𝓞 E) :
    ∃ a b : 𝓞 F, (x : E) * algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) =
      algebraMap F E a + algebraMap F E b * w := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  let W : 𝓞 E := ⟨w, isIntegral_of_trace_norm w t n ht hn⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hW : ((W : 𝓞 E) : E) = w := rfl
  obtain ⟨a, ha⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((s x * W - x * s W) * (W - s W)) (by
      change σ ((σ (x : E) * w - (x : E) * σ w) * (w - σ w)) = (σ (x : E) * w - (x : E) * σ w) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((x - s x) * (W - s W)) (by
      change σ (((x : E) - σ x) * (w - σ w)) = ((x : E) - σ x) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  have ha' : algebraMap F E a = (σ x * w - x * σ w) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) ha
  have hb' : algebraMap F E b = (x - σ x) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) hb
  refine ⟨a, b, ?_⟩
  have hd : algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) = (algebraMap F E t) ^ 2 - 4 * algebraMap F E n := by
    push_cast
    simp [map_sub, map_pow, map_mul, map_ofNat]
  rw [hd, ha', hb', ← ht, ← hn]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tmul_move {K : Type} [Field K] [Algebra F K] (m : K) (r : F) (e : E) :
    (algebraMap F K r * m) ⊗ₜ[F] e = m ⊗ₜ[F] (algebraMap F E r * e) := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coords_add {K : Type} [Field K] [Algebra F K] (a b a' b' : K) (w : E) :
    (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) + (a' ⊗ₜ[F] (1 : E) + b' ⊗ₜ[F] w) = (a + a') ⊗ₜ[F] (1 : E) + (b + b') ⊗ₜ[F] w := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coords_neg {K : Type} [Field K] [Algebra F K] (a b : K) (w : E) :
    -(a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) = (-a) ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] w := by
  rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]

end Field

end GlobalTheory.FixedUnitNorm.Coords

namespace GlobalTheory.FixedUnitNorm.Coords

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem mem_intV_coords : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n →
    t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F,
      ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  intro D v w t n ht hn hv z hz
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hcoe : ∀ r : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r :
      v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) :=
    fun r => rfl
  have hmem : ∀ r : 𝓞 D.host.F, algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈
      v.adicCompletionIntegers D.host.F := fun r => hcoe r ▸ (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r).2
  obtain ⟨u, hu⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (t ^ 2 - 4 * n)).2 hv).exists_left_inv
  set U : Fv D.host.F v := ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) with hU
  have hu' : U * algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 1 := by
    have := congrArg (fun y : v.adicCompletionIntegers D.host.F => (y : Fv D.host.F v)) hu
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
    exact this
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, rfl⟩ := hy
    obtain ⟨a, b, hab⟩ := exists_coords hcm w t n ht hn x
    refine ⟨c * U * algebraMap D.host.F (Fv D.host.F v) (a : D.host.F), mul_mem (mul_mem hc u.2) (hmem a),
      c * U * algebraMap D.host.F (Fv D.host.F v) (b : D.host.F), mul_mem (mul_mem hc u.2) (hmem b), ?_⟩
    have hc' : c = algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U) := by
      rw [mul_comm, mul_assoc, hu', mul_one]
    calc c ⊗ₜ[D.host.F] (x : D.host.E)
        = (algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U)) ⊗ₜ[D.host.F]
            (x : D.host.E) := by rw [← hc']
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * x) :=
          tmul_move _ _ _
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (a : D.host.F) * 1 +
            algebraMap D.host.F D.host.E (b : D.host.F) * w) := by rw [mul_comm (algebraMap D.host.F D.host.E _) (x : D.host.E), hab, mul_one]
      _ = (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F) * (c * U)) ⊗ₜ[D.host.F] (1 : D.host.E) +
            (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F) * (c * U)) ⊗ₜ[D.host.F] w := by
          rw [TensorProduct.tmul_add, tmul_move, tmul_move]
      _ = _ := by rw [mul_comm (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F)),
            mul_comm (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F))]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    exact coords_add a b a' b' w
  | neg y _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨-a, neg_mem ha, -b, neg_mem hb, ?_⟩
    exact coords_neg a b w

end GlobalTheory.FixedUnitNorm.Coords
