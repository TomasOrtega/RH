import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add, hu, hv, map_add]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed

open GlobalTheory.CharConjFixed in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.char_conj_fixed_eq_one : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n →
    ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  intro D μ n hμ hn V x hx
  have hfix : cA D (x : AE D) = x := by
    have h := hx
    simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at h
    exact h.symm
  obtain ⟨a, ha⟩ := fixed_unit D x hfix
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  have hμa : μ (idF D a) = η a ^ n := hall η hη a
  have hsq : η a ^ 2 = 1 := by
    rw [← map_pow]
    have : Units.map (↑(Algebra.norm (AF D.host.F)) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
      ext
      exact norm_scalar D (a : AF D.host.F)
    rw [← this]; exact hη.2.2.1 _
  obtain ⟨k, rfl⟩ := hn
  rw [← ha, hμa, ← two_mul, pow_mul, hsq, one_pow]
