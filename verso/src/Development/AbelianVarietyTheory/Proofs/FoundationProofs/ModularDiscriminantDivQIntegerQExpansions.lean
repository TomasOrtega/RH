import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem qParam_one_eq (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
  simp [Function.Periodic.qParam]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem disc_vadd (τ : ℍ) :
    ModularForm.discriminant ((1 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  have h := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
    one_mem_strictPeriods_SL (τ : ℂ)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h
  have e : UpperHalfPlane.ofComplex ((τ : ℂ) + ((1 : ℝ) : ℂ)) = (1 : ℝ) +ᵥ τ := by
    ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    simp [add_comm]
  rw [e] at h
  simpa [CuspForm.coe_discriminant] using h

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem qParam_ne (τ : ℍ) : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 :=
  Function.Periodic.qParam_ne_zero _

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem dd_div_q_and_q_div_dd :
    (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ))
      fun n => (c n : ℂ)) ∧
    ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ)
      fun n => (c n : ℂ) := by
  obtain ⟨U, hU0, hU⟩ := GlobalTheory.exists_hasQExpansion_discriminant
  have hu : GlobalTheory.HasQExpansion 1 (fun τ ↦ ModularForm.discriminant τ / Function.Periodic.qParam 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [qParam_ne τ])
  have hcast : ∀ (V : PowerSeries ℤ) (g : ℍ → ℂ),
      GlobalTheory.HasQExpansion 1 g (PowerSeries.map (Int.castRingHom ℂ) V) →
        HasQ 1 g fun n => ((PowerSeries.coeff n V : ℤ) : ℂ) := by
    intro V g hg
    have := (hasQ_coeff_iff_hasQExpansion 1 g _).mpr (by exact_mod_cast hg)
    simpa [PowerSeries.coeff_map] using this
  refine ⟨⟨fun n => PowerSeries.coeff n U, hU0, ?_⟩, ?_⟩
  · have := hcast U _ hu
    convert this using 2 with τ
    rw [qParam_one_eq]; rfl

  set f : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam 1 τ / ModularForm.discriminant τ with hf
  have hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ := fun τ ↦ by
    simp only [hf, GlobalTheory.qParam_one_vadd, disc_vadd]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
    ((GlobalTheory.HasQExpansion.qParam 1).mdifferentiable one_pos).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty f := by
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).div (hu.tendsto one_pos)
      (by simp [PowerSeries.coeff_map, hU0])
    have : f = fun τ ↦ 1 / (ModularForm.discriminant τ / Function.Periodic.qParam 1 τ) := by
      funext τ; simp only [hf]; field_simp
    rw [this]
    exact ht.isBigO_one ℝ
  have h1 := GlobalTheory.HasQExpansion.of_periodic one_pos
    (GlobalTheory.periodic_comp_ofComplex_of_vadd hper) hhol hbdd
  have h2 := (h1.mul hu).unique one_pos ((GlobalTheory.HasQExpansion.const 1 (1 : ℂ)).congr fun τ ↦ by
    simp only [hf]; field_simp [qParam_ne τ, ModularForm.discriminant_ne_zero τ])
  have hUV : U * U.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit U 1 (by simpa using hU0)
  have h3 : UpperHalfPlane.qExpansion 1 f =
      PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1) := by
    have e := congrArg (· * PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1)) h2
    simp only [mul_assoc, ← map_mul, hUV, map_one, mul_one, one_mul] at e
    exact e
  refine ⟨fun n => PowerSeries.coeff n (U.invOfUnit 1), ?_, ?_⟩
  · simp
  · have := hcast _ _ (h3 ▸ h1)
    convert this using 2 with τ
    simp only [hf, qParam_one_eq]; rfl

end GlobalTheory.FN
