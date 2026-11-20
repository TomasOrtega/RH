import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftModPSqPerfectFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCohomologyProjectiveModuleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CrysProj

/- English proof (translation)
Introduce `F _ _ k _ A₀ _ _ hA a`. Break down `CharP.char_is_prime_or_zero k (ringChar k) with hp | hp` into its components or cases. Use `haveI : Fact (ringChar k).Prime := ⟨hp⟩`. Use `GlobalTheory.T.de_rham_cohomology_projective_module F k ?_ A₀ hA a` and prove the remaining obligations. Introduce `B₀ _ _ hB b`.

Use `set K := AlgebraicClosure k`. Use `haveI : CharP K (ringChar k) := charP_of_injective_algebraMap (algebraMap k K).injective _`. Take `⟨Λ, _, π, hπ, hker, hp2, hann⟩` from `GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field (ringChar k) K`. Establish `hI : RingHom.ker π ^ 2 = 0`. Rewrite using `[hker, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.2 rfl]`.

Both sides reduce to the same expression. Take `⟨hfin, hfree, f, hf, hk⟩` from `GlobalTheory.T.crystal_finite_free_reduces_to_deRham F Λ K π hπ hI B₀ hB b`. Use `letI := tensorModule (divided₂ hI) (spMap π) b`. Use `haveI := isScalarTower_tensorModule (divided₂ hI) (spMap π) b`. Use `letI := tensorModule (dp0 K) (𝟙 _) b`.

Conclude with `GlobalTheory.T.projective_of_surjective_ker_le_smul (ringChar k) F Λ K π hπ hker hp2 hann _ hfin hfree _ f hf hk`. Use `haveI : CharP k 0 := hp ▸ ringChar.charP k haveI : CharZero k := CharP.charP_to_charZero k`. Use `letI := tensorModule (dp0 k) (𝟙 _) a`. Conclude with `GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' F k _`.
-/
theorem hdR_projective : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  intro F _ _ k _ A₀ _ _ hA a
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · haveI : Fact (ringChar k).Prime := ⟨hp⟩
    refine GlobalTheory.T.de_rham_cohomology_projective_module F k ?_ A₀ hA a
    intro B₀ _ _ hB b
    set K := AlgebraicClosure k
    haveI : CharP K (ringChar k) := charP_of_injective_algebraMap (algebraMap k K).injective _
    obtain ⟨Λ, _, π, hπ, hker, hp2, hann⟩ := GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field (ringChar k) K
    have hI : RingHom.ker π ^ 2 = 0 := by
      rw [hker, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.2 rfl]; rfl
    obtain ⟨hfin, hfree, f, hf, hk⟩ := GlobalTheory.T.crystal_finite_free_reduces_to_deRham F Λ K π hπ hI B₀ hB b
    letI := tensorModule (divided₂ hI) (spMap π) b
    haveI := isScalarTower_tensorModule (divided₂ hI) (spMap π) b
    letI := tensorModule (dp0 K) (𝟙 _) b
    exact GlobalTheory.T.projective_of_surjective_ker_le_smul (ringChar k) F Λ K π hπ hker hp2 hann _ hfin hfree _ f hf hk
  · haveI : CharP k 0 := hp ▸ ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    letI := tensorModule (dp0 k) (𝟙 _) a
    exact GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' F k _

end GlobalTheory.CrysProj
