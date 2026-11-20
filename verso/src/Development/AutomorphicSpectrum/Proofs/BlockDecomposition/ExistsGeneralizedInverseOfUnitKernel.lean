import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

/- English proof (translation)
Introduce `R P₀ P₁ _ _ _ _ _ _ _ _ _ a₀ e he hker`. Establish `hcomp : a₀ ∘ₗ LinearMap.toSpanSingleton R P₀ e = 0`. Use `ext`. Simplify using `[he]`. Establish `hexact : ∀ (m : Ideal R) [m.IsMaximal], Function.Exact (LinearMap.lTensor m.ResidueField (LinearMap.toSpanSingleton R P₀ e)) (LinearMap.lTensor m.ResidueField a₀)`.

Introduce `m _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨c, rfl⟩` from `hker m.ResidueField y hy`. Use `⟨c ⊗ₜ[R] (1 : R), ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]`. Take `⟨s, t, hst⟩` from `GlobalTheory.exists_homotopy_of_forall_exact_residueField hcomp hexact`. Use `⟨t, LinearMap.ext fun x => ?_⟩` and prove the remaining obligations.

Establish `hx : LinearMap.toSpanSingleton R P₀ e (s x) + t (a₀ x) = x` using `LinearMap.congr_fun hst x`. Establish `htx : t (a₀ x) = x - LinearMap.toSpanSingleton R P₀ e (s x)` using `eq_sub_of_add_eq' hx`. Use `show a₀ (t (a₀ x)) = a₀ x`. Rewrite using `[htx, map_sub, LinearMap.toSpanSingleton_apply, map_smul, he, smul_zero, sub_zero]`.
-/
theorem exists_generalisedInverse_of_fibre_ker_span :
    ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  intro R P₀ P₁ _ _ _ _ _ _ _ _ _ a₀ e he hker
  have hcomp : a₀ ∘ₗ LinearMap.toSpanSingleton R P₀ e = 0 := by
    ext
    simp [he]
  have hexact : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Exact (LinearMap.lTensor m.ResidueField (LinearMap.toSpanSingleton R P₀ e))
        (LinearMap.lTensor m.ResidueField a₀) := by
    intro m _ y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := hker m.ResidueField y hy
      refine ⟨c ⊗ₜ[R] (1 : R), ?_⟩
      rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul,
        TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rintro ⟨z, rfl⟩
      rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨s, t, hst⟩ := GlobalTheory.exists_homotopy_of_forall_exact_residueField hcomp hexact
  refine ⟨t, LinearMap.ext fun x => ?_⟩
  have hx : LinearMap.toSpanSingleton R P₀ e (s x) + t (a₀ x) = x := LinearMap.congr_fun hst x
  have htx : t (a₀ x) = x - LinearMap.toSpanSingleton R P₀ e (s x) := eq_sub_of_add_eq' hx
  show a₀ (t (a₀ x)) = a₀ x
  rw [htx, map_sub, LinearMap.toSpanSingleton_apply, map_smul, he, smul_zero, sub_zero]

end GlobalTheory.CompanionTheory.PerfVB
