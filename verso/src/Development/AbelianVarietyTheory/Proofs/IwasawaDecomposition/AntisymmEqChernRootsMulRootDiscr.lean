import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSignStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPermStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRootsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

/- English proof (translation)
Introduce `ι _ m Q`. Take `⟨S, hS⟩ : rootDiscr m ∣ antisymm Q` from `GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij => GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)`. Establish `hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S`. Introduce `w`. Establish `h1` using `GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w`.

Rewrite `h1` using `[hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc]`. Establish `hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0` using `Units.ne_zero _`. Conclude with `mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)`. Take `⟨R, hR⟩` from `GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym`. Conclude with `⟨R, by rw [hS, hR, mul_comm]⟩`.
-/
theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w
    rw [hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
