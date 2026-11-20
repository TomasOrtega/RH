import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameCplx

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [FD.gram, hermC, FD.col, of_apply, Matrix.neg_apply, transpose_apply, mul_apply, map_neg, map_apply, conjTranspose_apply, Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ (-Gᵀ) x = -(xᴴ * G.map τ * x)ᵀ := by
  ext a b
  simp only [FD.gram, hermC, FD.col, of_apply, Matrix.neg_apply, transpose_apply, mul_apply, map_neg, map_apply,
    conjTranspose_apply, Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hermC, FD.col, Matrix.neg_apply, transpose_apply, mul_apply, map_neg, map_apply, vecMul, dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib, Pi.star_apply, RCLike.star_def]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hermC_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (v : Fin r → ℂ) :
    hermC τ (-Gᵀ) (FD.col x a) v = -((star v ᵥ* (G.map τ * x)) a) := by
  simp only [hermC, FD.col, Matrix.neg_apply, transpose_apply, mul_apply, map_neg, map_apply, vecMul, dotProduct,
    Finset.mul_sum, ← Finset.sum_neg_distrib, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section lin
variable {r : ℕ} {G x S s : Matrix (Fin r) (Fin r) ℂ}

/- English proof (translation)
Establish `h : (-(S * (xᴴ * G))) * x = 1`. Rewrite using `[Matrix.neg_mul, Matrix.mul_assoc, hG, Matrix.mul_neg, neg_neg, hS]`. Conclude with `Matrix.isUnit_det_of_left_inverse h`.
-/
theorem isUnit_det (hS : S * S = 1) (hG : xᴴ * G * x = -S) : IsUnit x.det := by
  have h : (-(S * (xᴴ * G))) * x = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hG, Matrix.mul_neg, neg_neg, hS]
  exact Matrix.isUnit_det_of_left_inverse h

/- English proof (translation)
Establish `hx` using `isUnit_det hS hG`. Establish `: s = -(x * S) * x⁻¹` using `by rw [← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]`. Rewrite using `[this, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hx]`.
-/
theorem inv_mul_inv (hS : S * S = 1) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : x⁻¹ * s = -(S * x⁻¹) := by
  have hx := isUnit_det hS hG
  have : s = -(x * S) * x⁻¹ := by rw [← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  rw [this, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hx]

open scoped ComplexOrder in
/- English proof (translation)
Establish `hx` using `isUnit_det hS hG`. Establish `hxH : IsUnit xᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hx.star`. Establish `hs' : s = -(x * S * x⁻¹)` using `by rw [← Matrix.neg_mul, ← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]`. Establish `hG' : G = -((x⁻¹)ᴴ * S * x⁻¹)`. Rewrite using `[← Matrix.neg_mul, ← Matrix.mul_neg, ← hG, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc xᴴ, Matrix.nonsing_inv_mul_cancel_left _ _ hxH, Matrix.mul_nonsing_inv_cancel_right _ _ hx]`.

Establish `c1 : ∀ M : Matrix (Fin r) (Fin r) ℂ, x⁻¹ * (x * M) = M` using `fun M => Matrix.nonsing_inv_mul_cancel_left _ _ hx`. Establish `c2 : ∀ M : Matrix (Fin r) (Fin r) ℂ, S * (S * M) = M` using `fun M => by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]`. Establish `c3 : ∀ M : Matrix (Fin r) (Fin r) ℂ, xᴴ * ((x⁻¹)ᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hx, conjTranspose_one, Matrix.one_mul]`. Establish `hGs : G * s = (x⁻¹)ᴴ * x⁻¹`.

Rewrite using `[hG', hs']`. Simplify using `only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hs']`. Simplify using `only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]`.

Conclude with `Matrix.mul_nonsing_inv _ hx`. Rewrite using `[Matrix.mul_assoc, hGs, hG', hs']`. Simplify using `only [conjTranspose_neg, conjTranspose_mul, hH, Matrix.neg_mul, Matrix.mul_assoc, c3]`. Rewrite using `[hGs]`. Establish `hu : IsUnit x⁻¹` using `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hx)`.

Conclude with `Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hu)`.
-/
theorem cartan (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : IsCartanInv G s := by
  have hx := isUnit_det hS hG
  have hxH : IsUnit xᴴ.det := by rw [Matrix.det_conjTranspose]; exact hx.star
  have hs' : s = -(x * S * x⁻¹) := by rw [← Matrix.neg_mul, ← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have hG' : G = -((x⁻¹)ᴴ * S * x⁻¹) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_neg, ← hG, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc xᴴ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hxH, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have c1 : ∀ M : Matrix (Fin r) (Fin r) ℂ, x⁻¹ * (x * M) = M := fun M => Matrix.nonsing_inv_mul_cancel_left _ _ hx
  have c2 : ∀ M : Matrix (Fin r) (Fin r) ℂ, S * (S * M) = M := fun M => by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have c3 : ∀ M : Matrix (Fin r) (Fin r) ℂ, xᴴ * ((x⁻¹)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hx, conjTranspose_one, Matrix.one_mul]
  have hGs : G * s = (x⁻¹)ᴴ * x⁻¹ := by
    rw [hG', hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
    exact Matrix.mul_nonsing_inv _ hx
  · rw [Matrix.mul_assoc, hGs, hG', hs']
    simp only [conjTranspose_neg, conjTranspose_mul, hH, Matrix.neg_mul, Matrix.mul_assoc, c3]
  · rw [hGs]
    have hu : IsUnit x⁻¹ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hx)
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hu)

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `cartan hS hH hG hs`. Establish `: x = -(s * (x * S))`. Rewrite using `[← Matrix.mul_assoc, hs, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hS, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_neg, Matrix.mul_assoc]`.

Use `_ = _ := by rw [h2, Matrix.mul_assoc]`.
-/
theorem adj_inv (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) :
    sᴴ * (G * x) = -(G * x * S) := by
  obtain ⟨h1, h2, -⟩ := cartan hS hH hG hs
  have : x = -(s * (x * S)) := by
    rw [← Matrix.mul_assoc, hs, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hS, Matrix.mul_one]
  calc sᴴ * (G * x) = -((sᴴ * G * s) * (x * S)) := by
        conv_lhs => rw [this]
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_assoc]
end lin

/- English proof (translation)
Rewrite using `[sgnM, diagonal_mul_diagonal, ← diagonal_one]`. Apply the tactic sequence `congr 1; funext a; unfold FD.sgn; split_ifs <;> simp`.
-/
theorem sgnM_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; unfold FD.sgn; split_ifs <;> simp

/- English proof (translation)
Rewrite using `[sgnM, diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.
-/
theorem sgnM_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, diagonal_conjTranspose]
  congr 1; funext a; simp

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[hermC_eq, hermC_eq, star_smul, star_mulVec, smul_vecMul, vecMul_vecMul, adj_inv (sgnM_sq X) (sgnM_herm X) hG hs, vecMul_neg, ← vecMul_vecMul, sgnM]`. Simplify using `only [Pi.smul_apply, Pi.neg_apply, vecMul_diagonal]`. Simplify using `[FD.sgn, h]`. Rewrite using `[mulVec_smul, mulVec_mulVec, inv_mul_inv (sgnM_sq X) hG hs, neg_mulVec, ← mulVec_mulVec, sgnM]`.

Simplify using `only [Pi.smul_apply, Pi.neg_apply, mulVec_diagonal]`. Simplify using `[FD.sgn, h]`.
-/
theorem per_cplx {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x s : Matrix (Fin r) (Fin r) ℂ) (hG : xᴴ * G.map τ * x = -sgnM X)
    (hs : s * x = -(x * sgnM X)) (v : Fin r → ℂ) (a : Fin r) :
    (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) (I • (s *ᵥ v)) else (x⁻¹ *ᵥ (I • (s *ᵥ v))) a) =
      I * (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) v else (x⁻¹ *ᵥ v) a) := by
  split_ifs with h
  · rw [hermC_eq, hermC_eq, star_smul, star_mulVec, smul_vecMul, vecMul_vecMul,
      adj_inv (sgnM_sq X) (sgnM_herm X) hG hs, vecMul_neg, ← vecMul_vecMul, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, vecMul_diagonal]
    simp [FD.sgn, h]
  · rw [mulVec_smul, mulVec_mulVec, inv_mul_inv (sgnM_sq X) hG hs, neg_mulVec, ← mulVec_mulVec, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, mulVec_diagonal]
    simp [FD.sgn, h]

open scoped ComplexOrder in

/- English proof (translation)
Introduce `D ψ θ V W r g hr X bas idx _ hθ hV _ hM _ x s hx hs`. Substitute `hr` using the available equality. Establish `hGm : X.Gm = -(HSpace.gram W)ᵀ` using `hM.model.1`. Establish `hG : ∀ τ : X.Ψ, (mat x τ)ᴴ * (HSpace.gram W).map τ.1 * mat x τ = -sgnM X` using `fun τ => by`. Establish `h` using `hx τ`.

Rewrite `h` using `[hGm, gram_eq]`. Establish `h2 : (sgnM X)ᵀ = sgnM X` using `by rw [sgnM, diagonal_transpose]`. Rewrite using `[← h2, ← h, transpose_neg, transpose_transpose, neg_neg]`. Establish `hs' : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → s ρ * mat x τ = -(mat x τ * sgnM X)` using `hs`. Use `⟨fun ρ => ?_, fun ρ => ?_, fun ρ u => ?_⟩` and prove the remaining obligations.

Establish `h` using `hG ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩`. Conclude with `cartan (sgnM_sq X) (sgnM_herm X) h (hs' ρ _ rfl)`. Establish `: gramAt D V ρ = 1`. Rewrite using `[gramAt, hV]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Rewrite using `[this]`. Use `⟨by simp, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_one]`. Conclude with `Matrix.PosDef.one`. Establish `hL : ∀ z : Matrix (Fin W.rank) (Fin V.rank) ℂ, IsLineAt θ ρ z (lineAt θ ρ z)` using `fun z => Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ ρ z)`.

Use function extensionality and compare the values at `b j`. Simplify using `only [zOf, Pi.smul_apply, smul_eq_mul, perC]`. Take `⟨τ, a⟩` from `idx j`. Establish `hτ : ∃ ρ', τ.1 = tauE D ρ'` using `(hM.psi _).1 τ.2`. Simplify using `only [realM, dif_pos hτ, (hL _).2.2, hGm]`.

Distinguish the cases in `e : hτ.choose = ρ`. Simplify using `only [if_pos e]`. Use `per_cplx X τ.1 (HSpace.gram W) (mat x τ) (s ρ) (hG τ) (hs' ρ τ (e ▸ hτ.choose_spec)) (fun k => u k b) a` as an intermediate fact. Apply the tactic sequence `convert this using 3 <;> (try funext k) <;> simp [cplxO, mul_apply, mulVec, dotProduct]`. Simplify using `only [if_neg e]`.

Simplify using `[hermC, mulVec, dotProduct]`.
-/
theorem cplx_of_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧ (∀ τ, IsCartanInv (gramAt D V τ) 1) ∧ ∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ), zOf θ V W hr X idx x (lineAt θ τ (cplxO 1 (s τ) u) 1) = I • zOf θ V W hr X idx x (lineAt θ τ u 1) := by
  intro D ψ θ V W r g hr X bas idx _ hθ hV _ hM _ x s hx hs
  subst hr
  have hGm : X.Gm = -(HSpace.gram W)ᵀ := hM.model.1
  have hG : ∀ τ : X.Ψ, (mat x τ)ᴴ * (HSpace.gram W).map τ.1 * mat x τ = -sgnM X := fun τ => by
    have h := hx τ
    rw [hGm, gram_eq] at h
    have h2 : (sgnM X)ᵀ = sgnM X := by rw [sgnM, diagonal_transpose]
    rw [← h2, ← h, transpose_neg, transpose_transpose, neg_neg]
  have hs' : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → s ρ * mat x τ = -(mat x τ * sgnM X) := hs
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ u => ?_⟩
  · have h := hG ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    exact cartan (sgnM_sq X) (sgnM_herm X) h (hs' ρ _ rfl)
  · have : gramAt D V ρ = 1 := by
      rw [gramAt, hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    refine ⟨by simp, by simp, ?_⟩
    rw [Matrix.mul_one]; exact Matrix.PosDef.one
  · have hL : ∀ z : Matrix (Fin W.rank) (Fin V.rank) ℂ, IsLineAt θ ρ z (lineAt θ ρ z) := fun z =>
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ ρ z)
    funext b j
    simp only [zOf, Pi.smul_apply, smul_eq_mul, perC]
    obtain ⟨τ, a⟩ := idx j
    have hτ : ∃ ρ', τ.1 = tauE D ρ' := (hM.psi _).1 τ.2
    simp only [realM, dif_pos hτ, (hL _).2.2, hGm]
    by_cases e : hτ.choose = ρ
    · simp only [if_pos e]
      have := per_cplx X τ.1 (HSpace.gram W) (mat x τ) (s ρ) (hG τ) (hs' ρ τ (e ▸ hτ.choose_spec)) (fun k => u k b) a
      convert this using 3 <;> (try funext k) <;> simp [cplxO, mul_apply, mulVec, dotProduct]
    · simp only [if_neg e]
      simp [hermC, mulVec, dotProduct]

end GlobalTheory.FrameCplx
