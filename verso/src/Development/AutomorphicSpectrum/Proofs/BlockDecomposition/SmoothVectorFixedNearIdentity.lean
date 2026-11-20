import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

/- English proof (translation)
Establish `h0 : Continuous (fun h : HPG k i t => (((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Establish `hv : Continuous (fun h : HPG k i t => ((leviProj k (ePG i t) (hpgIncl k i t h)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k))` using `(h0.matrix_submatrix (fun j => (ePG i t) ⟨b, j⟩) (fun j => (ePG i t) ⟨b, j⟩)).congr (fun _ => rfl)`. Rewrite using `[Units.continuous_iff]`. Use `⟨hv, ?_⟩` and prove the remaining obligations. Establish `hinv : Continuous (fun h : HPG k i t => ((leviProj k (ePG i t) (hpgIncl k i t h⁻¹)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k))` using `hv.comp continuous_inv`.

Use `hinv.congr (fun h => ?_)` and prove the remaining obligations. Simplify using `only [map_inv, Pi.inv_apply]`.
-/
private theorem continuous_leviProj_hpgIncl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (b : Bool) :
    Continuous (fun h : HPG k i t => (leviProj k (ePG i t) (hpgIncl k i t h)) b) := by
  have h0 : Continuous (fun h : HPG k i t =>
      (((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    (h0.matrix_submatrix (fun j => (ePG i t) ⟨b, j⟩) (fun j => (ePG i t) ⟨b, j⟩)).congr (fun _ => rfl)
  rw [Units.continuous_iff]
  refine ⟨hv, ?_⟩
  have hinv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h⁻¹)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    hv.comp continuous_inv
  refine hinv.congr (fun h => ?_)
  simp only [map_inv, Pi.inv_apply]

/- English proof (translation)
Establish `h1 : Continuous (fun h : HPG k i t => (pgProj k i t h).1)` using `continuous_induced_rng.2 ((continuous_leviProj_hpgIncl k i t false).congr (fun _ => rfl))`. Establish `h2 : Continuous (fun h : HPG k i t => (pgProj k i t h).2)` using `(continuous_leviProj_hpgIncl k i t true).congr (fun _ => rfl)`. Conclude with `(h1.prodMk h2).congr (fun _ => rfl)`.
-/
theorem continuous_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) : Continuous (pgProj k i t) := by
  have h1 : Continuous (fun h : HPG k i t => (pgProj k i t h).1) :=
    continuous_induced_rng.2 ((continuous_leviProj_hpgIncl k i t false).congr (fun _ => rfl))
  have h2 : Continuous (fun h : HPG k i t => (pgProj k i t h).2) :=
    (continuous_leviProj_hpgIncl k i t true).congr (fun _ => rfl)
  exact (h1.prodMk h2).congr (fun _ => rfl)

/- English proof (translation)
Establish `hd : ∀ (n : ℕ) (s : ℂ), IsSmoothChar (detChar (Fin n) (absPow k s))` using `fun n s => IsSmoothChar.detChar (isSmoothChar_of_isUnram (isUnram_absPow k s))`. Establish `h1 : IsSmooth (mtw τ (↑(t + 1) / 2)).ρ`. Use `isSmooth_twist hτ ?_` and prove the remaining obligations. Unfold `dpowM dpow`. Unfold `IsSmoothChar`.

Rewrite using `[← MonoidHom.comap_ker]`. Conclude with `IsOpen.preimage continuous_subtype_val (hd _ _)`. Establish `h2 : IsSmooth (σ.tw (-↑(i + 1 + 1) / 2)).ρ`. Unfold `GRep.tw`. Conclude with `isSmooth_twist hσ (by unfold dpow; exact hd _ _)`.

Introduce `v`. Conclude with `(isSmooth_extTensor h1 h2 v).preimage (continuous_pgProj k (i + 1) (t + 1))`.
-/
theorem isSmooth_sigX {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : IsSmooth (sigX τ σ) := by
  have hd : ∀ (n : ℕ) (s : ℂ), IsSmoothChar (detChar (Fin n) (absPow k s)) :=
    fun n s => IsSmoothChar.detChar (isSmoothChar_of_isUnram (isUnram_absPow k s))
  have h1 : IsSmooth (mtw τ (↑(t + 1) / 2)).ρ := by
    refine isSmooth_twist hτ ?_
    unfold dpowM dpow
    unfold IsSmoothChar
    rw [← MonoidHom.comap_ker]
    exact IsOpen.preimage continuous_subtype_val (hd _ _)
  have h2 : IsSmooth (σ.tw (-↑(i + 1 + 1) / 2)).ρ := by
    unfold GRep.tw
    exact isSmooth_twist hσ (by unfold dpow; exact hd _ _)
  intro v
  exact (isSmooth_extTensor h1 h2 v).preimage (continuous_pgProj k (i + 1) (t + 1))

/- English proof (translation)
Introduce `k _ _ _ _ i t τ σ hτ hσ w`. Take `⟨O, hO, hOeq⟩` from `isOpen_induced_iff.1 (isSmooth_sigX τ σ hτ hσ w)`. Establish `h1 : (1 : HPG k (i + 1) (t + 1)) ∈ Subtype.val ⁻¹' O`. Rewrite using `[hOeq]`. Simplify using the standard rewrite rules.

Use `⟨O, hO.mem_nhds h1, fun h hh => ?_⟩` and prove the remaining obligations. Establish `hh' : h ∈ Subtype.val ⁻¹' O` using `hh`. Rewrite `hh'` using `[hOeq]`. Conclude with `hh'`.
-/
theorem sigX_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  intro k _ _ _ _ i t τ σ hτ hσ w
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isSmooth_sigX τ σ hτ hσ w)
  have h1 : (1 : HPG k (i + 1) (t + 1)) ∈ Subtype.val ⁻¹' O := by
    rw [hOeq]
    simp
  refine ⟨O, hO.mem_nhds h1, fun h hh => ?_⟩
  have hh' : h ∈ Subtype.val ⁻¹' O := hh
  rw [hOeq] at hh'
  exact hh'

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
