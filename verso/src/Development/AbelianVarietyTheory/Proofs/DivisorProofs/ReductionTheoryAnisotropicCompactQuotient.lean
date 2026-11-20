import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicDoubleCosetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicOfDefinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

namespace GlobalTheory.ThK.DefCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hn` using `h.1`. Break down `Nat.min_eq_zero_iff.1 h0 with rfl | rfl` into its components or cases. Take `rfl : s = n` from `by omega`. Conclude with `Or.inr h`. Take `rfl : r = n` from `by omega`.

Conclude with `Or.inl h`.
-/
theorem hasSig_definite {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) :
    HasSig M n 0 ∨ HasSig M 0 n := by
  have hn := h.1
  rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
  · obtain rfl : s = n := by omega
    exact Or.inr h
  · obtain rfl : r = n := by omega
    exact Or.inl h

/- English proof (translation)
Establish `h1` using `congrArg τ hx`. Establish `hy : (fun i => τ (x i)) ⬝ᵥ (J.map τ) *ᵥ star (fun i => τ (x i)) = 0`. Rewrite `h1` using `[map_zero]`. Rewrite using `[← h1]`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hcm.2.2.2, Matrix.map_apply, Pi.star_apply]`.

Establish `h2` using `GlobalTheory.DefiniteAniso.eq_zero_of_hasSig (hasSig_definite h h0) (fun i => τ (x i)) (by`. Rewrite using `[Matrix.smul_mulVec, dotProduct_smul, hy, smul_zero])`. Use function extensionality and compare the values at `i`. Simplify using `using congrFun h2 i`.
-/
theorem aniso_of_smul (hcm : IsCMExt F E σ) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : ℂ)
    (h : HasSig (a • J.map τ) r s) (h0 : min r s = 0) (x : Fin n → E) (hx : form σ J x x = 0) : x = 0 := by
  have h1 := congrArg τ hx
  have hy : (fun i => τ (x i)) ⬝ᵥ (J.map τ) *ᵥ star (fun i => τ (x i)) = 0 := by
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hcm.2.2.2, Matrix.map_apply, Pi.star_apply]
  have h2 := GlobalTheory.DefiniteAniso.eq_zero_of_hasSig (hasSig_definite h h0) (fun i => τ (x i)) (by
    rw [Matrix.smul_mulVec, dotProduct_smul, hy, smul_zero])
  funext i
  simpa using congrFun h2 i

/- English proof (translation)
Rewrite using `[one_smul]`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_apply]`. Rewrite using `[hX.herm i j]`. Establish `hmap : (X.J.map σ).det = σ X.J.det` using `GlobalTheory.ThK.SqIntHerm.det_map_ringHom (σ : E →+* E) X.J`.

Rewrite using `[hmap]`. Introduce `h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hM` using `GlobalTheory.ThK.SqIntHerm.det_ne_zero_of_hasSig (hX.sig w)`. Establish `hJ : X.J.det = 0` using `σ.toRingHom.injective (by simpa using h0)`.

Apply `hM` to reduce the goal to its premises. Rewrite using `[GlobalTheory.ThK.SqIntHerm.det_map_ringHom, hJ, map_zero]`.
-/
theorem isHermND_one_smul_map {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) :
    IsHermND σ ((1 : E) • X.J.map σ) := by
  rw [one_smul]
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply]
    rw [hX.herm i j]
  · have hmap : (X.J.map σ).det = σ X.J.det := GlobalTheory.ThK.SqIntHerm.det_map_ringHom (σ : E →+* E) X.J
    rw [hmap]
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hM := GlobalTheory.ThK.SqIntHerm.det_ne_zero_of_hasSig (hX.sig w)
    have hJ : X.J.det = 0 := σ.toRingHom.injective (by simpa using h0)
    apply hM
    rw [GlobalTheory.ThK.SqIntHerm.det_map_ringHom, hJ, map_zero]

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B hB`. Establish `hcm` using `hB.cm`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `⟨fun n r s' X hX h0 => ?_, fun d r₁ s₁ W hW h0 => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ThK.DefDcoset.cocompact_of_aniso hKP.siegelSetUnitary hcm X.J one_ne_zero (isHermND_one_smul_map hX) (aniso_of_smul hcm X.J (B.emb w).1 1 (by rw [one_smul]; exact hX.sig w) h0)`.

Establish `han` using `aniso_of_smul hcm W.J (B.emb w).1 Complex.I (hW.sig w) h0`. Take `⟨c, hc, hσc⟩` from `GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm`. Conclude with `⟨han, GlobalTheory.ThK.DefDcoset.cocompact_of_aniso hKP.siegelSetUnitary hcm W.J hc (GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ W _ _ hW c hc hσc) han⟩`.
-/
theorem cocompact_of_definite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    (∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
      ∃ C : Set (UA σ X.J), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU σ X.J, ∃ c ∈ C, g = γ * c) ∧
    ∀ (d r₁ s₁ : ℕ) (W : Spc F E d), W.IsSkew σ B r₁ s₁ → min r₁ s₁ = 0 → (∀ x, form σ W.J x x = 0 → x = 0) ∧
      ∃ C : Set (UA σ W.J), IsCompact C ∧ ∀ h, ∃ γ ∈ ratU σ W.J, ∃ c ∈ C, h = γ * c := by
  intro hKP F E _ _ _ _ _ σ B hB
  have hcm := hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun n r s' X hX h0 => ?_, fun d r₁ s₁ W hW h0 => ?_⟩
  · exact GlobalTheory.ThK.DefDcoset.cocompact_of_aniso hKP.siegelSetUnitary hcm X.J one_ne_zero (isHermND_one_smul_map hX)
      (aniso_of_smul hcm X.J (B.emb w).1 1 (by rw [one_smul]; exact hX.sig w) h0)
  · have han := aniso_of_smul hcm W.J (B.emb w).1 Complex.I (hW.sig w) h0
    obtain ⟨c, hc, hσc⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
    exact ⟨han, GlobalTheory.ThK.DefDcoset.cocompact_of_aniso hKP.siegelSetUnitary hcm W.J hc
      (GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ W _ _ hW c hc hσc) han⟩

end GlobalTheory.ThK.DefCocompact
