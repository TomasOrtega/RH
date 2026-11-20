import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main`. Consider the case `exact _root_.GlobalTheory.HermitianEigenvalueInequality.main`. Consider the case `(apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)`.
-/
theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main
  | exact _root_.GlobalTheory.HermitianEigenvalueInequality.main
  | (apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)

/- English proof (translation)
Introduce `E _ _ n n₁ L ι hL hι`. Establish `hfg : L.FG` using `Submodule.IsLattice.fg (self := hL)`. Establish `hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤` using `Submodule.IsLattice.span_eq_top (self := hL)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E)` to `(Matrix.mulVecLin ι).restrictScalars (𝓞 E)`.

Establish `hf : Function.Injective f` using `hι`. Establish `hle : (lowLat ι L).map f ≤ L` using `Submodule.map_comap_le f L`. Establish `hN : IsNoetherian (𝓞 E) L` using `isNoetherian_of_fg_of_noetherian L hfg`. Establish `hm : ((lowLat ι L).map f).FG` using `(isNoetherian_submodule.mp hN) _ hle`. Conclude with `Submodule.fg_of_fg_map_injective f hf hm`.

Rewrite using `[eq_top_iff]`. Introduce `u _`. Take `⟨d, hd, hdu⟩` from `exists_ne_zero_smul_mem_of_mem_span L (ι *ᵥ u) (by rw [hsp]; trivial)`. Establish `hd1 : algebraMap (𝓞 E) E d ≠ 0`. Introduce `h`.

Conclude with `hd (IsFractionRing.injective (𝓞 E) E (by simpa using h))`. Establish `hmem : (algebraMap (𝓞 E) E d) • u ∈ lowLat ι L`. Rewrite using `[mem_lowLat, Matrix.mulVec_smul, algebraMap_smul]`. Conclude with `hdu`. Establish `: u = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • u)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hd1, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem isLattice_lowLat : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  intro E _ _ n n₁ L ι hL hι
  have hfg : L.FG := Submodule.IsLattice.fg (self := hL)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := Submodule.IsLattice.span_eq_top (self := hL)
  refine ⟨?_, ?_⟩
  · let f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E)
    have hf : Function.Injective f := hι
    have hle : (lowLat ι L).map f ≤ L := Submodule.map_comap_le f L
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hm : ((lowLat ι L).map f).FG := (isNoetherian_submodule.mp hN) _ hle
    exact Submodule.fg_of_fg_map_injective f hf hm
  · rw [eq_top_iff]
    intro u _
    obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_mem_of_mem_span L (ι *ᵥ u) (by rw [hsp]; trivial)
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by
      intro h
      exact hd (IsFractionRing.injective (𝓞 E) E (by simpa using h))
    have hmem : (algebraMap (𝓞 E) E d) • u ∈ lowLat ι L := by
      rw [mem_lowLat, Matrix.mulVec_smul, algebraMap_smul]
      exact hdu
    have : u = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • u) := by
      rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.PlaneSkew
