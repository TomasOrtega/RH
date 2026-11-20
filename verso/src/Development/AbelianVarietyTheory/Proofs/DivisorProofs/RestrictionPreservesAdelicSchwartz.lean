import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv

namespace GlobalTheory.ThK.AdaptEv

noncomputable def extendByZeroCLM {κ ι κ₁ V : Type} [Fintype κ] [Fintype κ₁] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (eq : κ ≃ ι ⊕ κ₁) : (κ₁ → V) →L[ℝ] (κ → V) :=
  LinearMap.toContinuousLinearMap
    { toFun := ext0 eq
      map_add' := matrixExtendByZero_add eq
      map_smul' := fun c a => by
        funext k; simp only [ext0, Pi.smul_apply, RingHom.id_apply]; cases eq k <;> simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ext0CLM_apply {κ ι κ₁ V : Type} [Fintype κ] [Fintype κ₁] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → V) : extendByZeroCLM eq a = ext0 eq a := rfl

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Establish `h` using `norm_le_pi_norm (ext0 eq a) (eq.symm (Sum.inr j))`. Rewrite `h` using `[ext0_inr]`. Then use the resulting hypothesis.
-/
theorem norm_le_norm_extend_by_zero_block {κ ι κ₁ V : Type} [Fintype κ] [Fintype κ₁] [NormedAddCommGroup V]
    (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → V) : ‖a‖ ≤ ‖ext0 eq a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := norm_le_pi_norm (ext0 eq a) (eq.symm (Sum.inr j))
  rwa [ext0_inr] at h

/- English proof (translation)
Use `continuous_pi fun k => ?_` and prove the remaining obligations. Simplify using `only [ext0]`. Consider the cases of `eq k with`. Consider the case `inl i => exact continuous_const`. Consider the case `inr j => exact continuous_apply j`.
-/
theorem continuous_extend_by_zero_block {κ ι κ₁ R : Type} [Zero R] [TopologicalSpace R] (eq : κ ≃ ι ⊕ κ₁) :
    Continuous (ext0 (R := R) eq) := by
  refine continuous_pi fun k => ?_
  simp only [ext0]
  cases eq k with
  | inl i => exact continuous_const
  | inr j => exact continuous_apply j

def res2 {κ ι κ₁ R : Type} (eq : κ ≃ ι ⊕ κ₁) (x : κ → R) : κ₁ → R := fun j => x (eq.symm (Sum.inr j))

/- English proof (translation)
Use function extensionality and compare the values at `j`. Conclude with `ext0_inr eq a j`.
-/
theorem restrict_extend_by_zero {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → R) : res2 eq (ext0 eq a) = a := by
  funext j; exact ext0_inr eq a j

/- English proof (translation)
Establish `hr : Continuous (res2 (R` using `R) eq) := continuous_pi fun j => continuous_apply _`. Use `IsCompact.of_isClosed_subset (hg.image hr) (isClosed_tsupport _) ?_` and prove the remaining obligations. Use `(closure_minimal (fun y hy => ?_) ((isClosed_tsupport g).preimage (continuous_extend_by_zero_block eq))).trans ?_` and prove the remaining obligations. Conclude with `subset_tsupport g hy`. Introduce `y hy`.

Conclude with `⟨ext0 eq y, hy, restrict_extend_by_zero eq y⟩`.
-/
theorem hasCompactSupport_comp_extend_by_zero {κ ι κ₁ R : Type} [Zero R] [TopologicalSpace R]
    (eq : κ ≃ ι ⊕ κ₁) {g : (κ → R) → ℂ} (hg : HasCompactSupport g) : HasCompactSupport (g ∘ ext0 eq) := by
  have hr : Continuous (res2 (R := R) eq) := continuous_pi fun j => continuous_apply _
  refine IsCompact.of_isClosed_subset (hg.image hr) (isClosed_tsupport _) ?_
  refine (closure_minimal (fun y hy => ?_) ((isClosed_tsupport g).preimage (continuous_extend_by_zero_block eq))).trans ?_
  · exact subset_tsupport g hy
  · intro y hy
    exact ⟨ext0 eq y, hy, restrict_extend_by_zero eq y⟩

end GlobalTheory.ThK.AdaptEv

open GlobalTheory.ThK.AdaptEv in
open scoped Classical in

/- English proof (translation)
Introduce `F _ _ κ ι κ₁ _ _ _ eq Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨SchwartzMap.compCLM ℝ (extendByZeroCLM (V := mixedEmbedding.mixedSpace F) eq).hasTemperateGrowth ⟨1, 1, fun y => ?_⟩ f, g ∘ ext0 eq, ⟨hg.1.comp_continuous (continuous_extend_by_zero_block eq), hasCompactSupport_comp_extend_by_zero eq hg.2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_one, one_mul, ext0CLM_apply]`. Combine the linear relations using `[norm_le_norm_extend_by_zero_block eq y]`. Establish `h1 : (0 : AdeleRing (𝓞 F) F).1 = 0` using `rfl`. Establish `h2 : (0 : AdeleRing (𝓞 F) F).2 = 0` using `rfl`. Use function extensionality and compare the values at `y`.

Simplify using `only [restrL_apply, pureA, SchwartzMap.compCLM_apply, Function.comp_apply, ext0CLM_apply]`. Use `congr 2`. Apply the tactic sequence `funext k; simp only [ext0]; cases eq k <;> simp only [Sum.elim_inl, Sum.elim_inr, h1, map_zero]`. Apply the tactic sequence `funext k; simp only [ext0]; cases eq k <;> simp [h1, h2]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem GlobalTheory.ThK.AdaptEv.restrL_mem_schA : ∀ (F : Type) [Field F] [NumberField F] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    ∀ Φ ∈ schA F κ, restrL eq Φ ∈ schA F κ₁ := by
  intro F _ _ κ ι κ₁ _ _ _ eq Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨SchwartzMap.compCLM ℝ (extendByZeroCLM (V := mixedEmbedding.mixedSpace F) eq).hasTemperateGrowth
      ⟨1, 1, fun y => ?_⟩ f, g ∘ ext0 eq, ⟨hg.1.comp_continuous (continuous_extend_by_zero_block eq), hasCompactSupport_comp_extend_by_zero eq hg.2⟩, ?_⟩
    · rw [pow_one, one_mul, ext0CLM_apply]
      linarith [norm_le_norm_extend_by_zero_block eq y]
    · have h1 : (0 : AdeleRing (𝓞 F) F).1 = 0 := rfl
      have h2 : (0 : AdeleRing (𝓞 F) F).2 = 0 := rfl
      funext y
      simp only [restrL_apply, pureA, SchwartzMap.compCLM_apply, Function.comp_apply, ext0CLM_apply]
      congr 2
      · funext k; simp only [ext0]; cases eq k <;> simp only [Sum.elim_inl, Sum.elim_inr, h1, map_zero]
      · funext k; simp only [ext0]; cases eq k <;> simp [h1, h2]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
