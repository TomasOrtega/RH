import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelGramMemConeIntegerSquares
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedForms

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Set `B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ` to `∑ k, toReal (GlobalTheory.RedTh.sqForm b (Pi.single k 1))`. Establish `hv : ∀ i j, B₀ (b i) (b j) = if i = j then 1 else 0` using `fun i j => by`. Simplify using `only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_basis]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[Pi.single_apply]`. Simplify using `[Pi.single_apply, h]`. Use `⟨B₀, fun y z => ?_, (isPosDef_iff_basis b B₀).2 fun c hc => ?_⟩` and prove the remaining obligations. Simplify using `only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_apply, mul_comm]`. Simplify using `only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Take `⟨i, hi⟩` from `Function.ne_iff.1 hc`. Conclude with `Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩`.
-/
theorem exists_isPosDef_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    ∃ B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y z, B₀ y z = B₀ z y) ∧ IsPosDef B₀ := by
  classical
  let B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ k, toReal (GlobalTheory.RedTh.sqForm b (Pi.single k 1))
  have hv : ∀ i j, B₀ (b i) (b j) = if i = j then 1 else 0 := fun i j => by
    simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_basis]
    by_cases h : i = j
    · subst h
      simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
  refine ⟨B₀, fun y z => ?_, (isPosDef_iff_basis b B₀).2 fun c hc => ?_⟩
  · simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_apply, mul_comm]
  · simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

/- English proof (translation)
Introduce `X _ _ _`. Take `⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n` from `⟨_, rfl⟩`. Set `b₀ : Module.Basis (Fin n) ℤ X` to `Module.finBasisOfFinrankEq ℤ X hn`. Take `⟨B₀, hs₀, hp₀⟩` from `exists_isPosDef_of_basis b₀`. Take `⟨S, hS⟩` from `GlobalTheory.SiegelCone.gram_mem_cone n`.

Use `GlobalTheory.RedTh.hasRedCover_of_fintype (ι := ↥S) _ (fun l => GlobalTheory.RedTh.sqForm b₀ l.1) (fun l y z => ?_) (fun l y => ?_) fun B hB => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.RedTh.sqForm_apply, mul_comm]`. Simplify using `only [GlobalTheory.RedTh.sqForm_apply]`. Conclude with `mul_self_nonneg _`. Take `⟨X₁, _, m₁, hproj, r, B₁, hr, hB₁, hp₁, hBr⟩` from `hB`.

Take `rfl : m₁ = AddCommGroup.toIntModule X₁` from `Subsingleton.elim _ _`. Establish `: Module.Finite ℤ X₁` using `Module.Finite.of_surjective r hr`. Establish `: Module.Free ℤ X₁` using `inferInstance`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property r LinearMap.id hr`. Establish `hrσ : ∀ y, r (σ y) = y` using `fun y => LinearMap.congr_fun hσ y`.

Take `⟨b, d, d', u, t, hd, -, -, hg, -⟩` from `GlobalTheory.RedTh.exists_siegel_split r σ hrσ B₀ hs₀ hp₀ B₁ hB₁.1 hp₁ n hn`. Take `⟨c, hc, hG⟩` from `hS d u hd`. Set `e : X ≃ₗ[ℤ] X` to `b₀.equiv b (Equiv.refl _)`. Establish `he : ∀ i, e (b₀ i) = b i` using `fun i => by simp [e]`. Use `⟨e, fun l => c l.1, fun l => hc _, ?_⟩` and prove the remaining obligations.

Use `b₀.ext fun i => b₀.ext fun j => ?_` and prove the remaining obligations. Establish `hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ))`. Rewrite using `[hBr, hg, hG]`. Simplify using `[Matrix.sum_apply, Matrix.vecMulVec_apply]`. Simplify using `only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, GlobalTheory.RedTh.sqForm_basis]`.

Rewrite using `[← Finset.sum_coe_sort S]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem hasRedCover_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], HasRedCover (id : ℤ → ℤ) X := by
  intro X _ _ _
  classical
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  let b₀ : Module.Basis (Fin n) ℤ X := Module.finBasisOfFinrankEq ℤ X hn
  obtain ⟨B₀, hs₀, hp₀⟩ := exists_isPosDef_of_basis b₀
  obtain ⟨S, hS⟩ := GlobalTheory.SiegelCone.gram_mem_cone n
  refine GlobalTheory.RedTh.hasRedCover_of_fintype (ι := ↥S) _ (fun l => GlobalTheory.RedTh.sqForm b₀ l.1) (fun l y z => ?_)
    (fun l y => ?_) fun B hB => ?_
  · simp only [GlobalTheory.RedTh.sqForm_apply, mul_comm]
  · simp only [GlobalTheory.RedTh.sqForm_apply]
    exact mul_self_nonneg _
  obtain ⟨X₁, _, m₁, hproj, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  obtain rfl : m₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := inferInstance
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  obtain ⟨b, d, d', u, t, hd, -, -, hg, -⟩ :=
    GlobalTheory.RedTh.exists_siegel_split r σ hrσ B₀ hs₀ hp₀ B₁ hB₁.1 hp₁ n hn
  obtain ⟨c, hc, hG⟩ := hS d u hd
  let e : X ≃ₗ[ℤ] X := b₀.equiv b (Equiv.refl _)
  have he : ∀ i, e (b₀ i) = b i := fun i => by simp [e]
  refine ⟨e, fun l => c l.1, fun l => hc _, ?_⟩
  refine b₀.ext fun i => b₀.ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [hBr, hg, hG]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    GlobalTheory.RedTh.sqForm_basis]
  rw [← Finset.sum_coe_sort S]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Fan
