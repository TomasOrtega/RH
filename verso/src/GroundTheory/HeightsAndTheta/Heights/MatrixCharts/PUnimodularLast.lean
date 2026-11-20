import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace UnimodularLast

def dotForm {k : ℕ} (ρ : Fin (k + 1) → ℤ) : (Fin (k + 1) → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ρ ⬝ᵥ x
  map_add' x y := dotProduct_add ρ x y
  map_smul' c x := by rw [dotProduct_smul]; rfl

/- English proof (translation)
Use `set φ := dotForm ρ with hφ`. Establish `hφx : ∀ x, φ x = ρ ⬝ᵥ x` using `fun _ => rfl`. Use `set g := Submodule.IsPrincipal.generator (LinearMap.range φ) with hgdef`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp (Submodule.IsPrincipal.generator_mem (LinearMap.range φ))`. Establish `hg : g ≠ 0`.

Introduce `h0`. Establish `hbot` using `(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero (LinearMap.range φ)).mpr h0`. Apply `hρ` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `hi : φ (Pi.single i 1) ∈ LinearMap.range φ` using `LinearMap.mem_range_self φ _`.

Rewrite `hi` using `[hbot, Submodule.mem_bot, hφx, dotProduct_single, mul_one]`. Simplify using `using hi`. Establish `hli : ∀ (c : ℤ), ∀ x ∈ LinearMap.ker φ, c • y + x = 0 → c = 0`. Introduce `c x hx hc`. Establish `h1` using `congrArg φ hc`.

Rewrite `h1` using `[map_add, map_smul, LinearMap.mem_ker.mp hx, hy, map_zero, add_zero, smul_eq_mul]`. Conclude with `(mul_eq_zero.mp h1).resolve_right hg`. Establish `hsp : ∀ z, ∃ c : ℤ, z + c • y ∈ LinearMap.ker φ`. Introduce `z`. Take `⟨c, hc⟩` from `(Submodule.IsPrincipal.mem_iff_eq_smul_generator (LinearMap.range φ)).mp (LinearMap.mem_range_self φ z)`.

Use `⟨-c, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_add, map_smul, hy, hc, ← hgdef, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, bk⟩` from `Submodule.basisOfPid (Pi.basisFun ℤ (Fin (k + 1))) (LinearMap.ker φ)`. Set `b` to `Module.Basis.mkFinSnoc bk y hli hsp`.

Establish `hn : n = k`. Establish `h` using `Module.finrank_eq_card_basis b`. Rewrite `h` using `[Module.finrank_fin_fun, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Substitute `hn` using the available equality.

Use `⟨b, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `hb : b (Fin.castSucc j) = (bk j : Fin (n + 1) → ℤ)`. Simplify using `only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_castSucc, Function.comp_apply]`. Rewrite using `[hb, ← hφx]`. Conclude with `LinearMap.mem_ker.mp (bk j).2`.

Establish `hb : b (Fin.last n) = y`. Simplify using `only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_last]`. Rewrite using `[hb, ← hφx, hy]`. Conclude with `hg`.
-/
theorem exists_basis (k : ℕ) (ρ : Fin (k + 1) → ℤ) (hρ : ρ ≠ 0) :
    ∃ b : Module.Basis (Fin (k + 1)) ℤ (Fin (k + 1) → ℤ),
      (∀ j : Fin k, ρ ⬝ᵥ b (Fin.castSucc j) = 0) ∧ ρ ⬝ᵥ b (Fin.last k) ≠ 0 := by
  set φ := dotForm ρ with hφ
  have hφx : ∀ x, φ x = ρ ⬝ᵥ x := fun _ => rfl
  set g := Submodule.IsPrincipal.generator (LinearMap.range φ) with hgdef
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (Submodule.IsPrincipal.generator_mem (LinearMap.range φ))
  have hg : g ≠ 0 := by
    intro h0
    have hbot := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (LinearMap.range φ)).mpr h0
    apply hρ
    funext i
    have hi : φ (Pi.single i 1) ∈ LinearMap.range φ := LinearMap.mem_range_self φ _
    rw [hbot, Submodule.mem_bot, hφx, dotProduct_single, mul_one] at hi
    simpa using hi
  have hli : ∀ (c : ℤ), ∀ x ∈ LinearMap.ker φ, c • y + x = 0 → c = 0 := by
    intro c x hx hc
    have h1 := congrArg φ hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hy, map_zero, add_zero, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right hg
  have hsp : ∀ z, ∃ c : ℤ, z + c • y ∈ LinearMap.ker φ := by
    intro z
    obtain ⟨c, hc⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator
      (LinearMap.range φ)).mp (LinearMap.mem_range_self φ z)
    refine ⟨-c, ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hy, hc, ← hgdef, smul_eq_mul, smul_eq_mul]
    ring
  obtain ⟨n, bk⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (k + 1))) (LinearMap.ker φ)
  let b := Module.Basis.mkFinSnoc bk y hli hsp
  have hn : n = k := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    omega
  subst hn
  refine ⟨b, fun j => ?_, ?_⟩
  · have hb : b (Fin.castSucc j) = (bk j : Fin (n + 1) → ℤ) := by
      simp only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_castSucc, Function.comp_apply]
    rw [hb, ← hφx]
    exact LinearMap.mem_ker.mp (bk j).2
  · have hb : b (Fin.last n) = y := by
      simp only [b, Module.Basis.coe_mkFinSnoc, Fin.snoc_last]
    rw [hb, ← hφx, hy]
    exact hg

end UnimodularLast

/- English proof (translation)
Introduce `k ρ hρ`. Take `⟨b, hker, hlast⟩` from `UnimodularLast.exists_basis k ρ hρ`. Use `⟨(Pi.basisFun ℤ (Fin (k + 1))).toMatrix b, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)`. Introduce `j`.

Establish `: (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.castSucc j) = ρ ⬝ᵥ b (Fin.castSucc j)`. Simplify using `only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Rewrite using `[this]`. Conclude with `hker j`. Establish `: (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.last k) = ρ ⬝ᵥ b (Fin.last k)`.

Simplify using `only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Rewrite using `[this]`. Conclude with `hlast`.
-/
theorem UnimodularLast.proof : UnimodularLast.Statement := by
  intro k ρ hρ
  obtain ⟨b, hker, hlast⟩ := UnimodularLast.exists_basis k ρ hρ
  refine ⟨(Pi.basisFun ℤ (Fin (k + 1))).toMatrix b, ?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · intro j
    have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.castSucc j) =
        ρ ⬝ᵥ b (Fin.castSucc j) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hker j
  · have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.last k) =
        ρ ⬝ᵥ b (Fin.last k) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hlast

end

end GroundTheory.Heights₂.Heights
