import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.CoindKernel

variable {G : Type} [Group G] (P : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V)

open Classical in

noncomputable def delta : V →ₗ[ℂ] Representation.coindV P.subtype σ where
  toFun v := ⟨fun x => if h : x ∈ P then σ ⟨x, h⟩ v else 0, by
    intro p g
    by_cases hg : g ∈ P
    · have h1 : P.subtype p * g ∈ P := P.mul_mem p.2 hg
      simp only [dif_pos hg, dif_pos h1]
      have : (⟨P.subtype p * g, h1⟩ : P) = p * ⟨g, hg⟩ := rfl
      rw [this, map_mul]; rfl
    · have h1 : P.subtype p * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      simp only [dif_neg hg, dif_neg h1, map_zero]⟩
  map_add' v w := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  map_smul' c v := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem delta_apply (v : V) (x : G) :
    (delta P σ v).1 x = if h : x ∈ P then σ ⟨x, h⟩ v else 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coind_val (g : G) (f : Representation.coindV P.subtype σ) (x : G) :
    (Representation.coind P.subtype σ g f).1 x = f.1 (x * g) := rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[coind_val, delta_apply, delta_apply]`. Distinguish the cases in `hx : x ∈ P`. Establish `h1 : x * (p : G) ∈ P` using `P.mul_mem hx p.2`. Rewrite using `[dif_pos hx, dif_pos h1]`.

Establish `: (⟨x * (p : G), h1⟩ : P) = ⟨x, hx⟩ * p` using `rfl`. Rewrite using `[this, map_mul]`. Both sides reduce to the same expression. Establish `h1 : x * (p : G) ∉ P` using `fun h => hx ((P.mul_mem_cancel_right p.2).1 h)`. Rewrite using `[dif_neg hx, dif_neg h1]`.
-/
theorem coind_delta (p : P) (v : V) :
    Representation.coind P.subtype σ (p : G) (delta P σ v) = delta P σ (σ p v) := by
  ext x
  rw [coind_val, delta_apply, delta_apply]
  by_cases hx : x ∈ P
  · have h1 : x * (p : G) ∈ P := P.mul_mem hx p.2
    rw [dif_pos hx, dif_pos h1]
    have : (⟨x * (p : G), h1⟩ : P) = ⟨x, hx⟩ * p := rfl
    rw [this, map_mul]; rfl
  · have h1 : x * (p : G) ∉ P := fun h => hx ((P.mul_mem_cancel_right p.2).1 h)
    rw [dif_neg hx, dif_neg h1]

open Classical in
/- English proof (translation)
Use extensionality with `x`. Establish `h : ∀ g : G, (Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g))).1 x = if x * g⁻¹ ∈ P then f.1 x else 0`. Introduce `g`. Rewrite using `[coind_val, delta_apply]`. Distinguish the cases in `hx : x * g⁻¹ ∈ P`.

Rewrite using `[dif_pos hx, if_pos hx]`. Use `f.2 ⟨x * g⁻¹, hx⟩ g` as an intermediate fact. Rewrite using `[← this]`. Simplify using the standard rewrite rules. Rewrite using `[dif_neg hx, if_neg hx]`.

Rewrite using `[Submodule.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun g _ => h g]`. Establish `e` using `Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x)) (fun y : G => if y ∈ P then f.1 x else 0)`. Simplify using `only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at e`. Rewrite using `[e, ← Finset.sum_filter, Finset.sum_const, Submodule.coe_smul, Pi.smul_apply, Nat.cast_smul_eq_nsmul]`.
-/
theorem sum_delta [Fintype G] (f : Representation.coindV P.subtype σ) :
    ∑ g : G, Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g)) =
      ((Finset.univ.filter (· ∈ P)).card : ℂ) • f := by
  ext x
  have h : ∀ g : G, (Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g))).1 x
      = if x * g⁻¹ ∈ P then f.1 x else 0 := by
    intro g
    rw [coind_val, delta_apply]
    by_cases hx : x * g⁻¹ ∈ P
    · rw [dif_pos hx, if_pos hx]
      have := f.2 ⟨x * g⁻¹, hx⟩ g
      rw [← this]
      simp
    · rw [dif_neg hx, if_neg hx]
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun g _ => h g]
  have e := Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x))
    (fun y : G => if y ∈ P then f.1 x else 0)
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at e
  rw [e, ← Finset.sum_filter, Finset.sum_const, Submodule.coe_smul, Pi.smul_apply,
    Nat.cast_smul_eq_nsmul]

variable (P' : Subgroup G) {V' : Type} [AddCommGroup V'] [Module ℂ V']
  (σ' : Representation ℂ P' V')

noncomputable def kernel :
    Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V') where
  toFun Φ g := (LinearMap.proj g ∘ₗ (Representation.coindV P'.subtype σ').subtype) ∘ₗ
    Φ.toLinearMap ∘ₗ delta P σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kernel_apply (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ')) (g : G) (v : V) :
    kernel P σ P' σ' Φ g v = (Φ (delta P σ v)).1 g := rfl

/- English proof (translation)
Introduce `G _ _ P P' V V' _ _ _ _ σ σ'`. Use `haveI := Fintype.ofFinite G`. Use `⟨kernel P σ P' σ', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Φ hΦ`.

Establish `h0 : ∀ v, Φ (delta P σ v) = 0`. Introduce `v`. Use extensionality with `g`. Use `kernel_apply P σ P' σ' Φ g v` as an intermediate fact. Rewrite `this` using `[hΦ]`.

Conclude with `this.symm`. Apply `Representation.IntertwiningMap.ext` to reduce the goal to its premises. Use `ext1 f`. Establish `h1` using `congrArg Φ (sum_delta P σ f)`. Rewrite using `[map_sum, map_smul, Finset.sum_eq_zero (fun g _ => by`.

Rewrite `h1` using `[Φ.isIntertwining, h0, map_zero])]`. Establish `hc : ((Finset.univ.filter (fun x : G => x ∈ P)).card : ℂ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Finset.card_ne_zero]`. Conclude with `⟨1, by simp [P.one_mem]⟩`. Conclude with `(smul_eq_zero.1 h1.symm).resolve_left hc`.

Introduce `Φ p' g p`. Use extensionality with `v`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, kernel_apply, kernel_apply, ← coind_delta, Φ.isIntertwining, coind_val, mul_assoc]`. Conclude with `(Φ (delta P σ v)).2 p' (g * p)`.
-/
theorem exists_kernel : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  intro G _ _ P P' V V' _ _ _ _ σ σ'
  classical
  haveI := Fintype.ofFinite G
  refine ⟨kernel P σ P' σ', ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro Φ hΦ
    have h0 : ∀ v, Φ (delta P σ v) = 0 := by
      intro v
      ext g
      have := kernel_apply P σ P' σ' Φ g v
      rw [hΦ] at this
      exact this.symm
    apply Representation.IntertwiningMap.ext
    ext1 f
    have h1 := congrArg Φ (sum_delta P σ f)
    rw [map_sum, map_smul, Finset.sum_eq_zero (fun g _ => by
      rw [Φ.isIntertwining, h0, map_zero])] at h1
    have hc : ((Finset.univ.filter (fun x : G => x ∈ P)).card : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Finset.card_ne_zero]
      exact ⟨1, by simp [P.one_mem]⟩
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  · intro Φ p' g p
    ext v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, kernel_apply, kernel_apply, ← coind_delta,
      Φ.isIntertwining, coind_val, mul_assoc]
    exact (Φ (delta P σ v)).2 p' (g * p)

end GlobalTheory.CoindKernel
