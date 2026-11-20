import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

open Module

/- English proof (translation)
Introduce `m v φ h`. Set `L : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun x => φ ⬝ᵥ x map_add' := fun x y => dotProduct_add φ x y map_smul' := fun c x => by simp [dotProduct_smul] }`. Establish `hL : ∀ x, L x = φ ⬝ᵥ x` using `fun x => rfl`. Establish `hsurj : LinearMap.range L = ⊤`. Rewrite using `[LinearMap.range_eq_top]`.

Introduce `c`. Conclude with `⟨c • v, by rw [hL, dotProduct_smul, h]; simp⟩`. Establish `hdim : Module.finrank ℂ (LinearMap.ker L) = m`. Use `LinearMap.finrank_range_add_finrank_ker L` as an intermediate fact. Rewrite `this` using `[hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers. Set `bN` to `Module.finBasisOfFinrankEq ℂ (LinearMap.ker L) hdim`. Establish `hli : ∀ (c : ℂ), ∀ x ∈ LinearMap.ker L, c • v + x = 0 → c = 0`. Introduce `c x hx hc`. Use `congrArg L hc` as an intermediate fact.

Rewrite `this` using `[map_add, map_smul, LinearMap.mem_ker.mp hx, hL v, h, map_zero]`. Simplify using `using this`. Establish `hsp : ∀ z : Fin (m + 1) → ℂ, ∃ c : ℂ, z + c • v ∈ LinearMap.ker L`. Introduce `z`. Use `⟨-(L z), ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, map_add, map_smul, hL v, h]`. Simplify using the standard rewrite rules. Set `b` to `Module.Basis.mkFinCons v bN hli hsp`. Establish `hb : ⇑b = Fin.cons v (Subtype.val ∘ bN)` using `Module.Basis.coe_mkFinCons v bN hli hsp`. Set `e` to `Pi.basisFun ℂ (Fin (m + 1))`.

Establish `hcoord : b.coord 0 = L`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations. Rewrite using `[Basis.coord_apply, Basis.repr_self, hb]`. Simplify using `[hL, h]`.

Rewrite using `[Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]`. Establish `hmem : b k.succ ∈ LinearMap.ker L`. Rewrite using `[hb]`. Simplify using the standard rewrite rules. Rewrite using `[LinearMap.mem_ker.mp hmem]`.

Simplify using `[Fin.succ_ne_zero]`. Use `⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip e b, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[Basis.toMatrix_apply, hb]`. Simplify using `[e]`.

Introduce `j`. Rewrite using `[Basis.toMatrix_apply]`. Use `congrArg (fun f : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ => f (e j)) hcoord` as an intermediate fact. Simplify using `only [Basis.coord_apply] at this`. Rewrite using `[this, hL]`.

Simplify using `[e, dotProduct_single]`.
-/
theorem frame_first_column_first_row :
    ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  intro m v φ h
  let L : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := fun x y => dotProduct_add φ x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hL : ∀ x, L x = φ ⬝ᵥ x := fun x => rfl
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by rw [hL, dotProduct_smul, h]; simp⟩
  have hdim : Module.finrank ℂ (LinearMap.ker L) = m := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  let bN := Module.finBasisOfFinrankEq ℂ (LinearMap.ker L) hdim
  have hli : ∀ (c : ℂ), ∀ x ∈ LinearMap.ker L, c • v + x = 0 → c = 0 := by
    intro c x hx hc
    have := congrArg L hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hL v, h, map_zero] at this
    simpa using this
  have hsp : ∀ z : Fin (m + 1) → ℂ, ∃ c : ℂ, z + c • v ∈ LinearMap.ker L := by
    intro z
    refine ⟨-(L z), ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hL v, h]
    simp
  let b := Module.Basis.mkFinCons v bN hli hsp
  have hb : ⇑b = Fin.cons v (Subtype.val ∘ bN) := Module.Basis.coe_mkFinCons v bN hli hsp
  let e := Pi.basisFun ℂ (Fin (m + 1))
  have hcoord : b.coord 0 = L := by
    refine b.ext fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Basis.coord_apply, Basis.repr_self, hb]
      simp [hL, h]
    · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      have hmem : b k.succ ∈ LinearMap.ker L := by
        rw [hb]; simp
      rw [LinearMap.mem_ker.mp hmem]
      simp [Fin.succ_ne_zero]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip e b, ?_, ?_⟩
  · intro i
    rw [Basis.toMatrix_apply, hb]
    simp [e]
  · intro j
    rw [Basis.toMatrix_apply]
    have := congrArg (fun f : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ => f (e j)) hcoord
    simp only [Basis.coord_apply] at this
    rw [this, hL]
    simp [e, dotProduct_single]

end GlobalTheory
