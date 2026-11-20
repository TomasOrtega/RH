import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.TwoFormSum

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def coordPair (f g : Module.Dual B Ω[B⁄R]) : Module.Dual B (Om R B 2) :=
  exteriorPower.pairingDual B Ω[B⁄R] 2 (exteriorPower.ιMulti B 2 ![f, g])

/- English proof (translation)
Rewrite using `[wedge_eq_ιMulti, coordPair, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]`. Simplify using the standard rewrite rules.
-/
theorem coordPair_wedge (f g : Module.Dual B Ω[B⁄R]) (a b : Ω[B⁄R]) :
    coordPair f g (wedge R B a b) = f a * g b - g a * f b := by
  rw [wedge_eq_ιMulti, coordPair, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

/- English proof (translation)
Rewrite using `[wedge_eq_ιMulti]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem ιMulti_two (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by
  rw [wedge_eq_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h, not_lt.2 h.le]`. Substitute `h` using the available equality.

Simplify using `[hg]`. Simplify using `[h, not_lt.2 h.le]`. Use `_ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib`.

Use `_ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by`. Rewrite using `[Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]`. Use `_ = _ := by`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sum_sum_eq_lt {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, not_lt.2 h.le]
        · subst h; simp [hg]
        · simp [h, not_lt.2 h.le]
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by
        rw [Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

def expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) : Om R B 2 →ₗ[B] Om R B 2 :=
  ∑ i, ∑ j, if i < j then (coordPair (δ i) (δ j)).smulRight (wedge R B (w i) (w j)) else 0

/- English proof (translation)
Simplify using `only [expand, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem expand_apply {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) (x : Om R B 2) :
    expand w δ x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  simp only [expand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← expand_apply]`. Establish `hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M` using `Ω[B⁄R]))) := by`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Establish `hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)` using `by conv_lhs => rw [hs (v 0), hs (v 1)]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Rewrite using `[ιMulti_two, expand_apply]`. Use `conv_lhs => rw [hL, sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]`. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add, ← hy, ← hz]`. Consider the case `smul c y _ hy => rw [map_smul, ← hy]`.
-/
theorem eq_expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  rw [← expand_apply]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M := Ω[B⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j) := by
      conv_lhs => rw [hs (v 0), hs (v 1)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    rw [ιMulti_two, expand_apply]
    conv_lhs => rw [hL,
      sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]; abel
    · simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, ← hy, ← hz]
  | smul c y _ hy => rw [map_smul, ← hy]

end Alg

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Establish `hx : x ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M` using `Ω[F.obj T⁄R]))) := by`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨v, rfl⟩` from `hy`. Rewrite using `[ιMulti_two, pOm_wedge, coordPair_wedge, coordPair_wedge, Φ.nat, Φ.nat, Φ.nat, Φ.nat]`. Simplify using `only [map_sub, map_mul]`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => simp only [map_add, hy, hz]`.

Consider the case `smul c y _ hy => rw [pOm_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]`.
-/
theorem coordPair_nat {n : ℕ} (Φ : Frame F n) (i j : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (x : Om R (F.obj T) 2) :
    coordPair (Φ.δ i T') (Φ.δ j T') (pOm F 2 φ x) = mp F φ (coordPair (Φ.δ i T) (Φ.δ j T) x) := by
  have hx : x ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ιMulti_two, pOm_wedge, coordPair_wedge, coordPair_wedge, Φ.nat, Φ.nat, Φ.nat, Φ.nat]
    simp only [map_sub, map_mul]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul c y _ hy => rw [pOm_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.AbCoh.TwoFormSum

namespace GlobalTheory.AbCoh

open TwoFormSum in

/- English proof (translation)
Introduce `R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ`. Set `g : Fin n → Fin n → C0 F` to `fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)`. Establish `hg : ∀ i j, d0 F (g i j) = 0`. Introduce `i j`. Use function extensionality and compare the values at `T T' φ`.

Rewrite using `[amitsur_d0_apply]`. Simplify using `only [g]`. Rewrite using `[hζ φ, coordPair_nat, sub_self]`. Both sides reduce to the same expression. Use `choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists`.

Set `e : Fin (n * n) ≃ Fin n × Fin n` to `finProdFinEquiv.symm`. Use `⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1, fun k ↦ Φ.w (e k).2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T`. Simplify using `only [wsum]`. Rewrite using `[Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T) (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl), Fintype.sum_prod_type]`.

Use `conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]`. Use `split_ifs`. Use `hc i j T` as an intermediate fact.

Simplify using `only [g] at this`. Rewrite using `[this, algebraMap_smul]`. Simplify using the standard rewrite rules.
-/
theorem twoForm_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) →
      ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  intro R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ
  let g : Fin n → Fin n → C0 F := fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)
  have hg : ∀ i j, d0 F (g i j) = 0 := by
    intro i j
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [g]
    rw [hζ φ, coordPair_nat, sub_self]
    rfl
  choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  refine ⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1,
    fun k ↦ Φ.w (e k).2, ?_⟩
  funext T
  simp only [wsum]
  rw [Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T)
      (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl),
    Fintype.sum_prod_type]
  conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]
  split_ifs
  · have := hc i j T
    simp only [g] at this
    rw [this, algebraMap_smul]
  · simp

end GlobalTheory.AbCoh
