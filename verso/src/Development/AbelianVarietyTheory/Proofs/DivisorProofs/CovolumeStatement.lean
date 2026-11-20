import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetHT.Covol

open Matrix GlobalTheory.LineNorm

/- English proof (translation)
Distinguish the cases in `hσ : Function.Injective σ`. Establish `hb : Function.Bijective σ` using `Finite.injective_iff_bijective.1 hσ`. Set `π : Equiv.Perm (Fin m)` to `Equiv.ofBijective σ hb`. Establish `: g.submatrix id σ = g.submatrix id π` using `rfl`. Rewrite using `[this, Matrix.det_permute', norm_mul]`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, σ i = σ j ∧ i ≠ j := by`. Simplify using `only [Function.Injective, not_forall] at hσ`. Take `⟨i, j, h1, h2⟩` from `hσ`. Conclude with `⟨i, j, h1, h2⟩`.

Rewrite using `[Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]`. Simplify using the standard rewrite rules.
-/
theorem norm_det_col_le {C : Type} [NormedField C] {m : ℕ} (g : Matrix (Fin m) (Fin m) C) (σ : Fin m → Fin m) :
    ‖(g.submatrix id σ).det‖ ≤ ‖g.det‖ := by
  by_cases hσ : Function.Injective σ
  · have hb : Function.Bijective σ := Finite.injective_iff_bijective.1 hσ
    let π : Equiv.Perm (Fin m) := Equiv.ofBijective σ hb
    have : g.submatrix id σ = g.submatrix id π := rfl
    rw [this, Matrix.det_permute', norm_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, σ i = σ j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hσ
      obtain ⟨i, j, h1, h2⟩ := hσ
      exact ⟨i, j, h1, h2⟩
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]
    simp

/- English proof (translation)
Introduce `E _ _ _ H X t C _ _ x Λ m u u' g δ hδ htan _hind hΛ hu hdet`. Set `h : Fin m → Fin m → C` to `fun j i => if i = j then δ else 0`. Establish `hsum : ∀ (b : Fin m → C) (j : Fin m), ∑ i, h j i * b i = δ * b j`. Introduce `b j`. Simplify using `[h, ite_mul]`.

Establish `hh : ∀ c : Fin m → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0` using `fun c hc =>`. Use function extensionality and compare the values at `fun j => by`. Use `hc j` as an intermediate fact. Rewrite `this` using `[hsum]`. Simplify `this` using `[hδ]`.

Establish `hN : ∀ l, GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * g l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}` using `fun l => by`. Rewrite using `[GlobalTheory.LineNorm.WedgeMax.grNorm_eq t htan (P := fun b => ∀ i, ‖δ * b i‖ ≤ 1) hΛ hu l]`. Simplify using `only [hsum]`. Establish `hli : LinearIndependent C g` using `Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hdet))`. Take `⟨hpos, hprod⟩` from `GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor C m (Fin m) h hh m g hli (fun l => GlobalTheory.ShFam.Pad.grNorm t x Λ u l) hN`.

Establish `e` using `hprod m le_rfl`. Establish `key : ∀ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖ = ‖δ‖ ^ m * ‖(g.submatrix id σ).det‖`. Introduce `σ`. Rewrite using `[GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h (σ i)) g le_rfl]`. Establish `: (Matrix.of fun l i => ∑ t, h (σ i) t * g (Fin.castLE le_rfl l) t) = δ • g.submatrix id σ`.

Use extensionality with `l i`. Rewrite using `[Matrix.of_apply, hsum]`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.det_smul, norm_mul, norm_pow, Fintype.card_fin]`. Establish `hsup : (⨆ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖) = ‖δ‖ ^ m * ‖g.det‖` using `by haveI : Nonempty (Fin m → Fin m) := ⟨id⟩`.

Simplify using `only [key]`. Use `le_antisymm (ciSup_le fun σ => ?_) (le_ciSup_of_le (Finite.bddAbove_range _) id ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (norm_det_col_le g σ) (by positivity)`. Simplify using the standard rewrite rules. Rewrite `e` using `[hsup]`.

Simplify using `only [Fin.castLE_rfl, id] at e`. Rewrite using `[← Real.log_prod (fun l _ => (hpos l).ne'), e, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hdet), Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem covol : CovolSt := by
  intro E _ _ _ H X t C _ _ x Λ m u u' g δ hδ htan _hind hΛ hu hdet
  let h : Fin m → Fin m → C := fun j i => if i = j then δ else 0
  have hsum : ∀ (b : Fin m → C) (j : Fin m), ∑ i, h j i * b i = δ * b j := by
    intro b j
    simp [h, ite_mul]
  have hh : ∀ c : Fin m → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0 := fun c hc =>
    funext fun j => by
      have := hc j
      rw [hsum] at this
      simpa [hδ] using this
  have hN : ∀ l, GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧
      (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * g l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := fun l => by
    rw [GlobalTheory.LineNorm.WedgeMax.grNorm_eq t htan (P := fun b => ∀ i, ‖δ * b i‖ ≤ 1) hΛ hu l]
    simp only [hsum]
  have hli : LinearIndependent C g :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hdet))
  obtain ⟨hpos, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor C m (Fin m) h hh m g hli
    (fun l => GlobalTheory.ShFam.Pad.grNorm t x Λ u l) hN
  have e := hprod m le_rfl
  have key : ∀ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖ =
      ‖δ‖ ^ m * ‖(g.submatrix id σ).det‖ := by
    intro σ
    rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h (σ i)) g le_rfl]
    have : (Matrix.of fun l i => ∑ t, h (σ i) t * g (Fin.castLE le_rfl l) t) = δ • g.submatrix id σ := by
      ext l i
      rw [Matrix.of_apply, hsum]
      simp
    rw [this, Matrix.det_smul, norm_mul, norm_pow, Fintype.card_fin]
  have hsup : (⨆ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖) =
      ‖δ‖ ^ m * ‖g.det‖ := by
    haveI : Nonempty (Fin m → Fin m) := ⟨id⟩
    simp only [key]
    refine le_antisymm (ciSup_le fun σ => ?_) (le_ciSup_of_le (Finite.bddAbove_range _) id ?_)
    · exact mul_le_mul_of_nonneg_left (norm_det_col_le g σ) (by positivity)
    · simp
  rw [hsup] at e
  simp only [Fin.castLE_rfl, id] at e
  rw [← Real.log_prod (fun l _ => (hpos l).ne'), e, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hdet),
    Real.log_pow]
  ring

end GlobalTheory.DetHT.Covol
