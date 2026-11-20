import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
open MeasureTheory Matrix
open scoped Classical

noncomputable section
open Polynomial

namespace GlobalTheory.OrbDesc

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial n c`. Rewrite using `[aeval_monomial]`.

Conclude with `(Algebra.commute_algebraMap_right c F).mul_right (h.pow_right n)`.
-/
theorem commute_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F f : Module.End K V} (h : Commute F f) (p : K[X]) : Commute F (aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c F).mul_right (h.pow_right n)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hp` to reduce the goal to its premises. Rewrite using `[Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hp0]`. Simplify using `only [Nat.cast_eq_zero]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_pos_of_not_isUnit {K : Type} [Field K] {p : K[X]} (hp0 : p ≠ 0)
    (hp : ¬ IsUnit p) : 0 < p.natDegree := by
  by_contra h
  push_neg at h
  apply hp
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hp0]
  simp only [Nat.cast_eq_zero]
  omega

/- English proof (translation)
Introduce `K _ ι _ _ _ γ hsep hirr`. Use `set M : Matrix ι ι K := (γ : Matrix ι ι K) with hMdef`. Establish `hχ0 : M.charpoly ≠ 0` using `M.charpoly_monic.ne_zero`. Establish `hχu : ¬ IsUnit M.charpoly`. Introduce `hu`.

Establish `h1` using `Polynomial.natDegree_eq_zero_of_isUnit hu`. Rewrite `h1` using `[Matrix.charpoly_natDegree_eq_dim]`. Conclude with `Fintype.card_ne_zero h1`. Choose the witnesses or unpack the hypotheses as in `⟨p, q, hpq, hp, hq⟩ : ∃ p q, M.charpoly = p * q ∧ ¬ IsUnit p ∧ ¬ IsUnit q := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hirr (irreducible_iff.mpr ⟨hχu, fun p q h => by`. Assume the negation of the conclusion as `h'`. Use `push_neg at h'`. Conclude with `h'.2 (hc p q h h'.1)⟩)`.

Establish `hcop : IsCoprime p q` using `(hpq ▸ hsep).isCoprime`. Establish `hp0 : p ≠ 0` using `by rintro rfl; rw [zero_mul] at hpq; exact hχ0 hpq`. Establish `hq0 : q ≠ 0` using `by rintro rfl; rw [mul_zero] at hpq; exact hχ0 hpq`. Establish `hpd` using `natDegree_pos_of_not_isUnit hp0 hp`. Establish `hqd` using `natDegree_pos_of_not_isUnit hq0 hq`.

Set `f : Module.End K (ι → K)` to `Matrix.toLin' M`. Establish `haev : ∀ r : K[X], aeval f r = Matrix.toLin' (aeval M r)` using `fun r => aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) M r`. Establish `hχf : aeval f M.charpoly = 0` using `by rw [haev, Matrix.aeval_self_charpoly, map_zero]`. Use `set V₁ := LinearMap.ker (aeval f p) with hV₁`. Use `set V₂ := LinearMap.ker (aeval f q) with hV₂`.

Establish `hc : IsCompl V₁ V₂` using `⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, by`. Rewrite using `[codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ← hpq, hχf, LinearMap.ker_zero]⟩`. Establish `hcharf : LinearMap.charpoly f = M.charpoly` using `Matrix.charpoly_toLin' M`. Establish `hdvd : M.charpoly ∣ minpoly K f`. Use `GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable f (by rw [hcharf]; exact hsep)` as an intermediate fact.

Rewrite `this` using `[hcharf]`. Then use the resulting hypothesis. Establish `hV1 : V₁ ≠ ⊥`. Introduce `h`. Establish `h2 : V₂ = ⊤`. Use `hc.sup_eq_top` as an intermediate fact.

Rewrite `this` using `[h, bot_sup_eq]`. Then use the resulting hypothesis. Establish `h3 : aeval f q = 0` using `LinearMap.ker_eq_top.mp h2`. Establish `h4` using `Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hq0`. Rewrite `h4` using `[hpq, Polynomial.natDegree_mul hp0 hq0]`. Use linear arithmetic over natural numbers and integers.

Establish `hV2 : V₂ ≠ ⊥`. Introduce `h`. Establish `h2 : V₁ = ⊤`. Use `hc.sup_eq_top` as an intermediate fact. Rewrite `this` using `[h, sup_bot_eq]`. Then use the resulting hypothesis.

Establish `h3 : aeval f p = 0` using `LinearMap.ker_eq_top.mp h2`. Establish `h4` using `Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hp0`. Rewrite `h4` using `[hpq, Polynomial.natDegree_mul hp0 hq0]`. Use linear arithmetic over natural numbers and integers. Set `φ` to `Submodule.prodEquivOfIsCompl V₁ V₂ hc`.

Set `b1` to `Module.finBasis K V₁`. Set `b2` to `Module.finBasis K V₂`. Set `b0` to `(b1.prod b2).map φ`. Set `e : ι ≃ Fin (Module.finrank K V₁) ⊕ Fin (Module.finrank K V₂)` to `(b0.indexEquiv (Pi.basisFun K ι)).symm`. Set `bb` to `b0.reindex e.symm`.

Establish `hbb : ∀ i, bb i = b0 (e i)` using `fun i => by`. Simplify using `[bb, Module.Basis.reindex_apply]`. Establish `hbbr : ∀ v i, bb.repr v i = b0.repr v (e i)` using `fun v i => by`. Simplify using `[bb, Module.Basis.repr_reindex_apply]`. Establish `hmem1 : ∀ k, b0 (Sum.inl k) ∈ V₁` using `fun k => by`.

Simplify using `[b0, φ, Submodule.coe_prodEquivOfIsCompl']`. Establish `hmem2 : ∀ k, b0 (Sum.inr k) ∈ V₂` using `fun k => by`. Simplify using `[b0, φ, Submodule.coe_prodEquivOfIsCompl']`. Establish `hrep1 : ∀ v ∈ V₁, ∀ k, b0.repr v (Sum.inr k) = 0` using `fun v hv k => by`. Establish `: φ.symm v = (⟨v, hv⟩, 0)` using `Submodule.prodEquivOfIsCompl_symm_apply_left V₁ V₂ hc ⟨v, hv⟩`.

Simplify using `[b0, Module.Basis.map_repr, this]`. Establish `hrep2 : ∀ v ∈ V₂, ∀ k, b0.repr v (Sum.inl k) = 0` using `fun v hv k => by`. Establish `: φ.symm v = (0, ⟨v, hv⟩)` using `Submodule.prodEquivOfIsCompl_symm_apply_right V₁ V₂ hc ⟨v, hv⟩`. Simplify using `[b0, Module.Basis.map_repr, this]`. Set `std` to `Pi.basisFun K ι`.

Set `c : GL ι K` to `⟨std.toMatrix bb, bb.toMatrix std, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩`. Use `⟨_, _, e, Module.finrank_pos_iff.mpr ?_, Module.finrank_pos_iff.mpr ?_, c, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.nontrivial_iff_ne_bot.mpr hV1`. Conclude with `Submodule.nontrivial_iff_ne_bot.mpr hV2`. Introduce `g hg`.

Establish `hg' : g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g` using `hg`. Establish `hN : (c * g * c⁻¹) * γ = γ * (c * g * c⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Set `F : Module.End K (ι → K)` to `Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)`. Establish `hC : Commute F f` using `by show Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) ∘ₗ Matrix.toLin' (γ : Matrix ι ι K) = Matrix.toLin' (γ : Matrix ι ι K) ∘ₗ Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)`.

Rewrite using `[← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hN]`. Establish `hF1 : ∀ v ∈ V₁, F v ∈ V₁` using `fun v hv => by`. Rewrite `hv`, the goal using `[hV₁, LinearMap.mem_ker]`. Use `LinearMap.congr_fun (commute_aeval_of_commute hC p).eq v` as an intermediate fact. Simplify using `only [Module.End.mul_apply, hv, map_zero] at this`.

Conclude with `this.symm`. Establish `hF2 : ∀ v ∈ V₂, F v ∈ V₂` using `fun v hv => by`. Rewrite `hv`, the goal using `[hV₂, LinearMap.mem_ker]`. Use `LinearMap.congr_fun (commute_aeval_of_commute hC q).eq v` as an intermediate fact. Simplify using `only [Module.End.mul_apply, hv, map_zero] at this`.

Conclude with `this.symm`. Establish `hg2 : g = c⁻¹ * (c * g * c⁻¹) * c` using `by group`. Establish `hgm : (g : Matrix ι ι K) = bb.toMatrix std * ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) * std.toMatrix bb` using `by conv_lhs => rw [hg2]`. Both sides reduce to the same expression. Establish `hgF : (g : Matrix ι ι K) = LinearMap.toMatrix bb bb F`.

Rewrite using `[hgm, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bb std bb std F, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Establish `hz : ∀ i j, side e i ≠ side e j → (g : Matrix ι ι K) i j = 0`. Introduce `i j hij`. Rewrite using `[hgF, LinearMap.toMatrix_apply, hbb, hbbr]`. Consider the cases of `hi : e i with`.

Consider the case `inl k`. Consider the cases of `hj : e j with`. Consider the case `inl k' => simp [side, hi, hj] at hij`. Consider the case `inr k' => exact hrep2 _ (hF2 _ (hmem2 k')) k`. Consider the case `inr k`.

Consider the cases of `hj : e j with`. Consider the case `inl k' => exact hrep1 _ (hF1 _ (hmem1 k')) k`. Consider the case `inr k' => simp [side, hi, hj] at hij`. Use `Subgroup.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `show (g : Matrix ι ι K).BlockTriangular (side e)`.

Introduce `i j hlt`. Apply `hz` to reduce the goal to its premises. Introduce `heq`. Rewrite `hlt` using `[heq]`. Conclude with `lt_irrefl _ hlt`.

Use `show (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))`. Introduce `i j hlt`. Apply `hz` to reduce the goal to its premises. Introduce `heq`. Simplify using `only [] at hlt`.

Rewrite `hlt` using `[heq]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem exists_conj_cent_le_blockLevi : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (γ : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∃ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a ∧ 0 < b ∧ ∃ c : GL ι K,
    GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) (c⁻¹ * γ * c) ≤ GlobalTheory.OrbDesc.blockLevi e := by
  intro K _ ι _ _ _ γ hsep hirr
  set M : Matrix ι ι K := (γ : Matrix ι ι K) with hMdef
  have hχ0 : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  have hχu : ¬ IsUnit M.charpoly := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    exact Fintype.card_ne_zero h1
  obtain ⟨p, q, hpq, hp, hq⟩ : ∃ p q, M.charpoly = p * q ∧ ¬ IsUnit p ∧ ¬ IsUnit q := by
    by_contra hc
    push_neg at hc
    exact hirr (irreducible_iff.mpr ⟨hχu, fun p q h => by
      by_contra h'
      push_neg at h'
      exact h'.2 (hc p q h h'.1)⟩)
  have hcop : IsCoprime p q := (hpq ▸ hsep).isCoprime
  have hp0 : p ≠ 0 := by rintro rfl; rw [zero_mul] at hpq; exact hχ0 hpq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hχ0 hpq
  have hpd := natDegree_pos_of_not_isUnit hp0 hp
  have hqd := natDegree_pos_of_not_isUnit hq0 hq
  let f : Module.End K (ι → K) := Matrix.toLin' M
  have haev : ∀ r : K[X], aeval f r = Matrix.toLin' (aeval M r) := fun r =>
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) M r
  have hχf : aeval f M.charpoly = 0 := by rw [haev, Matrix.aeval_self_charpoly, map_zero]
  set V₁ := LinearMap.ker (aeval f p) with hV₁
  set V₂ := LinearMap.ker (aeval f q) with hV₂
  have hc : IsCompl V₁ V₂ := ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, by
    rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ← hpq, hχf,
      LinearMap.ker_zero]⟩
  have hcharf : LinearMap.charpoly f = M.charpoly := Matrix.charpoly_toLin' M
  have hdvd : M.charpoly ∣ minpoly K f := by
    have := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable f (by rw [hcharf]; exact hsep)
    rwa [hcharf] at this
  have hV1 : V₁ ≠ ⊥ := by
    intro h
    have h2 : V₂ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, bot_sup_eq] at this
    have h3 : aeval f q = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hq0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  have hV2 : V₂ ≠ ⊥ := by
    intro h
    have h2 : V₁ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this
    have h3 : aeval f p = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hp0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  let φ := Submodule.prodEquivOfIsCompl V₁ V₂ hc
  let b1 := Module.finBasis K V₁
  let b2 := Module.finBasis K V₂
  let b0 := (b1.prod b2).map φ
  let e : ι ≃ Fin (Module.finrank K V₁) ⊕ Fin (Module.finrank K V₂) :=
    (b0.indexEquiv (Pi.basisFun K ι)).symm
  let bb := b0.reindex e.symm
  have hbb : ∀ i, bb i = b0 (e i) := fun i => by
    simp [bb, Module.Basis.reindex_apply]
  have hbbr : ∀ v i, bb.repr v i = b0.repr v (e i) := fun v i => by
    simp [bb, Module.Basis.repr_reindex_apply]
  have hmem1 : ∀ k, b0 (Sum.inl k) ∈ V₁ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hmem2 : ∀ k, b0 (Sum.inr k) ∈ V₂ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hrep1 : ∀ v ∈ V₁, ∀ k, b0.repr v (Sum.inr k) = 0 := fun v hv k => by
    have : φ.symm v = (⟨v, hv⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  have hrep2 : ∀ v ∈ V₂, ∀ k, b0.repr v (Sum.inl k) = 0 := fun v hv k => by
    have : φ.symm v = (0, ⟨v, hv⟩) := Submodule.prodEquivOfIsCompl_symm_apply_right V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  let std := Pi.basisFun K ι
  let c : GL ι K := ⟨std.toMatrix bb, bb.toMatrix std,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨_, _, e, Module.finrank_pos_iff.mpr ?_, Module.finrank_pos_iff.mpr ?_, c, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV1
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV2
  intro g hg
  have hg' : g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g := hg
  have hN : (c * g * c⁻¹) * γ = γ * (c * g * c⁻¹) := by
    calc (c * g * c⁻¹) * γ = c * (g * (c⁻¹ * γ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * γ * c) * g) * c⁻¹ := by rw [hg']
      _ = γ * (c * g * c⁻¹) := by group
  let F : Module.End K (ι → K) := Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
  have hC : Commute F f := by
    show Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) ∘ₗ Matrix.toLin' (γ : Matrix ι ι K)
      = Matrix.toLin' (γ : Matrix ι ι K) ∘ₗ Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hN]
  have hF1 : ∀ v ∈ V₁, F v ∈ V₁ := fun v hv => by
    rw [hV₁, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC p).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hF2 : ∀ v ∈ V₂, F v ∈ V₂ := fun v hv => by
    rw [hV₂, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC q).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hg2 : g = c⁻¹ * (c * g * c⁻¹) * c := by group
  have hgm : (g : Matrix ι ι K) = bb.toMatrix std * ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) * std.toMatrix bb := by
    conv_lhs => rw [hg2]
    rfl
  have hgF : (g : Matrix ι ι K) = LinearMap.toMatrix bb bb F := by
    rw [hgm, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bb std bb std F,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hz : ∀ i j, side e i ≠ side e j → (g : Matrix ι ι K) i j = 0 := by
    intro i j hij
    rw [hgF, LinearMap.toMatrix_apply, hbb, hbbr]
    cases hi : e i with
    | inl k =>
      cases hj : e j with
      | inl k' => simp [side, hi, hj] at hij
      | inr k' => exact hrep2 _ (hF2 _ (hmem2 k')) k
    | inr k =>
      cases hj : e j with
      | inl k' => exact hrep1 _ (hF1 _ (hmem1 k')) k
      | inr k' => simp [side, hi, hj] at hij
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show (g : Matrix ι ι K).BlockTriangular (side e)
    intro i j hlt
    apply hz
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · show (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))
    intro i j hlt
    apply hz
    intro heq
    simp only [] at hlt
    rw [heq] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.OrbDesc
