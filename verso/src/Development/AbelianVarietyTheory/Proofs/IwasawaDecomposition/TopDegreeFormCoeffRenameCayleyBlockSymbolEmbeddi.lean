import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

namespace TopRename

variable {p q : ℕ} (hc : Fintype.card (Unit × Fin p × Fin q) = p * q)

def idx : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.punitProd (Fin p × Fin q)).symm.trans (Fintype.equivFinOfCardEq hc)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockEmb_eq (x : Fin q × Fin p × Fin p) :
    blockEmb hc x = (idx hc (x.2.1, x.1), idx hc (x.2.2, x.1)) := rfl

/- English proof (translation)
Introduce and unpack `⟨b, i, j⟩ ⟨b', i', j'⟩ h`. Simplify using `only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h`. Take `⟨⟨e1, e2⟩, ⟨e3, -⟩⟩` from `h`. Substitute `e1 e2 e3` using the available equality. Both sides reduce to the same expression.
-/
theorem blockEmb_injective : Function.Injective (blockEmb hc) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  simp only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩⟩ := h
  subst e1 e2 e3
  rfl

def permOf (τ : Fin q → Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p * q)) :=
  (idx hc).permCongr (Equiv.prodCongrLeft fun b => (τ b)⁻¹)

/- English proof (translation)
Simplify using `[permOf, Equiv.permCongr_apply]`.
-/
theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

/- English proof (translation)
Rewrite using `[permOf_apply']`. Simplify using the standard rewrite rules.
-/
theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

/- English proof (translation)
Simplify using `[permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]`.
-/
theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

/- English proof (translation)
Introduce `τ τ' e`. Use function extensionality and compare the values at `b`. Establish `h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j`. Introduce `j`. Use `congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e` as an intermediate fact.

Simplify using `only [permOf_apply'] at this`. Conclude with `congrArg Prod.fst ((idx hc).injective this)`. Conclude with `inv_inj.mp (Equiv.ext h)`.
-/
theorem permOf_injective : Function.Injective (permOf hc) := by
  intro τ τ' e
  funext b
  have h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j := by
    intro j
    have := congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e
    simp only [permOf_apply'] at this
    exact congrArg Prod.fst ((idx hc).injective this)
  exact inv_inj.mp (Equiv.ext h)

/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[blockGraph, Finsupp.mapDomain_finset_sum]`. Repeatedly rewrite using `[Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single, blockEmb_eq]`. Rewrite using `[← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[permOf_apply]`.
-/
theorem graph_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    (∑ a, Finsupp.single (a, permOf hc τ a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) =
      (blockGraph τ).mapDomain (blockEmb hc) := by
  rw [blockGraph, Finsupp.mapDomain_finset_sum]
  simp_rw [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single, blockEmb_eq]
  rw [← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  simp [permOf_apply]

/- English proof (translation)
Establish `hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2`. Introduce `x`. Establish `h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0`. Rewrite using `[graph_apply' (fun a => w a)]`. Simplify using the standard rewrite rules.

Rewrite `h0` using `[← h]`. Assume the negation of the conclusion as `hne`. Apply `h0` to reduce the goal to its premises. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨⟨b, i, j⟩, hy⟩`.

Rewrite `hy` using `[blockEmb_eq, Prod.mk.injEq]`. Apply `hne` to reduce the goal to its premises. Establish `hx : x = (i, b)` using `((idx hc).injective hy.1).symm`. Rewrite using `[← hy.2, Equiv.symm_apply_apply, hx]`. Set `f : Fin q → Fin p → Fin p` to `fun b i => ((idx hc).symm (w (idx hc (i, b)))).1`.

Establish `hf : ∀ b, Function.Injective (f b)`. Introduce `b i i' e`. Establish `: (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b)))` using `Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)`. Simplify using `using this`. Set `σ : Fin q → Equiv.Perm (Fin p)` to `fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))`.

Use `⟨fun b => (σ b)⁻¹, ?_⟩` and prove the remaining obligations. Use `ext1 a`. Take `⟨⟨i, b⟩, rfl⟩` from `(idx hc).surjective a`. Rewrite using `[permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]`. Use `congr 1`.

Conclude with `Prod.ext rfl (hr (i, b)).symm`.
-/
theorem mem_range_of_graph (w : Equiv.Perm (Fin (p * q))) (u : Fin q × Fin p × Fin p →₀ ℕ)
    (h : u.mapDomain (blockEmb hc) = ∑ a, Finsupp.single (a, w a) 1) : ∃ τ, permOf hc τ = w := by
  have hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2 := by
    intro x
    have h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0 := by
      rw [graph_apply' (fun a => w a)]
      simp
    rw [← h] at h0
    by_contra hne
    apply h0
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨b, i, j⟩, hy⟩
    rw [blockEmb_eq, Prod.mk.injEq] at hy
    apply hne
    have hx : x = (i, b) := ((idx hc).injective hy.1).symm
    rw [← hy.2, Equiv.symm_apply_apply, hx]
  let f : Fin q → Fin p → Fin p := fun b i => ((idx hc).symm (w (idx hc (i, b)))).1
  have hf : ∀ b, Function.Injective (f b) := by
    intro b i i' e
    have : (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b))) :=
      Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)
    simpa using this
  let σ : Fin q → Equiv.Perm (Fin p) := fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))
  refine ⟨fun b => (σ b)⁻¹, ?_⟩
  ext1 a
  obtain ⟨⟨i, b⟩, rfl⟩ := (idx hc).surjective a
  rw [permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]
  congr 1
  exact Prod.ext rfl (hr (i, b)).symm

end TopRename

open TopRename in

/- English proof (translation)
Introduce `p q h1 G`. Rewrite using `[GlobalTheory.GoodMetric.topCoeff]`. Use `symm`. Use `Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_` and prove the remaining obligations. Introduce `w hw`.

Rewrite using `[coeff_rename_eq_zero, mul_zero]`. Introduce `u hu`. Take `⟨τ, rfl⟩` from `mem_range_of_graph h1 w u hu`. Conclude with `absurd ⟨τ, rfl⟩ hw`. Introduce `τ`.

Rewrite using `[graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]`.
-/
theorem topCoeff_rename_blockEmb : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q)
    (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) =
      ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * coeff (blockGraph τ) G := by
  intro p q h1 G
  rw [GlobalTheory.GoodMetric.topCoeff]
  symm
  refine Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_
  · intro w hw
    rw [coeff_rename_eq_zero, mul_zero]
    intro u hu
    obtain ⟨τ, rfl⟩ := mem_range_of_graph h1 w u hu
    exact absurd ⟨τ, rfl⟩ hw
  · intro τ
    rw [graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]

end GlobalTheory.CayleyBlock
