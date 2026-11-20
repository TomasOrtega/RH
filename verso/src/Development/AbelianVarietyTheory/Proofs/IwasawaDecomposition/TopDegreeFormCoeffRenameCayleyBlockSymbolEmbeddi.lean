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
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Substitute using the available equality. Both sides reduce to the same expression.
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
Simplify using the standard rewrite rules.
-/
theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
