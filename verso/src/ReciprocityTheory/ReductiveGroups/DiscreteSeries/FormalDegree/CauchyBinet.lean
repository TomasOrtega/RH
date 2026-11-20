import Mathlib
import Lemmata.GeneralBFact.Imports

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma cauchyBinet_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  first | exact Bl.general_b_fact.goal1 .. | (apply Bl.general_b_fact.goal1 <;> assumption) | (intros; apply Bl.general_b_fact.goal1 <;> assumption)

private def cauchyBinetPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private lemma cauchyBinetPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cauchyBinetPar ⟨⟨S, hS⟩, σ⟩) = S := by
  ext x
  simp only [cauchyBinetPar, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem S hS _
  · intro hx
    have : x ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨b, rfl⟩ := this
    exact ⟨σ.symm b, by simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Substitute using the available equality.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma cauchyBinetPar_bij {i N : ℕ} : Function.Bijective (cauchyBinetPar (i := i) (N := N)) := by
  constructor
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h
    have hST : S = T := by
      rw [← cauchyBinetPar_image S hS σ, ← cauchyBinetPar_image T hT τ, h]
    subst hST
    have : σ = τ := by
      ext a
      have h2 := DFunLike.congr_fun h a
      simp only [cauchyBinetPar, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        RelEmbedding.coe_toEmbedding] at h2
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst this
    rfl
  · intro f
    have hS : (univ.map f).card = i := by simp
    have hmem : ∀ a, f a ∈ Set.range ((univ.map f).orderEmbOfFin hS) := by
      intro a
      rw [Finset.range_orderEmbOfFin]; simp
    choose τ hτ using hmem
    have hinj : Function.Injective τ := by
      intro a b hab
      apply f.injective
      rw [← hτ a, ← hτ b, hab]
    refine ⟨⟨⟨univ.map f, hS⟩, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)⟩, ?_⟩
    ext a
    simp [cauchyBinetPar, hτ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cauchyBinet {m i : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin i) (Fin m) R)
    (B : Matrix (Fin m) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin m) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  rw [cauchyBinet_det_mul_fun]
  set F : (Fin i → Fin m) → R := fun f => (∏ a, A a (f a)) * (B.submatrix f id).det with hF
  have h1 : ∑ f : Fin i → Fin m, F f = ∑ f : Fin i ↪ Fin m, F f := by
    have h0 : ∀ f : Fin i → Fin m, ¬ Function.Injective f → F f = 0 := by
      intro f hf
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨a, b, hab, hne⟩ := hf
      have : (B.submatrix f id).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hab])
      simp [hF, this]
    rw [← Finset.sum_filter_of_ne (p := Function.Injective) (s := univ) (f := F)
      (fun f _ hne => by by_contra hc; exact hne (h0 f hc))]
    symm
    apply Finset.sum_bij (fun (f : Fin i ↪ Fin m) _ => (f : Fin i → Fin m))
    · intro f _; simp [f.injective]
    · intro f _ g _ h; exact DFunLike.coe_injective h
    · intro f hf
      exact ⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _; rfl
  rw [h1, ← Function.Bijective.sum_comp cauchyBinetPar_bij (fun f => F f), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  rintro ⟨S, hS⟩ _
  set e := S.orderEmbOfFin hS with he
  have h2 : ∀ σ : Equiv.Perm (Fin i), F (cauchyBinetPar ⟨⟨S, hS⟩, σ⟩) =
      (Equiv.Perm.sign σ : R) * (∏ a, A a (e (σ a))) * (B.submatrix e id).det := by
    intro σ
    have h3 : (B.submatrix (fun a => e (σ a)) id).det =
        (Equiv.Perm.sign σ : R) * (B.submatrix e id).det := by
      have := Matrix.det_permute σ (B.submatrix e id)
      rw [← this]; rfl
    show (∏ a, A a (e (σ a))) * (B.submatrix (fun a => e (σ a)) id).det = _
    rw [h3]; ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  congr 1
  rw [Matrix.det_apply', ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin i)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.submatrix_apply, id]
  congr 1
  rw [← Equiv.prod_comp σ]
  simp

end ReciprocityTheory.ChartRestriction.DS
