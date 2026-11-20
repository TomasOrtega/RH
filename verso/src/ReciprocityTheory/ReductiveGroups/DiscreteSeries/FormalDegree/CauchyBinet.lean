import Mathlib
import Lemmata.GeneralBFact.Imports

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact.goal1 .. | (apply Bl.general_b_fact.goal1 <;> assumption) | (intros; apply Bl.general_b_fact.goal1 <;> assumption)`.
-/
private lemma cauchyBinet_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  first | exact Bl.general_b_fact.goal1 .. | (apply Bl.general_b_fact.goal1 <;> assumption) | (intros; apply Bl.general_b_fact.goal1 <;> assumption)

private def cauchyBinetPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [cauchyBinetPar, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `Finset.orderEmbOfFin_mem S hS _`.

Introduce `hx`. Establish `: x ∈ Set.range (S.orderEmbOfFin hS)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hx`. Take `⟨b, rfl⟩` from `this`.

Conclude with `⟨σ.symm b, by simp⟩`.
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
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h`. Establish `hST : S = T`. Rewrite using `[← cauchyBinetPar_image S hS σ, ← cauchyBinetPar_image T hT τ, h]`. Substitute `hST` using the available equality.

Establish `: σ = τ`. Use extensionality with `a`. Establish `h2` using `DFunLike.congr_fun h a`. Simplify using `only [cauchyBinetPar, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding] at h2`. Conclude with `congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)`.

Substitute `this` using the available equality. Both sides reduce to the same expression. Introduce `f`. Establish `hS : (univ.map f).card = i` using `by simp`. Establish `hmem : ∀ a, f a ∈ Set.range ((univ.map f).orderEmbOfFin hS)`.

Introduce `a`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using the standard rewrite rules. Use `choose τ hτ using hmem`. Establish `hinj : Function.Injective τ`.

Introduce `a b hab`. Apply `f.injective` to reduce the goal to its premises. Rewrite using `[← hτ a, ← hτ b, hab]`. Use `⟨⟨⟨univ.map f, hS⟩, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Simplify using `[cauchyBinetPar, hτ]`.
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
Rewrite using `[cauchyBinet_det_mul_fun]`. Use `set F : (Fin i → Fin m) → R := fun f => (∏ a, A a (f a)) * (B.submatrix f id).det with hF`. Establish `h1 : ∑ f : Fin i → Fin m, F f = ∑ f : Fin i ↪ Fin m, F f`. Establish `h0 : ∀ f : Fin i → Fin m, ¬ Function.Injective f → F f = 0`. Introduce `f hf`.

Simplify using `only [Function.Injective, not_forall] at hf`. Take `⟨a, b, hab, hne⟩` from `hf`. Establish `: (B.submatrix f id).det = 0` using `Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hab])`. Simplify using `[hF, this]`. Rewrite using `[← Finset.sum_filter_of_ne (p := Function.Injective) (s := univ) (f := F) (fun f _ hne => by by_contra hc; exact hne (h0 f hc))]`.

Use `symm`. Apply `Finset.sum_bij (fun (f : Fin i ↪ Fin m) _ => (f : Fin i → Fin m))` to reduce the goal to its premises. Introduce `f _`. Simplify using `[f.injective]`. Introduce `f _ g _ h`.

Conclude with `DFunLike.coe_injective h`. Introduce `f hf`. Conclude with `⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩`. Introduce `f _`. Both sides reduce to the same expression.

Rewrite using `[h1, ← Function.Bijective.sum_comp cauchyBinetPar_bij (fun f => F f), Fintype.sum_sigma]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce and unpack `⟨S, hS⟩ _`. Use `set e := S.orderEmbOfFin hS with he`. Establish `h2 : ∀ σ : Equiv.Perm (Fin i), F (cauchyBinetPar ⟨⟨S, hS⟩, σ⟩) = (Equiv.Perm.sign σ : R) * (∏ a, A a (e (σ a))) * (B.submatrix e id).det`.

Introduce `σ`. Establish `h3 : (B.submatrix (fun a => e (σ a)) id).det = (Equiv.Perm.sign σ : R) * (B.submatrix e id).det`. Use `Matrix.det_permute σ (B.submatrix e id)` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.

Use `show (∏ a, A a (e (σ a))) * (B.submatrix (fun a => e (σ a)) id).det = _`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[h2]`. Rewrite using `[← Finset.sum_mul]`.

Use `congr 1`. Rewrite using `[Matrix.det_apply', ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin i)))]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `σ _`. Simplify using `only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.submatrix_apply, id]`.

Use `congr 1`. Rewrite using `[← Equiv.prod_comp σ]`. Simplify using the standard rewrite rules.
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
