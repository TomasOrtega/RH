import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Lemmata.GeneralBFact.Imports

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j)`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[hrow]`. Establish `h1` using `(Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum (fun a j => A a j • B j)`.

Establish `h2 : ∀ f : Fin i → Fin N, (Matrix.detRowAlternating (R` using `R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) = (∏ a, A a (f a)) * (B.submatrix f id).det := by`. Introduce `f`. Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression. Conclude with `h1.trans (Finset.sum_congr rfl fun f _ => h2 f)`.
-/
private lemma cb_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j) := by
    ext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow]
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a j => A a j • B j)
  have h2 : ∀ f : Fin i → Fin N,
      (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) =
        (∏ a, A a (f a)) * (B.submatrix f id).det := by
    intro f
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  exact h1.trans (Finset.sum_congr rfl fun f _ => h2 f)

private def cbPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

/- English proof (translation)
Simplify using `only [cbPar]`. Rewrite using `[← Finset.map_map, Finset.map_univ_equiv]`. Conclude with `Finset.map_orderEmbOfFin_univ S hS`.
-/
private lemma cbPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cbPar ⟨⟨S, hS⟩, σ⟩) = S := by
  simp only [cbPar]
  rw [← Finset.map_map, Finset.map_univ_equiv]
  exact Finset.map_orderEmbOfFin_univ S hS

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h`. Establish `hSS : S = S'`. Rewrite using `[← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]`. Substitute `hSS` using the available equality.

Establish `hσ : σ = σ'`. Use extensionality with `a`. Establish `h2` using `DFunLike.congr_fun h a`. Conclude with `congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)`. Substitute `hσ` using the available equality.

Both sides reduce to the same expression. Introduce `g`. Establish `hcard : (univ.map g).card = i` using `by simp`. Establish `hmem : ∀ a, g a ∈ univ.map g` using `fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)`. Set `g' : Fin i ≃ (univ.map g)` to `Equiv.ofBijective (fun a => ⟨g a, hmem a⟩) ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by`.

Take `⟨a, _, rfl⟩` from `Finset.mem_map.1 hx`. Conclude with `⟨a, rfl⟩⟩`. Use `⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩` and prove the remaining obligations. Use `DFunLike.ext _ _ fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a`.

Rewrite using `[← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]`. Both sides reduce to the same expression.
-/
private lemma cbPar_bij {i N : ℕ} : Function.Bijective (cbPar (i := i) (N := N)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h
    have hSS : S = S' := by
      rw [← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]
    subst hSS
    have hσ : σ = σ' := by
      ext a
      have h2 := DFunLike.congr_fun h a
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst hσ
    rfl
  · intro g
    have hcard : (univ.map g).card = i := by simp
    have hmem : ∀ a, g a ∈ univ.map g := fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)
    let g' : Fin i ≃ (univ.map g) := Equiv.ofBijective (fun a => ⟨g a, hmem a⟩)
      ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact ⟨a, rfl⟩⟩
    refine ⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    change ((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl

/- English proof (translation)
Establish `hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f → (∏ a, A a (f a)) * (B.submatrix f id).det = 0`. Introduce `f hf`. Simplify using `only [Function.Injective, not_forall] at hf`. Take `⟨a, b, hab, hne⟩` from `hf`. Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]`.

Establish `hS : ∀ S : {S : Finset (Fin N) // S.card = i}, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det = (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det`. Introduce `S`. Establish `hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det = ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Both sides reduce to the same expression.

Rewrite using `[hA, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id` using `rfl`. Rewrite using `[hB, Matrix.det_permute]`. Express the relevant statement in the definitionally equal form `(∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hni`. Conclude with `hf (hz f hni)).symm`. Use `_ = ∑ x : {f : Fin i → Fin N // Function.Injective f}, (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det := Finset.sum_subtype _ (fun f => by simp) _`.

Use `_ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det := Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)`. Use `_ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det := (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm`. Use `_ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det := Fintype.sum_sigma _`. Use `_ = _ := Finset.sum_congr rfl fun S _ => hS S`.
-/
theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f →
      (∏ a, A a (f a)) * (B.submatrix f id).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]
  have hS : ∀ S : {S : Finset (Fin N) // S.card = i},
      ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det =
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    intro S
    have hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det =
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a)) := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hB, Matrix.det_permute]
    change (∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _
    ring
  calc (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        cb_det_mul_fun A B
    _ = ∑ f ∈ univ.filter Function.Injective, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        (Finset.sum_filter_of_ne fun f _ hf => by
          by_contra hni
          exact hf (hz f hni)).symm
    _ = ∑ x : {f : Fin i → Fin N // Function.Injective f},
          (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det :=
        Finset.sum_subtype _ (fun f => by simp) _
    _ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det :=
        Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)
    _ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det :=
        (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm
    _ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det :=
        Fintype.sum_sigma _
    _ = _ := Finset.sum_congr rfl fun S _ => hS S

/- English proof (translation)
Unfold `lead`. Rewrite using `[dif_pos hi]`. Establish `hsub : (U * Matrix.diagonal d * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d) * (U.submatrix (Fin.castLE hi) id)ᴴ`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply]`.

Rewrite using `[hsub, det_mul_eq_sum_submatrix]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Establish `h1 : (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d).submatrix id (J.1.orderEmbOfFin J.2) = U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2) * Matrix.diagonal (fun a => d (J.1.orderEmbOfFin J.2 a))`. Use extensionality with `a b`. Simplify using `[Matrix.mul_diagonal]`.

Establish `h2 : (U.submatrix (Fin.castLE hi) id)ᴴ.submatrix (J.1.orderEmbOfFin J.2) id = (U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2))ᴴ`. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `hp : ∏ a, d (J.1.orderEmbOfFin J.2 a) = ∏ j ∈ J.1, d j`. Combine the equalities or inequalities in the displayed calculation.

Establish `hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z`. Introduce `z`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hp, hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lead_unitary_diag {U : Matrix (Fin n) (Fin n) ℂ} (d : Fin n → ℂ) (i : ℕ) (hi : i ≤ n) :
    lead i (U * Matrix.diagonal d * Uᴴ) =
      ∑ J : {J : Finset (Fin n) // J.card = i},
        ((‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 : ℝ) : ℂ) * ∏ j ∈ J.1, d j := by
  unfold lead
  rw [dif_pos hi]
  have hsub : (U * Matrix.diagonal d * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d) * (U.submatrix (Fin.castLE hi) id)ᴴ := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsub, det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h1 : (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d).submatrix id (J.1.orderEmbOfFin J.2) =
      U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2) *
        Matrix.diagonal (fun a => d (J.1.orderEmbOfFin J.2 a)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  have h2 : (U.submatrix (Fin.castLE hi) id)ᴴ.submatrix (J.1.orderEmbOfFin J.2) id =
      (U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2))ᴴ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hp : ∏ a, d (J.1.orderEmbOfFin J.2 a) = ∏ j ∈ J.1, d j := by
    calc ∏ a, d (J.1.orderEmbOfFin J.2 a)
        = ∏ j ∈ univ.map (J.1.orderEmbOfFin J.2).toEmbedding, d j := (Finset.prod_map _ _ _).symm
      _ = ∏ j ∈ J.1, d j := by rw [Finset.map_orderEmbOfFin_univ]
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hp, hn]
  ring

end ReciprocityTheory.ChartRestriction.DS.S7
