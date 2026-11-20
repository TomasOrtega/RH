import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittMatrixCoeffMemOfFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntTensor

section Coord

variable {R O S T : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] {d : Type} (b : Module.Basis d R O)

def coordT (k : d) : O ⊗[R] S →ₗ[R] S :=
  (TensorProduct.lid R S).toLinearMap ∘ₗ TensorProduct.map (b.coord k) LinearMap.id

/- English proof (translation)
Simplify using `[coordT]`.
-/
theorem coordT_tmul (k : d) (o : O) (s : S) : coordT b k (o ⊗ₜ[R] s) = b.repr o k • s := by
  simp [coordT]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o s => rw [Algebra.TensorProduct.map_tmul, coordT_tmul, coordT_tmul, AlgHom.id_apply, map_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem coordT_map (f : S →ₐ[R] T) (k : d) (x : O ⊗[R] S) :
    coordT b k (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (coordT b k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s => rw [Algebra.TensorProduct.map_tmul, coordT_tmul, coordT_tmul, AlgHom.id_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o s' => rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coordT_tmul, coordT_tmul, smul_mul_assoc]`. Consider the case `add x y hx hy => simp only [add_mul, map_add, hx, hy]`.
-/
theorem coordT_mul_tmul (k : d) (z : O ⊗[R] S) (s : S) :
    coordT b k (z * ((1 : O) ⊗ₜ[R] s)) = coordT b k z * s := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o s' => rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coordT_tmul, coordT_tmul, smul_mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o s => conv_rhs => rw [← b.sum_repr o]`. Rewrite using `[TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[coordT_tmul, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]`.
-/
theorem sum_coordT [Fintype d] (x : O ⊗[R] S) : ∑ k, b k ⊗ₜ[R] coordT b k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s =>
    conv_rhs => rw [← b.sum_repr o]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordT_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

end Coord

section Witt

variable (l : ℕ) [Fact l.Prime]

def valSub : ValuationSubring (Cb l) where
  toSubring := (algebraMap (OCb l) (Cb l)).range
  mem_or_inv_mem' x := by
    rcases (ValuationRing.iff_isInteger_or_isInteger (OCb l) (Cb l)).mp inferInstance x with h | h
    · obtain ⟨y, hy⟩ := h
      exact Or.inl ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := h
      exact Or.inr ⟨y, hy⟩

set_option synthInstance.maxHeartbeats 400000 in

def toValSub : OCb l →+* valSub l :=
  (algebraMap (OCb l) (Cb l)).codRestrict (valSub l) fun x => ⟨x, rfl⟩

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [WittVector.map_coeff, inclW]`. Both sides reduce to the same expression.
-/
theorem map_toValSub (x : Ainf l) :
    WittVector.map (valSub l).subtype (WittVector.map (toValSub l) x) = inclW l x := by
  ext m
  simp only [WittVector.map_coeff, inclW]
  rfl

/- English proof (translation)
Establish `key` using `GlobalTheory.witt_matrix_coeff_mem_of_frobenius l (valSub l) (Matrix.of fun i (_ : n) => v i) (Y.map (WittVector.map (toValSub l))) (Or.inl (by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_toValSub]`. Rewrite using `[WittVector.frobenius_eq_map_frobenius]`. Conclude with `h i))`.

Establish `hc : ∀ m, ∃ y : OCb l, algebraMap (OCb l) (Cb l) y = (v i).coeff m` using `fun m => key i i m`. Use `⟨WittVector.mk l fun m => Classical.choose (hc m), ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[inclW, WittVector.map_coeff, WittVector.coeff_mk]`. Conclude with `Classical.choose_spec (hc m)`.
-/
theorem mem_range_inclW {n : Type} [Fintype n] (v : n → WCb l) (Y : Matrix n n (Ainf l))
    (h : ∀ i, frobW l (v i) = ∑ j, inclW l (Y i j) * v j) (i : n) : v i ∈ (inclW l).range := by
  have key := GlobalTheory.witt_matrix_coeff_mem_of_frobenius l (valSub l) (Matrix.of fun i (_ : n) => v i)
    (Y.map (WittVector.map (toValSub l))) (Or.inl (by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_toValSub]
      rw [WittVector.frobenius_eq_map_frobenius]
      exact h i))
  have hc : ∀ m, ∃ y : OCb l, algebraMap (OCb l) (Cb l) y = (v i).coeff m := fun m => key i i m
  refine ⟨WittVector.mk l fun m => Classical.choose (hc m), ?_⟩
  ext m
  rw [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  exact Classical.choose_spec (hc m)

end Witt

section Main

/- English proof (translation)
The claim follows from `coordT_map b (inclWA l) k y`.
-/
theorem coordT_inclO {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] {d : Type}
    (b : Module.Basis d ℤ_[l] O) (k : d) (y : OA l O) :
    coordT b k (inclO l O y) = inclW l (coordT b k y) :=
  coordT_map b (inclWA l) k y

/- English proof (translation)
Introduce `l _ O _ _ _ _ n _ v Y h i`. Set `b` to `Module.Free.chooseBasis ℤ_[l] O`. Set `v' : n × Module.Free.ChooseBasisIndex ℤ_[l] O → WCb l` to `fun p => coordT b p.2 (v p.1)`. Set `Yt : Matrix (n × Module.Free.ChooseBasisIndex ℤ_[l] O) (n × Module.Free.ChooseBasisIndex ℤ_[l] O) (Ainf l)` to `fun p q => coordT b p.2 (Y p.1 q.1 * (b q.2 ⊗ₜ[ℤ_[l]] (1 : Ainf l)))`. Establish `hv : ∀ j, v j = ∑ m, (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) * ((1 : O) ⊗ₜ[ℤ_[l]] v' (j, m))`.

Introduce `j`. Use `conv_lhs => rw [← sum_coordT b (v j)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `hY : ∀ p, frobW l (v' p) = ∑ q, inclW l (Yt p q) * v' q`.

Introduce and unpack `⟨i', k⟩`. Establish `e1 : frobW l (v' (i', k)) = coordT b k (frobOW l O (v i'))` using `(coordT_map b (frobW l) k (v i')).symm`. Rewrite using `[e1, h i', Matrix.mulVec, dotProduct, map_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply]`.

Use `conv_lhs => rw [hv j]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `e2 : inclO l O (Y i' j) * (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) = inclO l O (Y i' j * (b m ⊗ₜ[ℤ_[l]] (1 : Ainf l)))`. Rewrite using `[map_mul, inclO_tmul, map_one]`.

Rewrite using `[← mul_assoc, e2, coordT_mul_tmul, coordT_inclO]`. Establish `hr : ∀ p, v' p ∈ (inclW l).range` using `mem_range_inclW l v' Yt hY`. Use `⟨∑ k, b k ⊗ₜ[ℤ_[l]] Classical.choose (hr (i, k)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `conv_rhs => rw [← sum_coordT b (v i)]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(inclO_tmul _ _).trans (congrArg (fun w => b k ⊗ₜ[ℤ_[l]] w) (Classical.choose_spec (hr (i, k))))`.
-/
theorem mem_range_inclO : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {n : Type} [Fintype n] (v : n → OW l O)
    (Y : Matrix n n (OA l O)), (∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) →
    ∀ i, v i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ n _ v Y h i
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  let v' : n × Module.Free.ChooseBasisIndex ℤ_[l] O → WCb l := fun p => coordT b p.2 (v p.1)
  let Yt : Matrix (n × Module.Free.ChooseBasisIndex ℤ_[l] O) (n × Module.Free.ChooseBasisIndex ℤ_[l] O)
      (Ainf l) := fun p q => coordT b p.2 (Y p.1 q.1 * (b q.2 ⊗ₜ[ℤ_[l]] (1 : Ainf l)))
  have hv : ∀ j, v j = ∑ m, (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) * ((1 : O) ⊗ₜ[ℤ_[l]] v' (j, m)) := by
    intro j
    conv_lhs => rw [← sum_coordT b (v j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hY : ∀ p, frobW l (v' p) = ∑ q, inclW l (Yt p q) * v' q := by
    rintro ⟨i', k⟩
    have e1 : frobW l (v' (i', k)) = coordT b k (frobOW l O (v i')) := (coordT_map b (frobW l) k (v i')).symm
    rw [e1, h i', Matrix.mulVec, dotProduct, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply]
    conv_lhs => rw [hv j]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e2 : inclO l O (Y i' j) * (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) =
        inclO l O (Y i' j * (b m ⊗ₜ[ℤ_[l]] (1 : Ainf l))) := by
      rw [map_mul, inclO_tmul, map_one]
    rw [← mul_assoc, e2, coordT_mul_tmul, coordT_inclO]
  have hr : ∀ p, v' p ∈ (inclW l).range := mem_range_inclW l v' Yt hY
  refine ⟨∑ k, b k ⊗ₜ[ℤ_[l]] Classical.choose (hr (i, k)), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← sum_coordT b (v i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (inclO_tmul _ _).trans (congrArg (fun w => b k ⊗ₜ[ℤ_[l]] w) (Classical.choose_spec (hr (i, k))))

end Main

end GlobalTheory.FrobIntTensor
