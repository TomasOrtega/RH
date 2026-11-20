import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Columns

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def colMat (c : n → Matrix n n A) (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => (c j *ᵥ v) i

omit [DecidableEq n] in
/- English proof (translation)
Rewrite using `[Matrix.sum_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]`. Simplify using `[colMat, Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem colMat_mulVec (c : n → Matrix n n A) (v a : n → A) :
    colMat c v *ᵥ a = (∑ j, a j • c j) *ᵥ v := by
  rw [Matrix.sum_mulVec]
  funext i
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp [colMat, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[colMat, Matrix.mulVec, dotProduct]`.
-/
theorem colMat_map {B : Type} [CommRing B] (f : A →+* B) (c : n → Matrix n n A) (v : n → A) :
    (colMat c v).map f = colMat (fun j => (c j).map f) (fun i => f (v i)) := by
  ext i j
  simp [colMat, Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨a, ha⟩` from `Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)`. Use `⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Matrix.mulVec_surjective_iff_isUnit.2 hB y`. Establish `ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v` using `by rw [← colMat_mulVec]; exact ha`. Establish `h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N`.

Simplify using `[Finset.mul_sum, Finset.sum_mul, hN]`. Establish `h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j)` using `Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (Commute.smul_left (Commute.smul_right (hc i j) _) _)`. Simplify using `only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]`. Rewrite using `[h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']`.
-/
theorem eq_sum_of_commute_cols {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)
  refine ⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩
  obtain ⟨t, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB y
  have ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v := by rw [← colMat_mulVec]; exact ha
  have h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N := by
    simp [Finset.mul_sum, Finset.sum_mul, hN]
  have h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j) :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
      (Commute.smul_left (Commute.smul_right (hc i j) _) _)
  simp only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']

/- English proof (translation)
Unfold `genAlg at hl`. Proceed by induction on `hl using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `h`. Consider the case `algebraMap r`.

Establish `: (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B)`. Apply the tactic sequence `ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]`.

Consider the case `mul x y _ _ hx hy`. Rewrite using `[Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]`.
-/
theorem map_commute_of_mem_genAlg {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by
  unfold genAlg at hl
  induction hl using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap r =>
    have : (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; simp
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

end Columns

/- English proof (translation)
Take `⟨c, hc⟩` from `TensorProduct.eq_repr_basis_left b x`. Conclude with `⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩`.
-/
theorem exists_sum_basis_tmul {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b x
  exact ⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.commutes]`. Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ l a`.
-/
theorem toMat_tmul_eq_smul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (a : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ a) = a • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l a

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ _ hA hP R _ _`. Take `⟨-, ⟨b⟩, hbij⟩` from `hP`. Take `⟨-, -, -, ⟨v, hv⟩, -⟩` from `hA`. Set `c : n → Matrix n n E` to `fun j => ((b j : genAlg (γ : Matrix n n E)) : Matrix n n E)`. Establish `hB : IsUnit (colMat c v)`.

Use `Matrix.mulVec_surjective_iff_isUnit.1 fun y => ?_` and prove the remaining obligations. Take `⟨l, rfl⟩` from `hv.2 y`. Take `⟨x, rfl⟩` from `hbij.2 l`. Take `⟨a, rfl⟩` from `exists_sum_basis_tmul b x`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[colMat_mulVec]`. Use `congr 1`. Rewrite using `[map_sum, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]`.

Conclude with `Algebra.smul_def (a j) (c j)`. Set `f : E →+* E ⊗[F] R` to `inclE (F := F) R`. Establish `hB' : IsUnit (colMat (fun j => (c j).map f) (fun i => f (v i)))`. Rewrite using `[← colMat_map]`. Conclude with `hB.map f.mapMatrix`.

Establish `hsum : ∀ a : n → E ⊗[F] R, toMat σ J (γ : Matrix n n E) R (∑ j, b j ⊗ₜ[F] a j) = ∑ j, a j • (c j).map f` using `fun a => by`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => toMat_tmul_eq_smul _ _ _ _ _ _`. Use `⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `exists_sum_basis_tmul b u`.

Rewrite `hu` using `[hsum]`. Establish `: a = 0` using `Matrix.mulVec_injective_of_isUnit hB' (by rw [colMat_mulVec, hu, Matrix.zero_mulVec, Matrix.mulVec_zero])`. Simplify using `[this]`. Take `⟨a, ha⟩` from `eq_sum_of_commute_cols hB' (fun i j => by`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `congrArg (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E).map f) (mul_comm (b i : genAlg (γ : Matrix n n E)) (b j)))`. Use the proof step `(fun j => map_commute_of_mem_genAlg f hN (b j : genAlg (γ : Matrix n n E)).2)`. Conclude with `⟨_, (hsum a).trans ha⟩`. Introduce and unpack `⟨u, rfl⟩`. Take `⟨a, rfl⟩` from `exists_sum_basis_tmul b u`.

Rewrite using `[hsum]`. Use `Commute.sum_left _ _ _ fun j _ => Commute.smul_left ?_ _` and prove the remaining obligations. Conclude with `(map_commute_of_mem_genAlg f rfl (b j : genAlg (γ : Matrix n n E)).2).symm`.
-/
theorem pointsCommutant : PointsCommutant := by
  intro F E _ _ _ _ n _ _ σ J γ _ hA hP R _ _
  obtain ⟨-, ⟨b⟩, hbij⟩ := hP
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  let c : n → Matrix n n E := fun j => ((b j : genAlg (γ : Matrix n n E)) : Matrix n n E)
  have hB : IsUnit (colMat c v) := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 fun y => ?_
    obtain ⟨l, rfl⟩ := hv.2 y
    obtain ⟨x, rfl⟩ := hbij.2 l
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b x
    refine ⟨a, ?_⟩
    rw [colMat_mulVec]
    congr 1
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
    exact Algebra.smul_def (a j) (c j)
  let f : E →+* E ⊗[F] R := inclE (F := F) R
  have hB' : IsUnit (colMat (fun j => (c j).map f) (fun i => f (v i))) := by
    rw [← colMat_map]; exact hB.map f.mapMatrix
  have hsum : ∀ a : n → E ⊗[F] R, toMat σ J (γ : Matrix n n E) R (∑ j, b j ⊗ₜ[F] a j) =
      ∑ j, a j • (c j).map f := fun a => by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ => toMat_tmul_eq_smul _ _ _ _ _ _
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum] at hu
    have : a = 0 := Matrix.mulVec_injective_of_isUnit hB'
      (by rw [colMat_mulVec, hu, Matrix.zero_mulVec, Matrix.mulVec_zero])
    simp [this]
  · obtain ⟨a, ha⟩ := eq_sum_of_commute_cols hB' (fun i j => by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E).map f)
        (mul_comm (b i : genAlg (γ : Matrix n n E)) (b j)))
      (fun j => map_commute_of_mem_genAlg f hN (b j : genAlg (γ : Matrix n n E)).2)
    exact ⟨_, (hsum a).trans ha⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum]
    refine Commute.sum_left _ _ _ fun j _ => Commute.smul_left ?_ _
    exact (map_commute_of_mem_genAlg f rfl (b j : genAlg (γ : Matrix n n E)).2).symm

end GlobalTheory.RegSS
