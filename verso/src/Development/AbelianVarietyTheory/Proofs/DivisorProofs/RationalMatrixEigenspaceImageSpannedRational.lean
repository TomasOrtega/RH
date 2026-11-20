import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField

namespace GlobalTheory.RationalSpan

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `conv_lhs => rw [← b.linearCombination_repr (v i)]`. Rewrite using `[Finsupp.linearCombination_apply]`.

Rewrite using `[Finsupp.sum_of_support_subset _ (s := Finset.univ.biUnion (fun i => (b.repr (v i)).support))]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Introduce `j hj`. Conclude with `Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩`.

Introduce `j _`. Simplify using the standard rewrite rules.
-/
theorem expand {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (v : Fin n → L) :
    v = ∑ j ∈ Finset.univ.biUnion (fun i => (b.repr (v i)).support),
      b j • (fun i => algebraMap K L (b.repr (v i) j)) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (v i)]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset _ (s := Finset.univ.biUnion (fun i => (b.repr (v i)).support))]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  · intro j hj
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩
  · intro j _
    simp

/- English proof (translation)
Simplify using `[← Algebra.smul_def, map_sum, Finsupp.finset_sum_apply]`.
-/
theorem repr_coord {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (a : Fin n → K) (y : Fin n → L) (j : s) :
    b.repr (∑ k, algebraMap K L (a k) * y k) j = ∑ k, a k * b.repr (y k) j := by
  simp [← Algebra.smul_def, map_sum, Finsupp.finset_sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (algebraMap K L) M x i).symm`.
-/
theorem map_mulVec_comp {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (M.map (algebraMap K L)).mulVec (fun i => algebraMap K L (x i)) =
      fun i => algebraMap K L (M.mulVec x i) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap K L) M x i).symm

end GlobalTheory.RationalSpan

/- English proof (translation)
Introduce `K L _ _ _ n ι A lam e`. Set `b` to `Module.Basis.ofVectorSpace K L`. Set `f` to `algebraMap K L`. Use `⟨fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.RationalSpan.expand b y]`.

Use `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))` and prove the remaining obligations. Introduce `p`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (fun z => b.repr z j) (congrFun (h p) i)`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1`.

Rewrite `h1` using `[GlobalTheory.RationalSpan.repr_coord]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[h1, ← Algebra.smul_def]`. Simplify using the standard rewrite rules. Set `W : Submodule L (Fin n → L)` to `{ carrier := {y | ∀ p, ((A p).map f).mulVec y = f (lam p) • y} add_mem' := by`.

Introduce `a c ha hc p`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[Matrix.mulVec_add, ha p, hc p, smul_add]`. Use the proof step `zero_mem' := by`. Introduce `p`.

Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c a ha p`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[Matrix.mulVec_smul, ha p, smul_comm] }`.

Establish `hle : Submodule.span L ((fun x i => f (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x}) ≤ W`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩ p`. Rewrite using `[GlobalTheory.RationalSpan.map_mulVec_comp, hx p]`. Use function extensionality and compare the values at `i`.

Simplify using `[f, Algebra.smul_def]`. Conclude with `hle h`. Take `⟨z, rfl⟩` from `h`. Rewrite using `[GlobalTheory.RationalSpan.expand b z, map_sum]`. Use `Submodule.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.mulVec (fun i => b.repr (z i) j), ⟨_, rfl⟩, ?_⟩)` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]`. Establish `hle : Submodule.span L ((fun x i => f (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) ≤ LinearMap.range (e.map f).mulVecLin`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨x, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨fun i => f (w i), by rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]; rfl⟩`. Conclude with `hle h`.
-/
theorem GlobalTheory.rational_eigen_image_span : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  intro K L _ _ _ n ι A lam e
  classical
  let b := Module.Basis.ofVectorSpace K L
  let f := algebraMap K L
  refine ⟨fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [GlobalTheory.RationalSpan.expand b y]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    intro p
    funext i
    have h1 := congrArg (fun z => b.repr z j) (congrFun (h p) i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [GlobalTheory.RationalSpan.repr_coord] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h1, ← Algebra.smul_def]
    simp
  · let W : Submodule L (Fin n → L) :=
      { carrier := {y | ∀ p, ((A p).map f).mulVec y = f (lam p) • y}
        add_mem' := by
          intro a c ha hc p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_add, ha p, hc p, smul_add]
        zero_mem' := by
          intro p
          simp
        smul_mem' := by
          intro c a ha p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_smul, ha p, smul_comm] }
    have hle : Submodule.span L ((fun x i => f (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x}) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ p
      rw [GlobalTheory.RationalSpan.map_mulVec_comp, hx p]
      funext i
      simp [f, Algebra.smul_def]
    exact hle h
  · obtain ⟨z, rfl⟩ := h
    rw [GlobalTheory.RationalSpan.expand b z, map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.mulVec (fun i => b.repr (z i) j), ⟨_, rfl⟩, ?_⟩)
    rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]
  · have hle : Submodule.span L ((fun x i => f (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) ≤ LinearMap.range (e.map f).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨fun i => f (w i), by rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]; rfl⟩
    exact hle h
