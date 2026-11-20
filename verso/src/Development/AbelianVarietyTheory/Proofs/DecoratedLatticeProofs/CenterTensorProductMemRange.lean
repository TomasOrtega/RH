import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.CenterTensor

open Algebra.TensorProduct

/- English proof (translation)
Establish `h1 : z ∈ Subalgebra.centralizer ℂ ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B).range : Set (A ⊗[ℂ] B))`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `g _`. Conclude with `Subalgebra.mem_center_iff.1 hz g`. Rewrite `h1` using `[Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct]`.

Take `⟨w, hw⟩` from `h1`. Use `set f := Algebra.TensorProduct.map (AlgHom.id ℂ A) (Subalgebra.center ℂ B).val with hf`. Establish `finj : Function.Injective f`. Establish `: (f : A ⊗[ℂ] (Subalgebra.center ℂ B) → A ⊗[ℂ] B) = LinearMap.lTensor A (Subalgebra.center ℂ B).val.toLinearMap`. Use function extensionality and compare the values at `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [hf]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[this]`.

Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective`. Establish `hw2 : w ∈ Subalgebra.centralizer ℂ ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)).range : Set (A ⊗[ℂ] (Subalgebra.center ℂ B)))`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hw' : f w = z` using `hw`.

Establish `h3 : f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a) = a ⊗ₜ[ℂ] (1 : B)` using `by simp [hf]`. Apply `finj` to reduce the goal to its premises. Use `show f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a * w) = f (w * (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a)`. Rewrite using `[map_mul, map_mul, hw', h3]`. Conclude with `Subalgebra.mem_center_iff.1 hz _`.

Rewrite `hw2` using `[Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct]`. Take `⟨u, hu⟩` from `hw2`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hw' : f w = z` using `hw`. Establish `hu' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ (Subalgebra.center ℂ B)) u = w` using `hu`.

Rewrite using `[← hw', ← hu']`. Use `clear hw hu hw' hu' hz`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [hf]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem center_tensorProduct_mem_range {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (z : A ⊗[ℂ] B) (hz : z ∈ Subalgebra.center ℂ (A ⊗[ℂ] B)) :
    ∃ u : (Subalgebra.center ℂ A) ⊗[ℂ] (Subalgebra.center ℂ B),
      Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (Subalgebra.center ℂ B).val u = z := by
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B).range : Set (A ⊗[ℂ] B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact Subalgebra.mem_center_iff.1 hz g
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  set f := Algebra.TensorProduct.map (AlgHom.id ℂ A) (Subalgebra.center ℂ B).val with hf
  have finj : Function.Injective f := by
    have : (f : A ⊗[ℂ] (Subalgebra.center ℂ B) → A ⊗[ℂ] B) =
        LinearMap.lTensor A (Subalgebra.center ℂ B).val.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hf]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hw2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)).range :
        Set (A ⊗[ℂ] (Subalgebra.center ℂ B))) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have hw' : f w = z := hw
    have h3 : f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a) = a ⊗ₜ[ℂ] (1 : B) := by simp [hf]
    apply finj
    show f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a * w) = f (w * (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a)
    rw [map_mul, map_mul, hw', h3]
    exact Subalgebra.mem_center_iff.1 hz _
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at hw2
  obtain ⟨u, hu⟩ := hw2
  refine ⟨u, ?_⟩
  have hw' : f w = z := hw
  have hu' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
      (AlgHom.id ℂ (Subalgebra.center ℂ B)) u = w := hu
  rw [← hw', ← hu']
  clear hw hu hw' hu' hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce `A B C _ _ _ _ _ _ e`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `c hc`. Establish `hz : e.symm c ∈ Subalgebra.center ℂ (A ⊗[ℂ] B)`. Rewrite `hc`, the goal using `[Subalgebra.mem_center_iff]`.

Introduce `g`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, e.apply_symm_apply]`. Conclude with `hc (e g)`. Take `⟨u, hu⟩` from `center_tensorProduct_mem_range _ hz`.

Establish `hc' : c = e (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (Subalgebra.center ℂ B).val u)` using `by rw [hu, e.apply_symm_apply]`. Rewrite using `[hc']`. Use `clear hu hc'`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b`. Establish `: (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (Subalgebra.center ℂ B).val) (a ⊗ₜ b) = ((a : A) ⊗ₜ (1 : B)) * ((1 : A) ⊗ₜ (b : B))`. Simplify using the standard rewrite rules. Rewrite using `[this, map_mul]`. Use `Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_)` and prove the remaining obligations.

Conclude with `Or.inl ⟨a, a.2, rfl⟩`. Conclude with `Or.inr ⟨b, b.2, rfl⟩`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `Subalgebra.add_mem _ hx hy`. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce and unpack `_ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_center_iff]`. Introduce `g`. Take `⟨y, rfl⟩` from `e.surjective g`. Rewrite using `[← map_mul, ← map_mul]`.

Use `congr 1`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Simplify using `[Subalgebra.mem_center_iff.1 ha x]`.

Consider the case `add x y hx hy => rw [mul_add, add_mul, hx, hy]`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_center_iff]`. Introduce `g`. Take `⟨y, rfl⟩` from `e.surjective g`. Rewrite using `[← map_mul, ← map_mul]`.

Use `congr 1`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Simplify using `[Subalgebra.mem_center_iff.1 hb y]`.

Consider the case `add x y hx hy => rw [mul_add, add_mul, hx, hy]`.
-/
theorem center_eq_adjoin : ∀ (A B C : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Ring C] [Algebra ℂ C] (e : (A ⊗[ℂ] B) ≃ₐ[ℂ] C), Subalgebra.center ℂ C = Algebra.adjoin ℂ ((fun a => e (a ⊗ₜ 1)) '' (Subalgebra.center ℂ A : Set A) ∪ (fun b => e (1 ⊗ₜ b)) '' (Subalgebra.center ℂ B : Set B)) := by
  intro A B C _ _ _ _ _ _ e
  apply le_antisymm
  · intro c hc
    have hz : e.symm c ∈ Subalgebra.center ℂ (A ⊗[ℂ] B) := by
      rw [Subalgebra.mem_center_iff] at hc ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hc (e g)
    obtain ⟨u, hu⟩ := center_tensorProduct_mem_range _ hz
    have hc' : c = e (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
        (Subalgebra.center ℂ B).val u) := by rw [hu, e.apply_symm_apply]
    rw [hc']
    clear hu hc'
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
          (Subalgebra.center ℂ B).val) (a ⊗ₜ b) = ((a : A) ⊗ₜ (1 : B)) * ((1 : A) ⊗ₜ (b : B)) := by
        simp
      rw [this, map_mul]
      refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_)
      · exact Or.inl ⟨a, a.2, rfl⟩
      · exact Or.inr ⟨b, b.2, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 ha x]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 hb y]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end GlobalTheory.CenterTensor
