import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

section
variable {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

/- English proof (translation)
Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := A) (R.val.toLinearMap) Subtype.val_injective`. Establish `e : ∀ z : R ⊗[k] A, LinearMap.rTensor A R.val.toLinearMap z = Algebra.TensorProduct.map R.val (AlgHom.id k A) z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r a => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Introduce `x y hxy`. Apply `h` to reduce the goal to its premises. Rewrite using `[e, e, hxy]`.
-/
private lemma map_val_injective (R : Subalgebra k L) :
    Function.Injective
      (Algebra.TensorProduct.map R.val (AlgHom.id k A) : R ⊗[k] A →ₐ[k] L ⊗[k] A) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (R.val.toLinearMap) Subtype.val_injective
  have e : ∀ z : R ⊗[k] A, LinearMap.rTensor A R.val.toLinearMap z =
      Algebra.TensorProduct.map R.val (AlgHom.id k A) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply h
  rw [e, e, hxy]

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Take `⟨v, hv, rfl⟩` from `h'`. Conclude with `⟨u + v, by rw [map_add, hu, hv], by simp only [map_add]⟩`.
-/
private lemma spz_add {R : Subalgebra k L} {φ : R →ₐ[k] k} {y y' : L ⊗[k] A} {a a' : A}
    (h : Spz R φ y a) (h' : Spz R φ y' a') : Spz R φ (y + y') (a + a') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv, rfl⟩ := h'
  exact ⟨u + v, by rw [map_add, hu, hv], by simp only [map_add]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨r ⊗ₜ[k] a, by simp, by simp⟩`.
-/
private lemma spz_tmul (R : Subalgebra k L) (φ : R →ₐ[k] k) (r : R) (a : A) :
    Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a) :=
  ⟨r ⊗ₜ[k] a, by simp, by simp⟩

private noncomputable def contr (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] :
    B ⊗[k] A →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ LinearMap.lTensor B l

/- English proof (translation)
Simplify using `[contr]`.
-/
private lemma contr_tmul (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] (b : B) (a : A) :
    contr l B (b ⊗ₜ[k] a) = l a • b := by
  simp [contr]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace k A`. Set `E` to `TensorProduct.equivFinsuppOfBasisRight (R := k) (M := L) (N := A) b`. Establish `hE : E y ≠ 0` using `fun h => hy (E.injective (by rw [h, map_zero]))`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.mp hE`. Use `⟨b.coord i, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ z : L ⊗[k] A, contr (b.coord i) L z = E z i`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n => simp [contr_tmul, E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]`. Rewrite using `[key]`. Simplify using `using hi`.
-/
private lemma exists_contr_ne_zero {y : L ⊗[k] A} (hy : y ≠ 0) :
    ∃ l : A →ₗ[k] k, contr l L y ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k A
  let E := TensorProduct.equivFinsuppOfBasisRight (R := k) (M := L) (N := A) b
  have hE : E y ≠ 0 := fun h => hy (E.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hE
  refine ⟨b.coord i, ?_⟩
  have key : ∀ z : L ⊗[k] A, contr (b.coord i) L z = E z i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [contr_tmul, E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]
  rw [key]
  simpa using hi
end

/- English proof (translation)
Introduce `k L A _ _ _ _ _`. Use `⟨fun R φ => ⟨?_, ?_, spz_tmul R φ, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `y a a' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩`. Rewrite using `[map_val_injective R (hu.trans hv.symm)]`. Introduce `y y' a a' h h'`.

Use `⟨spz_add h h', ?_, ?_⟩` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `h`. Take `⟨v, hv, rfl⟩` from `h'`. Conclude with `⟨u * v, by rw [map_mul, hu, hv], by simp only [map_mul]⟩`. Take `⟨u, hu, rfl⟩` from `h`.

Take `⟨v, hv, rfl⟩` from `h'`. Conclude with `⟨u - v, by rw [map_sub, hu, hv], by simp only [map_sub]⟩`. Introduce and unpack `A' _ _ g y a ⟨u, rfl, rfl⟩`. Use `⟨Algebra.TensorProduct.map (AlgHom.id k R) g u, ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero`.

Conclude with `⟨∅, fun R _ φ => ⟨0, 0, by simp, by simp⟩⟩`. Consider the case `tmul l b => classical`. Use `⟨{l}, fun R hs φ => ?_⟩` and prove the remaining obligations. Establish `hl : l ∈ R` using `hs (by simp)`. Conclude with `⟨_, spz_tmul R φ ⟨l, hl⟩ b⟩`.

Consider the case `add x y hx hy => classical`. Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Use `⟨s ∪ t, fun R hst φ => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hs R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ`.

Take `⟨b, hb⟩` from `ht R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ`. Conclude with `⟨a + b, spz_add ha hb⟩`. Introduce `y hy classical`. Take `⟨l, hl⟩` from `exists_contr_ne_zero hy`. Use `set c := contr l L y with hc`.

Use `⟨{c, c⁻¹}, fun R hs φ a ha h0 => ?_⟩` and prove the remaining obligations. Establish `hcR : c ∈ R` using `hs (by simp)`. Establish `hcR' : c⁻¹ ∈ R` using `hs (by simp)`. Take `⟨u, hu, hua⟩` from `ha`. Establish `e1 : ∀ z : R ⊗[k] A, ((contr l R z : R) : L) = contr l L (Algebra.TensorProduct.map R.val (AlgHom.id k A) z)`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r b => simp [contr_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, Subalgebra.coe_add]`.

Establish `e2 : ∀ z : R ⊗[k] A, φ (contr l R z) = l (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) z))`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r b => simp [contr_tmul, mul_comm]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `h1 : contr l R u = ⟨c, hcR⟩` using `Subtype.ext (by rw [e1, hu])`. Establish `h2 : φ ⟨c, hcR⟩ = 0` using `by rw [← h1, e2, hua, h0, map_zero]`. Establish `h3 : (⟨c, hcR⟩ : R) * ⟨c⁻¹, hcR'⟩ = 1` using `Subtype.ext (mul_inv_cancel₀ hl)`. Establish `h4` using `congrArg φ h3`.

Rewrite `h4` using `[map_mul, h2, zero_mul, map_one]`. Conclude with `zero_ne_one h4`.
-/
theorem UpperTheory.specialization_tensor_ring_hom_properties :
    ∀ (k L A : Type) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A], (∀ (R : Subalgebra k L) (φ : R →ₐ[k] k), (∀ (y : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y a' → a = a') ∧ (∀ (y y' : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y' a' → Spz R φ (y + y') (a + a') ∧ Spz R φ (y * y') (a * a') ∧ Spz R φ (y - y') (a - a')) ∧ (∀ (r : R) (a : A), Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a)) ∧ ∀ (A' : Type) [CommRing A'] [Algebra k A'] (g : A →ₐ[k] A') (y : L ⊗[k] A) (a : A), Spz R φ y a → Spz R φ (Algebra.TensorProduct.map (AlgHom.id k L) g y) (g a)) ∧ (∀ y : L ⊗[k] A, ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ φ : R →ₐ[k] k, ∃ a, Spz R φ y a) ∧ ∀ y : L ⊗[k] A, y ≠ 0 → ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ (φ : R →ₐ[k] k) (a : A), Spz R φ y a → a ≠ 0 := by
  intro k L A _ _ _ _ _
  refine ⟨fun R φ => ⟨?_, ?_, spz_tmul R φ, ?_⟩, ?_, ?_⟩
  · rintro y a a' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [map_val_injective R (hu.trans hv.symm)]
  · intro y y' a a' h h'
    refine ⟨spz_add h h', ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u * v, by rw [map_mul, hu, hv], by simp only [map_mul]⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u - v, by rw [map_sub, hu, hv], by simp only [map_sub]⟩
  · rintro A' _ _ g y a ⟨u, rfl, rfl⟩
    refine ⟨Algebra.TensorProduct.map (AlgHom.id k R) g u, ?_, ?_⟩
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
  · intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact ⟨∅, fun R _ φ => ⟨0, 0, by simp, by simp⟩⟩
    | tmul l b =>
      classical
      refine ⟨{l}, fun R hs φ => ?_⟩
      have hl : l ∈ R := hs (by simp)
      exact ⟨_, spz_tmul R φ ⟨l, hl⟩ b⟩
    | add x y hx hy =>
      classical
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, fun R hst φ => ?_⟩
      obtain ⟨a, ha⟩ := hs R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      obtain ⟨b, hb⟩ := ht R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      exact ⟨a + b, spz_add ha hb⟩
  · intro y hy
    classical
    obtain ⟨l, hl⟩ := exists_contr_ne_zero hy
    set c := contr l L y with hc
    refine ⟨{c, c⁻¹}, fun R hs φ a ha h0 => ?_⟩
    have hcR : c ∈ R := hs (by simp)
    have hcR' : c⁻¹ ∈ R := hs (by simp)
    obtain ⟨u, hu, hua⟩ := ha
    have e1 : ∀ z : R ⊗[k] A, ((contr l R z : R) : L) =
        contr l L (Algebra.TensorProduct.map R.val (AlgHom.id k A) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul]
      | add x y hx hy => simp only [map_add, hx, hy, Subalgebra.coe_add]
    have e2 : ∀ z : R ⊗[k] A, φ (contr l R z) =
        l (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul, mul_comm]
      | add x y hx hy => simp only [map_add, hx, hy]
    have h1 : contr l R u = ⟨c, hcR⟩ := Subtype.ext (by rw [e1, hu])
    have h2 : φ ⟨c, hcR⟩ = 0 := by rw [← h1, e2, hua, h0, map_zero]
    have h3 : (⟨c, hcR⟩ : R) * ⟨c⁻¹, hcR'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hl)
    have h4 := congrArg φ h3
    rw [map_mul, h2, zero_mul, map_one] at h4
    exact zero_ne_one h4
