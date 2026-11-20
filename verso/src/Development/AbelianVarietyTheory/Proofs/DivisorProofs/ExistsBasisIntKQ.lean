import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchMu
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.BCFL
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IntBasisKQ
open ReciprocityTheory.DiscreteGroups.LocalClassField

variable (p : ℕ) [Fact p.Prime]

/- English proof (translation)
Use `letI := zpAlgOK p K`. Use `haveI := isScalarTower_zp_OK p K`. Use `haveI := isIntegralClosure_OK p K`. Use `haveI := isTorsionFree_zp_K p K`. Use `haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _`.

Use `haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K := IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)`. Set `β₀` to `Module.finBasis ℤ_[p] (OK p K)`. Set `β` to `β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K`. Use `⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations.

Establish `e : x = algebraMap (OK p K) K ⟨x, hx⟩` using `rfl`. Rewrite using `[e, Module.Basis.localizationLocalization_repr_algebraMap]`. Conclude with `(β₀.repr ⟨x, hx⟩ i).2`. Set `z : _ → ℤ_[p]` to `fun i => ⟨β.repr x i, hx i⟩`. Establish `hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i)` using `by conv_lhs => rw [← β.sum_repr x]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p] (nonZeroDivisors ℤ_[p]) K]`. Both sides reduce to the same expression. Rewrite using `[hx']`.

Conclude with `(∑ i, z i • β₀ i).2`.
-/
theorem exists_basis_OK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι ℚ_[p] K),
      ∀ x : K, x ∈ OK p K ↔ ∀ i, ‖β.repr x i‖ ≤ 1 := by
  letI := zpAlgOK p K
  haveI := isScalarTower_zp_OK p K
  haveI := isIntegralClosure_OK p K
  haveI := isTorsionFree_zp_K p K
  haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)
  let β₀ := Module.finBasis ℤ_[p] (OK p K)
  let β := β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have e : x = algebraMap (OK p K) K ⟨x, hx⟩ := rfl
    rw [e, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (β₀.repr ⟨x, hx⟩ i).2
  · let z : _ → ℤ_[p] := fun i => ⟨β.repr x i, hx i⟩
    have hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i) := by
      conv_lhs => rw [← β.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p]
        (nonZeroDivisors ℤ_[p]) K]
      rfl
    rw [hx']
    exact (∑ i, z i • β₀ i).2

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

variable (p : ℕ) [Fact p.Prime]

section Tensor

variable {A B : Type} [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
  {ι κ : Type} [Fintype ι] [Fintype κ] (β : Module.Basis ι ℚ_[p] A) (γ : Module.Basis κ ℚ_[p] B)
  (OA : Subring A) (OB : Subring B)

def IntCoord (z : A ⊗[ℚ_[p]] B) : Prop := ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1

variable {p β γ}

/- English proof (translation)
Introduce `k` and use `by rw [map_add, Finsupp.add_apply] exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))`.
-/
theorem intCoord_add {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) :
    IntCoord p β γ (z + w) := fun k => by
  rw [map_add, Finsupp.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))

/- English proof (translation)
Introduce `k` and use `by rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul] exact mul_le_one₀ hc (norm_nonneg _) (hz k)`.
-/
theorem intCoord_smul {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    IntCoord p β γ (c • z) := fun k => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hz k)

/- English proof (translation)
Introduce `k` and use `by rw [map_neg, Finsupp.neg_apply, norm_neg] exact hz k`.
-/
theorem intCoord_neg {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) : IntCoord p β γ (-z) := fun k => by
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hz k

/- English proof (translation)
Introduce `k` and use `by simp`.
-/
theorem intCoord_zero : IntCoord p β γ (0 : A ⊗[ℚ_[p]] B) := fun k => by simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using intCoord_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))`.
-/
theorem intCoord_sum {σ : Type} (s : Finset σ) (f : σ → A ⊗[ℚ_[p]] B) (h : ∀ t ∈ s, IntCoord p β γ (f t)) :
    IntCoord p β γ (∑ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using intCoord_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

variable {OA OB}

/- English proof (translation)
Introduce `⟨i, j⟩` and use `by rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul] exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)`.
-/
theorem intCoord_tmul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {a : A} {b : B} (ha : a ∈ OA) (hb : b ∈ OB) : IntCoord p β γ (a ⊗ₜ[ℚ_[p]] b) := fun ⟨i, j⟩ => by
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)

/- English proof (translation)
The claim follows from `(hA _).2 fun i' => by rw [Module.Basis.repr_self, Finsupp.single_apply] split_ifs <;> simp`.
-/
theorem basis_mem (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (i : ι) : β i ∈ OA :=
  (hA _).2 fun i' => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

/- English proof (translation)
Use `set b := β.tensorProduct γ`. Establish `e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l)` using `by conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm]`.

Rewrite using `[e]`. Use `intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_` and prove the remaining obligations. Take `⟨i, j⟩` from `k`. Take `⟨i', j'⟩` from `l`. Simplify using `only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]`.

Conclude with `intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i')) (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hz k) (norm_nonneg _) (hw l)`.
-/
theorem intCoord_mul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) : IntCoord p β γ (z * w) := by
  set b := β.tensorProduct γ
  have e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l) := by
    conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  rw [e]
  refine intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i'))
      (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))
  · rw [norm_mul]
    exact mul_le_one₀ (hz k) (norm_nonneg _) (hw l)

/- English proof (translation)
Set `S : Subring (A ⊗[ℚ_[p]] B)` to `{ carrier := {z | IntCoord p β γ z} mul_mem' := intCoord_mul hA hB one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem add_mem' := intCoord_add zero_mem' := intCoord_zero neg_mem' := intCoord_neg }`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `(Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `intCoord_tmul hA hB a.2 OB.one_mem`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `intCoord_tmul hA hB OA.one_mem b.2`. Introduce `hz`. Rewrite using `[← (β.tensorProduct γ).sum_repr z]`.

Use `Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul', show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j = (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) * (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] …`. Rewrite using `[Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]`. Use `Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))` and prove the remaining obligations. Use `(hA _).2 fun i' => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]`. Use `mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_closure_iff (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    (z : A ⊗[ℚ_[p]] B) :
    z ∈ Subring.closure (Set.range (fun a : OA => (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) a) ∪
      Set.range (fun b : OB => (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) b)) ↔
      ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1 := by
  let S : Subring (A ⊗[ℚ_[p]] B) :=
    { carrier := {z | IntCoord p β γ z}
      mul_mem' := intCoord_mul hA hB
      one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem
      add_mem' := intCoord_add
      zero_mem' := intCoord_zero
      neg_mem' := intCoord_neg }
  constructor
  · intro hz
    refine (Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz
    · rintro _ ⟨a, rfl⟩
      exact intCoord_tmul hA hB a.2 OB.one_mem
    · rintro _ ⟨b, rfl⟩
      exact intCoord_tmul hA hB OA.one_mem b.2
  · intro hz
    rw [← (β.tensorProduct γ).sum_repr z]
    refine Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_
    rw [Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul',
      show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) (γ j) by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))
    refine (hA _).2 fun i' => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]
    refine mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_
    split_ifs <;> simp

end Tensor

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

/- English proof (translation)
Introduce `p _ K hK r hr`. Take `⟨ι₁, _, β, hβ⟩` from `exists_basis_OK p K hK`. Take `⟨ι₂, _, γ, hγ⟩` from `exists_basis_OK p (Qr p r) (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)`. Use `⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩` and prove the remaining obligations. Conclude with `mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x`.
-/
theorem exists_basis_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ_[p] (KQ p K r)),
      ∀ x, x ∈ intKQ p K r ↔ ∀ i, ‖b.repr x i‖ ≤ 1 := by
  intro p _ K hK r hr
  obtain ⟨ι₁, _, β, hβ⟩ := exists_basis_OK p K hK
  obtain ⟨ι₂, _, γ, hγ⟩ := exists_basis_OK p (Qr p r)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)
  refine ⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩
  exact mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x

end GlobalTheory.IntBasisKQ
