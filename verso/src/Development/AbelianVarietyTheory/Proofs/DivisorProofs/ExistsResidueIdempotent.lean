import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulEq
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaResidue

/- English proof (translation)
Use `IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_` and prove the remaining obligations. Distinguish the cases in `h : I = ⊥`. Conclude with `Or.inl h`. Use `right`. Choose the witnesses or unpack the hypotheses as in `⟨z, hzI, hz0⟩ : ∃ z ∈ I, z ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[TwoSidedIdeal.mem_bot]`.

Conclude with `⟨hc x, fun hx => hx ▸ I.zero_mem⟩`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual k B, φ z ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hz0 ((Module.forall_dual_apply_eq_zero_iff k z).1 hc)`.

Set `f : B →ₗ[k] B` to `(φ z)⁻¹ • φ.smulRight (1 : B)`. Establish `hf : f z = 1`. Simplify using `[f, hφ]`. Take `⟨t, ht⟩` from `(IsAzumaya.bij (R := k) (A := B)).2 f`. Establish `key : ∀ t : B ⊗[k] Bᵐᵒᵖ, AlgHom.mulLeftRight k B t z ∈ I`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp [I.zero_mem]`. Consider the case `tmul a b`. Rewrite using `[AlgHom.mulLeftRight_apply]`.

Conclude with `I.mul_mem_right _ _ (I.mul_mem_left _ _ hzI)`. Consider the case `add x y hx hy`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `I.add_mem hx hy`. Rewrite using `[← TwoSidedIdeal.one_mem_iff, ← hf, ← ht]`.

Conclude with `key t`.
-/
theorem isSimpleRing_of_isAzumaya (k B : Type) [Field k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] : IsSimpleRing B := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases h : I = ⊥
  · exact Or.inl h
  right
  obtain ⟨z, hzI, hz0⟩ : ∃ z ∈ I, z ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨hc x, fun hx => hx ▸ I.zero_mem⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k B, φ z ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz0 ((Module.forall_dual_apply_eq_zero_iff k z).1 hc)
  let f : B →ₗ[k] B := (φ z)⁻¹ • φ.smulRight (1 : B)
  have hf : f z = 1 := by
    simp [f, hφ]
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := k) (A := B)).2 f
  have key : ∀ t : B ⊗[k] Bᵐᵒᵖ, AlgHom.mulLeftRight k B t z ∈ I := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [I.zero_mem]
    | tmul a b =>
      rw [AlgHom.mulLeftRight_apply]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hzI)
    | add x y hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact I.add_mem hx hy
  rw [← TwoSidedIdeal.one_mem_iff, ← hf, ← ht]
  exact key t

/- English proof (translation)
Use `haveI : IsSimpleRing B := isSimpleRing_of_isAzumaya k B`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite k B`. Take `⟨n, hn, D, _, _, _, ⟨e⟩⟩` from `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B`. Use `haveI : Finite D := Module.finite_of_finite k`. Establish `hcomm : ∀ a b : D, a * b = b * a` using `(littleWedderburn D).mul_comm`.

Establish `hD : ∀ d : D, ∃ c : k, algebraMap k D c = d`. Introduce `d`. Establish `hcen : e.symm (Matrix.scalar (Fin n) d) ∈ Subalgebra.center k B`. Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `y`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, AlgEquiv.apply_symm_apply]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hcomm]`. Take `⟨c, hc⟩` from `Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg e hc`. Rewrite `h2` using `[AlgEquiv.apply_symm_apply, AlgEquiv.commutes]`. Establish `h3` using `congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hn.out⟩) ⟨0, Nat.pos_of_ne_zero hn.out⟩`. Simplify `h3` using `[Matrix.algebraMap_eq_diagonal]`.

Set `i₀ : Fin n` to `⟨0, Nat.pos_of_ne_zero hn.out⟩`. Set `E : Matrix (Fin n) (Fin n) D` to `Matrix.single i₀ i₀ 1`. Use `⟨e.symm E, ?_, ?_, n, fun i => e.symm (Matrix.single i i₀ 1), fun i => e.symm (Matrix.single i₀ i 1), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Simplify using `[E, Matrix.single_mul_single_same]`.

Introduce `y`. Take `⟨c, hc⟩` from `hD (e y i₀ i₀)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, AlgEquiv.apply_symm_apply, map_smul, AlgEquiv.apply_symm_apply]`.

Simplify using `only [E, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, ← hc]`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Apply `e.injective` to reduce the goal to its premises. Simplify using `[E, map_sum, Matrix.single_mul_single_same, Matrix.sum_single_one]`.
-/
theorem exists_rankOne_idempotent (k B : Type) [Field k] [Finite k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] :
    ∃ x : B, x * x = x ∧ (∀ y : B, ∃ c : k, x * y * x = c • x) ∧
      ∃ (N : ℕ) (a b : Fin N → B), ∑ i, a i * x * b i = 1 := by
  classical
  haveI : IsSimpleRing B := isSimpleRing_of_isAzumaya k B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
  haveI : Finite D := Module.finite_of_finite k
  have hcomm : ∀ a b : D, a * b = b * a := (littleWedderburn D).mul_comm
  have hD : ∀ d : D, ∃ c : k, algebraMap k D c = d := by
    intro d
    have hcen : e.symm (Matrix.scalar (Fin n) d) ∈ Subalgebra.center k B := by
      rw [Subalgebra.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hcomm]
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)
    refine ⟨c, ?_⟩
    have h2 := congrArg e hc
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at h2
    have h3 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hn.out⟩) ⟨0, Nat.pos_of_ne_zero hn.out⟩
    simpa [Matrix.algebraMap_eq_diagonal] using h3
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn.out⟩
  let E : Matrix (Fin n) (Fin n) D := Matrix.single i₀ i₀ 1
  refine ⟨e.symm E, ?_, ?_, n, fun i => e.symm (Matrix.single i i₀ 1),
    fun i => e.symm (Matrix.single i₀ i 1), ?_⟩
  · rw [← map_mul]
    simp [E, Matrix.single_mul_single_same]
  · intro y
    obtain ⟨c, hc⟩ := hD (e y i₀ i₀)
    refine ⟨c, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, map_smul, AlgEquiv.apply_symm_apply]
    simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, ← hc]
    rw [Algebra.algebraMap_eq_smul_one]
  · apply e.injective
    simp [E, map_sum, Matrix.single_mul_single_same, Matrix.sum_single_one]

end GlobalTheory.AzumayaResidue

namespace GlobalTheory.AzumayaResidue

/- English proof (translation)
Use `TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := Λ) (maximalIdeal A) y` as an intermediate fact. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← this]`. Conclude with `(congrArg (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal A)) h).trans (map_zero _)`.
-/
theorem mem_smul_top_of_one_tmul_eq_zero (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (y : Λ) (h : (1 : ResidueField A) ⊗ₜ[A] y = 0) :
    y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
  have := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := Λ) (maximalIdeal A) y
  rw [← Submodule.Quotient.mk_eq_zero, ← this]
  exact (congrArg (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal A)) h).trans (map_zero _)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq`. Consider the case `exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq`. Consider the case `(apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq ..)`.
-/
theorem one_tmul_surjective (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (z : ResidueField A ⊗[A] Λ) : ∃ y : Λ, (1 : ResidueField A) ⊗ₜ[A] y = z := by
  first
  | exact @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | (apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq ..)

/- English proof (translation)
Introduce `A _ _ _ Λ _ _ _ _ _`. Set `k` to `ResidueField A`. Use `haveI : IsAzumaya k (k ⊗[A] Λ) := GlobalTheory.isAzumaya_baseChange A k Λ`. Use `haveI : Nontrivial (k ⊗[A] Λ) := by`. Assume the negation of the conclusion as `hB`.

Rewrite `hB` using `[not_nontrivial_iff_subsingleton]`. Establish `: (0 : k) = 1` using `FaithfulSMul.eq_of_smul_eq_smul (α := k ⊗[A] Λ) fun _ => Subsingleton.elim _ _`. Conclude with `zero_ne_one this`. Set `π : Λ →ₐ[A] k ⊗[A] Λ` to `Algebra.TensorProduct.includeRight`. Establish `hπ : ∀ y, π y = (1 : k) ⊗ₜ[A] y` using `fun y => rfl`.

Establish `hker : ∀ y, π y = 0 → y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ)` using `fun y h => mem_smul_top_of_one_tmul_eq_zero A Λ y ((hπ y).symm.trans h)`. Establish `hsurj : ∀ z, ∃ y, π y = z` using `one_tmul_surjective A Λ`. Take `⟨xb, hxx, hxy, N, ab, bb, hsum⟩` from `exists_rankOne_idempotent k (k ⊗[A] Λ)`. Take `⟨x, rfl⟩` from `hsurj xb`. Use `choose a ha using fun i => hsurj (ab i)`.

Use `choose b hb using fun i => hsurj (bb i)`. Use `⟨x, hker _ ?_, fun y => ?_, N, a, b, hker _ ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, hxx, sub_self]`. Take `⟨cb, hc⟩` from `hxy (π y)`. Take `⟨c, rfl⟩` from `IsLocalRing.residue_surjective cb`.

Use `⟨c, hker _ ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_mul, hc, map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul, sub_self]`. Simplify using `only [map_sub, map_sum, map_mul, map_one, ha, hb, hsum, sub_self]`.
-/
theorem exists_residue_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  intro A _ _ _ Λ _ _ _ _ _
  classical
  let k := ResidueField A
  haveI : IsAzumaya k (k ⊗[A] Λ) := GlobalTheory.isAzumaya_baseChange A k Λ
  haveI : Nontrivial (k ⊗[A] Λ) := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    have : (0 : k) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := k ⊗[A] Λ) fun _ => Subsingleton.elim _ _
    exact zero_ne_one this
  let π : Λ →ₐ[A] k ⊗[A] Λ := Algebra.TensorProduct.includeRight
  have hπ : ∀ y, π y = (1 : k) ⊗ₜ[A] y := fun y => rfl
  have hker : ∀ y, π y = 0 → y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := fun y h =>
    mem_smul_top_of_one_tmul_eq_zero A Λ y ((hπ y).symm.trans h)
  have hsurj : ∀ z, ∃ y, π y = z := one_tmul_surjective A Λ
  obtain ⟨xb, hxx, hxy, N, ab, bb, hsum⟩ := exists_rankOne_idempotent k (k ⊗[A] Λ)
  obtain ⟨x, rfl⟩ := hsurj xb
  choose a ha using fun i => hsurj (ab i)
  choose b hb using fun i => hsurj (bb i)
  refine ⟨x, hker _ ?_, fun y => ?_, N, a, b, hker _ ?_⟩
  · rw [map_sub, map_mul, hxx, sub_self]
  · obtain ⟨cb, hc⟩ := hxy (π y)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective cb
    refine ⟨c, hker _ ?_⟩
    rw [map_sub, map_mul, map_mul, hc, map_smul, ← ResidueField.algebraMap_eq,
      algebraMap_smul, sub_self]
  · simp only [map_sub, map_sum, map_mul, map_one, ha, hb, hsum, sub_self]

end GlobalTheory.AzumayaResidue
