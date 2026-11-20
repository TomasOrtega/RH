import Mathlib

noncomputable section

namespace GlobalTheory

open TensorProduct

/- English proof (translation)
Rewrite using `[← AdicCompletion.of_surjective_iff]`. Introduce `y`. Take `⟨t, rfl⟩` from `AdicCompletion.ofTensorProduct_surjective_of_finite I M y`. Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul a m`. Take `⟨r, rfl⟩` from `AdicCompletion.of_surjective I R a`. Use `⟨r • m, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r = algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply], algebraMap_smul, map_smul]`. Consider the case `add x y hx hy`.

Take `⟨u, hu⟩` from `hx`. Take `⟨v, hv⟩` from `hy`. Conclude with `⟨u + v, by simp [hu, hv]⟩`.
-/
theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

/- English proof (translation)
The claim follows from `IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I) toIsPrecomplete := isPrecomplete_of_finite I M`.
-/
theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M

/- English proof (translation)
Rewrite using `[IsAdicComplete.map_algebraMap_iff]`. Conclude with `isAdicComplete_of_finite I S`.
-/
theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)

/- English proof (translation)
Use `choose x hx using fun n ↦ hπ n (c n)`. Establish `hcauchy : ∀ {m n}, m ≤ n → x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R M)]`. Use `(AdicCompletion.isAdicCauchy_iff I M x).2 fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, ← hker, hx, ← ht, hx, hc]`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := I) x hcauchy`.

Establish `hLc : ∀ n, π n L = c n` using `fun n ↦ by`. Rewrite using `[← hx, hker, ← SModEq.sub_mem]`. Conclude with `(hL n).symm`. Use `⟨L, hLc, fun y hy ↦ sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)⟩` and prove the remaining obligations. Rewrite using `[SModEq.zero, ← hker, hy, hLc]`.
-/
theorem existsUnique_of_compatible_tower {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] {C : ℕ → Type*} (π : ∀ n, M → C n)
    (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x y, π n x = π n y ↔ x - y ∈ (I ^ n • ⊤ : Submodule R M))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (c : ∀ n, C n) (hc : ∀ n, t n (c (n + 1)) = c n) : ∃! x : M, ∀ n, π n x = c n := by
  choose x hx using fun n ↦ hπ n (c n)
  have hcauchy : ∀ {m n}, m ≤ n → x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    refine (AdicCompletion.isAdicCauchy_iff I M x).2 fun n ↦ ?_
    rw [SModEq.sub_mem, ← hker, hx, ← ht, hx, hc]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) x hcauchy
  have hLc : ∀ n, π n L = c n := fun n ↦ by
    rw [← hx, hker, ← SModEq.sub_mem]
    exact (hL n).symm
  refine ⟨L, hLc, fun y hy ↦ sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)⟩
  rw [SModEq.zero, ← hker, hy, hLc]

/- English proof (translation)
Establish `H` using `fun a ↦ existsUnique_of_compatible_tower I (fun n ↦ π n) hπ (fun n x y ↦ by rw [← hker, map_sub, sub_eq_zero]) t ht (fun n ↦ f n a) (fun n ↦ hf n a)`. Use `choose g hg hu using H`. Use `⟨{ toFun := g map_one' := (hu _ _ fun n ↦ by simp).symm map_mul' a b := (hu _ _ fun n ↦ by simp [hg]).symm map_zero' := (hu _ _ fun n ↦ by simp).symm map_add' a b := (hu _ _ fun n ↦ by simp [hg]).symm commutes' r := (hu _ _ fun n ↦ by simp).symm }, fun n a ↦ hg a n, fun g' hg' ↦ …` and prove the remaining obligations.
-/
theorem existsUnique_algHom_of_compatible_tower {A B : Type*} [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [IsAdicComplete I B] {C : ℕ → Type*} [∀ n, Ring (C n)] [∀ n, Algebra R (C n)]
    (π : ∀ n, B →ₐ[R] C n) (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x, π n x = 0 ↔ x ∈ (I ^ n • ⊤ : Submodule R B))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (f : ∀ n, A →ₐ[R] C n) (hf : ∀ n a, t n (f (n + 1) a) = f n a) :
    ∃! g : A →ₐ[R] B, ∀ n a, π n (g a) = f n a := by
  have H := fun a ↦ existsUnique_of_compatible_tower I (fun n ↦ π n) hπ
    (fun n x y ↦ by rw [← hker, map_sub, sub_eq_zero]) t ht (fun n ↦ f n a) (fun n ↦ hf n a)
  choose g hg hu using H
  refine ⟨{ toFun := g
            map_one' := (hu _ _ fun n ↦ by simp).symm
            map_mul' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            map_zero' := (hu _ _ fun n ↦ by simp).symm
            map_add' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            commutes' r := (hu _ _ fun n ↦ by simp).symm }, fun n a ↦ hg a n,
    fun g' hg' ↦ AlgHom.ext fun a ↦ hu a _ fun n ↦ hg' n a⟩

end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicQuotTransition (A : Type*) [CommRing A] [Algebra R A] (n : ℕ) :
    (A ⧸ (I ^ (n + 1)).map (algebraMap R A)) →ₐ[R] A ⧸ (I ^ n).map (algebraMap R A) :=
  Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_pow_right n.le_succ))

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/- English proof (translation)
Use `isAdicComplete_of_finite I B` as an intermediate fact. Conclude with `existsUnique_algHom_of_compatible_tower I (C := fun n ↦ B ⧸ (I ^ n).map (algebraMap R B)) (fun _ ↦ Ideal.Quotient.mkₐ R _) (fun _ ↦ Ideal.Quotient.mk_surjective) (fun n x ↦ by`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem])`. Use the proof step `(fun n ↦ adicQuotTransition I B n) (fun _ _ ↦ rfl)`. Use the proof step `(fun n ↦ (f n).comp (Ideal.Quotient.mkₐ R _))`.

Use the proof step `(fun n a ↦ hf n (Ideal.Quotient.mk _ a))`.
-/
theorem existsUnique_algHom_of_compatible_quotient [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) →ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  have := isAdicComplete_of_finite I B
  exact existsUnique_algHom_of_compatible_tower I
    (C := fun n ↦ B ⧸ (I ^ n).map (algebraMap R B)) (fun _ ↦ Ideal.Quotient.mkₐ R _)
    (fun _ ↦ Ideal.Quotient.mk_surjective)
    (fun n x ↦ by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem])
    (fun n ↦ adicQuotTransition I B n) (fun _ _ ↦ rfl)
    (fun n ↦ (f n).comp (Ideal.Quotient.mkₐ R _))
    (fun n a ↦ hf n (Ideal.Quotient.mk _ a))

/- English proof (translation)
Take `⟨g, hg, hu⟩` from `existsUnique_algHom_of_compatible_quotient I (fun n ↦ (f n).toAlgHom) hf`. Take `⟨g', hg', -⟩` from `existsUnique_algHom_of_compatible_quotient I (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by`. Apply `(f n).injective` to reduce the goal to its premises. Simplify using `using (hf n ((f (n + 1)).symm x)).symm`. Establish `hA` using `(existsUnique_algHom_of_compatible_quotient I (A := A) (B := A) (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g'.comp g) (y₂ := .id _ _) (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl`.

Establish `hB` using `(existsUnique_algHom_of_compatible_quotient I (A := B) (B := B) (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g.comp g') (y₂ := .id _ _) (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl`. Conclude with `⟨.ofAlgHom g g' hB hA, hg, fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩`.
-/
theorem existsUnique_algEquiv_of_compatible_quotient [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) ≃ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_quotient I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_quotient I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simpa using (hf n ((f (n + 1)).symm x)).symm
  have hA := (existsUnique_algHom_of_compatible_quotient I (A := A) (B := A)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g'.comp g) (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  have hB := (existsUnique_algHom_of_compatible_quotient I (A := B) (B := B)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g.comp g') (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩

end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev adicTensorTransition (A : Type*) [Ring A] [Algebra R A] (n : ℕ) :
    (R ⧸ I ^ (n + 1)) ⊗[R] A →ₐ[R] (R ⧸ I ^ n) ⊗[R] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ))
    (AlgHom.id R A)

/- English proof (translation)
Rewrite using `[← (quotTensorEquivQuotSMul M J).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]`.
-/
theorem one_tmul_quotient_eq_zero_iff (J : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) : (1 : R ⧸ J) ⊗ₜ[R] x = 0 ↔ x ∈ (J • ⊤ : Submodule R M) := by
  rw [← (quotTensorEquivQuotSMul M J).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero]

variable [IsNoetherianRing R] [IsAdicComplete I R]

/- English proof (translation)
Use `isAdicComplete_of_finite I M` as an intermediate fact. Use `sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, ← one_tmul_quotient_eq_zero_iff, tmul_sub, h, sub_self]`.
-/
theorem eq_of_forall_one_tmul_quotient_eq {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x y : M}
    (h : ∀ n, (1 : R ⧸ I ^ n) ⊗ₜ[R] x = (1 : R ⧸ I ^ n) ⊗ₜ[R] y) : x = y := by
  have := isAdicComplete_of_finite I M
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)
  rw [SModEq.zero, ← one_tmul_quotient_eq_zero_iff, tmul_sub, h, sub_self]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/- English proof (translation)
The claim follows from `have := isAdicComplete_of_finite I B existsUnique_algHom_of_compatible_tower I (fun _ ↦ Algebra.TensorProduct.includeRight) (fun n x ↦ by obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul B (I ^ n) x) exact ⟨y, by rw [← (quotTensorEquivQuotSMul B (I ^ …`.
-/
theorem existsUnique_algHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) :=
  have := isAdicComplete_of_finite I B
  existsUnique_algHom_of_compatible_tower I (fun _ ↦ Algebra.TensorProduct.includeRight)
    (fun n x ↦ by
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul B (I ^ n) x)
      exact ⟨y, by rw [← (quotTensorEquivQuotSMul B (I ^ n)).symm_apply_apply x, ← hy]; rfl⟩)
    (fun n x ↦ one_tmul_quotient_eq_zero_iff _ x)
    (fun n ↦ adicTensorTransition I B n) (fun _ _ ↦ by simp)
    (fun n ↦ ((f n).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    (fun n _ ↦ (hf n _).trans (by simp))

/- English proof (translation)
Take `⟨g, hg, hu⟩` from `existsUnique_algHom_of_compatible_tensor I (fun n ↦ (f n).toAlgHom) hf`. Take `⟨g', hg', -⟩` from `existsUnique_algHom_of_compatible_tensor I (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by`. Apply `(f n).injective` to reduce the goal to its premises. Simplify using `[← hf]`. Establish `hA : g'.comp g = .id _ _` using `AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']`.

Establish `hB : g.comp g' = .id _ _` using `AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']`. Conclude with `⟨.ofAlgHom g g' hB hA, hg, fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩`.
-/
theorem existsUnique_algEquiv_of_compatible_tensor [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_tensor I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simp [← hf]
  have hA : g'.comp g = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  have hB : g.comp g' = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩

end

omit [IsNoetherianRing R] [IsAdicComplete I R] in

/- English proof (translation)
Rewrite using `[TensorProduct.comul_tmul]`. Proceed by induction on `(Coalgebra.comul a : A ⊗[R] A) with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`. Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy]`.
-/
theorem comul_one_tmul_eq_distribBaseChange (S : Type*) [CommRing S] [Algebra R S] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (a : A) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a) =
      AlgebraTensorModule.distribBaseChange R S A A (1 ⊗ₜ Coalgebra.comul a) := by
  rw [TensorProduct.comul_tmul]
  induction (Coalgebra.comul a : A ⊗[R] A) with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

/- English proof (translation)
Take `⟨g, hg, hu⟩` from `existsUnique_algHom_of_compatible_tensor I (A := A) (B := B) (fun n ↦ (f n : (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)) hf`. Use `replace hg : ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := hg`. Use `⟨.ofAlgHom g ?_ ?_, hg, fun g' hg' ↦ BialgHom.ext fun a ↦ congr($(hu g' hg') a)⟩` and prove the remaining obligations. Use `AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_` and prove the remaining obligations. Use `CoalgHomClass.counit_comp_apply (f n) (1 ⊗ₜ a)` as an intermediate fact.

Rewrite `this` using `[← hg, TensorProduct.counit_tmul, TensorProduct.counit_tmul]`. Apply `(TensorProduct.rid R _).injective` to reduce the goal to its premises. Simplify using `using this`. Use `AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_` and prove the remaining obligations. Use `CoalgHomClass.map_comp_comul_apply (f n) (1 ⊗ₜ a)` as an intermediate fact.

Rewrite `this` using `[← hg, comul_one_tmul_eq_distribBaseChange, comul_one_tmul_eq_distribBaseChange]`. Apply `(AlgebraTensorModule.distribBaseChange R (R ⧸ I ^ n) B B).injective` to reduce the goal to its premises. Simplify using `only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]`. Rewrite using `[← this]`. Proceed by induction on `(Coalgebra.comul a : A ⊗[R] A) with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [hg]`. Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy]`.
-/
theorem existsUnique_bialgHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n : (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)) hf
  replace hg : ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := hg
  refine ⟨.ofAlgHom g ?_ ?_, hg, fun g' hg' ↦ BialgHom.ext fun a ↦ congr($(hu g' hg') a)⟩
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.counit_comp_apply (f n) (1 ⊗ₜ a)
    rw [← hg, TensorProduct.counit_tmul, TensorProduct.counit_tmul] at this
    apply (TensorProduct.rid R _).injective
    simpa using this
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.map_comp_comul_apply (f n) (1 ⊗ₜ a)
    rw [← hg, comul_one_tmul_eq_distribBaseChange, comul_one_tmul_eq_distribBaseChange] at this
    apply (AlgebraTensorModule.distribBaseChange R (R ⧸ I ^ n) B B).injective
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [← this]
    induction (Coalgebra.comul a : A ⊗[R] A) with
    | zero => simp
    | tmul x y => simp [hg]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/- English proof (translation)
Take `⟨g, hg, hu⟩` from `existsUnique_bialgHom_of_compatible_tensor I (A := A) (B := B) (fun n ↦ (f n).toBialgHom) hf`. Take `⟨e, he, -⟩` from `existsUnique_algEquiv_of_compatible_tensor I (A := A) (B := B) (fun n ↦ (f n).toAlgEquiv) hf`. Establish `hge : ⇑g = e` using `funext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ (hg n a).trans (he n a).symm`. Conclude with `⟨.ofBijective g (hge ▸ e.bijective), hg, fun g' hg' ↦ BialgEquiv.ext fun a ↦ congr($(hu g' hg') a)⟩`.
-/
theorem existsUnique_bialgEquiv_of_compatible_tensor [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_bialgHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toBialgHom) hf
  obtain ⟨e, he, -⟩ := existsUnique_algEquiv_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toAlgEquiv) hf
  have hge : ⇑g = e := funext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ (hg n a).trans (he n a).symm
  exact ⟨.ofBijective g (hge ▸ e.bijective), hg,
    fun g' hg' ↦ BialgEquiv.ext fun a ↦ congr($(hu g' hg') a)⟩

end

end Tensor

end GlobalTheory
