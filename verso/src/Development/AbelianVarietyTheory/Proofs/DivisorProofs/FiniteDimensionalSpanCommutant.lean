import Mathlib

noncomputable section
namespace GlobalTheory.FiniteLengthCommutant

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Break down `hirr _ (hker c) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)`. Establish `hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.range_eq_top]`.

Break down `hirr _ (hran c) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1)` using `LinearMap.mem_range_self _ _`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hv₀ (hinj c (by rw [h1, map_zero]))`.

Conclude with `h`. Establish `hrep : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p)`. Introduce `p hp`. Establish `hs` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree`. Establish `hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1`.

Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `key : ∀ m : Multiset ℂ, Function.Injective (Polynomial.aeval T (m.map fun a => Polynomial.X - Polynomial.C a).prod)`. Introduce `m`. Proceed by induction on `m using Multiset.induction_on with`.

Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]`. Conclude with `Function.injective_id`. Consider the case `cons a m ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`.

Use `Function.Injective.comp ?_ ih` and prove the remaining obligations. Rewrite using `[hlin]`. Conclude with `hinj a`. Rewrite using `[← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`. Use `Function.Injective.comp ?_ (key _)` and prove the remaining obligations.

Rewrite using `[Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]`. Introduce `x y hxy`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply] at hxy`. Conclude with `smul_right_injective V (Polynomial.leadingCoeff_ne_zero.mpr hp) hxy`. Set `S : ℂ → V ≃ₗ[ℂ] V` to `fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩`.

Set `w : ℂ → V` to `fun c => (S c).symm v₀`. Establish `hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀` using `fun c => (S c).apply_symm_apply v₀`. Establish `hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1`. Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Establish `hli : LinearIndependent ℂ w`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`. Set `q : ℂ → Polynomial ℂ` to `fun c => ∏ d ∈ s.erase c, (Polynomial.X - Polynomial.C d)`. Establish `hq : ∀ c ∈ s, Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d)) (w c) = Polynomial.aeval T (q c) v₀`.

Introduce `c hc`. Rewrite using `[← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]`. Establish `h0 : Polynomial.aeval T (∑ c ∈ s, g c • q c) v₀ = 0`. Establish `h2` using `congrArg (Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d))) hsum`. Rewrite `h2` using `[map_zero, map_sum]`.

Rewrite using `[map_sum, LinearMap.sum_apply, ← h2]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]`. Establish `hp0 : ∑ c ∈ s, g c • q c = 0`. Assume the negation of the conclusion as `hp`.

Conclude with `hv₀ (hrep _ hp (by rw [h0, map_zero]))`. Establish `h3` using `congrArg (Polynomial.eval i) hp0`. Rewrite `h3` using `[Polynomial.eval_finset_sum, Finset.sum_eq_single i]`. Simplify using `only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Polynomial.eval_zero] at h3`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[Finset.prod_eq_zero_iff]`. Take `⟨d, hd, hd0⟩` from `h`. Conclude with `(Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm`.

Introduce `c hc hci`. Simplify using `only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]`. Introduce `h`. Conclude with `absurd hi h`.

Establish `h4` using `hli.cardinal_le_rank`. Rewrite `h4` using `[Cardinal.mk_complex]`. Conclude with `absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)`.
-/
theorem scalar_of_irred {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V → Prop)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (hirr : ∀ N, P N → N = ⊥ ∨ N = ⊤) (T : Module.End ℂ V)
    (hker : ∀ c : ℂ, P (LinearMap.ker (T - c • 1))) (hran : ∀ c : ℂ, P (LinearMap.range (T - c • 1))) :
    ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr _ (hker c) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr _ (hran c) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  have hrep : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p) := by
    intro p hp
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
    have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
      intro a; simp [Algebra.algebraMap_eq_smul_one]
    have key : ∀ m : Multiset ℂ,
        Function.Injective (Polynomial.aeval T (m.map fun a => Polynomial.X - Polynomial.C a).prod) := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
        simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
        exact Function.injective_id
      | cons a m ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
        refine Function.Injective.comp ?_ ih
        rw [hlin]; exact hinj a
    rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
    refine Function.Injective.comp ?_ (key _)
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    intro x y hxy
    simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
    exact smul_right_injective V (Polynomial.leadingCoeff_ne_zero.mpr hp) hxy
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → Polynomial ℂ := fun c => ∏ d ∈ s.erase c, (Polynomial.X - Polynomial.C d)
    have hq : ∀ c ∈ s, Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d)) (w c) =
        Polynomial.aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : Polynomial.aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (hrep _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul, Polynomial.eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

section Hom

variable {R : Type} [Ring R] [Algebra ℂ R]

/- English proof (translation)
Distinguish the cases in `h : ∀ f : M →ₗ[R] N, f = 0`. Use `haveI : Subsingleton (M →ₗ[R] N) := ⟨fun a b => (h a).trans (h b).symm⟩ infer_instance`. Use `push_neg at h`. Take `⟨f, hf⟩` from `h`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)`.

Establish `htop : Submodule.span ℂ {f} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `g _`. Set `T : M →ₗ[R] M` to `e.symm.toLinearMap ∘ₗ g`. Establish `hT : ∀ c : ℂ, (T.restrictScalars ℂ - c • 1 : Module.End ℂ M) = (T - c • LinearMap.id : M →ₗ[R] M).restrictScalars ℂ` using `fun c => by`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `scalar_of_irred (fun P : Submodule ℂ M => ∃ Q : Submodule R M, P = Q.restrictScalars ℂ) hM (by`. Introduce and unpack `_ ⟨Q, rfl⟩`. Break down `eq_bot_or_eq_top Q with rfl | rfl` into its components or cases.

Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl)`. Use the proof step `(T.restrictScalars ℂ)`. Use the proof step `(fun c => ⟨LinearMap.ker (T - c • LinearMap.id : M →ₗ[R] M), by rw [hT]; rfl⟩)`. Use the proof step `(fun c => ⟨LinearMap.range (T - c • LinearMap.id : M →ₗ[R] M), by rw [hT]; rfl⟩)`.

Use `Submodule.mem_span_singleton.2 ⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h1 : e.symm (g x) = c • x` using `congrArg (fun u : Module.End ℂ M => u x) hc`. Establish `h2 : g x = f (c • x)`. Rewrite using `[← h1]`.

Conclude with `(e.apply_symm_apply _).symm`. Rewrite using `[h2, LinearMap.smul_apply, LinearMap.map_smul_of_tower]`. Conclude with `⟨⟨{f}, by simpa using htop⟩⟩`.
-/
theorem finiteDimensional_hom_simple (M N : Type) [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (hM : Module.rank ℂ M ≤ Cardinal.aleph0) : FiniteDimensional ℂ (M →ₗ[R] N) := by
  by_cases h : ∀ f : M →ₗ[R] N, f = 0
  · haveI : Subsingleton (M →ₗ[R] N) := ⟨fun a b => (h a).trans (h b).symm⟩
    infer_instance
  push_neg at h
  obtain ⟨f, hf⟩ := h
  let e : M ≃ₗ[R] N := LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)
  have htop : Submodule.span ℂ {f} = ⊤ := by
    rw [eq_top_iff]
    intro g _
    let T : M →ₗ[R] M := e.symm.toLinearMap ∘ₗ g
    have hT : ∀ c : ℂ, (T.restrictScalars ℂ - c • 1 : Module.End ℂ M) =
        (T - c • LinearMap.id : M →ₗ[R] M).restrictScalars ℂ := fun c => by
      ext x; simp
    obtain ⟨c, hc⟩ := scalar_of_irred (fun P : Submodule ℂ M => ∃ Q : Submodule R M, P = Q.restrictScalars ℂ) hM
      (by
        rintro _ ⟨Q, rfl⟩
        rcases eq_bot_or_eq_top Q with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)
      (T.restrictScalars ℂ)
      (fun c => ⟨LinearMap.ker (T - c • LinearMap.id : M →ₗ[R] M), by rw [hT]; rfl⟩)
      (fun c => ⟨LinearMap.range (T - c • LinearMap.id : M →ₗ[R] M), by rw [hT]; rfl⟩)
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    ext x
    have h1 : e.symm (g x) = c • x := congrArg (fun u : Module.End ℂ M => u x) hc
    have h2 : g x = f (c • x) := by
      rw [← h1]; exact (e.apply_symm_apply _).symm
    rw [h2, LinearMap.smul_apply, LinearMap.map_smul_of_tower]
  exact ⟨⟨{f}, by simpa using htop⟩⟩

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (LinearMap.ker g) := Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f) fun b hb => h b hb`. Use `haveI : IsNoetherian ℂ B := isNoetherian_of_range_eq_ker (LinearMap.ker g).subtype g (Submodule.range_subtype _)`. Use `infer_instance`.
-/
theorem finiteDimensional_of_exact {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] [FiniteDimensional ℂ C] (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C)
    (h : ∀ b, g b = 0 → ∃ a, f a = b) : FiniteDimensional ℂ B := by
  haveI : FiniteDimensional ℂ (LinearMap.ker g) :=
    Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f) fun b hb => h b hb
  haveI : IsNoetherian ℂ B := isNoetherian_of_range_eq_ker (LinearMap.ker g).subtype g (Submodule.range_subtype _)
  infer_instance

/- English proof (translation)
Proceed by induction on `hN with`. Consider the case `of_subsingleton => intro _ _`. Use `infer_instance`. Consider the case `@of_simple_quotient N _ _ P _ _ ih`. Introduce `_ _`.

Use `haveI := ih`. Use `haveI := finiteDimensional_hom_simple (R := R) M (N ⧸ P) hM`. Use `finiteDimensional_of_exact (A := M →ₗ[R] P) (C := M →ₗ[R] N ⧸ P) (LinearMap.compRight ℂ P.subtype) (LinearMap.compRight ℂ P.mkQ) ?_` and prove the remaining obligations. Introduce `b hb`. Use `⟨b.codRestrict P fun x => ?_, by ext x; rfl⟩` and prove the remaining obligations.

Use `congrArg (fun u : M →ₗ[R] N ⧸ P => u x) hb` as an intermediate fact. Simplify using `using this`.
-/
theorem finiteDimensional_hom_of_simple (M : Type) [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    [IsSimpleModule R M] (hM : Module.rank ℂ M ≤ Cardinal.aleph0)
    (N : Type) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    ∀ [Module ℂ N] [IsScalarTower ℂ R N], FiniteDimensional ℂ (M →ₗ[R] N) := by
  induction hN with
  | of_subsingleton => intro _ _; infer_instance
  | @of_simple_quotient N _ _ P _ _ ih =>
    intro _ _
    haveI := ih
    haveI := finiteDimensional_hom_simple (R := R) M (N ⧸ P) hM
    refine finiteDimensional_of_exact (A := M →ₗ[R] P) (C := M →ₗ[R] N ⧸ P)
      (LinearMap.compRight ℂ P.subtype) (LinearMap.compRight ℂ P.mkQ) ?_
    intro b hb
    refine ⟨b.codRestrict P fun x => ?_, by ext x; rfl⟩
    have := congrArg (fun u : M →ₗ[R] N ⧸ P => u x) hb
    simpa using this

/- English proof (translation)
Proceed by induction on `hM with`. Consider the case `of_subsingleton => intro _ _ _`. Use `infer_instance`. Consider the case `@of_simple_quotient M _ _ P _ _ ih`. Introduce `_ _ hr`.

Use `haveI := ih ((Submodule.rank_le (P.restrictScalars ℂ)).trans hr)`. Use `haveI := finiteDimensional_hom_of_simple (R := R) (M ⧸ P) ((LinearMap.rank_le_of_surjective (P.mkQ.restrictScalars ℂ) P.mkQ_surjective).trans hr) N hN`. Use `finiteDimensional_of_exact (LinearMap.lcomp ℂ N P.mkQ) (LinearMap.lcomp ℂ N P.subtype) ?_` and prove the remaining obligations. Introduce `b hb`. Use `⟨P.liftQ b fun x hx => ?_, by ext x; rfl⟩` and prove the remaining obligations.

Conclude with `congrArg (fun u : P →ₗ[R] N => u ⟨x, hx⟩) hb`.
-/
theorem finiteDimensional_hom (N : Type) [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
    (hN : IsFiniteLength R N) (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∀ [Module ℂ M] [IsScalarTower ℂ R M], Module.rank ℂ M ≤ Cardinal.aleph0 → FiniteDimensional ℂ (M →ₗ[R] N) := by
  induction hM with
  | of_subsingleton => intro _ _ _; infer_instance
  | @of_simple_quotient M _ _ P _ _ ih =>
    intro _ _ hr
    haveI := ih ((Submodule.rank_le (P.restrictScalars ℂ)).trans hr)
    haveI := finiteDimensional_hom_of_simple (R := R) (M ⧸ P)
      ((LinearMap.rank_le_of_surjective (P.mkQ.restrictScalars ℂ) P.mkQ_surjective).trans hr) N hN
    refine finiteDimensional_of_exact (LinearMap.lcomp ℂ N P.mkQ) (LinearMap.lcomp ℂ N P.subtype) ?_
    intro b hb
    refine ⟨P.liftQ b fun x hx => ?_, by ext x; rfl⟩
    exact congrArg (fun u : P →ₗ[R] N => u ⟨x, hx⟩) hb

end Hom

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `⟨RelEmbedding.wellFounded_iff_isEmpty.2 ⟨fun f => ?_⟩⟩` and prove the remaining obligations. Use `h (L + 1) (fun i => f (L - i)) (fun i j hij => f.map_rel_iff.2 (by` as an intermediate fact. Use `j.2` as an intermediate fact. Establish `: (i : ℕ) < j` using `hij`.

Use `show L - (i : ℕ) > L - j`. Use the proof step `omega))`. Use linear arithmetic over natural numbers and integers. Use `⟨RelEmbedding.wellFounded_iff_isEmpty.2 ⟨fun f => ?_⟩⟩` and prove the remaining obligations. Use `h (L + 1) (fun i => f i) (fun i j hij => f.map_rel_iff.2 hij)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem wellFounded_of_bounded {α : Type} [PartialOrder α] (L : ℕ)
    (h : ∀ (m : ℕ) (N : Fin m → α), StrictMono N → m ≤ L) : WellFoundedLT α ∧ WellFoundedGT α := by
  constructor
  · refine ⟨RelEmbedding.wellFounded_iff_isEmpty.2 ⟨fun f => ?_⟩⟩
    have := h (L + 1) (fun i => f (L - i)) (fun i j hij => f.map_rel_iff.2 (by
      have := j.2; have : (i : ℕ) < j := hij; show L - (i : ℕ) > L - j; omega))
    omega
  · refine ⟨RelEmbedding.wellFounded_iff_isEmpty.2 ⟨fun f => ?_⟩⟩
    have := h (L + 1) (fun i => f i) (fun i j hij => f.map_rel_iff.2 hij)
    omega

/- English proof (translation)
Introduce `V _ _ S hr ⟨L, hL⟩`. Set `R` to `Algebra.adjoin ℂ S`. Take `⟨h1, h2⟩` from `wellFounded_of_bounded (α := Submodule R V) L fun m N hN => hL m (fun i => (N i).restrictScalars ℂ) (fun i j hij => (Submodule.restrictScalarsEmbedding ℂ R V).strictMono (hN hij)) (fun i s hs x hx => (N i).smul_mem (⟨s, Algebra.subset_adjoin hs⟩ : R) hx)`. Establish `hfl : IsFiniteLength R V` using `isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_iff'.2 h2, h1⟩`. Use `haveI := finiteDimensional_hom (R := R) V hfl V hfl hr`.

Establish `hcomm : ∀ T : Subalgebra.centralizer ℂ S, ∀ r : R, T.1 * r.1 = r.1 * T.1`. Introduce `T r`. Establish `: R ≤ Subalgebra.centralizer ℂ {T.1}` using `Algebra.adjoin_le fun s hs t ht => by`. Rewrite using `[Set.mem_singleton_iff.1 ht]`. Conclude with `(T.2 s hs).symm`.

Conclude with `this r.2 _ rfl`. Set `Φ : Subalgebra.centralizer ℂ S →ₗ[ℂ] (V →ₗ[R] V)` to `{ toFun := fun T => { toFun := T.1, map_add' := map_add _, map_smul' := fun r x => congrArg (fun u : Module.End ℂ V => u x) (hcomm T r) } map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Module.Finite.of_injective Φ fun T U h => Subtype.ext (LinearMap.ext fun x => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun u : V →ₗ[R] V => u x) h`.
-/
theorem finiteDimensional_centralizer : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (Module.End ℂ V)),
    Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ i, ∀ s ∈ S, ∀ x ∈ N i, s x ∈ N i) → m ≤ L) →
    FiniteDimensional ℂ (Subalgebra.centralizer ℂ S) := by
  intro V _ _ S hr ⟨L, hL⟩
  let R := Algebra.adjoin ℂ S
  obtain ⟨h1, h2⟩ := wellFounded_of_bounded (α := Submodule R V) L fun m N hN =>
    hL m (fun i => (N i).restrictScalars ℂ)
      (fun i j hij => (Submodule.restrictScalarsEmbedding ℂ R V).strictMono (hN hij))
      (fun i s hs x hx => (N i).smul_mem (⟨s, Algebra.subset_adjoin hs⟩ : R) hx)
  have hfl : IsFiniteLength R V := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_iff'.2 h2, h1⟩
  haveI := finiteDimensional_hom (R := R) V hfl V hfl hr
  have hcomm : ∀ T : Subalgebra.centralizer ℂ S, ∀ r : R, T.1 * r.1 = r.1 * T.1 := by
    intro T r
    have : R ≤ Subalgebra.centralizer ℂ {T.1} := Algebra.adjoin_le fun s hs t ht => by
      rw [Set.mem_singleton_iff.1 ht]; exact (T.2 s hs).symm
    exact this r.2 _ rfl
  let Φ : Subalgebra.centralizer ℂ S →ₗ[ℂ] (V →ₗ[R] V) :=
    { toFun := fun T => { toFun := T.1, map_add' := map_add _,
                          map_smul' := fun r x => congrArg (fun u : Module.End ℂ V => u x) (hcomm T r) }
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ fun T U h => Subtype.ext (LinearMap.ext fun x => ?_)
  exact congrArg (fun u : V →ₗ[R] V => u x) h

/- English proof (translation)
Use `haveI := finiteDimensional_centralizer V S hr hL`. Set `ev : Subalgebra.centralizer ℂ S →ₗ[ℂ] V` to `{ toFun := fun T => T.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨T, hT, rfl⟩`. Conclude with `⟨⟨T, hT⟩, rfl⟩`.
-/
theorem finiteDimensional_span_commutant (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (Module.End ℂ V))
    (hr : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ i, ∀ s ∈ S, ∀ x ∈ N i, s x ∈ N i) → m ≤ L)
    (v : V) :
    FiniteDimensional ℂ (Submodule.span ℂ {w : V | ∃ T : Module.End ℂ V, (∀ s ∈ S, s * T = T * s) ∧ T v = w}) := by
  haveI := finiteDimensional_centralizer V S hr hL
  let ev : Subalgebra.centralizer ℂ S →ₗ[ℂ] V :=
    { toFun := fun T => T.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev) (Submodule.span_le.2 ?_)
  rintro _ ⟨T, hT, rfl⟩
  exact ⟨⟨T, hT⟩, rfl⟩

end GlobalTheory.FiniteLengthCommutant
