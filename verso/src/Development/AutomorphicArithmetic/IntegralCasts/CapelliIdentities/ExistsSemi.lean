import Mathlib

/- English proof (translation)
Introduce `A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli`. Set `f : K →+ M →+ W` to `{ toFun := fun k => { toFun := fun m => ι k • sp m map_zero' := by simp map_add' := by intro x y; simp [smul_add] } map_zero' := by ext m; simp map_add' := by intro x y; ext m; simp [add_smul] }`. Establish `hfa : ∀ (k : K) (m : M), f k m = ι k • sp m` using `fun _ _ => rfl`. Establish `hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m)`. Introduce `r k m`.

Establish `h` using `hsp r m`. Rewrite using `[hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]`. Set `Ψ : TensorProduct A K M →+ W` to `TensorProduct.liftAddHom f hf`. Establish `hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m` using `fun k m => by`. Simplify using `only [Ψ, TensorProduct.liftAddHom_tmul, hfa]`.

Establish `hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v`. Introduce `k v`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]`.

Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`. Use `⟨Ψ, hΨ, hsemi, ?_, ?_⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero Ψ).2 ?_` and prove the remaining obligations. Introduce `v hv`. Set `b` to `Module.Free.chooseBasis A M`.

Set `bK` to `Algebra.TensorProduct.basis K b`. Establish `hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i)) ((bK.repr v).mapRange ι (map_zero ι))`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]`. Use `conv_lhs => rw [← bK.linearCombination_repr v]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]`.

Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `i _`. Rewrite using `[hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]`. Establish `hl` using `(linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)`. Establish `hr : bK.repr v = 0`.

Use extensionality with `i`. Establish `h` using `DFunLike.congr_fun hl i`. Simplify using `using h`. Simplify using `using hr`. Introduce `w`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, rfl⟩` from `hx`.

Conclude with `⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩`. Consider the case `zero => exact ⟨0, map_zero Ψ⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨c, rfl⟩` from `hy`.

Conclude with `⟨a + c, map_add Ψ a c⟩`. Consider the case `smul c x _ hx`. Take `⟨v, rfl⟩` from `hx`. Conclude with `⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩`. Introduce and unpack `⟨v, rfl⟩`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k m`. Rewrite using `[hΨ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)`.

Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem UpperTheory.Reformulated.B.Ra9.exists_semi :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : Field K] (M : Type) [inst_2 : AddCommGroup M] [inst_3 : _root_.Module A M] [inst_4 : Algebra A K]
    [Module.Free A M] {C W : Type} [inst_6 : Field C] [inst_7 : AddCommGroup W] [inst_8 : _root_.Module C W] (ι : K ≃+* C)
    (sp : M →+ W),
    (∀ (a : A) (m : M), (sp : M → W) (a • m) = (ι : K → C) ((Algebra.algebraMap A K : A → K) a) • (sp : M → W) m) →
      (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun (i : κ) ↦ (sp : M → W) ((b : κ → M) i)) →
        ∃ (Ψ : TensorProduct A K M →+ W),
          (∀ (k : K) (m : M), (Ψ : TensorProduct A K M → W) (k ⊗ₜ[A] m) = (ι : K → C) k • (sp : M → W) m) ∧
            (∀ (k : K) (v : TensorProduct A K M),
                (Ψ : TensorProduct A K M → W) (k • v) = (ι : K → C) k • (Ψ : TensorProduct A K M → W) v) ∧
              Function.Injective (⇑Ψ : TensorProduct A K M → W) ∧
                ∀ (w : W),
                  w ∈ Submodule.span C (Set.range (⇑sp : M → W)) ↔
                    ∃ (v : TensorProduct A K M), (Ψ : TensorProduct A K M → W) v = w := by
  intro A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli
  classical
  let f : K →+ M →+ W :=
    { toFun := fun k =>
        { toFun := fun m => ι k • sp m
          map_zero' := by simp
          map_add' := by intro x y; simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := by intro x y; ext m; simp [add_smul] }
  have hfa : ∀ (k : K) (m : M), f k m = ι k • sp m := fun _ _ => rfl
  have hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m) := by
    intro r k m
    have h := hsp r m
    rw [hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]
  let Ψ : TensorProduct A K M →+ W := TensorProduct.liftAddHom f hf
  have hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m := fun k m => by
    simp only [Ψ, TensorProduct.liftAddHom_tmul, hfa]
  have hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  refine ⟨Ψ, hΨ, hsemi, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Ψ).2 ?_
    intro v hv
    let b := Module.Free.chooseBasis A M
    let bK := Algebra.TensorProduct.basis K b
    have hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i))
        ((bK.repr v).mapRange ι (map_zero ι)) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      conv_lhs => rw [← bK.linearCombination_repr v]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]
    have hl := (linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)
    have hr : bK.repr v = 0 := by
      ext i
      have h := DFunLike.congr_fun hl i
      simpa using h
    simpa using hr
  · intro w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩
      | zero => exact ⟨0, map_zero Ψ⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add Ψ a c⟩
      | smul c x _ hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨v, rfl⟩
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul k m =>
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
