import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullBaseChange

/- English proof (translation)
Use `set K : Ideal (R ⊗[B] C) := I.map (algebraMap B (R ⊗[B] C)) with hK`. Establish `hKQ : K ≤ Q₁`. Rewrite using `[hK, Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Establish `h1` using `hI (Ideal.mem_map_of_mem (algebraMap B R) hb)`.

Simplify `h1` using `[Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply]`. Establish `key : ∀ (b : B) (c : C), (1 : R) ⊗ₜ[B] (b • c) = (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c)`. Introduce `b c`. Rewrite using `[TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]`. Set `φ : M ⊗[B] C →+ (R ⊗[B] C) ⊗[R] M` to `(TensorProduct.liftAddHom { toFun := fun m => { toFun := fun c => ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m map_zero' := by simp map_add' := by intro a b; simp [TensorProduct.tmul_add, TensorProduct.add_tmul] } map_zero' := by ext c; simp map_add' := by intro a b; ext c; simp [TensorProduct.tmul …`.

Introduce `b m c`. Establish `h : (b • m : M) = (algebraMap B R b) • m` using `(algebraMap_smul R b m).symm`. Simplify using `only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, key]`. Rewrite using `[TensorProduct.smul_tmul]))`. Establish `hφ : ∀ (m : M) (c : C), φ (m ⊗ₜ[B] c) = ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m` using `fun m c => rfl`.

Establish `hmem : ∀ (n : ℕ) (z : M), z ∈ (I ^ n • ⊤ : Submodule B M) → ∀ c : C, ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] z ∈ (K ^ n • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M))`. Introduce `n z hz c`. Proceed by induction on `hz using Submodule.smul_induction_on' with`. Consider the case `smul b hb m hm`. Establish `h : (b • m : M) = (algebraMap B R b) • m` using `(algebraMap_smul R b m).symm`.

Establish `h2 : ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] (b • m) = (algebraMap B (R ⊗[B] C) b) • (((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m)`. Establish `h3 : (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) = (algebraMap B (R ⊗[B] C) b) • ((1 : R) ⊗ₜ[B] c)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]`. Simplify using the standard rewrite rules. Rewrite using `[h, ← TensorProduct.smul_tmul, h3, TensorProduct.smul_tmul']`.

Rewrite using `[h2]`. Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Rewrite using `[hK, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hb`. Consider the case `add x _ y _ hx hy`.

Rewrite using `[TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Establish `hall : ∀ n : ℕ, ∀ x : (I ^ (n + 1) • ⊤ : Submodule B M) ⊗[B] C, φ ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C x) ∈ (K ^ (n + 1) • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M))`. Introduce `n x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul z c`. Simplify `hmem (n + 1) z z.2 c` using `[hφ]`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Establish `hone : φ (y ⊗ₜ[B] (1 : C)) = (1 : R ⊗[B] C) ⊗ₜ[R] y` using `rfl`. Establish `hinf : ((1 : R ⊗[B] C) ⊗ₜ[R] y) ∈ (⨅ i : ℕ, K ^ i • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M))`. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`.

Take `⟨x, hx⟩` from `hy i`. Establish `h` using `hall i x`. Rewrite `h` using `[hx, hone]`. Conclude with `Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h`. Use `haveI : Module.Finite (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := Module.Finite.base_change R (R ⊗[B] C) M`.

Use `haveI : IsNoetherian (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := isNoetherian_of_isNoetherianRing_of_finite _ _`. Take `⟨⟨r, hr⟩, e⟩` from `(Ideal.mem_iInf_smul_pow_eq_bot_iff K _).1 hinf`. Use `⟨1 - r, ?_, ?_⟩` and prove the remaining obligations. Introduce `hw`. Conclude with `hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by`.

Use `Q₁.add_mem hw (hKQ hr)` as an intermediate fact. Simplify using `using this))`. Rewrite using `[sub_smul, one_smul]`. Conclude with `sub_eq_zero.2 e.symm`.
-/
theorem krull_after_base_change {B R C M : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M)
    (hy : ∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈
      LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C))
    (Q₁ : Ideal (R ⊗[B] C)) (hQ : Q₁.IsPrime)
    (hI : I.map (algebraMap B R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)) :
    ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  classical
  set K : Ideal (R ⊗[B] C) := I.map (algebraMap B (R ⊗[B] C)) with hK
  have hKQ : K ≤ Q₁ := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro b hb
    have h1 := hI (Ideal.mem_map_of_mem (algebraMap B R) hb)
    simpa [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply] using h1
  have key : ∀ (b : B) (c : C), (1 : R) ⊗ₜ[B] (b • c) = (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) := by
    intro b c
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one]
  let φ : M ⊗[B] C →+ (R ⊗[B] C) ⊗[R] M :=
    (TensorProduct.liftAddHom
      { toFun := fun m =>
          { toFun := fun c => ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m
            map_zero' := by simp
            map_add' := by intro a b; simp [TensorProduct.tmul_add, TensorProduct.add_tmul] }
        map_zero' := by ext c; simp
        map_add' := by intro a b; ext c; simp [TensorProduct.tmul_add] }
      (by
        intro b m c
        have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, key]
        rw [TensorProduct.smul_tmul]))
  have hφ : ∀ (m : M) (c : C), φ (m ⊗ₜ[B] c) = ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m := fun m c => rfl
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (I ^ n • ⊤ : Submodule B M) → ∀ c : C,
      ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] z ∈ (K ^ n • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n z hz c
    induction hz using Submodule.smul_induction_on' with
    | smul b hb m hm =>
      have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
      have h2 : ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] (b • m) =
          (algebraMap B (R ⊗[B] C) b) • (((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m) := by
        have h3 : (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) =
            (algebraMap B (R ⊗[B] C) b) • ((1 : R) ⊗ₜ[B] c) := by
          rw [Algebra.TensorProduct.algebraMap_apply, smul_eq_mul,
            Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
          simp
        rw [h, ← TensorProduct.smul_tmul, h3, TensorProduct.smul_tmul']
      rw [h2]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hb
    | add x _ y _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have hall : ∀ n : ℕ, ∀ x : (I ^ (n + 1) • ⊤ : Submodule B M) ⊗[B] C,
      φ ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C x) ∈
        (K ^ (n + 1) • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      simpa [hφ] using hmem (n + 1) z z.2 c
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  have hone : φ (y ⊗ₜ[B] (1 : C)) = (1 : R ⊗[B] C) ⊗ₜ[R] y := rfl
  have hinf : ((1 : R ⊗[B] C) ⊗ₜ[R] y) ∈
      (⨅ i : ℕ, K ^ i • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨x, hx⟩ := hy i
    have h := hall i x
    rw [hx, hone] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h
  haveI : Module.Finite (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := Module.Finite.base_change R (R ⊗[B] C) M
  haveI : IsNoetherian (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨⟨r, hr⟩, e⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff K _).1 hinf
  refine ⟨1 - r, ?_, ?_⟩
  · intro hw
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := Q₁.add_mem hw (hKQ hr)
      simpa using this))
  · rw [sub_smul, one_smul]
    exact sub_eq_zero.2 e.symm

end GlobalTheory.CompanionTheory.KrullBaseChange
