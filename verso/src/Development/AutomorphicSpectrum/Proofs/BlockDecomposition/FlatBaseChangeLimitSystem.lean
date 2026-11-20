import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicCompleteTensorFiniteStatement

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerExt

section
variable {W : Type} [CommRing W] (l : ℕ) {A : Type} [CommRing A] [Algebra W A]
  {M : Type*} [AddCommGroup M] [Module W M]

/- English proof (translation)
Establish `h : ((l : W) ^ n) • a = (l : A) ^ n * a`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[← TensorProduct.smul_tmul, h, TensorProduct.smul_tmul', smul_eq_mul]`.
-/
theorem pow_smul_tmul (n : ℕ) (a : A) (m : M) :
    ((l : A) ^ n) • (a ⊗ₜ[W] m) = a ⊗ₜ[W] (((l : W) ^ n) • m) := by
  have h : ((l : W) ^ n) • a = (l : A) ^ n * a := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [← TensorProduct.smul_tmul, h, TensorProduct.smul_tmul', smul_eq_mul]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m => rw [pow_smul_tmul, h, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, add_zero]`.
-/
theorem pow_smul_eq_zero (n : ℕ) (h : ∀ x : M, ((l : W) ^ n) • x = 0) (t : A ⊗[W] M) :
    ((l : A) ^ n) • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [pow_smul_tmul, h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[pow_smul_tmul, LinearMap.lTensor_tmul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.
-/
theorem lTensor_pow_smul (n : ℕ) (v : A ⊗[W] M) :
    LinearMap.lTensor A (((l : W) ^ n) • (LinearMap.id : M →ₗ[W] M)) v = ((l : A) ^ n) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [pow_smul_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, -, rfl⟩`. Conclude with `⟨u, rfl⟩`. Introduce and unpack `⟨u, rfl⟩`.

Conclude with `⟨u, Submodule.mem_top, rfl⟩`.
-/
theorem mem_pow_smul_top {N : Type*} [AddCommGroup N] [Module A N] (n : ℕ) (v : N) :
    v ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A N) ↔ ∃ u : N, v = ((l : A) ^ n) • u := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Submodule.mem_top, rfl⟩
end

section
variable {W : Type} [CommRing W] (l : ℕ) (S : Sys.{1} W) (A : Type) [CommRing A] [Algebra W A]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Establish `hx : S.r n (x.1 (n + 1)) = x.1 n` using `x.2 n`. Simplify using `only [LinearMap.baseChange_tmul]`.

Express the relevant statement in the definitionally equal form `a ⊗ₜ[W] S.r n (x.1 (n + 1)) = a ⊗ₜ[W] x.1 n`. Rewrite using `[hx]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem r_baseChange_pr (n : ℕ) (w : A ⊗[W] S.lim) :
    (S.r n).baseChange A ((pr S (n + 1)).baseChange A w) = (pr S n).baseChange A w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have hx : S.r n (x.1 (n + 1)) = x.1 n := x.2 n
    simp only [LinearMap.baseChange_tmul]
    change a ⊗ₜ[W] S.r n (x.1 (n + 1)) = a ⊗ₜ[W] x.1 n
    rw [hx]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `hex : Function.Exact (((l : W) ^ n) • (LinearMap.id : S.lim →ₗ[W] S.lim)) (pr S n)`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, rfl⟩` from `hker x hx`.

Conclude with `⟨y, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Express the relevant statement in the definitionally equal form `(pr S n) (((l : W) ^ n) • y) = 0`. Rewrite using `[map_smul]`. Conclude with `hkill _`.

Establish `hw' : (LinearMap.lTensor A (pr S n)) w = 0`. Rewrite using `[← LinearMap.baseChange_eq_ltensor]`. Conclude with `hw`. Take `⟨v, rfl⟩` from `(Module.Flat.lTensor_exact A hex w).1 hw'`. Conclude with `⟨v, lTensor_pow_smul l n v⟩`.
-/
theorem exists_eq_pow_smul [Module.Flat W A] (n : ℕ)
    (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : (pr S n).baseChange A w = 0) :
    ∃ v : A ⊗[W] S.lim, w = ((l : A) ^ n) • v := by
  have hex : Function.Exact (((l : W) ^ n) • (LinearMap.id : S.lim →ₗ[W] S.lim)) (pr S n) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hker x hx
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      change (pr S n) (((l : W) ^ n) • y) = 0
      rw [map_smul]
      exact hkill _
  have hw' : (LinearMap.lTensor A (pr S n)) w = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hw
  obtain ⟨v, rfl⟩ := (Module.Flat.lTensor_exact A hex w).1 hw'
  exact ⟨v, lTensor_pow_smul l n v⟩

/- English proof (translation)
Rewrite using `[map_smul]`. Conclude with `pow_smul_eq_zero l n hkill _`.
-/
theorem baseChange_pr_pow_smul (n : ℕ) (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (u : A ⊗[W] S.lim) : (pr S n).baseChange A (((l : A) ^ n) • u) = 0 := by
  rw [map_smul]
  exact pow_smul_eq_zero l n hkill _

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul a m`. Take `⟨y, hy⟩` from `hcok m`. Use `⟨a ⊗ₜ[W] y, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_smul_tmul, ← hy, LinearMap.baseChange_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`. Take `⟨w₁, h₁⟩` from `hx`. Take `⟨w₂, h₂⟩` from `hy`.

Conclude with `⟨w₁ + w₂, by rw [map_add, h₁, h₂, smul_add]⟩`.
-/
theorem exists_baseChange_pr_eq (n c : ℕ)
    (hcok : ∀ (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) (t : A ⊗[W] S.M n) :
    ∃ w : A ⊗[W] S.lim, (pr S n).baseChange A w = ((l : A) ^ c) • t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨y, hy⟩ := hcok m
    refine ⟨a ⊗ₜ[W] y, ?_⟩
    rw [pow_smul_tmul, ← hy, LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, smul_add]⟩

/- English proof (translation)
Use `IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance w fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, mem_pow_smul_top]`. Conclude with `exists_eq_pow_smul l S A n (hkill n) (hker n) w (hw n)`.
-/
theorem eq_zero_of_baseChange_pr [Module.Flat W A]
    [IsHausdorff (Ideal.span {(l : A)}) (A ⊗[W] S.lim)]
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : ∀ n, (pr S n).baseChange A w = 0) : w = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance w fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top]
  exact exists_eq_pow_smul l S A n (hkill n) (hker n) w (hw n)

/- English proof (translation)
Use `choose f hf using fun n => exists_baseChange_pr_eq l S A n c (hcok n) (z n)`. Establish `hstep : ∀ n, f n ≡ f (n + 1) [SMOD ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A (A ⊗[W] S.lim))]`. Introduce `n`. Rewrite using `[SModEq.sub_mem, mem_pow_smul_top]`. Use `exists_eq_pow_smul l S A n (hkill n) (hker n) _ ?_` and prove the remaining obligations.

Rewrite using `[map_sub, ← r_baseChange_pr S A n (f (n + 1)), hf (n + 1), map_smul, hz, hf n, sub_self]`. Establish `hmono : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD ((Ideal.span {(l : A)}) ^ m • ⊤ : Submodule A (A ⊗[W] S.lim))]`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => rfl`.

Consider the case `succ n hmn ih`. Use `ih.trans ?_` and prove the remaining obligations. Rewrite `*` using `[SModEq.sub_mem]`. Conclude with `Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) ((SModEq.sub_mem).1 (hstep n))`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance hmono`.

Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h` using `hL n`. Rewrite `h` using `[SModEq.sub_mem, mem_pow_smul_top]`. Take `⟨u, hu⟩` from `h`. Establish `h0 : (pr S n).baseChange A (f n - L) = 0`.

Rewrite using `[hu]`. Conclude with `baseChange_pr_pow_smul l S A n (hkill n) u`. Rewrite `h0` using `[map_sub, sub_eq_zero, hf n]`. Conclude with `h0.symm`.
-/
theorem exists_lift [Module.Flat W A]
    [IsPrecomplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim)] (c : ℕ)
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (hcok : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x)
    (z : ∀ n, A ⊗[W] S.M n) (hz : ∀ n, (S.r n).baseChange A (z (n + 1)) = z n) :
    ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w = ((l : A) ^ c) • z n := by
  choose f hf using fun n => exists_baseChange_pr_eq l S A n c (hcok n) (z n)
  have hstep : ∀ n, f n ≡ f (n + 1) [SMOD ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro n
    rw [SModEq.sub_mem, mem_pow_smul_top]
    refine exists_eq_pow_smul l S A n (hkill n) (hker n) _ ?_
    rw [map_sub, ← r_baseChange_pr S A n (f (n + 1)), hf (n + 1), map_smul, hz, hf n, sub_self]
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {(l : A)}) ^ m • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem] at *
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) ((SModEq.sub_mem).1 (hstep n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance hmono
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, mem_pow_smul_top] at h
  obtain ⟨u, hu⟩ := h
  have h0 : (pr S n).baseChange A (f n - L) = 0 := by
    rw [hu]
    exact baseChange_pr_pow_smul l S A n (hkill n) u
  rw [map_sub, sub_eq_zero, hf n] at h0
  exact h0.symm

end

/- English proof (translation)
Introduce `W _ _ _ l hl S c hfin hkill hker hcok A _ _ _ _`. Use `haveI hcompl : IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim) := GlobalTheory.T.adic_complete_tensor_finite W l hl A S.lim`. Establish `hinj` using `eq_zero_of_baseChange_pr l S A hkill hker`. Use `⟨hinj, ?_⟩` and prove the remaining obligations. Establish `hlift : ∀ z : (tens A S).lim, ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n)` using `fun z => exists_lift l S A c hkill hker hcok (fun n => z.1 n) fun n => z.2 n`.

Use `choose g hg using hlift`. Use `⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hg⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `hinj _ fun n => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_add, hg, hg, hg]`.

Conclude with `sub_eq_zero.2 (smul_add ((l : A) ^ c) (x.1 n : A ⊗[W] S.M n) (y.1 n : A ⊗[W] S.M n))`. Rewrite using `[← sub_eq_zero]`. Use `hinj _ fun n => ?_` and prove the remaining obligations. Rewrite using `[map_sub, RingHom.id_apply, map_smul, hg, hg]`. Conclude with `sub_eq_zero.2 (smul_comm ((l : A) ^ c) a (x.1 n : A ⊗[W] S.M n))`.
-/
theorem limit_extension_upTo : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  intro W _ _ _ l hl S c hfin hkill hker hcok A _ _ _ _
  haveI hcompl : IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim) :=
    GlobalTheory.T.adic_complete_tensor_finite W l hl A S.lim
  have hinj := eq_zero_of_baseChange_pr l S A hkill hker
  refine ⟨hinj, ?_⟩
  have hlift : ∀ z : (tens A S).lim, ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w =
      ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := fun z =>
    exists_lift l S A c hkill hker hcok (fun n => z.1 n) fun n => z.2 n
  choose g hg using hlift
  refine ⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hg⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, map_add, hg, hg, hg]
    exact sub_eq_zero.2 (smul_add ((l : A) ^ c) (x.1 n : A ⊗[W] S.M n) (y.1 n : A ⊗[W] S.M n))
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, RingHom.id_apply, map_smul, hg, hg]
    exact sub_eq_zero.2 (smul_comm ((l : A) ^ c) a (x.1 n : A ⊗[W] S.M n))

end GlobalTheory.CompanionTheory.TowerExt
