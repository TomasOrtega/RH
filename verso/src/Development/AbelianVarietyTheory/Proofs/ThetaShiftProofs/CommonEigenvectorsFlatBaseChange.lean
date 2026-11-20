import Mathlib

open Matrix TensorProduct

namespace GlobalTheory

namespace EigFlat

variable {A : Type} [CommRing A]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, Matrix.add_vecMul]`. Consider the case `tmul s v`. Use extensionality with `j`.

Simplify using `[Matrix.vecMul, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_right_comm]`.
-/
theorem piScalarRight_lTensor_vecMul {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B]
    (x : B ⊗[A] (a → A)) :
    TensorProduct.piScalarRight A B B b (LinearMap.lTensor B U.vecMulLinear x)
      = (TensorProduct.piScalarRight A B B a x) ᵥ* U.map (algebraMap A B) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.add_vecMul]
  | tmul s v =>
    ext j
    simp [Matrix.vecMul, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_right_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h w`. Take `⟨y, rfl⟩` from `(TensorProduct.piScalarRight A B B b).surjective w`. Rewrite using `[← piScalarRight_lTensor_vecMul, LinearEquiv.map_eq_zero_iff, h y]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩`. Introduce and unpack `⟨cf, hcf⟩`. Take `⟨x, rfl⟩` from `(TensorProduct.piScalarRight A B B a).surjective cf`. Rewrite `hcf` using `[← piScalarRight_lTensor_vecMul]`.

Conclude with `⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩`. Introduce `h y`. Rewrite using `[← (TensorProduct.piScalarRight A B B c).map_eq_zero_iff, piScalarRight_lTensor_vecMul, h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨cf, hcf⟩`.

Take `⟨x, rfl⟩` from `(TensorProduct.piScalarRight A B B a).surjective cf`. Rewrite `hcf` using `[← piScalarRight_lTensor_vecMul]`. Conclude with `⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩`.
-/
theorem exact_iff {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    [DecidableEq b] [DecidableEq c] (U : Matrix a b A) (H : Matrix b c A)
    (B : Type) [CommRing B] [Algebra A B] :
    Function.Exact (LinearMap.lTensor B U.vecMulLinear) (LinearMap.lTensor B H.vecMulLinear) ↔
      ∀ w : b → B, w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∃ cf : a → B, cf ᵥ* U.map (algebraMap A B) = w := by
  constructor
  · intro h w
    obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight A B B b).surjective w
    rw [← piScalarRight_lTensor_vecMul, LinearEquiv.map_eq_zero_iff, h y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
  · intro h y
    rw [← (TensorProduct.piScalarRight A B B c).map_eq_zero_iff, piScalarRight_lTensor_vecMul, h]
    constructor
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩

/- English proof (translation)
Establish `h : (TensorProduct.piScalarRight A B B b) ∘ (LinearMap.lTensor B U.vecMulLinear) = (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) ∘ (TensorProduct.piScalarRight A B B a)`. Use function extensionality and compare the values at `fun x => piScalarRight_lTensor_vecMul U B x`. Rewrite using `[← Function.Injective.of_comp_iff (TensorProduct.piScalarRight A B B b).injective, h, Function.Injective.of_comp_iff' _ (TensorProduct.piScalarRight A B B a).bijective]`.
-/
theorem injective_iff {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B] :
    Function.Injective (LinearMap.lTensor B U.vecMulLinear) ↔
      Function.Injective (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) := by
  have h : (TensorProduct.piScalarRight A B B b) ∘ (LinearMap.lTensor B U.vecMulLinear)
      = (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) ∘ (TensorProduct.piScalarRight A B B a) :=
    funext fun x => piScalarRight_lTensor_vecMul U B x
  rw [← Function.Injective.of_comp_iff (TensorProduct.piScalarRight A B B b).injective, h,
    Function.Injective.of_comp_iff' _ (TensorProduct.piScalarRight A B B a).bijective]

/- English proof (translation)
Establish `hfg : (Submodule.span A (Set.range D)).FG` using `IsNoetherian.noetherian _`. Take `⟨n, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp hfg`. Use `⟨n, Matrix.of fun j p => s p.1 j p.2, fun B _ _ w => ?_⟩` and prove the remaining obligations. Set `K : Submodule A (Matrix (Fin g) (Fin g) A)` to `{ carrier := {X | w ᵥ* X.map (algebraMap A B) = 0} zero_mem' := by simp add_mem' := by`. Introduce `X Y hX hY`.

Simplify using `only [Set.mem_setOf_eq] at hX hY ⊢`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.vecMul_add, hX, hY, add_zero]`. Use the proof step `smul_mem' := by`. Introduce `r X hX`. Simplify using `only [Set.mem_setOf_eq] at hX ⊢`.

Establish `: (r • X).map (algebraMap A B) = algebraMap A B r • X.map (algebraMap A B)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.vecMul_smul, hX, smul_zero] }`. Establish `h1 : (∀ i, w ᵥ* (D i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range D) ≤ K`.

Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Both sides reduce to the same expression. Establish `h2 : (∀ i, w ᵥ* (s i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range s) ≤ K`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Both sides reduce to the same expression.

Rewrite using `[h1, ← hs, ← h2]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use function extensionality and compare the values at `j`. Conclude with `congrFun h (i, j)`.

Introduce `h`. Use function extensionality and compare the values at `p`. Conclude with `congrFun (h p.1) p.2`.
-/
theorem exists_matrix [IsNoetherianRing A] {I : Type} {g : ℕ} (D : I → Matrix (Fin g) (Fin g) A) :
    ∃ (n : ℕ) (H : Matrix (Fin g) (Fin n × Fin g) A), ∀ (B : Type) [CommRing B] [Algebra A B]
      (w : Fin g → B), w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∀ i, w ᵥ* (D i).map (algebraMap A B) = 0 := by
  have hfg : (Submodule.span A (Set.range D)).FG := IsNoetherian.noetherian _
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨n, Matrix.of fun j p => s p.1 j p.2, fun B _ _ w => ?_⟩
  let K : Submodule A (Matrix (Fin g) (Fin g) A) :=
    { carrier := {X | w ᵥ* X.map (algebraMap A B) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro X Y hX hY
        simp only [Set.mem_setOf_eq] at hX hY ⊢
        rw [Matrix.map_add _ (map_add _), Matrix.vecMul_add, hX, hY, add_zero]
      smul_mem' := by
        intro r X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have : (r • X).map (algebraMap A B) = algebraMap A B r • X.map (algebraMap A B) := by
          ext i j; simp
        rw [this, Matrix.vecMul_smul, hX, smul_zero] }
  have h1 : (∀ i, w ᵥ* (D i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range D) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  have h2 : (∀ i, w ᵥ* (s i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range s) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  rw [h1, ← hs, ← h2]
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

/- English proof (translation)
Establish `: (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B) = M.map (algebraMap A B) - algebraMap A B ρ • (1 : Matrix (Fin g) (Fin g) B)`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h, Algebra.algebraMap_eq_smul_one, sub_smul]`. Rewrite using `[this, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero]`.
-/
theorem eig_iff {g : ℕ} (M : Matrix (Fin g) (Fin g) A) (ρ : A) (B : Type) [CommRing B]
    [Algebra A B] (w : Fin g → B) :
    w ᵥ* (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B) = 0 ↔
      w ᵥ* M.map (algebraMap A B) = algebraMap A B ρ • w := by
  have : (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B)
      = M.map (algebraMap A B) - algebraMap A B ρ • (1 : Matrix (Fin g) (Fin g) B) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Algebra.algebraMap_eq_smul_one, sub_smul]
  rw [this, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[Matrix.vecMul, dotProduct, Finset.sum_apply]`.
-/
theorem sum_eq {g m : ℕ} (u : Fin m → Fin g → A) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (∑ k, cf k • (fun j => algebraMap A B (u k j)))
      = cf ᵥ* (Matrix.of u).map (algebraMap A B) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

/- English proof (translation)
Establish `h : Matrix.of u * M = ρ • Matrix.of u`. Use extensionality with `k j`. Conclude with `congrFun (hu k) j`. Establish `h2 : (ρ • Matrix.of u).map (algebraMap A B) = algebraMap A B ρ • (Matrix.of u).map (algebraMap A B)`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.vecMul_vecMul, ← Matrix.map_mul, h, h2, Matrix.vecMul_smul]`.
-/
theorem eig_map {g m : ℕ} (u : Fin m → Fin g → A) (M : Matrix (Fin g) (Fin g) A) (ρ : A)
    (hu : ∀ k, u k ᵥ* M = ρ • u k) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (cf ᵥ* (Matrix.of u).map (algebraMap A B)) ᵥ* M.map (algebraMap A B)
      = algebraMap A B ρ • (cf ᵥ* (Matrix.of u).map (algebraMap A B)) := by
  have h : Matrix.of u * M = ρ • Matrix.of u := by
    ext k j
    exact congrFun (hu k) j
  have h2 : (ρ • Matrix.of u).map (algebraMap A B)
      = algebraMap A B ρ • (Matrix.of u).map (algebraMap A B) := by
    ext i j; simp
  rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, h, h2, Matrix.vecMul_smul]

end EigFlat

open EigFlat in

/- English proof (translation)
Introduce `A _ I g m M ρ`. Prove the components needed by the constructor for the conclusion. Introduce `R _ _ _ _ u hu hR S _ _ _ w hw`. Take `⟨n, H, hH⟩` from `exists_matrix (fun i => M i - ρ i • (1 : Matrix (Fin g) (Fin g) A))`. Simplify using `only [eig_iff] at hH`.

Simplify using `only [sum_eq] at hR ⊢`. Establish `hexR : Function.Exact (LinearMap.lTensor R (Matrix.of u).vecMulLinear) (LinearMap.lTensor R H.vecMulLinear)`. Rewrite using `[exact_iff]`. Introduce `v`. Rewrite using `[hH]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨cf, hcf, -⟩` from `hR v hv`. Conclude with `⟨cf, hcf.symm⟩`. Introduce and unpack `⟨cf, rfl⟩ i`.

Conclude with `eig_map u (M i) (ρ i) (fun k => hu k i) R cf`. Establish `hinjR : Function.Injective (LinearMap.lTensor R (Matrix.of u).vecMulLinear)`. Rewrite using `[injective_iff]`. Introduce `c₁ c₂ hc`. Conclude with `(hR _ (fun i => eig_map u (M i) (ρ i) (fun k => hu k i) R c₁)).unique rfl hc`.

Establish `hex` using `(Module.FaithfullyFlat.lTensor_exact_iff_exact A R _ _).mp hexR`. Establish `hinj` using `(Module.FaithfullyFlat.lTensor_injective_iff_injective A R _).mp hinjR`. Establish `hexS` using `(exact_iff _ _ S).mp (Module.Flat.lTensor_exact S hex)`. Establish `hinjS` using `(injective_iff _ S).mp (Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hinj)`. Take `⟨cf, hcf⟩` from `(hexS w).mp ((hH S w).mpr hw)`.

Conclude with `⟨cf, hcf.symm, fun c' hc' => hinjS (hc'.symm.trans hcf.symm)⟩`. Introduce `_ _`. Set `N : Submodule A (Fin g → A)` to `{ carrier := {w | ∀ i, w ᵥ* M i = ρ i • w} zero_mem' := by simp add_mem' := by`. Introduce `x y hx hy i`. Rewrite using `[Matrix.add_vecMul, hx i, hy i, smul_add]`.

Use the proof step `smul_mem' := by`. Introduce `r x hx i`. Rewrite using `[Matrix.smul_vecMul, hx i, smul_comm] }`. Take `⟨n, b⟩` from `Submodule.basisOfPid (Pi.basisFun A (Fin g)) N`. Use `⟨n, fun k => (b k : Fin g → A), fun k i => (b k).2 i, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ cf : Fin n → A, (∑ k, cf k • (b k : Fin g → A)) = ((b.equivFun.symm cf : N) : Fin g → A)`. Introduce `cf`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using the standard rewrite rules. Use `⟨b.equivFun ⟨w, hw⟩, ?_, fun cf hcf => ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[key]`. Simplify using the standard rewrite rules. Use `beta_reduce at hcf`. Rewrite `hcf` using `[key]`.

Establish `: (⟨w, hw⟩ : N) = b.equivFun.symm cf` using `Subtype.ext hcf`. Conclude with `((congrArg b.equivFun this).trans (b.equivFun.apply_symm_apply cf)).symm`.
-/
theorem commonEigenvectors_flat_baseChange :
    ∀ (A : Type) [CommRing A] (I : Type) (g m : ℕ) (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A), (∀ (R : Type) [CommRing R] [Algebra A R] [Module.FaithfullyFlat A R] [IsNoetherianRing A] (u : Fin m → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) → (∀ w : Fin g → R, (∀ i, w ᵥ* (M i).map (algebraMap A R) = algebraMap A R (ρ i) • w) → ∃! cf : Fin m → R, w = ∑ k, cf k • (fun j => algebraMap A R (u k j))) → ∀ (S : Type) [CommRing S] [Algebra A S] [Module.Flat A S] (w : Fin g → S), (∀ i, w ᵥ* (M i).map (algebraMap A S) = algebraMap A S (ρ i) • w) → ∃! cf : Fin m → S, w = ∑ k, cf k • (fun j => algebraMap A S (u k j))) ∧ ∀ [IsDomain A] [IsPrincipalIdealRing A], ∃ (n : ℕ) (u : Fin n → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) ∧ ∀ w : Fin g → A, (∀ i, w ᵥ* M i = ρ i • w) → ∃! cf : Fin n → A, w = ∑ k, cf k • u k := by
  intro A _ I g m M ρ
  constructor
  · intro R _ _ _ _ u hu hR S _ _ _ w hw
    obtain ⟨n, H, hH⟩ := exists_matrix (fun i => M i - ρ i • (1 : Matrix (Fin g) (Fin g) A))
    simp only [eig_iff] at hH
    simp only [sum_eq] at hR ⊢
    have hexR : Function.Exact (LinearMap.lTensor R (Matrix.of u).vecMulLinear)
        (LinearMap.lTensor R H.vecMulLinear) := by
      rw [exact_iff]
      intro v
      rw [hH]
      constructor
      · intro hv
        obtain ⟨cf, hcf, -⟩ := hR v hv
        exact ⟨cf, hcf.symm⟩
      · rintro ⟨cf, rfl⟩ i
        exact eig_map u (M i) (ρ i) (fun k => hu k i) R cf
    have hinjR : Function.Injective (LinearMap.lTensor R (Matrix.of u).vecMulLinear) := by
      rw [injective_iff]
      intro c₁ c₂ hc
      exact (hR _ (fun i => eig_map u (M i) (ρ i) (fun k => hu k i) R c₁)).unique rfl hc
    have hex := (Module.FaithfullyFlat.lTensor_exact_iff_exact A R _ _).mp hexR
    have hinj := (Module.FaithfullyFlat.lTensor_injective_iff_injective A R _).mp hinjR
    have hexS := (exact_iff _ _ S).mp (Module.Flat.lTensor_exact S hex)
    have hinjS := (injective_iff _ S).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hinj)
    obtain ⟨cf, hcf⟩ := (hexS w).mp ((hH S w).mpr hw)
    exact ⟨cf, hcf.symm, fun c' hc' => hinjS (hc'.symm.trans hcf.symm)⟩
  · intro _ _
    let N : Submodule A (Fin g → A) :=
      { carrier := {w | ∀ i, w ᵥ* M i = ρ i • w}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy i
          rw [Matrix.add_vecMul, hx i, hy i, smul_add]
        smul_mem' := by
          intro r x hx i
          rw [Matrix.smul_vecMul, hx i, smul_comm] }
    obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin g)) N
    refine ⟨n, fun k => (b k : Fin g → A), fun k i => (b k).2 i, fun w hw => ?_⟩
    have key : ∀ cf : Fin n → A, (∑ k, cf k • (b k : Fin g → A))
        = ((b.equivFun.symm cf : N) : Fin g → A) := by
      intro cf
      rw [Module.Basis.equivFun_symm_apply]
      simp
    refine ⟨b.equivFun ⟨w, hw⟩, ?_, fun cf hcf => ?_⟩
    · beta_reduce
      rw [key]; simp
    · beta_reduce at hcf
      rw [key] at hcf
      have : (⟨w, hw⟩ : N) = b.equivFun.symm cf := Subtype.ext hcf
      exact ((congrArg b.equivFun this).trans (b.equivFun.apply_symm_apply cf)).symm

end GlobalTheory
