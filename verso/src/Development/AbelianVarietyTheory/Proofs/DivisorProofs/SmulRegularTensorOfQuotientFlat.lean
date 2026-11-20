import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `a b hab`. Establish `: f • (a - b) = 0` using `by rw [smul_sub]; exact sub_eq_zero.mpr hab`. Conclude with `sub_eq_zero.mp (h _ this)`.
-/
theorem isSMulRegular_of_smul_eq_zero_imp {A X : Type} [CommRing A] [AddCommGroup X] [Module A X]
    (f : A) (h : ∀ x : X, f • x = 0 → x = 0) : IsSMulRegular X f := by
  intro a b hab
  have : f • (a - b) = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (h _ this)

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [TensorProduct.smul_tmul']`. Consider the case `add a b ha hb => simp [ha, hb, smul_add]`.
-/
theorem rTensor_lsmul_apply_eq_smul {A X Y : Type} [CommRing A] [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : A) (t : X ⊗[A] Y) :
    (LinearMap.lsmul A X f).rTensor Y t = f • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb, smul_add]

/- English proof (translation)
Use `set I : Ideal A := Ideal.span {f} with hI`. Use `haveI := hfl`. Set `B` to `A ⧸ I`. Set `F` to `M →₀ A`. Set `π : F →ₗ[A] M` to `Finsupp.linearCombination A id`.

Establish `hπ : Function.Surjective π` using `Finsupp.linearCombination_id_surjective A M`. Set `K` to `LinearMap.ker π`. Set `ι : K →ₗ[A] F` to `K.subtype`. Establish `hex : Function.Exact ι π` using `LinearMap.exact_subtype_ker_map π`. Establish `kerq : ∀ {X : Type} [AddCommGroup X] [Module A X] (x : X), ((1 : B) ⊗ₜ[A] x = 0) ↔ ∃ y, f • y = x`.

Introduce `X _ _ x`. Rewrite using `[← (quotTensorEquivQuotSMul X I).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules. Establish `hb : Function.Injective (ι.lTensor B)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k : K, (1 : B) ⊗ₜ[A] k = x := by`. Take `⟨k, hk⟩` from `Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul K I x)`. Use `⟨k, (quotTensorEquivQuotSMul K I).injective ?_⟩` and prove the remaining obligations. Rewrite using `[quotTensorEquivQuotSMul_mk_one_tmul, hk]`.

Rewrite `hx` using `[LinearMap.lTensor_tmul]`. Take `⟨y, hy⟩` from `(kerq (ι k)).1 hx`. Establish `hy0 : π y = 0`. Apply `hM` to reduce the goal to its premises. Use `show f • π y = f • 0`.

Rewrite using `[smul_zero, ← map_smul, hy]`. Simplify `k.2` using `[ι]`. Rewrite using `[kerq]`. Conclude with `⟨⟨y, hy0⟩, Subtype.ext hy⟩`. Set `P` to `B ⊗[A] N`.

Establish `hc : Function.Injective (ι.lTensor P)`. Establish `hsurjB : Function.Surjective (π.baseChange B)`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `LinearMap.lTensor_surjective _ hπ`. Establish `hinjB : Function.Injective (ι.baseChange B)`.

Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `hb`. Establish `hexB : Function.Exact (ι.baseChange B) (π.baseChange B)`. Rewrite using `[LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]`. Conclude with `lTensor_exact B hex hπ`.

Establish `h` using `LinearMap.lTensor_injective_of_exact_of_flat (π.baseChange B) hsurjB (ι.baseChange B) hinjB hexB P`. Set `cK` to `AlgebraTensorModule.cancelBaseChange A B B P K`. Set `cF` to `AlgebraTensorModule.cancelBaseChange A B B P F`. Establish `nat : ∀ v, ι.lTensor P (cK v) = cF ((ι.baseChange B).lTensor P v)`. Introduce `v`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul p y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul b k => simp [cK, cF]`. Consider the case `add a c ha hc => simp_all [tmul_add]`. Consider the case `add a c ha hc => simp_all`. Introduce `u v huv`. Take `⟨u, rfl⟩` from `cK.surjective u`.

Take `⟨v, rfl⟩` from `cK.surjective v`. Rewrite `huv` using `[nat, nat]`. Rewrite using `[h (cF.injective huv)]`. Establish `hfB : algebraMap A B f = 0`. Rewrite using `[Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_span_singleton_self f`. Establish `killP : ∀ t : P ⊗[A] F, f • t = 0`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul p x => rw [smul_tmul', ← algebraMap_smul B f p, hfB, zero_smul, zero_tmul]`. Consider the case `add a c ha hc => rw [smul_add, ha, hc, add_zero]`. Set `q : N →ₗ[A] P` to `TensorProduct.mk A B N 1`. Establish `hqs : Function.Surjective q`. Introduce `t`.

Take `⟨n, hn⟩` from `Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul N I t)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Apply `(quotTensorEquivQuotSMul N I).injective` to reduce the goal to its premises. Rewrite using `[← hn]`. Use `show quotTensorEquivQuotSMul N I ((1 : B) ⊗ₜ[A] n) = _`.

Rewrite using `[quotTensorEquivQuotSMul_mk_one_tmul]`. Establish `hqex : Function.Exact (LinearMap.lsmul A N f) q`. Introduce `n`. Simplify using `only [q, TensorProduct.mk_apply, Set.mem_range, LinearMap.lsmul_apply]`. Conclude with `kerq n`.

Establish `ha : IsSMulRegular (N ⊗[A] F) f`. Establish `hinj : Function.Injective ((LinearMap.lsmul A N f).rTensor F)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => hN (by simpa using h))`. Introduce `a b hab`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[rTensor_lsmul_apply_eq_smul, rTensor_lsmul_apply_eq_smul]`.

Conclude with `hab`. Apply `isSMulRegular_of_smul_eq_zero_imp` to reduce the goal to its premises. Introduce `y hy`. Take `⟨z, rfl⟩` from `LinearMap.lTensor_surjective N hπ y`. Establish `h1 : π.lTensor N (f • z) = 0` using `by rw [map_smul, hy]`.

Take `⟨w, hw⟩` from `(lTensor_exact N hex hπ (f • z)).1 h1`. Establish `h2 : ι.lTensor P (q.rTensor K w) = 0`. Establish `: ι.lTensor P (q.rTensor K w) = q.rTensor F (ι.lTensor N w)`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]`. Rewrite using `[this, hw, map_smul, killP]`.

Establish `h3 : q.rTensor K w = 0`. Apply `hc` to reduce the goal to its premises. Rewrite using `[h2, map_zero]`. Take `⟨w', hw'⟩` from `(rTensor_exact K hqex hqs w).1 h3`. Rewrite `hw'` using `[rTensor_lsmul_apply_eq_smul]`.

Establish `h4 : z = ι.lTensor N w'`. Apply `ha` to reduce the goal to its premises. Use `show f • z = f • ι.lTensor N w'`. Rewrite using `[← map_smul, hw', hw]`. Rewrite using `[h4]`.

Conclude with `(lTensor_exact N hex hπ).apply_apply_eq_zero w'`.
-/
theorem isSMulRegular_tensor_of_flat_quot (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M]
    [Module A M] (hM : IsSMulRegular M f)
    (hfl : Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M))
    (N : Type) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f) :
    IsSMulRegular (TensorProduct A N M) f := by
  classical
  set I : Ideal A := Ideal.span {f} with hI
  haveI := hfl
  let B := A ⧸ I
  let F := M →₀ A
  let π : F →ₗ[A] M := Finsupp.linearCombination A id
  have hπ : Function.Surjective π := Finsupp.linearCombination_id_surjective A M
  let K := LinearMap.ker π
  let ι : K →ₗ[A] F := K.subtype
  have hex : Function.Exact ι π := LinearMap.exact_subtype_ker_map π
  have kerq : ∀ {X : Type} [AddCommGroup X] [Module A X] (x : X),
      ((1 : B) ⊗ₜ[A] x = 0) ↔ ∃ y, f • y = x := by
    intro X _ _ x
    rw [← (quotTensorEquivQuotSMul X I).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
      Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb : Function.Injective (ι.lTensor B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨k, rfl⟩ : ∃ k : K, (1 : B) ⊗ₜ[A] k = x := by
      obtain ⟨k, hk⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul K I x)
      refine ⟨k, (quotTensorEquivQuotSMul K I).injective ?_⟩
      rw [quotTensorEquivQuotSMul_mk_one_tmul, hk]
    rw [LinearMap.lTensor_tmul] at hx
    obtain ⟨y, hy⟩ := (kerq (ι k)).1 hx
    have hy0 : π y = 0 := by
      apply hM
      show f • π y = f • 0
      rw [smul_zero, ← map_smul, hy]
      simpa [ι] using k.2
    rw [kerq]
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let P := B ⊗[A] N
  have hc : Function.Injective (ι.lTensor P) := by
    have hsurjB : Function.Surjective (π.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective _ hπ
    have hinjB : Function.Injective (ι.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]; exact hb
    have hexB : Function.Exact (ι.baseChange B) (π.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact B hex hπ
    have h := LinearMap.lTensor_injective_of_exact_of_flat (π.baseChange B) hsurjB (ι.baseChange B)
      hinjB hexB P
    let cK := AlgebraTensorModule.cancelBaseChange A B B P K
    let cF := AlgebraTensorModule.cancelBaseChange A B B P F
    have nat : ∀ v, ι.lTensor P (cK v) = cF ((ι.baseChange B).lTensor P v) := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul p y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b k => simp [cK, cF]
        | add a c ha hc => simp_all [tmul_add]
      | add a c ha hc => simp_all
    intro u v huv
    obtain ⟨u, rfl⟩ := cK.surjective u
    obtain ⟨v, rfl⟩ := cK.surjective v
    rw [nat, nat] at huv
    rw [h (cF.injective huv)]
  have hfB : algebraMap A B f = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self f
  have killP : ∀ t : P ⊗[A] F, f • t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p x => rw [smul_tmul', ← algebraMap_smul B f p, hfB, zero_smul, zero_tmul]
    | add a c ha hc => rw [smul_add, ha, hc, add_zero]
  let q : N →ₗ[A] P := TensorProduct.mk A B N 1
  have hqs : Function.Surjective q := by
    intro t
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul N I t)
    refine ⟨n, ?_⟩
    apply (quotTensorEquivQuotSMul N I).injective
    rw [← hn]
    show quotTensorEquivQuotSMul N I ((1 : B) ⊗ₜ[A] n) = _
    rw [quotTensorEquivQuotSMul_mk_one_tmul]
  have hqex : Function.Exact (LinearMap.lsmul A N f) q := by
    intro n
    simp only [q, TensorProduct.mk_apply, Set.mem_range, LinearMap.lsmul_apply]
    exact kerq n
  have ha : IsSMulRegular (N ⊗[A] F) f := by
    have hinj : Function.Injective ((LinearMap.lsmul A N f).rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => hN (by simpa using h))
    intro a b hab
    apply hinj
    rw [rTensor_lsmul_apply_eq_smul, rTensor_lsmul_apply_eq_smul]
    exact hab
  apply isSMulRegular_of_smul_eq_zero_imp
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective N hπ y
  have h1 : π.lTensor N (f • z) = 0 := by rw [map_smul, hy]
  obtain ⟨w, hw⟩ := (lTensor_exact N hex hπ (f • z)).1 h1
  have h2 : ι.lTensor P (q.rTensor K w) = 0 := by
    have : ι.lTensor P (q.rTensor K w) = q.rTensor F (ι.lTensor N w) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    rw [this, hw, map_smul, killP]
  have h3 : q.rTensor K w = 0 := by
    apply hc
    rw [h2, map_zero]
  obtain ⟨w', hw'⟩ := (rTensor_exact K hqex hqs w).1 h3
  rw [rTensor_lsmul_apply_eq_smul] at hw'
  have h4 : z = ι.lTensor N w' := by
    apply ha
    show f • z = f • ι.lTensor N w'
    rw [← map_smul, hw', hw]
  rw [h4]
  exact (lTensor_exact N hex hπ).apply_apply_eq_zero w'

end GlobalTheory
