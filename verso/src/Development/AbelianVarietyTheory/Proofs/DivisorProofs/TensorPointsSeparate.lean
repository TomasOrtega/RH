import Mathlib
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_ne_zero, 0, by simp⟩`. Consider the case `tmul k c`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R) k`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hbK : algebraMap R K b ≠ 0`. Simplify using `using hb0`. Use `⟨b, hb0, a • c, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]`. Use `congr 1`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts. Consider the case `add x y hx hy`. Take `⟨s, hs, c, hc⟩` from `hx`. Take `⟨t, ht, d, hd⟩` from `hy`.

Use `⟨s * t, mul_ne_zero hs ht, t • c + s • d, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hc, ← hd, smul_smul, smul_smul, mul_comm t s]`.
-/
theorem exists_smul_eq_one_tmul_of_isFractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (C' : Type) [CommRing C'] [Algebra R C']
    (w : K ⊗[R] C') : ∃ s : R, s ≠ 0 ∧ ∃ c : C', s • w = (1 : K) ⊗ₜ[R] c := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul k c =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap R K b ≠ 0 := by
      simpa using hb0
    refine ⟨b, hb0, a • c, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    field_simp
  | add x y hx hy =>
    obtain ⟨s, hs, c, hc⟩ := hx
    obtain ⟨t, ht, d, hd⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, t • c + s • d, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← hc, ← hd, smul_smul, smul_smul, mul_comm t s]

/- English proof (translation)
Take `⟨s, hs, c, hc⟩` from `exists_smul_eq_one_tmul_of_isFractionRing R K C' w`. Establish `hc0 : c = 0`. Apply `h'` to reduce the goal to its premises. Introduce `ψ`. Establish `h1` using `congrArg (Algebra.TensorProduct.productMap (AlgHom.id R K) ψ) hc`.

Rewrite `h1` using `[map_smul, hw ψ, smul_zero]`. Simplify using `using h1.symm`. Establish `hsK : algebraMap R K s ≠ 0` using `by simpa using hs`. Rewrite `hc` using `[hc0, TensorProduct.tmul_zero, ← algebraMap_smul K s w]`. Conclude with `(smul_eq_zero.mp hc).resolve_left hsK`.
-/
theorem fractionRing_tensor_eq_zero_of_points (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (C' : Type) [CommRing C'] [Algebra R C']
    (h' : ∀ a : C', (∀ ψ : C' →ₐ[R] K, ψ a = 0) → a = 0) (w : K ⊗[R] C')
    (hw : ∀ ψ : C' →ₐ[R] K, Algebra.TensorProduct.productMap (AlgHom.id R K) ψ w = 0) :
    w = 0 := by
  obtain ⟨s, hs, c, hc⟩ := exists_smul_eq_one_tmul_of_isFractionRing R K C' w
  have hc0 : c = 0 := by
    apply h'
    intro ψ
    have h1 := congrArg (Algebra.TensorProduct.productMap (AlgHom.id R K) ψ) hc
    rw [map_smul, hw ψ, smul_zero] at h1
    simpa using h1.symm
  have hsK : algebraMap R K s ≠ 0 := by simpa using hs
  rw [hc0, TensorProduct.tmul_zero, ← algebraMap_smul K s w] at hc
  exact (smul_eq_zero.mp hc).resolve_left hsK

/- English proof (translation)
Introduce `R K _ _ _ _ _ C C' _ _ _ _ _ hfin h h' d hd`. Use `letI : Fintype (C →ₐ[R] K) := Fintype.ofFinite _`. Set `e : C →ₗ[R] ((C →ₐ[R] K) → K)` to `LinearMap.pi fun ψ => ψ.toLinearMap`. Establish `he : Function.Injective e`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Conclude with `h a fun ψ => congrFun ha ψ`. Establish `hinj : Function.Injective (e.rTensor C')` using `Module.Flat.rTensor_preserves_injective_linearMap e he`. Set `P` to `TensorProduct.piLeft R C' (fun _ : (C →ₐ[R] K) => K)`. Establish `key : ∀ (x : C ⊗[R] C') (ψ : C →ₐ[R] K) (ψ' : C' →ₐ[R] K), Algebra.TensorProduct.productMap (AlgHom.id R K) ψ' (P (e.rTensor C' x) ψ) = Algebra.TensorProduct.productMap ψ ψ' x`.

Introduce `x ψ ψ'`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [P, e, TensorProduct.piLeft]`. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]`.

Apply `hinj` to reduce the goal to its premises. Apply `P.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `ψ`. Rewrite using `[map_zero, map_zero]`. Apply `fractionRing_tensor_eq_zero_of_points R K C' h'` to reduce the goal to its premises.

Introduce `ψ'`. Rewrite using `[key]`. Conclude with `hd _`.
-/
theorem tensor_eq_zero_of_points_separate :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (C C' : Type) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C'] [Module.Flat R C'], Finite (C →ₐ[R] K) → (∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0) → (∀ a : C', (∀ ψ : C' →ₐ[R] K, ψ a = 0) → a = 0) → ∀ d : C ⊗[R] C', (∀ Ψ : C ⊗[R] C' →ₐ[R] K, Ψ d = 0) → d = 0 := by
  intro R K _ _ _ _ _ C C' _ _ _ _ _ hfin h h' d hd
  classical
  letI : Fintype (C →ₐ[R] K) := Fintype.ofFinite _
  let e : C →ₗ[R] ((C →ₐ[R] K) → K) := LinearMap.pi fun ψ => ψ.toLinearMap
  have he : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact h a fun ψ => congrFun ha ψ
  have hinj : Function.Injective (e.rTensor C') :=
    Module.Flat.rTensor_preserves_injective_linearMap e he
  let P := TensorProduct.piLeft R C' (fun _ : (C →ₐ[R] K) => K)
  have key : ∀ (x : C ⊗[R] C') (ψ : C →ₐ[R] K) (ψ' : C' →ₐ[R] K),
      Algebra.TensorProduct.productMap (AlgHom.id R K) ψ' (P (e.rTensor C' x) ψ)
        = Algebra.TensorProduct.productMap ψ ψ' x := by
    intro x ψ ψ'
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, e, TensorProduct.piLeft]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  apply hinj
  apply P.injective
  funext ψ
  rw [map_zero, map_zero]
  apply fractionRing_tensor_eq_zero_of_points R K C' h'
  intro ψ'
  rw [key]
  exact hd _

end GlobalTheory
