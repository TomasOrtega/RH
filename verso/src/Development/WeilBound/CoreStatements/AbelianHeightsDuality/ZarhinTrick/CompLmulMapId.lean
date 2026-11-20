import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply, map_mul, AlgHom.commutes]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.
-/
theorem comp_lmul_map_id (ε : H →ₐ[K] K) (f : H →ₐ[K] H) (t : H ⊗[K] H) :
    f (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε) t)) =
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f ((Algebra.ofId K H).comp ε) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply,
      AlgHom.comp_apply, Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add s t hs ht => simp only [map_add, hs, ht]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => ext x`. Simplify using `[pw]`. Consider the case `succ n ih`. Use extensionality with `x`.

Establish `key : ∀ t : H ⊗[K] H, ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) t)) = ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H) t))`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`.

Simplify using `only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]`. Rewrite using `[← AlgHom.comp_apply ε (pw Δ ε n), ih]`. Simplify using the standard rewrite rules. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Establish `hx` using `DFunLike.congr_fun hL x`.

Simplify using `only [CounitL, AlgHom.comp_apply, AlgHom.id_apply] at hx`. Use `show ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))) = ε x`. Rewrite using `[key, hx]`.
-/
theorem counit_pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ) :
    ε.comp (pw Δ ε n) = ε := by
  induction n with
  | zero => ext x; simp [pw]
  | succ n ih =>
    ext x
    have key : ∀ t : H ⊗[K] H,
        ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) t)) =
          ε (Algebra.TensorProduct.lmul' K
            (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]
        rw [← AlgHom.comp_apply ε (pw Δ ε n), ih]
        simp
      | add s t hs ht => simp only [map_add, hs, ht]
    have hx := DFunLike.congr_fun hL x
    simp only [CounitL, AlgHom.comp_apply, AlgHom.id_apply] at hx
    show ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))) = ε x
    rw [key, hx]

/- English proof (translation)
Establish `hx0 : ε x = 0` using `hx`. Use `set e : H →ₐ[K] H := (Algebra.ofId K H).comp ε with he`. Establish `gen : ∀ f : H →ₐ[K] H, ε.comp f = ε → ∀ t : H ⊗[K] H, Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f (AlgHom.id K H) t) - Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e (AlgHom.id K H) t) - Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f e t) + …`. Introduce `f hf t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, he, AlgHom.comp_apply, Algebra.ofId_apply]`. Establish `e1 : f a * b - algebraMap K H (ε a) * b - f a * algebraMap K H (ε b) + algebraMap K H (ε a) * algebraMap K H (ε b) = (f a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))` using `by ring`. Rewrite using `[e1, pow_two]`.

Use `Ideal.mul_mem_mul ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hf, AlgHom.commutes]`. Simplify using the standard rewrite rules. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules.

Consider the case `add s t hs ht`. Simplify using `only [map_add]`. Use `Ideal.add_mem _ hs ht using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `n with`.

Consider the case `zero => simp [pw, hx0]`. Consider the case `succ n ih`. Establish `h1` using `gen (pw Δ ε n) (counit_pw Δ ε hL hR n) (Δ x)`. Establish `hLx` using `DFunLike.congr_fun hL x`. Establish `hRx` using `DFunLike.congr_fun hR x`.

Simplify using `only [CounitL, CounitR, AlgHom.comp_apply, AlgHom.id_apply] at hLx hRx`. Rewrite `h1` using `[← comp_lmul_map_id ε (pw Δ ε n), ← comp_lmul_map_id ε e, hRx, hLx]`. Establish `hex : e x = 0` using `by simp [he, hx0]`. Rewrite `h1` using `[hex, add_zero]`. Establish `h2` using `Ideal.add_mem _ h1 ih`.

Establish `hp : pw Δ ε (n + 1) x = Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))` using `rfl`. Rewrite using `[hp]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pw_sub_mem (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ)
    {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε n x - (n : H) * x ∈ RingHom.ker ε ^ 2 := by
  have hx0 : ε x = 0 := hx
  set e : H →ₐ[K] H := (Algebra.ofId K H).comp ε with he
  have gen : ∀ f : H →ₐ[K] H, ε.comp f = ε → ∀ t : H ⊗[K] H,
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f e t) +
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e e t) ∈ RingHom.ker ε ^ 2 := by
    intro f hf t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, he,
        AlgHom.comp_apply, Algebra.ofId_apply]
      have e1 : f a * b - algebraMap K H (ε a) * b - f a * algebraMap K H (ε b) +
          algebraMap K H (ε a) * algebraMap K H (ε b) =
          (f a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) := by ring
      rw [e1, pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hf, AlgHom.commutes]; simp
      · rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    | add s t hs ht =>
      simp only [map_add]
      convert Ideal.add_mem _ hs ht using 1
      ring
  induction n with
  | zero => simp [pw, hx0]
  | succ n ih =>
    have h1 := gen (pw Δ ε n) (counit_pw Δ ε hL hR n) (Δ x)
    have hLx := DFunLike.congr_fun hL x
    have hRx := DFunLike.congr_fun hR x
    simp only [CounitL, CounitR, AlgHom.comp_apply, AlgHom.id_apply] at hLx hRx
    rw [← comp_lmul_map_id ε (pw Δ ε n), ← comp_lmul_map_id ε e, hRx, hLx] at h1
    have hex : e x = 0 := by simp [he, hx0]
    rw [hex, add_zero] at h1
    have h2 := Ideal.add_mem _ h1 ih
    have hp : pw Δ ε (n + 1) x =
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x)) := rfl
    rw [hp]
    convert h2 using 1
    push_cast
    ring

end PositivityTheory.PrwZar.Qi
