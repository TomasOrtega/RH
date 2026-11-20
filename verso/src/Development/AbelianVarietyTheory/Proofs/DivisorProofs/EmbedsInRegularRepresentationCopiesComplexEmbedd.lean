import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq

open Module NumberField

namespace GlobalTheory.BadCount

/- English proof (translation)
Use `conv_lhs => rw [pi_eq_sum_univ' x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`.
-/
theorem semilin_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (x : Fin N → K) : f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]

/- English proof (translation)
Rewrite using `[← h, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[semilin_eq_sum f x]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem top_le_span_single {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (h : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  rw [← h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [semilin_eq_sum f x]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Take `⟨j, hj, hje⟩` from `h`. Set `m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H` to `MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)`. Establish `hm : ∀ x a, (m x).coeff a = τ (x.coeff a)` using `fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _`. Establish `hmi : Function.Injective m`. Introduce `x y hxy`.

Use extensionality with `a`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[← hm, ← hm, hxy]`. Use `⟨{ toFun := fun v i => m (j (T v) i) map_add' := fun v w => ?_ map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`. Use extensionality with `a`. Simplify using `[hs, hm]`. Conclude with `hi (hj (funext fun i => hmi (congrFun hvw i)))`.

Use `show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)`. Rewrite using `[he, hje, map_mul]`. Use `congr 1`. Conclude with `(MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])`.
-/
theorem embReg_of_semilinear {V V' G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [Group G] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (τ : ℂ ≃+* ℂ) (T : V' →+ V)
    (hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v) (hi : Function.Injective T)
    (he : ∀ g v, T (ρ' g v) = ρ g (T v)) (H : Subgroup G) (n : ℕ) (h : EmbReg ρ H n) : EmbReg ρ' H n := by
  obtain ⟨j, hj, hje⟩ := h
  let m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H := MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)
  have hm : ∀ x a, (m x).coeff a = τ (x.coeff a) := fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hmi : Function.Injective m := by
    intro x y hxy
    ext a
    apply τ.injective
    rw [← hm, ← hm, hxy]
  refine ⟨{ toFun := fun v i => m (j (T v) i)
            map_add' := fun v w => ?_
            map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩
  · funext i
    simp
  · funext i
    ext a
    simp [hs, hm]
  · exact hi (hj (funext fun i => hmi (congrFun hvw i)))
  · show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)
    rw [he, hje, map_mul]
    congr 1
    exact (MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

/- English proof (translation)
Introduce `K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h`. Use `haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable`. Take `⟨τ, hτ⟩` from `GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'`. Set `b' : Basis (Fin N) ℂ V'` to `Basis.mk hl' (top_le_span_single f' hsp')`. Establish `hb' : ∀ k, b' k = f' (Pi.single k 1)` using `fun k => Basis.mk_apply _ _ k`.

Set `T : V' →+ V` to `{ toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) map_zero' := by simp map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }`. Establish `hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)` using `fun _ => rfl`. Establish `hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v` using `fun c v => by`. Simplify using `[hT, Finset.smul_sum, mul_smul]`. Establish `hTf : ∀ x, T (f' x) = f x` using `fun x => by`.

Establish `hr : ∀ k, b'.repr (f' x) k = σ' (x k)` using `fun k => by`. Rewrite using `[semilin_eq_sum f' x]`. Simplify using `only [← hb']`. Conclude with `congrFun (b'.repr_sum_self _) k`. Rewrite using `[hT, semilin_eq_sum f x]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hr, ← hτ, RingEquiv.symm_apply_apply]`. Use `embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`.

Rewrite `hv` using `[hT]`. Establish `h0` using `Fintype.linearIndependent_iff.1 hl _ hv`. Apply `b'.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Simplify using `using h0 k`.

Establish `hv : v ∈ Submodule.span ℂ (Set.range f')` using `hsp' ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, rfl⟩` from `hx`. Rewrite using `[he', hTf, hTf, he]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]`.
-/
theorem embReg_of_baseChange : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K))
    (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V)
    (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) →
    (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ),
    GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  intro K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'
  let b' : Basis (Fin N) ℂ V' := Basis.mk hl' (top_le_span_single f' hsp')
  have hb' : ∀ k, b' k = f' (Pi.single k 1) := fun k => Basis.mk_apply _ _ k
  let T : V' →+ V :=
    { toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)
      map_zero' := by simp
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) := fun _ => rfl
  have hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v := fun c v => by
    simp [hT, Finset.smul_sum, mul_smul]
  have hTf : ∀ x, T (f' x) = f x := fun x => by
    have hr : ∀ k, b'.repr (f' x) k = σ' (x k) := fun k => by
      rw [semilin_eq_sum f' x]
      simp only [← hb']
      exact congrFun (b'.repr_sum_self _) k
    rw [hT, semilin_eq_sum f x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr, ← hτ, RingEquiv.symm_apply_apply]
  refine embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT] at hv
    have h0 := Fintype.linearIndependent_iff.1 hl _ hv
    apply b'.repr.injective
    ext k
    simpa using h0 k
  · have hv : v ∈ Submodule.span ℂ (Set.range f') := hsp' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [he', hTf, hTf, he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]

end GlobalTheory.BadCount
