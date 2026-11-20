import Mathlib

namespace GlobalTheory

open TensorProduct

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp`. Establish `hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') = (I ^ k).map (algebraMap R C')`. Introduce `k`. Rewrite using `[← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Use `set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) with hφ`.

Establish `hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r`. Introduce `c r`. Simplify using `[φ, Algebra.TensorProduct.lift_tmul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y`.

Establish `key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R', Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t)`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul x r`.

Take `⟨c, hc⟩` from `Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))`. Use `⟨c ⊗ₜ r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]`. Simplify using `[map_mul]`. Consider the case `add a b ha hb`.

Take `⟨ta, hta⟩` from `ha`. Take `⟨tb, htb⟩` from `hb`. Conclude with `⟨ta + tb, by rw [map_add, hta, htb, map_add, map_add]⟩`. Take `⟨s, hs⟩` from `(hi 0).1 (Ideal.Quotient.mk _ y)`. Take `⟨t, ht⟩` from `key s`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h1` using `(Ideal.Quotient.eq).1 (hs.symm.trans ht)`. Establish `h2` using `hJ 1`. Rewrite `h2` using `[pow_one]`. Rewrite using `[h2]`.

Simplify using `using h1`. Introduce `n t ht`. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.one_eq_top, Ideal.map_top]`.

Conclude with `Submodule.mem_top`. Consider the case `succ e`. Rewrite `ht`, the goal using `[← Ideal.map_pow]`. Rewrite `ht` using `[Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Use `set K := (I ^ (e + 1)).map (algebraMap R C) with hK`.

Use `set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC`. Establish `hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R')`. Rewrite using `[Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]`. Use `congr 1`. Use extensionality with `a`.

Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') = K.map (algebraMap C (C ⊗[R] R'))`. Establish `: ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') = algebraMap C (C ⊗[R] R')`. Use extensionality with `c`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`.

Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0`. Introduce `a ha`. Rewrite using `[AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Establish `: (a : C') ∈ K.map (algebraMap C C')` using `Ideal.mem_map_of_mem _ ha`. Rewrite `this` using `[hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Then use the resulting hypothesis. Use `set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') := Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ`. Establish `hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) = Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C')` using `fun c => rfl`. Use `set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' := Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG`.

Establish `hGs : Function.Surjective G` using `Algebra.TensorProduct.map_surjective _ _ ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id`. Establish `hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x r`. Take `⟨c, hc⟩` from `Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))`. Establish `hc'` using `hcomp e x c hc.symm`. Simplify using `only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]`. Use `show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _`.

Rewrite using `[← hc, ← hc']`. Use `congr 1`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add]`. Establish `hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R)`. Use `Algebra.TensorProduct.ext' fun c r => ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, hφt]`. Rewrite using `[map_mul]`. Use `congr 1`. Establish `hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u)` using `fun u => by`. Use `congrArg (fun f => f u) hΛπ'` as an intermediate fact.

Simplify using `using this`. Take `⟨s, hs⟩` from `hGs (πC t)`. Establish `hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _))`. Rewrite using `[RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `ht`.

Rewrite `hs0` using `[(hi e).2]`. Establish `hGz : G s = 0`. Establish `hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]`. Conclude with `hle hs0`. Rewrite using `[← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]`.
-/
theorem quot_tensor_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  intro R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp

  have hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') =
      (I ^ k).map (algebraMap R C') := by
    intro k
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C')
    (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r := by
    intro c r
    simp [φ, Algebra.TensorProduct.lift_tmul]
  refine ⟨?_, ?_⟩
  · intro y
    have key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R',
        Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
          (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t) := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))
        refine ⟨c ⊗ₜ r, ?_⟩
        rw [Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]
        simp [map_mul]
      | add a b ha hb =>
        obtain ⟨ta, hta⟩ := ha
        obtain ⟨tb, htb⟩ := hb
        exact ⟨ta + tb, by rw [map_add, hta, htb, map_add, map_add]⟩
    obtain ⟨s, hs⟩ := (hi 0).1 (Ideal.Quotient.mk _ y)
    obtain ⟨t, ht⟩ := key s
    refine ⟨t, ?_⟩
    have h1 := (Ideal.Quotient.eq).1 (hs.symm.trans ht)
    have h2 := hJ 1
    rw [pow_one] at h2
    rw [h2]
    simpa using h1
  · intro n t ht
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ e =>
    rw [← Ideal.map_pow] at ht ⊢
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at ht
    set K := (I ^ (e + 1)).map (algebraMap R C) with hK
    set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC
    have hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') := by
      rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]
      congr 1
      ext a
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') =
        K.map (algebraMap C (C ⊗[R] R')) := by
      have : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') =
          algebraMap C (C ⊗[R] R') := by
        ext c
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      rfl
    have hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (a : C') ∈ K.map (algebraMap C C') := Ideal.mem_map_of_mem _ ha
      rwa [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') :=
      Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ
    have hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) =
        Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') := fun c => rfl
    set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG
    have hGs : Function.Surjective G :=
      Algebra.TensorProduct.map_surjective _ _
        ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id
    have hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))
        have hc' := hcomp e x c hc.symm
        simp only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _
        rw [← hc, ← hc']
        congr 1
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    have hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R) := by
      refine Algebra.TensorProduct.ext' fun c r => ?_
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, hφt]
      rw [map_mul]
      congr 1
    have hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u) := fun u => by
      have := congrArg (fun f => f u) hΛπ'
      simpa using this
    obtain ⟨s, hs⟩ := hGs (πC t)
    have hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)) := by
      rw [RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [(hi e).2] at hs0
    have hGz : G s = 0 := by
      have hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]
      exact hle hs0
    rw [← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]

end GlobalTheory
