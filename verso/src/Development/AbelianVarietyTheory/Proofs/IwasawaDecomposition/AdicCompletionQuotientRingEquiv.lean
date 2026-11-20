import Mathlib

open IsLocalRing

namespace GlobalTheory.AdicQuot

open AdicCompletion

variable {A : Type} [CommRing A] (J q : Ideal A)

/- English proof (translation)
Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]`. Both sides reduce to the same expression.
-/
theorem mem_smul_top_iff (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  rfl

/- English proof (translation)
Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.le_comap_map`.
-/
theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (Ideal.Quotient.mk q)) ^ n).comap (Ideal.Quotient.mk q) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* (A ⧸ q) ⧸ (J.map (Ideal.Quotient.mk q)) ^ n :=
  (Ideal.quotientMap _ (Ideal.Quotient.mk q) (pow_le_comap J q n)).comp (evalₐ J n).toRingHom

/- English proof (translation)
Simplify using `[lev, evalₐ_mk, Ideal.quotientMap_mk]`.
-/
theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (Ideal.Quotient.mk q (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

/- English proof (translation)
Use extensionality with `x`. Take `⟨s, rfl⟩` from `AdicCompletion.mk_surjective J A x`. Establish `h1` using `s.property hle`. Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Simplify using `only [RingHom.comp_apply, lev_mk]`.

Rewrite using `[Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]`. Establish `h3 : s n - s m ∈ J ^ m` using `by rw [← neg_sub]; exact neg_mem h1`. Conclude with `Ideal.mem_comap.mp (pow_le_comap J q m h3)`.
-/
theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev J q n) = lev J q m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap J q m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
  AdicCompletion.liftRingHom _ (lev J q) (fun hle ↦ lev_compat J q hle)

/- English proof (translation)
Simplify using `[psi]`.
-/
theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by
  simp [psi]

/- English proof (translation)
Rewrite using `[map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]`. Both sides reduce to the same expression.
-/
theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Establish `hz : map J (Submodule.mkQ q) x = 0`. Take `⟨s, rfl⟩` from `AdicCompletion.mk_surjective J A x`.

Use extensionality with `n`. Use `(map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])` as an intermediate fact. Simplify using `using this`. Take `⟨y, rfl⟩` from `((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ) Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz`. Take `⟨t, rfl⟩` from `ofTensorProduct_surjective_of_finite J q y`.

Use `clear hx hz`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r m`. Rewrite using `[ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]`.

Establish `hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A)`. Rewrite using `[AdicCompletion.algebraMap_apply]`. Both sides reduce to the same expression. Rewrite using `[hm]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)`.

Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `add_mem ha hb`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`.

Use `ext_evalₐ fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]`.
-/
theorem ker_psi [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Submodule.mkQ q) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]

/- English proof (translation)
Introduce `y`. Take `⟨t, rfl⟩` from `AdicCompletion.mk_surjective _ _ y`. Set `t' : AdicCauchySequence J (A ⧸ q)` to `⟨t.val, fun {m n} hmn ↦ by`. Establish `h` using `t.property hmn`. Rewrite `h` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.

Rewrite using `[SModEq.sub_mem, mem_smul_top_iff]`. Conclude with `h⟩`. Take `⟨x, hx⟩` from `map_surjective J (Submodule.mkQ_surjective q) (AdicCompletion.mk J _ t')`. Take `⟨s, rfl⟩` from `AdicCompletion.mk_surjective J A x`. Use `⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[evalₐ_psi, evalₐ_mk]`. Use `(map_val_mk_eq_iff J q s n (t n)).mp ?_` and prove the remaining obligations. Rewrite using `[hx]`. Both sides reduce to the same expression.
-/
theorem psi_surjective [IsNoetherianRing A] : Function.Surjective (psi J q) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J (A ⧸ q) := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (Submodule.mkQ_surjective q) (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff J q s n (t n)).mp ?_
  rw [hx]; rfl

end GlobalTheory.AdicQuot

/- English proof (translation)
Introduce `A _ _ J q`. Conclude with `⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩`.
-/
theorem GlobalTheory.adicCompletion_quotient_ringEquiv :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A),
      Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+*
        AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  intro A _ _ J q
  exact ⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩
