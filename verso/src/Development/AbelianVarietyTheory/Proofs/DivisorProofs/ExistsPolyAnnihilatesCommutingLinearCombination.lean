import Mathlib

noncomputable section

open Polynomial

namespace GlobalTheory.CommutingPoly

/- English proof (translation)
Introduce `M _ _ ι _ A hc c P hP`. Use `letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := Algebra.adjoinCommRingOfComm ℂ (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hc i j)`. Set `S` to `Algebra.adjoin ℂ (Set.range A)`. Set `I : Ideal S` to `{ carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0} add_mem' := by`. Introduce `a b ha hb v hv`.

Simplify using `only [Set.mem_setOf_eq] at ha hb`. Simplify using `[ha v hv, hb v hv]`. Use the proof step `zero_mem' := by intro v _; simp`. Use the proof step `smul_mem' := by`. Introduce `a b hb v hv`.

Use `show ((a * b : S) : Module.End ℂ M) v = 0`. Rewrite using `[Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }`. Establish `hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0` using `fun a => Iff.rfl`. Set `t : ι → S` to `fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩`. Set `q : S →ₐ[ℂ] S ⧸ I` to `Ideal.Quotient.mkₐ ℂ I`.

Establish `hint : ∀ i, IsIntegral ℂ (q (t i))`. Introduce `i`. Use `IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_algHom_apply]`. Apply `(Ideal.Quotient.eq_zero_iff_mem).mpr` to reduce the goal to its premises.

Rewrite using `[hI]`. Introduce `v hv`. Rewrite using `[aeval_subalgebra_coe]`. Conclude with `hv i`. Establish `hs : IsIntegral ℂ (q (∑ i, c i • t i))`.

Rewrite using `[map_sum]`. Conclude with `IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)`. Take `⟨p, hpm, hp⟩` from `hs`. Use `⟨p, hpm.ne_zero, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hq : q (aeval (∑ i, c i • t i) p) = 0`.

Rewrite using `[← aeval_algHom_apply, aeval_def]`. Conclude with `hp`. Establish `hmem : aeval (∑ i, c i • t i) p ∈ I` using `(Ideal.Quotient.eq_zero_iff_mem).mp hq`. Establish `h` using `(hI _).mp hmem v hv`. Rewrite `h` using `[aeval_subalgebra_coe]`.

Establish `hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i`. Rewrite using `[show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]`. Simplify using `[t]`. Rewrite `h` using `[hsum]`. Conclude with `h`.
-/
theorem exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  intro M _ _ ι _ A hc c P hP
  classical
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := Algebra.adjoinCommRingOfComm ℂ
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hc i j)
  let S := Algebra.adjoin ℂ (Set.range A)
  let I : Ideal S :=
    { carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0}
      add_mem' := by
        intro a b ha hb v hv
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha v hv, hb v hv]
      zero_mem' := by intro v _; simp
      smul_mem' := by
        intro a b hb v hv
        show ((a * b : S) : Module.End ℂ M) v = 0
        rw [Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }
  have hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0 :=
    fun a => Iff.rfl
  let t : ι → S := fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let q : S →ₐ[ℂ] S ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hint : ∀ i, IsIntegral ℂ (q (t i)) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩
    rw [aeval_algHom_apply]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    rw [hI]
    intro v hv
    rw [aeval_subalgebra_coe]
    exact hv i
  have hs : IsIntegral ℂ (q (∑ i, c i • t i)) := by
    rw [map_sum]
    exact IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)
  obtain ⟨p, hpm, hp⟩ := hs
  refine ⟨p, hpm.ne_zero, fun v hv => ?_⟩
  have hq : q (aeval (∑ i, c i • t i) p) = 0 := by
    rw [← aeval_algHom_apply, aeval_def]
    exact hp
  have hmem : aeval (∑ i, c i • t i) p ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have h := (hI _).mp hmem v hv
  rw [aeval_subalgebra_coe] at h
  have hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i := by
    rw [show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]
    simp [t]
  rw [hsum] at h
  exact h

end GlobalTheory.CommutingPoly
