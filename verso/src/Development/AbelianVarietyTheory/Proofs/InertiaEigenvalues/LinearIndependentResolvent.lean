import Mathlib

namespace GlobalTheory.NonUnitShift

open Polynomial

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hp hp0`. Establish `hc : p.coeff 0 ≠ 0`.

Introduce `h0`. Apply `hp0` to reduce the goal to its premises. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hp, h0, map_zero]`. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.aeval_C]`. Conclude with `(isUnit_iff_ne_zero.2 hc).map (algebraMap ℂ (Module.End ℂ V))`.

Consider the case `succ n ih`. Introduce `p hp hp0`. Establish `hdeg : 0 < p.degree`. Rewrite using `[Polynomial.degree_eq_natDegree hp0, hp]`. Conclude with `Nat.succ_pos n` after adjusting the coercions.

Take `⟨r, hr⟩` from `IsAlgClosed.exists_root p hdeg.ne'`. Take `⟨q, hq⟩` from `Polynomial.dvd_iff_isRoot.2 hr`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Rewrite `hq` using `[mul_zero]`.

Conclude with `hp0 hq`. Establish `hqdeg : q.natDegree = n`. Establish `h2` using `congrArg Polynomial.natDegree hq`. Rewrite `h2` using `[Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0, Polynomial.natDegree_X_sub_C, hp]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hq, map_mul]`. Use `IsUnit.mul ?_ (ih q hqdeg hq0)` and prove the remaining obligations. Simplify `h r` using `[map_sub]`.
-/
theorem isUnit_aeval (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → IsUnit (aeval T p) := by
  intro n
  induction n with
  | zero =>
    intro p hp hp0
    have hc : p.coeff 0 ≠ 0 := by
      intro h0
      apply hp0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp, h0, map_zero]
    rw [Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.aeval_C]
    exact (isUnit_iff_ne_zero.2 hc).map (algebraMap ℂ (Module.End ℂ V))
  | succ n ih =>
    intro p hp hp0
    have hdeg : 0 < p.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, hp]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg.ne'
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 hr
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hp0 hq
    have hqdeg : q.natDegree = n := by
      have h2 := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0, Polynomial.natDegree_X_sub_C, hp] at h2
      omega
    rw [hq, map_mul]
    refine IsUnit.mul ?_ (ih q hqdeg hq0)
    simpa [map_sub] using h r

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hs i hi`. Use `set q : ℂ[X] := ∑ j ∈ s, C (g j) * ∏ k ∈ s.erase j, (X - C k) with hq`. Establish `key : aeval T q v = 0`. Establish `h1 : aeval T (∏ k ∈ s, (X - C k)) (∑ j ∈ s, g j • w j) = 0`.

Rewrite using `[hs, map_zero]`. Rewrite using `[← h1, hq, map_sum, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul s _ hj, map_mul, map_mul, aeval_C, map_sub, aeval_X, aeval_C, map_smul, Module.End.mul_apply, Module.End.mul_apply, hw, Module.algebraMap_end_apply]`. Establish `hq0 : q = 0`.

Assume the negation of the conclusion as `hne`. Establish `hu` using `isUnit_aeval T h _ q rfl hne`. Establish `hinj` using `((Module.End.isUnit_iff _).1 hu).1`. Conclude with `hv (hinj (by rw [key, map_zero]))`. Establish `h2 : eval i q = g i * ∏ k ∈ s.erase i, (i - k)`.

Rewrite using `[hq, eval_finsetSum, Finset.sum_eq_single i]`. Simplify using `[eval_prod]`. Introduce `j _ hji`. Rewrite using `[eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hji.symm, hi⟩) (by simp), mul_zero]`. Introduce `h3`.

Conclude with `absurd hi h3`. Rewrite `h2` using `[hq0, eval_zero]`. Break down `mul_eq_zero.1 h2.symm with h3 | h3` into its components or cases. Conclude with `h3`. Take `⟨k, hk, hk0⟩` from `Finset.prod_eq_zero_iff.1 h3`.

Conclude with `absurd (sub_eq_zero.1 hk0).symm (Finset.mem_erase.1 hk).1`.
-/
theorem linearIndependent_resolvent (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) (v : V) (hv : v ≠ 0)
    (w : ℂ → V) (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  set q : ℂ[X] := ∑ j ∈ s, C (g j) * ∏ k ∈ s.erase j, (X - C k) with hq
  have key : aeval T q v = 0 := by
    have h1 : aeval T (∏ k ∈ s, (X - C k)) (∑ j ∈ s, g j • w j) = 0 := by
      rw [hs, map_zero]
    rw [← h1, hq, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul s _ hj, map_mul, map_mul, aeval_C, map_sub, aeval_X, aeval_C,
      map_smul, Module.End.mul_apply, Module.End.mul_apply, hw, Module.algebraMap_end_apply]
  have hq0 : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval T h _ q rfl hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [key, map_zero]))
  have h2 : eval i q = g i * ∏ k ∈ s.erase i, (i - k) := by
    rw [hq, eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro j _ hji
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hji.symm, hi⟩) (by simp),
        mul_zero]
    · intro h3
      exact absurd hi h3
  rw [hq0, eval_zero] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact h3
  · obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 h3
    exact absurd (sub_eq_zero.1 hk0).symm (Finset.mem_erase.1 hk).1

/- English proof (translation)
Introduce `V _ _ _ hrank T`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Set `w : ℂ → V` to `fun c => (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) v`.

Establish `hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v` using `fun c => by`. Establish `h1 : ((hcon c).unit : Module.End ℂ V) * (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = 1` using `(hcon c).unit.mul_inv`. Rewrite `h1` using `[IsUnit.unit_spec]`. Establish `h2` using `congrArg (fun f : Module.End ℂ V => f v) h1`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply] at h2`.

Conclude with `h2`. Establish `hli` using `linearIndependent_resolvent T hcon v hv w hw`. Establish `h1 : Cardinal.mk ℂ ≤ Cardinal.aleph0` using `hli.cardinal_le_rank.trans hrank`. Rewrite `h1` using `[Cardinal.mk_complex]`. Conclude with `absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)`.
-/
theorem exists_not_isUnit_sub : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Nontrivial V], Module.rank ℂ V ≤ Cardinal.aleph0 → ∀ (T : Module.End ℂ V), ∃ (c : ℂ), ¬IsUnit (T - (Algebra.algebraMap ℂ (Module.End ℂ V) : ℂ → Module.End ℂ V) c) := by
  intro V _ _ _ hrank T
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w : ℂ → V := fun c => (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) v
  have hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v := fun c => by
    have h1 : ((hcon c).unit : Module.End ℂ V) * (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = 1 :=
      (hcon c).unit.mul_inv
    rw [IsUnit.unit_spec] at h1
    have h2 := congrArg (fun f : Module.End ℂ V => f v) h1
    simp only [Module.End.mul_apply, Module.End.one_apply] at h2
    exact h2
  have hli := linearIndependent_resolvent T hcon v hv w hw
  have h1 : Cardinal.mk ℂ ≤ Cardinal.aleph0 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory.NonUnitShift
