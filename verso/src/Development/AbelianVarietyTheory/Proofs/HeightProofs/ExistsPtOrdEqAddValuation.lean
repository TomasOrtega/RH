import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

def valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) : Ideal S where
  carrier := {a | 0 < u (a : A)}
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) (b : A)
    exact lt_of_lt_of_le (lt_min ha hb) this
  zero_mem' := by
    change 0 < u ((0 : S) : A)
    simp
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * (a : A))
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (h0 _ c.2))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_valCentreOn {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O A)
    (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) (a : S) :
    a ∈ valCentreOn S u h0 ↔ 0 < u (a : A) := Iff.rfl

/- English proof (translation)
Use `⟨?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, mem_valCentreOn]`. Simplify using the standard rewrite rules. Rewrite `hab` using `[mem_valCentreOn]`. Rewrite using `[mem_valCentreOn, mem_valCentreOn]`.

Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or, not_lt, not_lt]`. Rewrite `hab` using `[MulMemClass.coe_mul, u.map_mul]`. Conclude with `absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))`.
-/
theorem valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_valCentreOn]
    simp
  · rw [mem_valCentreOn] at hab
    rw [mem_valCentreOn, mem_valCentreOn]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    rw [MulMemClass.coe_mul, u.map_mul] at hab
    exact absurd hab (not_lt.2 (add_nonpos hc.1 hc.2))

/- English proof (translation)
Take `⟨w, hw⟩` from `hab`. Take `⟨⟨s, t⟩, hst⟩` from `IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)`. Establish `ht : IsUnit (algebraMap (As O A) (Loc ζ) t)` using `IsLocalization.map_units _ t`. Establish `hs : s ∉ ζ.asIdeal`. Establish `h1 : IsUnit (algebraMap (As O A) (Loc ζ) s)`.

Use `w.isUnit.mul ht` as an intermediate fact. Simplify `this` using `only [hst]`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1`. Establish `h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t)`. Rewrite using `[map_mul, map_mul, ← hw, mul_assoc]`.

Conclude with `congrArg _ hst.symm`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2`. Establish `h3` using `congrArg (fun x : As O A => u (x : A)) hc`. Simplify using `only [MulMemClass.coe_mul, AddValuation.map_mul] at h3`. Rewrite `h3` using `[hz _ c.2, hz _ hs, hz _ t.2]`.

Simplify using `using h3`.
-/
theorem addVal_eq_of_associated_loc {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3

/- English proof (translation)
Introduce `O A _ _ _ _ _ ϖ h hD u h0 hϖ h1`. Use `haveI hP := valCentreOn_isPrime (As O A) u h0`. Establish `hcm : ((valCentreOn (As O A) u h0).comap (algebraMap O (As O A))).IsMaximal`. Establish `hle : IsLocalRing.maximalIdeal O ≤ (valCentreOn (As O A) u h0).comap (algebraMap O (As O A))`. Rewrite using `[h.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, mem_valCentreOn]`.

Conclude with `hϖ`. Use `(IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle` as an intermediate fact. Rewrite using `[← this]`. Use `infer_instance`. Establish `hmax : (valCentreOn (As O A) u h0).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcm`.

Set `ζ : Pts O A` to `⟨valCentreOn (As O A) u h0, hmax⟩`. Establish `hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0` using `fun s hs => le_antisymm (not_lt.1 hs) (h0 _ s.2)`. Use `⟨ζ, ?_⟩` and prove the remaining obligations. Use `haveI : IsDVRAt ζ := hD ζ`. Use `haveI : IsDomain (Loc ζ) := IsDVRAt.isDomain`.

Use `haveI : IsDiscreteValuationRing (Loc ζ) := IsDVRAt.isDVR`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible (Loc ζ)`. Take `⟨⟨π, t⟩, hπt⟩` from `IsLocalization.surj ζ.asIdeal.primeCompl p`. Establish `hπ : Irreducible (algebraMap (As O A) (Loc ζ) π)`. Establish `ht : IsUnit (algebraMap (As O A) (Loc ζ) t)` using `IsLocalization.map_units _ t`.

Establish `: Associated p (algebraMap (As O A) (Loc ζ) π)` using `⟨ht.unit, hπt⟩`. Conclude with `this.irreducible hp`. Establish `hπpos : 0 < u (π : A)`. Assume the negation of the conclusion as `hc`. Conclude with `hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)`.

Establish `key : ∀ a : As O A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨ ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A)`. Introduce `a`. Distinguish the cases in `ha : algebraMap (As O A) (Loc ζ) a = 0`. Use `Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩` and prove the remaining obligations. Rewrite using `[addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]`.

Simplify using the standard rewrite rules. Take `⟨n, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ`. Use `Or.inr ⟨n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[vL_eq_addVal]`. Conclude with `IsDiscreteValuationRing.addVal_def _ w hπ n hw`.

Rewrite using `[addVal_eq_of_associated_loc ζ u hz a (π ^ n) (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]`. Rewrite using `[SubmonoidClass.coe_pow, u.map_pow]`. Establish `hϖtop : u (algebraMap O A ϖ) ≠ ⊤`. Introduce `ht`. Take `⟨v, hv⟩` from `h.isUnit.exists_right_inv`.

Use `congrArg u hv` as an intermediate fact. Rewrite `this` using `[u.map_mul, ht, top_add, u.map_one]`. Conclude with `WithTop.top_ne_zero this`. Establish `hϖe : u (algebraMap O A ϖ) = ep ϖ ζ • u (π : A)`. Break down `key (algebraMap O (As O A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩` into its components or cases.

Conclude with `absurd h2 hϖtop`. Rewrite `h2` using `[← coe_ep ζ h, Nat.cast_inj]`. Rewrite using `[h2]`. Conclude with `h3`. Establish `hmtop : u (π : A) ≠ ⊤`.

Introduce `ht`. Apply `hϖtop` to reduce the goal to its premises. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'`. Rewrite using `[hϖe, hk, succ_nsmul, ht, add_top]`. Take `⟨M, hM⟩` from `WithTop.ne_top_iff_exists.1 hmtop`.

Establish `hM0 : 0 < M`. Rewrite `hπpos` using `[← hM]`. Conclude with `hπpos` after adjusting the coercions. Establish `key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨ ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ)`. Introduce `x`.

Take `⟨k, hk⟩` from `h.denom x`. Establish `e1` using `ord_pow_smul ζ h k x`. Rewrite `e1` using `[ord_of_mem ζ h hk]`. Establish `e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x`. Rewrite using `[Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]`.

Break down `key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩` into its components or cases. Use `left`. Rewrite `e1` using `[h2, ENat.map_top, eq_comm, WithTop.add_eq_top]`. Express the relevant statement in the definitionally equal form `u (ϖ ^ k • x) = ⊤ at h3`. Rewrite `e2` using `[h3, eq_comm, WithTop.add_eq_top]`.

Conclude with `⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩`. Use `right`. Rewrite `e1` using `[h2, ENat.map_natCast]`. Express the relevant statement in the definitionally equal form `u (ϖ ^ k • x) = _ at h3`. Rewrite `e2` using `[h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul]`.

Use `⟨n - k * ep ϖ ζ, ?_, ?_⟩` and prove the remaining obligations. Generalize the expression as in `ord ϖ ζ x = y at e1`. Consider the cases of `y with`. Consider the case `top => simp at e1`. Consider the case `coe y`.

Rewrite `e1` using `[← WithTop.coe_add, WithTop.coe_inj]`. Rewrite using `[WithTop.coe_inj]`. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `u x = y at e2`. Consider the cases of `y with`.

Consider the case `top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top`. Consider the case `coe y`. Rewrite `e2` using `[← WithTop.coe_add, WithTop.coe_inj]`. Rewrite using `[WithTop.coe_inj]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM1 : M = 1`. Take `⟨a, ha⟩` from `h1`. Break down `key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩` into its components or cases. Rewrite `h3` using `[ha]`. Conclude with `absurd h3 WithTop.one_ne_top`.

Rewrite `h3` using `[ha, ← WithTop.coe_one, WithTop.coe_inj]`. Conclude with `Int.eq_one_of_mul_eq_one_left hM0.le h3.symm`. Introduce `a`. Break down `key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩` into its components or cases. Rewrite using `[h2, h3]`.

Rewrite using `[h2, h3, hM1, mul_one]`.
-/
theorem exists_pt_ord_eq_addValuation : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] (u : AddValuation A (WithTop ℤ)), (∀ a ∈ As O A, 0 ≤ u a) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a, ord ϖ ζ a = u a := by
  intro O A _ _ _ _ _ ϖ h hD u h0 hϖ h1
  haveI hP := valCentreOn_isPrime (As O A) u h0
  have hcm : ((valCentreOn (As O A) u h0).comap (algebraMap O (As O A))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤
        (valCentreOn (As O A) u h0).comap (algebraMap O (As O A)) := by
      rw [h.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
        mem_valCentreOn]
      exact hϖ
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
    rw [← this]
    infer_instance
  have hmax : (valCentreOn (As O A) u h0).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcm
  let ζ : Pts O A := ⟨valCentreOn (As O A) u h0, hmax⟩
  have hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0 := fun s hs =>
    le_antisymm (not_lt.1 hs) (h0 _ s.2)
  refine ⟨ζ, ?_⟩
  haveI : IsDVRAt ζ := hD ζ
  haveI : IsDomain (Loc ζ) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ) := IsDVRAt.isDVR
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj ζ.asIdeal.primeCompl p
  have hπ : Irreducible (algebraMap (As O A) (Loc ζ) π) := by
    have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
    have : Associated p (algebraMap (As O A) (Loc ζ) π) := ⟨ht.unit, hπt⟩
    exact this.irreducible hp
  have hπpos : 0 < u (π : A) := by
    by_contra hc
    exact hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)
  have key : ∀ a : As O A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨
      ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A) := by
    intro a
    by_cases ha : algebraMap (As O A) (Loc ζ) a = 0
    · refine Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩
      rw [addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]
      simp
    · obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine Or.inr ⟨n, ?_, ?_⟩
      · rw [vL_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def _ w hπ n hw
      · rw [addVal_eq_of_associated_loc ζ u hz a (π ^ n)
          (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]
        rw [SubmonoidClass.coe_pow, u.map_pow]
  have hϖtop : u (algebraMap O A ϖ) ≠ ⊤ := by
    intro ht
    obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
    have := congrArg u hv
    rw [u.map_mul, ht, top_add, u.map_one] at this
    exact WithTop.top_ne_zero this
  have hϖe : u (algebraMap O A ϖ) = ep ϖ ζ • u (π : A) := by
    rcases key (algebraMap O (As O A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩
    · exact absurd h2 hϖtop
    · rw [← coe_ep ζ h, Nat.cast_inj] at h2
      rw [h2]
      exact h3
  have hmtop : u (π : A) ≠ ⊤ := by
    intro ht
    apply hϖtop
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖe, hk, succ_nsmul, ht, add_top]
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hmtop
  have hM0 : 0 < M := by
    rw [← hM] at hπpos
    exact_mod_cast hπpos
  have key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨k, hk⟩ := h.denom x
    have e1 := ord_pow_smul ζ h k x
    rw [ord_of_mem ζ h hk] at e1
    have e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
    rcases key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩
    · left
      rw [h2, ENat.map_top, eq_comm, WithTop.add_eq_top] at e1
      change u (ϖ ^ k • x) = ⊤ at h3
      rw [h3, eq_comm, WithTop.add_eq_top] at e2
      exact ⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩
    · right
      rw [h2, ENat.map_natCast] at e1
      change u (ϖ ^ k • x) = _ at h3
      rw [h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul] at e2
      refine ⟨n - k * ep ϖ ζ, ?_, ?_⟩
      · generalize ord ϖ ζ x = y at e1
        cases y with
        | top => simp at e1
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e1
          rw [WithTop.coe_inj]
          linarith
      · generalize u x = y at e2
        cases y with
        | top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top
        | coe y =>
          rw [← WithTop.coe_add, WithTop.coe_inj] at e2
          rw [WithTop.coe_inj]
          linarith
  have hM1 : M = 1 := by
    obtain ⟨a, ha⟩ := h1
    rcases key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩
    · rw [ha] at h3
      exact absurd h3 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h3
      exact Int.eq_one_of_mul_eq_one_left hM0.le h3.symm
  intro a
  rcases key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3, hM1, mul_one]

end GlobalTheory
