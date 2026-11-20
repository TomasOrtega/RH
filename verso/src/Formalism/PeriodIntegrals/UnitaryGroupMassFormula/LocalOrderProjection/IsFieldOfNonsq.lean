import Mathlib
import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.AlgebraMapMemO
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.LocOProjOf

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.OProj

section Fld

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use `SlopeTestRemainingChoices.nontrivial_E L` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Establish `h2D : (2 * D : F) ≠ 0` using `mul_ne_zero two_ne_zero hD0`. Use `⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `SlopeTestRemainingChoices.nm_ex L x`.

Distinguish the cases in `hn0 : n = 0`. It suffices to derive a contradiction. Take `⟨t, c, -, -, hdec⟩` from `SlopeTestRemainingChoices.decomp L θ hc D hD x`. Establish `hcjx : algebraMap F E (2 * D) * L.cj x = algebraMap F E (D * t) - algebraMap F E c * θ`. Establish `h` using `congrArg L.cj hdec`.

Simplify using `only [map_add, map_mul, AlgEquiv.commutes, hc] at h`. Simplify using `only [map_mul]`. Take the linear combination `h`. Establish `hprod : (algebraMap F E (D * t)) ^ 2 - (algebraMap F E c) ^ 2 * algebraMap F E D = 0`. Establish `h0 : (algebraMap F E (2 * D) * x) * (algebraMap F E (2 * D) * L.cj x) = 0`.

Rewrite using `[mul_mul_mul_comm, ← hn, hn0, map_zero, mul_zero]`. Rewrite `h0` using `[hdec, hcjx]`. Take the linear combination `h0 + (algebraMap F E c) ^ 2 * hD`. Establish `hF : (D * t) ^ 2 - c ^ 2 * D = 0`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_zero, ← hprod]`. Simplify using `only [map_sub, map_pow, map_mul]`. Distinguish the cases in `hc0 : c = 0`. Rewrite `hF`, `hdec` using `[hc0]`. Establish `hsq : (D * t) ^ 2 = 0` using `by linear_combination hF`.

Establish `hDt : D * t = 0` using `(pow_eq_zero_iff two_ne_zero).mp hsq`. Rewrite `hdec` using `[hDt, map_zero, zero_mul, add_zero]`. Establish `hu : IsUnit (algebraMap F E (2 * D))` using `(IsUnit.mk0 _ h2D).map _`. Conclude with `hx (hu.mul_right_eq_zero.mp hdec)`. Apply `hns` to reduce the goal to its premises.

Use `⟨D * t / c, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, div_eq_iff (mul_ne_zero hc0 hc0)]`. Take the linear combination `hF`. Use `⟨L.cj x * algebraMap F E n⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hn, ← map_mul, mul_inv_cancel₀ hn0, map_one]`.
-/
theorem isField_of_nonsq [CharZero F] (L : LocE F E) (θ : E) (hc : L.cj θ = -θ) (D : F)
    (hD0 : D ≠ 0) (hD : θ * θ = algebraMap F E D) (hns : ¬ ∃ s : F, s * s = D) : IsField E := by
  have := SlopeTestRemainingChoices.nontrivial_E L
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have h2D : (2 * D : F) ≠ 0 := mul_ne_zero two_ne_zero hD0
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, hn⟩ := SlopeTestRemainingChoices.nm_ex L x
  by_cases hn0 : n = 0
  · exfalso
    obtain ⟨t, c, -, -, hdec⟩ := SlopeTestRemainingChoices.decomp L θ hc D hD x
    have hcjx : algebraMap F E (2 * D) * L.cj x = algebraMap F E (D * t) - algebraMap F E c * θ := by
      have h := congrArg L.cj hdec
      simp only [map_add, map_mul, AlgEquiv.commutes, hc] at h
      simp only [map_mul]
      linear_combination h
    have hprod : (algebraMap F E (D * t)) ^ 2 - (algebraMap F E c) ^ 2 * algebraMap F E D = 0 := by
      have h0 : (algebraMap F E (2 * D) * x) * (algebraMap F E (2 * D) * L.cj x) = 0 := by
        rw [mul_mul_mul_comm, ← hn, hn0, map_zero, mul_zero]
      rw [hdec, hcjx] at h0
      linear_combination h0 + (algebraMap F E c) ^ 2 * hD
    have hF : (D * t) ^ 2 - c ^ 2 * D = 0 := by
      apply hinj
      rw [map_zero, ← hprod]
      simp only [map_sub, map_pow, map_mul]
    by_cases hc0 : c = 0
    · rw [hc0] at hF hdec
      have hsq : (D * t) ^ 2 = 0 := by linear_combination hF
      have hDt : D * t = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
      rw [hDt, map_zero, zero_mul, add_zero] at hdec
      have hu : IsUnit (algebraMap F E (2 * D)) := (IsUnit.mk0 _ h2D).map _
      exact hx (hu.mul_right_eq_zero.mp hdec)
    · apply hns
      refine ⟨D * t / c, ?_⟩
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hc0 hc0)]
      linear_combination hF
  · refine ⟨L.cj x * algebraMap F E n⁻¹, ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, mul_inv_cancel₀ hn0, map_one]

end Fld

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK θ _ hθc D hD0 hθD hns W _ _ P hP`. Use `hOK.loc` as an intermediate fact. Use `hOK.char0` as an intermediate fact. Establish `hE : IsField E` using `isField_of_nonsq M.L θ hθc (D : F) hD0 hθD hns`. Set `_ : Field E` to `hE.toField`.

Use `M.L.free` as an intermediate fact. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ M.L.rank`. Establish `hO : (integralClosure 𝒪[F] E).toSubring = M.L.O`. Use extensionality with `x`. Rewrite using `[M.L.O_def]`.

Both sides reduce to the same expression. Establish `: IsDedekindDomain (integralClosure 𝒪[F] E)` using `integralClosure.isDedekindDomain 𝒪[F] F E`. Use `set C := integralClosure 𝒪[F] E with hC`. Establish `: Module.IsTorsionFree 𝒪[F] C` using `.of_smul_eq_zero fun r c h => by`. Distinguish the cases in `hr : r = 0`.

Conclude with `Or.inl hr`. Use `right`. Establish `h' : ((r • c : C) : E) = 0` using `by rw [h]; rfl`. Rewrite `h'` using `[Subalgebra.coe_smul, Algebra.smul_def, mul_eq_zero]`. Establish `hr' : algebraMap 𝒪[F] E r ≠ 0`.

Rewrite using `[IsScalarTower.algebraMap_apply 𝒪[F] F E]`. Use `(map_ne_zero _).mpr fun h0 => hr (Subtype.ext h0)` and prove the remaining obligations. Conclude with `Subtype.ext (h'.resolve_left hr')`. Establish `hfinP : {I : Ideal C | I.IsPrime}.Finite`. Establish `hm` using `IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal 𝒪[F]) C`.

Use `(hm.insert ⊥).subset fun I hI => ?_` and prove the remaining obligations. Distinguish the cases in `hI0 : I = ⊥`. Conclude with `Or.inl hI0`. Use `right`. Establish `hI : I.IsPrime` using `hI`.

Establish `hne : I.under 𝒪[F] ≠ ⊥` using `fun h => hI0 (Ideal.eq_bot_of_comap_eq_bot h)`. Establish `hmax : (I.under 𝒪[F]).IsMaximal` using `(Ideal.IsPrime.under 𝒪[F] I).isMaximal hne`. Use `⟨hI, ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩⟩` and prove the remaining obligations. Establish `: IsPrincipalIdealRing C` using `IsPrincipalIdealRing.of_finite_primes hfinP`. Set `e : C ≃+* M.L.O` to `RingEquiv.subringCongr hO`.

Establish `: IsPrincipalIdealRing M.L.O` using `IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective`. Establish `: Module.Finite M.L.O P` using `Module.Finite.iff_fg.mpr hP`. Establish `: Module.IsTorsionFree M.L.O P` using `.of_smul_eq_zero fun r p h => by`. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`.

Use `right`. Establish `h' : ((r : E) • (p : W)) = 0`. Establish `h2 : r • (p : W) = 0`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `using this`.

Conclude with `h2`. Establish `hr' : (r : E) ≠ 0` using `fun h0 => hr (Subtype.ext h0)`. Conclude with `Subtype.ext ((smul_eq_zero.mp h').resolve_left hr')`. Use `infer_instance`.
-/
theorem nonSqCase : NonSqCase := by
  intro F _ _ _ E _ _ _ _ M hOK θ _ hθc D hD0 hθD hns W _ _ P hP
  have := hOK.loc
  have := hOK.char0
  have hE : IsField E := isField_of_nonsq M.L θ hθc (D : F) hD0 hθD hns
  let _ : Field E := hE.toField
  have := M.L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ M.L.rank
  have hO : (integralClosure 𝒪[F] E).toSubring = M.L.O := by
    ext x
    rw [M.L.O_def]
    rfl
  have : IsDedekindDomain (integralClosure 𝒪[F] E) := integralClosure.isDedekindDomain 𝒪[F] F E
  set C := integralClosure 𝒪[F] E with hC
  have : Module.IsTorsionFree 𝒪[F] C := .of_smul_eq_zero fun r c h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h' : ((r • c : C) : E) = 0 := by rw [h]; rfl
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_eq_zero] at h'
      have hr' : algebraMap 𝒪[F] E r ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
        refine (map_ne_zero _).mpr fun h0 => hr (Subtype.ext h0)
      exact Subtype.ext (h'.resolve_left hr')
  have hfinP : {I : Ideal C | I.IsPrime}.Finite := by
    have hm := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal 𝒪[F]) C
    refine (hm.insert ⊥).subset fun I hI => ?_
    by_cases hI0 : I = ⊥
    · exact Or.inl hI0
    · right
      have hI : I.IsPrime := hI
      have hne : I.under 𝒪[F] ≠ ⊥ := fun h => hI0 (Ideal.eq_bot_of_comap_eq_bot h)
      have hmax : (I.under 𝒪[F]).IsMaximal := (Ideal.IsPrime.under 𝒪[F] I).isMaximal hne
      refine ⟨hI, ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩⟩
  have : IsPrincipalIdealRing C := IsPrincipalIdealRing.of_finite_primes hfinP
  let e : C ≃+* M.L.O := RingEquiv.subringCongr hO
  have : IsPrincipalIdealRing M.L.O := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Module.Finite M.L.O P := Module.Finite.iff_fg.mpr hP
  have : Module.IsTorsionFree M.L.O P := .of_smul_eq_zero fun r p h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h' : ((r : E) • (p : W)) = 0 := by
        have h2 : r • (p : W) = 0 := by
          have := congrArg Subtype.val h
          simpa using this
        exact h2
      have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
      exact Subtype.ext ((smul_eq_zero.mp h').resolve_left hr')
  infer_instance

end PI.LocHerm.OProj
