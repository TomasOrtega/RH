import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Use `set N := c.totalDegree + 1 with hN`. Establish `hNpos : 0 < N` using `Nat.succ_pos _`. Establish `: NeZero ((N : ℕ) : ℚ)` using `⟨by exact_mod_cast hNpos.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N`. Use `set S := Polynomial.nthRootsFinset N (1 : AlgebraicClosure ℚ)`.

Establish `hS : S.card = N` using `hζ.card_nthRootsFinset`. Use `set c' := MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) c`. Establish `hc' : c' ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Conclude with `MvPolynomial.map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective (h.trans (map_zero _).symm)`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hc'` to reduce the goal to its premises. Use `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c' (fun _ ↦ S) (fun i ↦ ?_) ?_` and prove the remaining obligations.

Rewrite using `[hS]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [c', MvPolynomial.degreeOf_def, MvPolynomial.degrees_map_of_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]`. Use `_ ≤ c.totalDegree := MvPolynomial.degreeOf_le_totalDegree c i`. Use `_ < N := Nat.lt_succ_self _`.

Introduce `x hx`. Establish `hx' : ∀ j, x j ^ N = 1` using `fun j ↦ (Polynomial.mem_nthRootsFinset hNpos 1).mp (hx j)`. Use `hcon N x hNpos hx'` as an intermediate fact. Rewrite using `[MvPolynomial.eval_map]`. Rewrite `this` using `[MvPolynomial.aeval_def]`.

Conclude with `this`.
-/
theorem exists_rootsOfUnity_eval_ne_zero {s : ℕ} {c : MvPolynomial (Fin s) ℚ} (hc : c ≠ 0) :
    ∃ (N : ℕ) (y : Fin s → AlgebraicClosure ℚ), 0 < N ∧ (∀ j, y j ^ N = 1) ∧ aeval y c ≠ 0 := by
  classical
  set N := c.totalDegree + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hNpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  set S := Polynomial.nthRootsFinset N (1 : AlgebraicClosure ℚ)
  have hS : S.card = N := hζ.card_nthRootsFinset
  set c' := MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) c
  have hc' : c' ≠ 0 := by
    intro h
    apply hc
    exact MvPolynomial.map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
      (h.trans (map_zero _).symm)
  by_contra hcon
  push Not at hcon
  apply hc'
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c' (fun _ ↦ S) (fun i ↦ ?_) ?_
  · rw [hS]
    calc c'.degreeOf i = c.degreeOf i := by
          simp only [c', MvPolynomial.degreeOf_def,
            MvPolynomial.degrees_map_of_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
      _ ≤ c.totalDegree := MvPolynomial.degreeOf_le_totalDegree c i
      _ < N := Nat.lt_succ_self _
  · intro x hx
    have hx' : ∀ j, x j ^ N = 1 := fun j ↦ (Polynomial.mem_nthRootsFinset hNpos 1).mp (hx j)
    have := hcon N x hNpos hx'
    rw [MvPolynomial.eval_map]
    rw [MvPolynomial.aeval_def] at this
    exact this

/- English proof (translation)
Set `: Algebra (MvPolynomial (Fin s) ℚ) B` to `g0.toRingHom.toAlgebra`. Establish `hmap : ∀ a, algebraMap (MvPolynomial (Fin s) ℚ) B a = g0 a` using `fun _ ↦ rfl`. Establish `hInt : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ) B` using `⟨hint⟩`. Establish `hI : (Ideal.span {g}).comap (algebraMap (MvPolynomial (Fin s) ℚ) B) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem hg (Ideal.mem_span_singleton_self g) (Algebra.IsIntegral.isIntegral g)`. Take `⟨c, hcI, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hcI)`. Take `⟨N, y, hNpos, hy, hcy⟩` from `exists_rootsOfUnity_eval_ne_zero hc0`. Use `set ev : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ := (aeval y).toRingHom with hev`. Establish `: (RingHom.ker ev).IsPrime` using `RingHom.ker_isPrime ev`. Establish `hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) ℚ) B) ≤ RingHom.ker ev`.

Introduce `a ha`. Rewrite `ha` using `[RingHom.mem_ker, hmap]`. Establish `: a = 0` using `hinj (ha.trans (map_zero g0).symm)`. Rewrite using `[this]`. Conclude with `(RingHom.ker ev).zero_mem`.

Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (RingHom.ker ev) hker`. Use `hQ` as an intermediate fact. Use `set p := Q.comap (algebraMap (MvPolynomial (Fin s) ℚ) B) with hp`. Establish `: p.IsPrime` using `Ideal.comap_isPrime _ Q`. Establish `hvan : ∀ a ∈ p, ev a = 0` using `fun a ha ↦ by`.

Rewrite `ha` using `[hQc]`. Conclude with `RingHom.mem_ker.mp ha`. Set `evq : MvPolynomial (Fin s) ℚ ⧸ p →+* AlgebraicClosure ℚ` to `Ideal.Quotient.lift p ev hvan`. Establish `hevq : Function.Injective evq` using `RingHom.lift_injective_of_ker_le_ideal p hvan (by rw [hQc])`. Set `: Algebra (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ)` to `evq.toAlgebra`.

Establish `: Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ)` using `(Module.isTorsionFree_iff_algebraMap_injective).mpr hevq`. Establish `: Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q)` using `(Module.isTorsionFree_iff_algebraMap_injective).mpr Ideal.algebraMap_quotient_injective`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q)` using `Algebra.IsIntegral.quotient`. Set `ψq : (B ⧸ Q) →ₐ[MvPolynomial (Fin s) ℚ ⧸ p] AlgebraicClosure ℚ` to `IsAlgClosed.lift`. Set `ψ0 : B →+* AlgebraicClosure ℚ` to `ψq.toRingHom.comp (Ideal.Quotient.mk Q)`.

Establish `hψ0 : ∀ a, ψ0 (g0 a) = aeval y a`. Introduce `a`. Establish `h1 : Ideal.Quotient.mk Q (g0 a) = algebraMap (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p a)` using `rfl`. Express the relevant statement in the definitionally equal form `ψq (Ideal.Quotient.mk Q (g0 a)) = aeval y a`. Rewrite using `[h1, ψq.commutes]`.

Both sides reduce to the same expression. Use `⟨ψ0.toRatAlgHom, ?_, fun j ↦ ⟨N, hNpos, ?_⟩⟩` and prove the remaining obligations. Introduce `h0`. Apply `hcy` to reduce the goal to its premises. Rewrite using `[← hψ0, ← hmap, ← hb]`.

Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `ψ0 b * ψ0.toRatAlgHom g = 0`. Rewrite using `[h0, mul_zero]`. Express the relevant statement in the definitionally equal form `ψ0 (g0 (X j)) ^ N = 1`. Rewrite using `[hψ0, aeval_X]`.

Conclude with `hy j`.
-/
theorem exists_algHom_rootsOfUnity_ne_zero {B : Type*} [CommRing B] [IsDomain B] [Algebra ℚ B]
    {s : ℕ} (g0 : MvPolynomial (Fin s) ℚ →ₐ[ℚ] B) (hinj : Function.Injective g0)
    (hint : g0.IsIntegral) {g : B} (hg : g ≠ 0) :
    ∃ ψ : B →ₐ[ℚ] AlgebraicClosure ℚ, ψ g ≠ 0 ∧
      ∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (MvPolynomial.X j)) ^ N = 1 := by
  classical
  let : Algebra (MvPolynomial (Fin s) ℚ) B := g0.toRingHom.toAlgebra
  have hmap : ∀ a, algebraMap (MvPolynomial (Fin s) ℚ) B a = g0 a := fun _ ↦ rfl
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ) B := ⟨hint⟩

  have hI : (Ideal.span {g}).comap (algebraMap (MvPolynomial (Fin s) ℚ) B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hg (Ideal.mem_span_singleton_self g)
      (Algebra.IsIntegral.isIntegral g)
  obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hcI)

  obtain ⟨N, y, hNpos, hy, hcy⟩ := exists_rootsOfUnity_eval_ne_zero hc0
  set ev : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ := (aeval y).toRingHom with hev
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) ℚ) B) ≤ RingHom.ker ev := by
    intro a ha
    rw [RingHom.mem_ker, hmap] at ha
    have : a = 0 := hinj (ha.trans (map_zero g0).symm)
    rw [this]
    exact (RingHom.ker ev).zero_mem
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (RingHom.ker ev) hker
  have := hQ
  set p := Q.comap (algebraMap (MvPolynomial (Fin s) ℚ) B) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ Q

  have hvan : ∀ a ∈ p, ev a = 0 := fun a ha ↦ by
    rw [hQc] at ha
    exact RingHom.mem_ker.mp ha
  let evq : MvPolynomial (Fin s) ℚ ⧸ p →+* AlgebraicClosure ℚ := Ideal.Quotient.lift p ev hvan
  have hevq : Function.Injective evq :=
    RingHom.lift_injective_of_ker_le_ideal p hvan (by rw [hQc])
  let : Algebra (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) := evq.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hevq
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr Ideal.algebraMap_quotient_injective
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) := Algebra.IsIntegral.quotient
  let ψq : (B ⧸ Q) →ₐ[MvPolynomial (Fin s) ℚ ⧸ p] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ψ0 : B →+* AlgebraicClosure ℚ := ψq.toRingHom.comp (Ideal.Quotient.mk Q)
  have hψ0 : ∀ a, ψ0 (g0 a) = aeval y a := by
    intro a
    have h1 : Ideal.Quotient.mk Q (g0 a) =
        algebraMap (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p a) := rfl
    change ψq (Ideal.Quotient.mk Q (g0 a)) = aeval y a
    rw [h1, ψq.commutes]
    rfl
  refine ⟨ψ0.toRatAlgHom, ?_, fun j ↦ ⟨N, hNpos, ?_⟩⟩
  · intro h0
    apply hcy
    rw [← hψ0, ← hmap, ← hb]
    rw [map_mul]
    change ψ0 b * ψ0.toRatAlgHom g = 0
    rw [h0, mul_zero]
  · change ψ0 (g0 (X j)) ^ N = 1
    rw [hψ0, aeval_X]
    exact hy j

end GroundTheory.Heights₂.Heights
