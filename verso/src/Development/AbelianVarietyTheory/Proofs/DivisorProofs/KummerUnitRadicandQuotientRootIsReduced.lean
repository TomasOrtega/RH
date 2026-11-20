import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ _ ϖ u m k hϖ hm hk`. Use `set f : A[X] := X ^ m - C (u : A) with hf`. Use `set c : AdjoinRoot f := AdjoinRoot.of f ϖ * AdjoinRoot.root f with hc`. Use `set g : (AdjoinRoot f)[X] := X ^ k - C c with hg`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hm`. Establish `hy : IsUnit (AdjoinRoot.root f)`. Establish `h0` using `AdjoinRoot.eval₂_root f`. Establish `h1 : AdjoinRoot.root f ^ m = AdjoinRoot.of f (u : A)`.

Rewrite `h0` using `[hf]`. Simplify using `only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0`. Conclude with `sub_eq_zero.mp h0`. Establish `h2 : IsUnit (AdjoinRoot.root f ^ m)`. Rewrite using `[h1]`.

Conclude with `(u.isUnit.map _)`. Conclude with `(isUnit_pow_iff hm0).mp h2`. Establish `hspan : Ideal.span {c} = (Ideal.span {ϖ}).map (AdjoinRoot.of f)`. Rewrite using `[Ideal.map_span, Set.image_singleton, hc]`. Conclude with `Ideal.span_singleton_mul_right_unit hy _`.

Use `haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Use `letI : Field (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`. Establish `hredK : IsReduced ((A ⧸ Ideal.span {ϖ})[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (Ideal.span {ϖ}))})`. Rewrite using `[← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]`. Apply `Squarefree.isRadical` to reduce the goal to its premises.

Apply `Polynomial.Separable.squarefree` to reduce the goal to its premises. Establish `hmap : f.map (Ideal.Quotient.mk (Ideal.span {ϖ})) = X ^ m - C ((Units.map (Ideal.Quotient.mk (Ideal.span {ϖ})).toMonoidHom u : (A ⧸ Ideal.span {ϖ})ˣ) : A ⧸ Ideal.span {ϖ})`. Simplify using `[hf, Polynomial.map_sub]`. Rewrite using `[hmap]`. Apply `separable_X_pow_sub_C_unit` to reduce the goal to its premises.

Simplify using `using hm.map (Ideal.Quotient.mk (Ideal.span {ϖ}))`. Establish `hred1 : IsReduced (AdjoinRoot f ⧸ Ideal.span {c})`. Establish `e` using `(Ideal.quotEquivOfEq hspan).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {ϖ}) f)`. Conclude with `isReduced_of_injective e.toRingHom e.injective`. Establish `hgroot : AdjoinRoot.of g c = AdjoinRoot.root g ^ k`.

Establish `h0` using `AdjoinRoot.eval₂_root g`. Rewrite `h0` using `[hg]`. Simplify using `only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0`. Conclude with `(sub_eq_zero.mp h0).symm`. Set `φ0 : AdjoinRoot g →+* AdjoinRoot f ⧸ Ideal.span {c}` to `AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {c})) 0 (by`.

Rewrite using `[hg]`. Simplify using `only [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hk.ne', zero_sub, neg_eq_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c))`. Set `φ : AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} →+* AdjoinRoot f ⧸ Ideal.span {c}` to `Ideal.Quotient.lift _ φ0 (by`. Introduce `a ha`.

Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Simplify using `[φ0])`. Set `ψ : AdjoinRoot f ⧸ Ideal.span {c} →+* AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g}` to `Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of g)) (by`. Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`.

Rewrite using `[RingHom.comp_apply, map_mul, hgroot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) k hk))`. Establish `hcomp : ψ.comp φ = RingHom.id _`. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Apply `AdjoinRoot.ringHom_ext` to reduce the goal to its premises.

Apply the tactic sequence `ext <;> simp [φ, φ0, ψ]`. Simplify using `[φ, φ0, ψ]`. Establish `hinj : Function.Injective φ`. Introduce `x y hxy`. Use `congrArg ψ hxy` as an intermediate fact.

Simplify `this` using `[← RingHom.comp_apply, hcomp]`. Conclude with `isReduced_of_injective φ hinj`.
-/
theorem kummerUnit_quotRoot_isReduced : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A) (u : Aˣ) (m k : ℕ), Irreducible ϖ → IsUnit (m : A) → 0 < k → IsReduced (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  intro A _ _ _ ϖ u m k hϖ hm hk
  set f : A[X] := X ^ m - C (u : A) with hf
  set c : AdjoinRoot f := AdjoinRoot.of f ϖ * AdjoinRoot.root f with hc
  set g : (AdjoinRoot f)[X] := X ^ k - C c with hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hy : IsUnit (AdjoinRoot.root f) := by
    have h0 := AdjoinRoot.eval₂_root f
    have h1 : AdjoinRoot.root f ^ m = AdjoinRoot.of f (u : A) := by
      rw [hf] at h0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
      exact sub_eq_zero.mp h0
    have h2 : IsUnit (AdjoinRoot.root f ^ m) := by
      rw [h1]; exact (u.isUnit.map _)
    exact (isUnit_pow_iff hm0).mp h2
  have hspan : Ideal.span {c} = (Ideal.span {ϖ}).map (AdjoinRoot.of f) := by
    rw [Ideal.map_span, Set.image_singleton, hc]
    exact Ideal.span_singleton_mul_right_unit hy _
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hredK : IsReduced ((A ⧸ Ideal.span {ϖ})[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    apply Squarefree.isRadical
    apply Polynomial.Separable.squarefree
    have hmap : f.map (Ideal.Quotient.mk (Ideal.span {ϖ})) =
        X ^ m - C ((Units.map (Ideal.Quotient.mk (Ideal.span {ϖ})).toMonoidHom u : (A ⧸ Ideal.span {ϖ})ˣ) : A ⧸ Ideal.span {ϖ}) := by
      simp [hf, Polynomial.map_sub]
    rw [hmap]
    apply separable_X_pow_sub_C_unit
    simpa using hm.map (Ideal.Quotient.mk (Ideal.span {ϖ}))
  have hred1 : IsReduced (AdjoinRoot f ⧸ Ideal.span {c}) := by
    have e := (Ideal.quotEquivOfEq hspan).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {ϖ}) f)
    exact isReduced_of_injective e.toRingHom e.injective
  have hgroot : AdjoinRoot.of g c = AdjoinRoot.root g ^ k := by
    have h0 := AdjoinRoot.eval₂_root g
    rw [hg] at h0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
    exact (sub_eq_zero.mp h0).symm
  let φ0 : AdjoinRoot g →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {c})) 0 (by
      rw [hg]
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hk.ne', zero_sub, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c))
  let φ : AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    Ideal.Quotient.lift _ φ0 (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [φ0])
  let ψ : AdjoinRoot f ⧸ Ideal.span {c} →+* AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of g)) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, hgroot, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) k hk))
  have hcomp : ψ.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext <;> simp [φ, φ0, ψ]
    · simp [φ, φ0, ψ]
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg ψ hxy
    simpa [← RingHom.comp_apply, hcomp] using this
  exact isReduced_of_injective φ hinj

end GlobalTheory
