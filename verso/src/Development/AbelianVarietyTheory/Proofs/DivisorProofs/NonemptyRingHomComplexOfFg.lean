import Mathlib

set_option autoImplicit false

namespace GlobalTheory.FGFieldEmb

open Cardinal

/- English proof (translation)
Set `F` to `FractionRing (MvPolynomial ℝ K)`. Set `L` to `AlgebraicClosure F`. Establish `hF : #F = 𝔠`. Rewrite using `[Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK, max_eq_left Cardinal.aleph0_le_continuum]`. Establish `hL : #L = 𝔠`.

Use `le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)` and prove the remaining obligations. Use `Algebra.IsAlgebraic.cardinalMk_le_max F L` as an intermediate fact. Rewrite `this` using `[hF, max_eq_left Cardinal.aleph0_le_continuum]`. Then use the resulting hypothesis. Set `j : K →+* L` to `(algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)`. Establish `: CharZero L` using `(RingHom.charZero_iff j.injective).1 inferInstance`.

Take `⟨e⟩` from `IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ) (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))`. Conclude with `⟨e.toRingHom.comp j⟩`.
-/
theorem nonempty_ringHom_complex_of_mk_le (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

/- English proof (translation)
Introduce `K _ _ k hk`. Take `⟨t, rfl⟩` from `hk`. Use `nonempty_ringHom_complex_of_mk_le _ ?_` and prove the remaining obligations. Use `le_trans ?_ Cardinal.aleph0_le_continuum` and prove the remaining obligations. Use `(IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_` and prove the remaining obligations.

Use `max_le (max_le ?_ ?_) le_rfl` and prove the remaining obligations. Simplify using `[Cardinal.mkRat]`. Conclude with `(Cardinal.lt_aleph0_of_finite _).le`.
-/
theorem nonempty_ringHom_complex_of_fg :
    ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  intro K _ _ k hk
  obtain ⟨t, rfl⟩ := hk
  refine nonempty_ringHom_complex_of_mk_le _ ?_
  refine le_trans ?_ Cardinal.aleph0_le_continuum
  refine (IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_
  refine max_le (max_le ?_ ?_) le_rfl
  · simp [Cardinal.mkRat]
  · exact (Cardinal.lt_aleph0_of_finite _).le

end GlobalTheory.FGFieldEmb
