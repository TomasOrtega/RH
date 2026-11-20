import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMaxHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M hM`. Establish `h` using `Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top`.

Rewrite `h` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin, CharP.cast_eq_zero, add_zero] at h`. Establish `h' : M.height ≤ 0` using `by exact_mod_cast h`. Simplify using `using h'`. Consider the case `succ n ih`.

Introduce `M hM`. Set `e` to `(finSuccEquiv F n).toRingEquiv`. Rewrite using `[← e.height_map M]`. Use `set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef`. Establish `hP : P.IsMaximal` using `Ideal.map_isMaximal_of_equiv e`.

Establish `hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal` using `Polynomial.isMaximal_comap_C_of_isJacobsonRing P`. Establish `hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F))` using `⟨rfl⟩`. Rewrite using `[Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P, ih (P.under (MvPolynomial (Fin n) F)) hc]`. Use `norm_cast`.
-/
theorem height_eq_of_isMaximal_mvPolynomial_fin (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, CharP.cast_eq_zero, add_zero] at h
    have h' : M.height ≤ 0 := by exact_mod_cast h
    simpa using h'
  | succ n ih =>
    intro M hM
    let e := (finSuccEquiv F n).toRingEquiv
    rw [← e.height_map M]
    set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef
    have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F)) := ⟨rfl⟩
    rw [Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P,
      ih (P.under (MvPolynomial (Fin n) F)) hc]
    norm_cast

/- English proof (translation)
Introduce `F _ A _ _ _ _ m hm`. Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg F A`. Set `_ : Algebra (MvPolynomial (Fin s) F) A` to `g.toRingHom.toAlgebra`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin s) F) A` using `⟨hint⟩`. Establish `: FaithfulSMul (MvPolynomial (Fin s) F) A` using `(faithfulSMul_iff_algebraMap_injective _ A).mpr hinj`.

Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing F A`. Establish `: m.IsPrime` using `hm.isPrime`. Establish `hR : ringKrullDim (MvPolynomial (Fin s) F) = s`. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules.

Establish `hdim : ringKrullDim A ≤ s`. Rewrite using `[← hR]`. Use `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_` and prove the remaining obligations. Conclude with `Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq`. Set `n` to `m.under (MvPolynomial (Fin s) F)`.

Establish `: n.IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m`. Establish `h1` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m`. Rewrite `h1` using `[height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance]`. Use `le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `le_self_add` after adjusting the coercions.
-/
theorem MaximalIdealHeightFG.proof : MaximalIdealHeightFG.Statement.{u} := by
  intro F _ A _ _ _ _ m hm
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F A
  let _ : Algebra (MvPolynomial (Fin s) F) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : m.IsPrime := hm.isPrime
  have hR : ringKrullDim (MvPolynomial (Fin s) F) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim : ringKrullDim A ≤ s := by
    rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_
    exact Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq
  let n := m.under (MvPolynomial (Fin s) F)
  have : n.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m
  rw [height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance] at h1
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)
  rw [h1]
  exact_mod_cast le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
