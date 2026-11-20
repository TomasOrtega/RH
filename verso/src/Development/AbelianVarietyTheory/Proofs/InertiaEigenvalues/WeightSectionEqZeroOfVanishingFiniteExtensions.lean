import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c a n h hh hv`. Take `⟨hL, -, -, -⟩` from `evLaws_genFr_nonempty_comp E H Dw l Xo c`. Use function extensionality and compare the values at `p y`. Use `show h p y = 0`. Establish `key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m`.

Introduce `m hm`. Use `letI : Field (p.R ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance`. Use `haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)`. Take `⟨w, hw⟩` from `hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y`.

Establish `e` using `evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw`. Rewrite `e` using `[hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp e.symm`. Establish `hj : h p y ∈ (⊥ : Ideal p.R).jacobson` using `Ideal.mem_sInf.mpr fun J hJ => key J hJ.2`. Establish `hrad : (⊥ : Ideal p.R).IsRadical`.

Introduce `x hx`. Take `⟨k, hk⟩` from `hx`. Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hk` using `[Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `p.rad ⟨k, hk⟩`. Rewrite `hj` using `[IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad]`. Conclude with `hj`.
-/
theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
