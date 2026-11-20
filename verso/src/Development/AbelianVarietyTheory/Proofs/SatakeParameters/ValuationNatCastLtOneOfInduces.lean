import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

omit [IsAlgClosure E Ω] [IsCMField E] in

/- English proof (translation)
Establish `h` using `PadicAlgCl.norm_extends l ((l : ℕ) : ℚ_[l])`. Rewrite `h` using `[map_natCast]`. Rewrite using `[h]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_natCast_om_lt_one : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

omit [NumberField E] [IsAlgClosure E Ω] [IsCMField E] in

/- English proof (translation)
Establish `hn : ‖Bw.j ((l : ℕ) : Ω)‖ < 1` using `by rw [map_natCast]; exact norm_natCast_om_lt_one`. Establish `hl0 : ((l : ℕ) : Ω) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Bw.j h0`. Rewrite `h1` using `[map_natCast, map_zero]`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1`. Establish `hmem : ((l : ℕ) : Ω) ∈ A` using `(hj _).2 hn.le`. Establish `hinv : ((l : ℕ) : Ω)⁻¹ ∉ A`. Introduce `hm`. Establish `h1` using `(hj _).1 hm`.

Rewrite `h1` using `[map_inv₀, norm_inv]`. Establish `hpos : 0 < ‖Bw.j ((l : ℕ) : Ω)‖` using `norm_pos_iff.2 ((_root_.map_ne_zero _).2 hl0)`. Use `(one_lt_inv₀ hpos).2 hn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `lt_of_le_of_ne ((A.valuation_le_one_iff _).2 hmem) fun h1 => hinv ?_` and prove the remaining obligations.

Rewrite using `[← A.valuation_le_one_iff, map_inv₀, h1, inv_one]`.
-/
theorem valuation_natCast_lt_one_of_induces {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    A.valuation ((l : ℕ) : Ω) < 1 := by
  have hn : ‖Bw.j ((l : ℕ) : Ω)‖ < 1 := by rw [map_natCast]; exact norm_natCast_om_lt_one
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    have h1 := congrArg Bw.j h0
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hmem : ((l : ℕ) : Ω) ∈ A := (hj _).2 hn.le
  have hinv : ((l : ℕ) : Ω)⁻¹ ∉ A := by
    intro hm
    have h1 := (hj _).1 hm
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖Bw.j ((l : ℕ) : Ω)‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hl0)
    have := (one_lt_inv₀ hpos).2 hn
    linarith
  refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 hmem) fun h1 => hinv ?_
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

omit [IsAlgClosure E Ω] [IsCMField E] in

/- English proof (translation)
Use `(hA _).1 ?_` and prove the remaining obligations. Establish `h` using `valuation_natCast_lt_one_of_induces Bw hj`. Simplify `h` using `[map_natCast]`.
-/
theorem mem_of_induces {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  refine (hA _).1 ?_
  have h := valuation_natCast_lt_one_of_induces Bw hj
  simpa [map_natCast] using h

end GlobalTheory.GalCut
