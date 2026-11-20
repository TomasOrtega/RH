import Formalism.LocalToGlobal.CharacterGerms.RowTieCuts

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

/- English proof (translation)
Establish `hle` using `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t`. Unfold `vV valV`. Generalize the expression as in `(IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules.

Take `⟨a, rfl⟩` from `WithZero.ne_zero_iff_exists.1 hy`. Establish `ha : a ≤ 1` using `WithZero.coe_le_one.1 hle`. Establish `hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a` using `rfl`. Rewrite using `[hlog, neg_nonneg]`. Conclude with `ha`.
-/
theorem vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha

/- English proof (translation)
Unfold `EmbIntSt`. Introduce `T C _ V ι h t`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Rewrite using `[map_zero, map_zero]`.

Conclude with `VF.Ge.zero 0`. Establish `hx : algebraMap T.V T.Fr t ≠ 0` using `fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))`. Establish `hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V)` using `(map_natCast _ _).symm`. Establish `h1` using `vV_algebraMap_nonneg T t`. Establish `h2` using `vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)`.

Rewrite `h2` using `[← hl]`. Unfold `VF.Ge`. Rewrite using `[h (algebraMap T.V T.Fr t) hx]`. Conclude with `WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))`.
-/
theorem embIntSt_holds : EmbIntSt := by
  unfold EmbIntSt
  intro T C _ V ι h t
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, map_zero]
    exact VF.Ge.zero 0
  · have hx : algebraMap T.V T.Fr t ≠ 0 :=
      fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))
    have hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V) := (map_natCast _ _).symm
    have h1 := vV_algebraMap_nonneg T t
    have h2 := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rw [← hl] at h2
    unfold VF.Ge
    rw [h (algebraMap T.V T.Fr t) hx]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))

end Formalism.L2.FormalSeriesBounds
