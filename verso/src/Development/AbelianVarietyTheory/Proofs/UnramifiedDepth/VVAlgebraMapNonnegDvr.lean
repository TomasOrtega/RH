import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

/- English proof (translation)
Unfold `vV valV`. Rewrite using `[neg_nonneg]`. Establish `h1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr) (IsDiscreteValuationRing.maximalIdeal T.V) x`. Distinguish the cases in `h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0`. Rewrite using `[h0, WithZero.log_zero]`.

Rewrite using `[WithZero.log_le_iff_le_exp h0]`. Simplify using `using h1`.
-/
theorem vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by
  unfold vV valV
  rw [neg_nonneg]
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
    (IsDiscreteValuationRing.maximalIdeal T.V) x
  by_cases h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
      (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0
  · rw [h0, WithZero.log_zero]
  · rw [WithZero.log_le_iff_le_exp h0]
    simpa using h1

/- English proof (translation)
Introduce `T C _ v l hl hv ι hι`. Establish `hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr)`. Establish `h` using `vV_algebraMap_nonneg_dvr T (l : T.V)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ)`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hvl]`. Use `⟨fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Establish `hx' : algebraMap T.V T.Fr x ≠ 0` using `fun h => hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))`. Rewrite using `[hι _ hx']`. Establish `h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ)`. Conclude with `vV_algebraMap_nonneg_dvr T x` after adjusting the coercions. Establish `h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ)` using `by exact_mod_cast hvl`.

Conclude with `WithTop.coe_le_coe.mpr (div_nonneg h1 h2)`. Unfold `nval split_ifs with hx`. Substitute `hx` using the available equality. Simplify using `only [map_zero, AddValuation.map_zero]`. Both sides reduce to the same expression.

Rewrite using `[hι x hx, hcast]`. Both sides reduce to the same expression.
-/
theorem nval_eq_of_extension :
    ∀ (T : CDVR) (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l ≠ 0 → v (l : C) = 1 → ∀ (ι : T.Fr →+* C), (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) ∧ ∀ x : T.Fr, nval T.V (vV T.V ((l : ℕ) : T.Fr)).toNat x = (WithBot.some (v (ι x)) : WithBot (WithTop ℝ)) := by
  intro T C _ v l hl hv ι hι
  have hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg_dvr T (l : T.V)
    rwa [map_natCast] at h
  have hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hvl]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : algebraMap T.V T.Fr x ≠ 0 := fun h =>
        hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))
      rw [hι _ hx']
      have h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ) := by
        exact_mod_cast vV_algebraMap_nonneg_dvr T x
      have h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ) := by exact_mod_cast hvl
      exact WithTop.coe_le_coe.mpr (div_nonneg h1 h2)
  · unfold nval
    split_ifs with hx
    · subst hx
      simp only [map_zero, AddValuation.map_zero]
      rfl
    · rw [hι x hx, hcast]
      rfl

end GlobalTheory
