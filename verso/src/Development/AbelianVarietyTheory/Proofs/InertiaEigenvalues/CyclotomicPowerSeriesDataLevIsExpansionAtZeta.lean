import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.LevExp

/- English proof (translation)
Conclude with `PowerSeries.exp_unique_of_derivative_eq_self h1 h0`.
-/
theorem eq_exp {F : Type} [Field F] [CharZero F] [Algebra ℚ F] (E : PowerSeries F)
    (h0 : PowerSeries.constantCoeff E = 1) (h1 : PowerSeries.derivative F E = E) :
    E = PowerSeries.exp F := by
  exact PowerSeries.exp_unique_of_derivative_eq_self h1 h0

/- English proof (translation)
Establish `hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) = f (fun _ => ((p i : Polynomial O) : PowerSeries O))`. Establish `h` using `hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) - (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[hfam]`. Establish `hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ)`.

Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply, Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (fun φ => φ (p i)) hg`. Simplify using `only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self, PowerSeries.map_id] at h2`.

Conclude with `h2`.
-/
theorem map_poly {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} (f : LetA O n →ₐ[O] A)
    (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) = Polynomial.aeval (f letπ) (p i) := by
  have hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      f (fun _ => ((p i : Polynomial O) : PowerSeries O)) := by
    have h := hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) -
      (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)
    rwa [map_sub, sub_eq_zero] at h
  rw [hfam]
  have hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp
      (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply,
      Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have h2 := congrArg (fun φ => φ (p i)) hg
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
    PowerSeries.map_id] at h2
  exact h2

/- English proof (translation)
Rewrite using `[map_poly f i hf p, Polynomial.aeval_map_algebraMap]`.
-/
theorem map_poly_series {O L : Type} [CommRing O] [CommRing L] [Algebra O L] {n : ℕ}
    (f : LetA O n →ₐ[O] PowerSeries L) (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      Polynomial.aeval (f letπ) ((p i).map (algebraMap O L)) := by
  rw [map_poly f i hf p, Polynomial.aeval_map_algebraMap]

/- English proof (translation)
Introduce `l _ P K s LL Γ R i ζ hζ a`. Establish `hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1`. Take `⟨E, hE0, hE1, hE⟩` from `R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)`. Rewrite `hE` using `[eq_exp E hE0 hE1]`. Rewrite using `[← hE]`.

Expand and normalize the polynomial expressions, which then agree. Establish `htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) (PowerSeries.trunc m (toLL a i)) = R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL)))`. Introduce `m`. Rewrite using `[map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]`. Simplify using `only [toLL, PowerSeries.trunc_map]`.

Introduce `k`. Simplify using `only [htr]`. Rewrite using `[Metric.tendsto_atTop]`. Introduce `ε hε`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by`. Take `⟨r, hr⟩` from `exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]`. Conclude with `hr`.

Take `⟨m₀, hm₀⟩` from `R.lev_cont i ζ a k r`. Use `⟨m₀, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hv` using `hm₀ m hm`. Rewrite `hv` using `[← WithTop.coe_natCast]`. Establish `hn` using `((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv`.

Rewrite using `[dist_eq_norm, ← norm_neg, neg_sub]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lev_isExp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  intro l _ P K s LL Γ R i ζ hζ a
  have hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 := by
    obtain ⟨E, hE0, hE1, hE⟩ := R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)
    rw [eq_exp E hE0 hE1] at hE
    rw [← hE]
    ring
  have htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1)
      (PowerSeries.trunc m (toLL a i)) =
      R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL))) := by
    intro m
    rw [map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]
    simp only [toLL, PowerSeries.trunc_map]
  intro k
  simp only [htr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
    refine ⟨r, ?_⟩
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
    exact hr
  obtain ⟨m₀, hm₀⟩ := R.lev_cont i ζ a k r
  refine ⟨m₀, fun m hm => ?_⟩
  have hv := hm₀ m hm
  rw [← WithTop.coe_natCast] at hv
  have hn := ((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc _ = _ := by push_cast; rfl
    _ ≤ _ := hn
    _ = (l : ℝ) ^ (-(r : ℝ)) := by push_cast; rfl
    _ < ε := hr

end GlobalTheory.HWL.LevExp
