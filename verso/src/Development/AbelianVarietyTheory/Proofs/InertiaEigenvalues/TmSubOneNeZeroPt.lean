import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZeroStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Trans

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hr1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Take `⟨N, h01, -, -, hmul, hA⟩` from `GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1`. Establish `hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n)`. Introduce `a`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Establish `h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1` using `(GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2`. Establish `h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1` using `Real.rpow_le_one (norm_nonneg _) h1 (by positivity)`. Establish `h3 : ((l : ℝ)⁻¹) ^ n ≤ 1` using `pow_le_one₀ (by positivity) hr1.le`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a)`. Introduce `a ha0`. Choose the witnesses or unpack the hypotheses as in `⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Apply `ha0` to reduce the goal to its premises. Use `WittVector.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[WittVector.zero_coeff]`. Assume the negation of the conclusion as `hn`. Conclude with `hc ⟨n, hn⟩`.

Rewrite using `[hA]`. Use `lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)` and prove the remaining obligations. Establish `hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises.

Use `(GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_` and prove the remaining obligations. Conclude with `Subtype.ext h`. Establish `hl0 : (0 : ℝ) < l` using `lt_trans one_pos hl`. Conclude with `mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)`. Establish `hN0 : N 0 = 0`.

Establish `hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0` using `fun n => Real.zero_rpow (by positivity)`. Rewrite using `[← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]`. Establish `hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0` using `fun n => Real.zero_rpow (by positivity)`. Simplify using `[hz, hz', GlobalTheory.GaussExt.untilt_zero]`. Introduce `y hy h0`.

Use `hpos y hy` as an intermediate fact. Rewrite `this` using `[h0, hN0]`. Conclude with `lt_irrefl _ this`.
-/
theorem map_ne_zero_pt : ∀ y : Formalism.Per.Ainf l, y ≠ 0 →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) y ≠ 0 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  obtain ⟨N, h01, -, -, hmul, hA⟩ := GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1
  have hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ =>
      ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n) := by
    intro a
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 :=
      (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
    have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) h1 (by positivity)
    have h3 : ((l : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) hr1.le
    calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a) := by
    intro a ha0
    obtain ⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by
      by_contra hc
      apply ha0
      refine WittVector.ext fun n => ?_
      rw [WittVector.zero_coeff]
      by_contra hn
      exact hc ⟨n, hn⟩
    rw [hA]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)
    have hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
      intro h
      apply ha
      refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_
      exact Subtype.ext h
    have hl0 : (0 : ℝ) < l := lt_trans one_pos hl
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)
  have hN0 : N 0 = 0 := by
    have hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0 := fun n => Real.zero_rpow (by positivity)
    rw [← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]
    have hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0 := fun n => Real.zero_rpow (by positivity)
    simp [hz, hz', GlobalTheory.GaussExt.untilt_zero]
  intro y hy h0
  have := hpos y hy
  rw [h0, hN0] at this
  exact lt_irrefl _ this

/- English proof (translation)
Introduce `h`. Apply `he` to reduce the goal to its premises. Establish `h'` using `congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)`. Simplify using `using h'`.
-/
theorem tm_sub_one_ne_zero_pt (e : Formalism.Per.Fl l) (he : e ≠ 1) : (Formalism.Per.tm e - 1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  apply he
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)
  simpa using h'

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h`. Simplify using `at h'`.
-/
theorem one_ne_zero_pt : (1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h
  simp at h'

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `nil`. Introduce `_`. Rewrite using `[List.map_nil, List.prod_nil]`.

Conclude with `map_ne_zero_pt l 1 (one_ne_zero_pt l)`. Consider the case `cons e s ih`. Introduce `hs`. Rewrite using `[List.map_cons, List.prod_cons, map_mul]`. Introduce `h`.

Conclude with `(GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).elim (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self))) (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))`.
-/
theorem map_prod_ne_zero_pt : ∀ s : List (Formalism.Per.Fl l), (∀ e ∈ s, e ≠ 1) →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (s.map fun e => Formalism.Per.tm e - 1).prod ≠ 0 := by
  intro s
  induction s with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil]
    exact map_ne_zero_pt l 1 (one_ne_zero_pt l)
  | cons e s ih =>
    intro hs
    rw [List.map_cons, List.prod_cons, map_mul]
    intro h
    exact (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).elim
      (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self)))
      (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))

end GlobalTheory.PMon.Trans

/- English proof (translation)
Introduce `l _`. Use `⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨e, he, hne⟩` from `GlobalTheory.CrisLoc.exists_root_ne_one l`. Take `⟨n, h⟩` from `GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx`.

Use `(GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).resolve_left ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e) fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne`. Rewrite `h1` using `[List.map_replicate, List.prod_replicate, map_pow]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.PMon.Trans.acris_bcris : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)) ∧ (∀ x : Formalism.Per.Acris l, Formalism.Per.φB l (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l x)) ∧ ∀ c : ℤ_[l], algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (zc l c) = Formalism.Per.zB l c := by
  intro l _
  refine ⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, h⟩ := GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx
  refine (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).resolve_left ?_
  have h1 := GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e)
    fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne
  rwa [List.map_replicate, List.prod_replicate, map_pow] at h1
