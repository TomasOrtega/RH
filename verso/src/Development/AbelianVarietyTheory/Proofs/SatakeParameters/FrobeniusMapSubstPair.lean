import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeRead

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

local notation "φ" => Formalism.L2.G.Pend.k0ToC p

def lK {ι : Type} (p : ℕ) [Fact p.Prime] (i : ι) : MvPowerSeries ι (FormalGroupSystem.K0 p) :=
  PowerSeries.subst (X i : MvPowerSeries ι (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Unfold `FormalGroupSystem.logF`. Rewrite using `[PowerSeries.coeff_mk]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Conclude with `(pow_pos hp.out.pos _).ne`.
-/
theorem cc_logK : PowerSeries.constantCoeff (FormalGroupSystem.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold FormalGroupSystem.logF
  rw [PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  exact (pow_pos hp.out.pos _).ne

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ cc_logK`.
-/
theorem cc_lK {ι : Type} (i : ι) : constantCoeff (lK (ι := ι) p i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ cc_logK

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero cc_lK`.
-/
theorem hasSubst_lK {ι : Type} [Finite ι] : HasSubst (lK (ι := ι) p) :=
  hasSubst_of_constantCoeff_zero cc_lK

/- English proof (translation)
Unfold `lK GlobalTheory.ThBe0.lg`. Rewrite using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)), map_X, Formalism.L2.G.Pend.logF_map]`.
-/
theorem map_lK {ι : Type} (i : ι) : map φ (lK (ι := ι) p i) = GlobalTheory.ThBe0.lg i := by
  unfold lK GlobalTheory.ThBe0.lg
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)), map_X,
    Formalism.L2.G.Pend.logF_map]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inParam_eq {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) : inParam p f = subst (lK p) f := rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_map]`. Use `show φ (expS p f n) = Formalism.MainNotions.TaylorLogMetric.expMv (map φ f) n`. Unfold `expS Formalism.MainNotions.TaylorLogMetric.expMv`. Rewrite using `[map_sum]`.

Establish `hd : n.degree = n.sum fun _ k => k` using `rfl`. Rewrite using `[hd]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, coeff_map, map_mul, map_inv₀, map_natCast, div_eq_inv_mul]`.
-/
theorem map_expS {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) :
    map φ (expS p f) = Formalism.MainNotions.TaylorLogMetric.expMv (map φ f) := by
  ext n
  rw [coeff_map]
  show φ (expS p f n) = Formalism.MainNotions.TaylorLogMetric.expMv (map φ f) n
  unfold expS Formalism.MainNotions.TaylorLogMetric.expMv
  rw [map_sum]
  have hd : n.degree = n.sum fun _ k => k := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_map, map_mul, map_inv₀, map_natCast, div_eq_inv_mul]

/- English proof (translation)
Take `⟨h0, w, -, hw⟩` from `h`. Establish `hs : map φ (inParam p f) - map φ (inParam p g) = map φ (inParam p (f - g))`. Rewrite using `[inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]`. Establish `hc : constantCoeff (inParam p (f - g)) = 0` using `constantCoeff_subst_eq_zero hasSubst_lK cc_lK h0`. Unfold `Formalism.MainNotions.GL3Theta.SimeqW`.

Rewrite using `[hs]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `congrArg (φ) hc` as an intermediate fact. Rewrite `this` using `[map_zero]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]`.

Conclude with `this`. Rewrite using `[← map_expS, hw]`. Use `(Formalism.L2.G.Pend.integralW_iff _).2 ⟨1 + w, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Simplify using `[coeff_map, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]`.
-/
theorem simeqW_of_simeq {ι : Type} [Finite ι] {f g : MvPowerSeries ι (FormalGroupSystem.K0 p)} (h : FormalGroupSystem.Simeq p f g) :
    Formalism.MainNotions.GL3Theta.SimeqW (map φ (inParam p f)) (map φ (inParam p g)) := by
  obtain ⟨h0, w, -, hw⟩ := h
  have hs : map φ (inParam p f) - map φ (inParam p g) = map φ (inParam p (f - g)) := by
    rw [inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]
  have hc : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero hasSubst_lK cc_lK h0
  unfold Formalism.MainNotions.GL3Theta.SimeqW
  rw [hs]
  refine ⟨?_, ?_⟩
  · have := congrArg (φ) hc
    rw [map_zero] at this
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
    exact this
  · rw [← map_expS, hw]
    refine (Formalism.L2.G.Pend.integralW_iff _).2 ⟨1 + w, ?_⟩
    ext n
    simp [coeff_map, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]

def mI {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) : MvPowerSeries ι ℂ_[p] := map φ (inParam p f)

/- English proof (translation)
Unfold `mI`. Rewrite using `[inParam_eq, subst_X hasSubst_lK, map_lK]`.
-/
theorem mI_X {ι : Type} [Finite ι] (i : ι) : mI (X i : MvPowerSeries ι (FormalGroupSystem.K0 p)) = GlobalTheory.ThBe0.lg i := by
  unfold mI
  rw [inParam_eq, subst_X hasSubst_lK, map_lK]

/- English proof (translation)
Unfold `mI`. Rewrite using `[inParam_eq, inParam_eq, inParam_eq, subst_add hasSubst_lK, map_add]`.
-/
theorem mI_add {ι : Type} [Finite ι] (f g : MvPowerSeries ι (FormalGroupSystem.K0 p)) : mI (f + g) = mI f + mI g := by
  unfold mI
  rw [inParam_eq, inParam_eq, inParam_eq, subst_add hasSubst_lK, map_add]

/- English proof (translation)
Unfold `mI`. Rewrite using `[inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]`.
-/
theorem mI_sub {ι : Type} [Finite ι] (f g : MvPowerSeries ι (FormalGroupSystem.K0 p)) : mI (f - g) = mI f - mI g := by
  unfold mI
  rw [inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]

/- English proof (translation)
Unfold `mI`. Rewrite using `[inParam_eq, inParam_eq, ← smul_eq_C_mul, subst_smul hasSubst_lK, smul_eq_C_mul, map_mul, map_C]`.
-/
theorem mI_C_mul {ι : Type} [Finite ι] (a : FormalGroupSystem.K0 p) (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) :
    mI (C a * f) = C (φ a) * mI f := by
  unfold mI
  rw [inParam_eq, inParam_eq, ← smul_eq_C_mul, subst_smul hasSubst_lK, smul_eq_C_mul, map_mul, map_C]

/- English proof (translation)
Use `mI_sub (0 : MvPowerSeries ι (FormalGroupSystem.K0 p)) 0` as an intermediate fact. Rewrite `this` using `[sub_zero, sub_self]`. Then use the resulting hypothesis.
-/
theorem mI_zero {ι : Type} [Finite ι] : mI (0 : MvPowerSeries ι (FormalGroupSystem.K0 p)) = 0 := by
  have := mI_sub (0 : MvPowerSeries ι (FormalGroupSystem.K0 p)) 0
  rwa [sub_zero, sub_self] at this

/- English proof (translation)
Apply the tactic sequence `have ha : HasSubst (![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) := hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hx, hy]`. Apply the tactic sequence `have hb : HasSubst (fun i : Fin 2 => subst (lK (ι := κ) p) ((![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) i)) := hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hasSubst_lK cc_lK (by fin_cases i <;> simp [hx, hy])`. Unfold `mI sub2 GlobalTheory.ThBe0.at2`. Rewrite using `[inParam_eq, subst_comp_subst_apply ha hasSubst_lK, map_subst hb]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [inParam_eq]`.
-/
theorem frobenius_map_subst_pair {κ : Type} [Finite κ] (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)) {x y : MvPowerSeries κ (FormalGroupSystem.K0 p)}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    mI (sub2 p be x y) = GlobalTheory.ThBe0.at2 (map φ be) (mI x) (mI y) := by
  have ha : HasSubst (![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) :=
    hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hx, hy]
  have hb : HasSubst (fun i : Fin 2 => subst (lK (ι := κ) p) ((![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) i)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hasSubst_lK cc_lK (by fin_cases i <;> simp [hx, hy])
  unfold mI sub2 GlobalTheory.ThBe0.at2
  rw [inParam_eq, subst_comp_subst_apply ha hasSubst_lK, map_subst hb]
  congr 1
  funext i
  fin_cases i <;> simp [inParam_eq]

/- English proof (translation)
Establish `e : a - (b + c) = a - b - c - 0` using `by ring`. Unfold `Formalism.MainNotions.GL3Theta.SimeqW at h ⊢`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem simeqW_add {κ : Type} {a b c : MvPowerSeries κ ℂ_[p]} (h : Formalism.MainNotions.GL3Theta.SimeqW (a - b - c) 0) :
    Formalism.MainNotions.GL3Theta.SimeqW a (b + c) := by
  have e : a - (b + c) = a - b - c - 0 := by ring
  unfold Formalism.MainNotions.GL3Theta.SimeqW at h ⊢
  rw [e]
  exact h

/- English proof (translation)
Introduce `p _ σ _ hs be hbe`. Establish `cX : ∀ {κ : Type} (i : κ), constantCoeff (X i : MvPowerSeries κ (FormalGroupSystem.K0 p)) = 0` using `fun i => constantCoeff_X i`. Use `⟨(Formalism.L2.G.Pend.coefWf_iff _).2 ⟨be, rfl⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n hn`. Establish `h0 : coeff n be ≠ 0`.

Introduce `h`. Apply `hn` to reduce the goal to its premises. Rewrite using `[coeff_map, h, map_zero]`. Take `⟨h1, h2⟩` from `hbe.ab n h0`. Conclude with `⟨by omega, by omega⟩`.

Establish `h` using `simeqW_of_simeq hbe.add1`. Apply `simeqW_add` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h`. Rewrite `h` using `[mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (by simp) (cX 2), frobenius_map_subst_pair be (cX 0) (cX 2), frobenius_map_subst_pair be (cX 1) (cX 2), mI_add, mI_X, mI_X, mI_X]`. Conclude with `h`.

Establish `h` using `simeqW_of_simeq hbe.add2`. Apply `simeqW_add` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h`. Rewrite `h` using `[mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (cX 0) (by simp), frobenius_map_subst_pair be (cX 0) (cX 1), frobenius_map_subst_pair be (cX 0) (cX 2), mI_add, mI_X, mI_X, mI_X]`. Conclude with `h`.

Introduce `α hα h2`. Take `⟨x, rfl⟩` from `(Formalism.L2.G.Pend.mem_Wp_iff p α).1 hα`. Establish `hx : (sigW p)^[2] x = x`. Apply `Formalism.L2.G.Pend.wToC_injective p` to reduce the goal to its premises. Rewrite using `[← h2, hs x, hs (sigW p x)]`.

Both sides reduce to the same expression. Establish `h` using `simeqW_of_simeq (hbe.conj x hx)`. Express the relevant statement in the definitionally equal form `Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h`. Rewrite `h` using `[frobenius_map_subst_pair be (by simp) (cX 1), frobenius_map_subst_pair be (cX 0) (by simp), mI_C_mul, mI_C_mul, mI_X, mI_X, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hs x]`. Conclude with `h`.
-/
theorem isBe0_map : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), GlobalTheory.ThBe0.IsFrob σ →
    (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) →
    ∀ be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p), BeProp p be →
      GlobalTheory.ThBe0.IsBe0 σ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) := by
  intro p _ σ _ hs be hbe
  have cX : ∀ {κ : Type} (i : κ), constantCoeff (X i : MvPowerSeries κ (FormalGroupSystem.K0 p)) = 0 := fun i => constantCoeff_X i
  refine ⟨(Formalism.L2.G.Pend.coefWf_iff _).2 ⟨be, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have h0 : coeff n be ≠ 0 := by
      intro h
      apply hn
      rw [coeff_map, h, map_zero]
    obtain ⟨h1, h2⟩ := hbe.ab n h0
    exact ⟨by omega, by omega⟩
  · have h := simeqW_of_simeq hbe.add1
    apply simeqW_add
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (by simp) (cX 2), frobenius_map_subst_pair be (cX 0) (cX 2), frobenius_map_subst_pair be (cX 1) (cX 2),
      mI_add, mI_X, mI_X, mI_X] at h
    exact h
  · have h := simeqW_of_simeq hbe.add2
    apply simeqW_add
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (cX 0) (by simp), frobenius_map_subst_pair be (cX 0) (cX 1), frobenius_map_subst_pair be (cX 0) (cX 2),
      mI_add, mI_X, mI_X, mI_X] at h
    exact h
  · intro α hα h2
    obtain ⟨x, rfl⟩ := (Formalism.L2.G.Pend.mem_Wp_iff p α).1 hα
    have hx : (sigW p)^[2] x = x := by
      apply Formalism.L2.G.Pend.wToC_injective p
      rw [← h2, hs x, hs (sigW p x)]
      rfl
    have h := simeqW_of_simeq (hbe.conj x hx)
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [frobenius_map_subst_pair be (by simp) (cX 1), frobenius_map_subst_pair be (cX 0) (by simp), mI_C_mul, mI_C_mul, mI_X, mI_X,
      Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hs x] at h
    exact h

end GlobalTheory.BeRead

end
