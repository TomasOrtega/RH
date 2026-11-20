import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AtPiEqRescale

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF expSum eq_of_low Gser)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section ExpFormal

variable {K : Type} [Field K]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_expK, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[zero_pow hk]`.

Introduce `h`. Simplify using `at h`.
-/
theorem th_expK_zero {ι : Type} : expK (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_expK, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

/- English proof (translation)
Rewrite using `[expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]`.
-/
theorem th_subst_expSum {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ K) (M : ℕ) : MvPowerSeries.subst a (expSum f M) = expSum (MvPowerSeries.subst a f) M := by
  rw [expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Establish `hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0` using `MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf`. Use `eq_of_low fun M => ?_` and prove the remaining obligations. Establish `h1` using `Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)`. Establish `h2` using `low_expK_sub hsf M`.

Establish `e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) = MvPowerSeries.subst a (expK f - expSum f M) - (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M)`. Rewrite using `[← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `low_sub h1 h2`.
-/
theorem th_subst_expK {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (expK f) = expK (MvPowerSeries.subst a f) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf
  refine eq_of_low fun M => ?_
  have h1 := Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)
  have h2 := low_expK_sub hsf M
  have e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) =
      MvPowerSeries.subst a (expK f - expSum f M) -
        (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M) := by
    rw [← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]
    ring
  rw [e]
  exact low_sub h1 h2

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]`.
-/
theorem th_map_expK {ι K2 : Type} [Field K2] (φ : K →+* K2) (f : MvPowerSeries ι K) :
    MvPowerSeries.map φ (expK f) = expK (MvPowerSeries.map φ f) := by
  ext n
  rw [MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]

end ExpFormal

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def E0 {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
    expK f = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

/- English proof (translation)
Use `⟨map_zero _, 0, map_zero _, ?_⟩` and prove the remaining obligations. Rewrite using `[th_expK_zero, map_zero, add_zero]`.
-/
theorem integralExp_zero {ι : Type} : E0 p (0 : MvPowerSeries ι (K0 p)) := by
  refine ⟨map_zero _, 0, map_zero _, ?_⟩
  rw [th_expK_zero, map_zero, add_zero]

/- English proof (translation)
Take `⟨hf0, h, hh0, hfe⟩` from `hf`. Take `⟨hg0, h', hh0', hge⟩` from `hg`. Use `⟨by rw [map_add, hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩` and prove the remaining obligations. Rewrite using `[expK_add hf0 hg0, hfe, hge, map_add, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integralExp_add {ι : Type} {f g : MvPowerSeries ι (K0 p)} (hf : E0 p f) (hg : E0 p g) : E0 p (f + g) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  obtain ⟨hg0, h', hh0', hge⟩ := hg
  refine ⟨by rw [map_add, hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩
  rw [expK_add hf0 hg0, hfe, hge, map_add, map_add, map_mul]
  ring

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.sum_empty]`. Conclude with `integralExp_zero p`.

Introduce `a s ha ih h`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))`.
-/
theorem integralExp_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι (K0 p)) (h : ∀ a ∈ s, E0 p (f a)) :
    E0 p (∑ a ∈ s, f a) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact integralExp_zero p
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def ren {κ σ R : Type} [CommRing R] (φ : κ → σ) (f : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) f

/- English proof (translation)
Take `⟨hf0, h, hh0, hfe⟩` from `hf`. Establish `hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0` using `fun k => MvPowerSeries.constantCoeff_X _`. Establish `hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0` using `fun k => MvPowerSeries.constantCoeff_X _`. Establish `haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hXW`. Establish `haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hXK`.

Use `⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h, MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩` and prove the remaining obligations. Unfold `ren`. Rewrite using `[← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add, map_one, MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]`. Simplify using `only [MvPowerSeries.map_X]`.
-/
theorem integralExp_rename {κ σ : Type} [Finite κ] (φ : κ → σ) {f : MvPowerSeries κ (K0 p)} (hf : E0 p f) :
    E0 p (ren φ f) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  have hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXW
  have haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXK
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h,
    MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩
  unfold ren
  rw [← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add, map_one,
    MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]
  simp only [MvPowerSeries.map_X]

/- English proof (translation)
Take `⟨hf0, h, hh0, hfe⟩` from `hf`. Use `⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩` and prove the remaining obligations. Establish `hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1` using `MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])`. Establish `hneg : expK (-f) * expK f = 1`. Rewrite using `[← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfe, map_mul, map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hneg, one_mul]`.
-/
theorem exp_neg_integral {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : E0 p f) :
    ∃ w : MvPowerSeries ι (WW p), expK (-f) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])
  have hneg : expK (-f) * expK f = 1 := by
    rw [← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]
  calc expK (-f) = expK (-f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        ((1 + h) * MvPowerSeries.invOfUnit (1 + h) 1) := by rw [hinv, map_one, mul_one]
    _ = (expK (-f) * expK f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by
      rw [hfe, map_mul, map_add, map_one]
      ring
    _ = _ := by rw [hneg, one_mul]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
