import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.ThStr GlobalTheory.ThBe0 MvPowerSeries
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D Formalism.L2.Th1.D.Pair
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB d1 swap2 in3 UnrOK IsLawOfLog)
open GlobalTheory.CompareInert (mem_Wp_of_kur Wp_subset_Kur exists_pow_norm_le norm_l_lt)

namespace GlobalTheory.OnePlace.Unr

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `hc : (l : ℂ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `e : x = ((l : ℂ_[l]) ^ k)⁻¹ * ((l : ℂ_[l]) ^ k * x)` using `by field_simp`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (pow_mem (natCast_mem _ l) k)) (Wp_subset_Kur hk)`.
-/
theorem kur_of_inWf {x : ℂ_[l]} (h : InWf x) : x ∈ MaximalUnramifiedExtension l := by
  obtain ⟨k, hk⟩ := h
  have hc : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have e : x = ((l : ℂ_[l]) ^ k)⁻¹ * ((l : ℂ_[l]) ^ k * x) := by field_simp
  rw [e]
  exact mul_mem (inv_mem (pow_mem (natCast_mem _ l) k)) (Wp_subset_Kur hk)

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_pow_norm_le (norm_l_lt (l := l)) x`. Conclude with `⟨k, mem_Wp_of_kur (mul_mem (pow_mem (natCast_mem _ l) k) h) hk⟩`.
-/
theorem inWf_of_kur {x : ℂ_[l]} (h : x ∈ MaximalUnramifiedExtension l) : InWf x := by
  obtain ⟨k, hk⟩ := exists_pow_norm_le (norm_l_lt (l := l)) x
  exact ⟨k, mem_Wp_of_kur (mul_mem (pow_mem (natCast_mem _ l) k) h) hk⟩

/- English proof (translation)
Take `⟨k, hk⟩` from `inWf_of_kur hx`. Take `⟨y, hy, e⟩` from `hσ.lift _ hk`. Use `kur_of_inWf ⟨k, ?_⟩` and prove the remaining obligations. Establish `e' : (l : ℂ_[l]) ^ k * σ x = ((l : ℂ_[l]) ^ k * x) ^ l + l * y`. Rewrite using `[← e, map_mul, map_pow, map_natCast]`.

Rewrite using `[e']`. Conclude with `add_mem (pow_mem hk _) (mul_mem (natCast_mem _ l) hy)`.
-/
theorem frob_mem_kur {σ : ℂ_[l] →+* ℂ_[l]} (hσ : IsFrob σ) {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  obtain ⟨k, hk⟩ := inWf_of_kur hx
  obtain ⟨y, hy, e⟩ := hσ.lift _ hk
  refine kur_of_inWf ⟨k, ?_⟩
  have e' : (l : ℂ_[l]) ^ k * σ x = ((l : ℂ_[l]) ^ k * x) ^ l + l * y := by
    rw [← e, map_mul, map_pow, map_natCast]
  rw [e']
  exact add_mem (pow_mem hk _) (mul_mem (natCast_mem _ l) hy)

/- English proof (translation)
Use `⟨(σ.comp (MaximalUnramifiedExtension l).subtype).codRestrict (MaximalUnramifiedExtension l) fun x => frob_mem_kur hσ x.2, fun _ => rfl, ?_⟩` and prove the remaining obligations. Take `⟨τ0, ⟨h1, h2, h3, h4, -⟩, -⟩` from `Formalism.L2.Th1.D.kurFrob l (by omega)`. Use `⟨h1, h2, h3, h4, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hσ.lift a (mem_Wp_of_kur a.2 ha)`. Use `show ‖σ (a : ℂ_[l]) - (a : ℂ_[l]) ^ l‖ ≤ _`.

Rewrite using `[e, add_sub_cancel_left, norm_mul, Formalism.L2.G.Pend.norm_p_C]`. Conclude with `mul_le_of_le_one_right (by positivity) (GlobalTheory.UnitModel.norm_le_one_of_mem_Wp hy)`.
-/
theorem exists_restrict (h5 : 5 ≤ l) {σ : ℂ_[l] →+* ℂ_[l]} (hσ : IsFrob σ) :
    ∃ τ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, (∀ x, (MaximalUnramifiedExtension l).subtype (τ x) = σ ((MaximalUnramifiedExtension l).subtype x)) ∧ UnrOK (MaximalUnramifiedExtension l) l τ := by
  refine ⟨(σ.comp (MaximalUnramifiedExtension l).subtype).codRestrict (MaximalUnramifiedExtension l) fun x => frob_mem_kur hσ x.2, fun _ => rfl, ?_⟩
  obtain ⟨τ0, ⟨h1, h2, h3, h4, -⟩, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  refine ⟨h1, h2, h3, h4, fun a ha => ?_⟩
  obtain ⟨y, hy, e⟩ := hσ.lift a (mem_Wp_of_kur a.2 ha)
  show ‖σ (a : ℂ_[l]) - (a : ℂ_[l]) ^ l‖ ≤ _
  rw [e, add_sub_cancel_left, norm_mul, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnitModel.norm_le_one_of_mem_Wp hy)

/- English proof (translation)
Use `forall_congr' fun n => ?_` and prove the remaining obligations. Rewrite using `[coeff_map]`. Conclude with `⟨fun h => GlobalTheory.UnitModel.norm_le_one_of_mem_Wp h, fun h => mem_Wp_of_kur (coeff n f).2 h⟩`.
-/
theorem integralW_map_iff {κ : Type} (f : MvPowerSeries κ (MaximalUnramifiedExtension l)) :
    IntegralW (map (MaximalUnramifiedExtension l).subtype f) ↔ Integral f := by
  refine forall_congr' fun n => ?_
  rw [coeff_map]
  exact ⟨fun h => GlobalTheory.UnitModel.norm_le_one_of_mem_Wp h, fun h => mem_Wp_of_kur (coeff n f).2 h⟩

/- English proof (translation)
Unfold `SimeqW Formalism.InvariantFactorPaths.G7.Simeq`. Rewrite using `[← map_sub]`. Establish `h0 : constantCoeff (map (MaximalUnramifiedExtension l).subtype (f - g)) = 0 ↔ constantCoeff (f - g) = 0`. Rewrite using `[constantCoeff_map]`. Conclude with `map_eq_zero _`.

Rewrite using `[h0]`. Use `and_congr_right fun h => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.ExpLogMv.expMv_eq_subst (h0.2 h), ← integralW_map_iff, Formalism.DworkPowerSeriesWeights.Transfer.map_mvExp _ h]`. Both sides reduce to the same expression.
-/
theorem simeqW_map_iff {κ : Type} (f g : MvPowerSeries κ (MaximalUnramifiedExtension l)) :
    SimeqW (map (MaximalUnramifiedExtension l).subtype f) (map (MaximalUnramifiedExtension l).subtype g) ↔ Formalism.InvariantFactorPaths.G7.Simeq f g := by
  unfold SimeqW Formalism.InvariantFactorPaths.G7.Simeq
  rw [← map_sub]
  have h0 : constantCoeff (map (MaximalUnramifiedExtension l).subtype (f - g)) = 0 ↔ constantCoeff (f - g) = 0 := by
    rw [constantCoeff_map]
    exact map_eq_zero _
  rw [h0]
  refine and_congr_right fun h => ?_
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (h0.2 h), ← integralW_map_iff, Formalism.DworkPowerSeriesWeights.Transfer.map_mvExp _ h]
  rfl

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [logF, lgF, PowerSeries.coeff_mk, ← pow_mul]`.
-/
theorem lgF_eq : lgF ℂ_[l] l = logF l := by
  ext n
  simp only [logF, lgF, PowerSeries.coeff_mk, ← pow_mul]

/- English proof (translation)
Rewrite using `[GlobalTheory.KerStd.CofactorConverse.map_inVar, BiextensionSums.map_lgF', lgF_eq]`. Both sides reduce to the same expression.
-/
theorem map_lg {κ : Type} (k : κ) : map (MaximalUnramifiedExtension l).subtype (at1 k (lgF (MaximalUnramifiedExtension l) l)) = lg k := by
  rw [GlobalTheory.KerStd.CofactorConverse.map_inVar, BiextensionSums.map_lgF', lgF_eq]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `n`. Unfold `letLog laS`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Use `push_cast`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem letLog_eq (d : ℕ) [NeZero d] (s : ZMod d) : letLog (K := ℂ_[l]) l s = laS l d s := by
  funext n
  unfold letLog laS
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← pow_mul]
  push_cast
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[map_subst (hs2 hx hy)]`. Unfold `at2`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem map_pair {κ : Type} (b : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) {x y : MvPowerSeries κ (MaximalUnramifiedExtension l)}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    map (MaximalUnramifiedExtension l).subtype (subst ![x, y] b) =
      at2 (map (MaximalUnramifiedExtension l).subtype b) (map (MaximalUnramifiedExtension l).subtype x) (map (MaximalUnramifiedExtension l).subtype y) := by
  rw [map_subst (hs2 hx hy)]
  unfold at2
  congr 1
  funext i
  fin_cases i <;> rfl

section Par

variable {K : Type} [Field K]

def inPar (l : ℕ) (b : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  subst ![at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] b

/- English proof (translation)
Unfold `inPar`. Rewrite using `[subst2_comp (hs2 hx hy) (constantCoeff_inVar_eq_zero _ (cc_lgF hl)) (constantCoeff_inVar_eq_zero _ (cc_lgF hl)), subst_single_var (hs2 hx hy), subst_single_var (hs2 hx hy)]`. Both sides reduce to the same expression.
-/
theorem subst_inPar {l : ℕ} (hl : 2 ≤ l) (b : MvPowerSeries (Fin 2) K) {κ : Type} {x y : MvPowerSeries κ K}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    subst ![x, y] (inPar l b) = subst ![PowerSeries.subst x (lgF K l), PowerSeries.subst y (lgF K l)] b := by
  unfold inPar
  rw [subst2_comp (hs2 hx hy) (constantCoeff_inVar_eq_zero _ (cc_lgF hl)) (constantCoeff_inVar_eq_zero _ (cc_lgF hl)), subst_single_var (hs2 hx hy),
    subst_single_var (hs2 hx hy)]
  rfl

/- English proof (translation)
Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.2 hf`. Unfold `at1`. Rewrite using `[PowerSeries.subst_mul (PowerSeries.HasSubst.X k), PowerSeries.subst_X (PowerSeries.HasSubst.X k)]`. Conclude with `dvd_mul_right _ _`.
-/
theorem X_dvd_at1_of_constantCoeff_eq_zero {κ : Type} (k : κ) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    (X k : MvPowerSeries κ K) ∣ at1 k f := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  unfold at1
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X k), PowerSeries.subst_X (PowerSeries.HasSubst.X k)]
  exact dvd_mul_right _ _

/- English proof (translation)
Establish `hs` using `hs2 (constantCoeff_inVar_eq_zero (0 : Fin 2) (cc_lgF (K := K) hl)) (constantCoeff_inVar_eq_zero (1 : Fin 2) (cc_lgF (K := K) hl))`. Introduce `n hn`. Break down `hn with hn | hn` into its components or cases. Take `⟨g, hg⟩` from `(X_dvd_iff (s := (0 : Fin 2)) (φ := b)).2 fun m hm => hb m (Or.inl hm)`. Use `(X_dvd_iff (s := (0 : Fin 2))).1 ?_ n hn` and prove the remaining obligations.

Unfold `inPar`. Rewrite using `[hg, subst_mul hs, subst_X hs]`. Conclude with `Dvd.dvd.mul_right (X_dvd_at1_of_constantCoeff_eq_zero 0 (cc_lgF hl)) _`. Take `⟨g, hg⟩` from `(X_dvd_iff (s := (1 : Fin 2)) (φ := b)).2 fun m hm => hb m (Or.inr hm)`. Use `(X_dvd_iff (s := (1 : Fin 2))).1 ?_ n hn` and prove the remaining obligations.

Unfold `inPar`. Rewrite using `[hg, subst_mul hs, subst_X hs]`. Conclude with `Dvd.dvd.mul_right (X_dvd_at1_of_constantCoeff_eq_zero 1 (cc_lgF hl)) _`.
-/
theorem divAB_inPar {l : ℕ} (hl : 2 ≤ l) {b : MvPowerSeries (Fin 2) K} (hb : DivAB b) : DivAB (inPar l b) := by
  have hs := hs2 (constantCoeff_inVar_eq_zero (0 : Fin 2) (cc_lgF (K := K) hl)) (constantCoeff_inVar_eq_zero (1 : Fin 2) (cc_lgF (K := K) hl))
  intro n hn
  rcases hn with hn | hn
  · obtain ⟨g, hg⟩ := (X_dvd_iff (s := (0 : Fin 2)) (φ := b)).2 fun m hm => hb m (Or.inl hm)
    refine (X_dvd_iff (s := (0 : Fin 2))).1 ?_ n hn
    unfold inPar
    rw [hg, subst_mul hs, subst_X hs]
    exact Dvd.dvd.mul_right (X_dvd_at1_of_constantCoeff_eq_zero 0 (cc_lgF hl)) _
  · obtain ⟨g, hg⟩ := (X_dvd_iff (s := (1 : Fin 2)) (φ := b)).2 fun m hm => hb m (Or.inr hm)
    refine (X_dvd_iff (s := (1 : Fin 2))).1 ?_ n hn
    unfold inPar
    rw [hg, subst_mul hs, subst_X hs]
    exact Dvd.dvd.mul_right (X_dvd_at1_of_constantCoeff_eq_zero 1 (cc_lgF hl)) _

end Par

/- English proof (translation)
Unfold `Formalism.InvariantFactorPaths.G7.Simeq at H ⊢`. Rewrite using `[sub_zero, sub_sub]` and apply the resulting hypothesis.
-/
theorem simeq_zero {K κ : Type} [NormedField K] [CharZero K] {f g h : MvPowerSeries κ K}
    (H : Formalism.InvariantFactorPaths.G7.Simeq f (g + h)) : Formalism.InvariantFactorPaths.G7.Simeq (f - g - h) 0 := by
  unfold Formalism.InvariantFactorPaths.G7.Simeq at H ⊢
  rwa [sub_zero, sub_sub]

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hL : ∀ i : Fin 3, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0` using `fun i => constantCoeff_inVar_eq_zero _ (cc_lgF hl)`. Establish `hL2 : ∀ i j : Fin 3, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l) + at1 j (lgF (MaximalUnramifiedExtension l) l)) = 0` using `fun i j => by`. Rewrite using `[map_add, hL, hL, add_zero]`. Establish `hin : constantCoeff (in3 F) = 0`.

Unfold `in3`. Apply the tactic sequence `exact constantCoeff_subst_eq_zero (hs2 (by simp) (by simp)) (by intro i; fin_cases i <;> simp) hF.1`. Establish `hlaw : PowerSeries.subst (in3 F) (lgF (MaximalUnramifiedExtension l) l) = at1 0 (lgF (MaximalUnramifiedExtension l) l) + at1 1 (lgF (MaximalUnramifiedExtension l) l)` using `log_law hF.1 hF.2.2 (constantCoeff_X _) (constantCoeff_X _)`. Use `⟨divAB_inPar hl fun n hn => ?_, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Use `hb.axes n (by rw [coeff_map]; exact (map_ne_zero _).2 h)` as an intermediate fact. The claim follows by propositional logic. Unfold `d1`. Rewrite using `[subst_inPar hl b hin (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _), hlaw]`. Use `simeq_zero ((simeqW_map_iff _ _).1 ?_)` and prove the remaining obligations.

Establish `h` using `hb.add₁`. Rewrite `h` using `[← map_lg, ← map_lg, ← map_lg, ← map_add, ← map_pair b (hL2 _ _) (hL _), ← map_pair b (hL _) (hL _), ← map_pair b (hL _) (hL _), ← map_add]`. Conclude with `h`. Unfold `d1`. Rewrite using `[subst_swap2 hin (constantCoeff_X _), subst_swap2 (constantCoeff_X _) (constantCoeff_X _), subst_swap2 (constantCoeff_X _) (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) hin, subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) …`.

Use `simeq_zero ?_` and prove the remaining obligations. Establish `h` using `hb.add₂`. Rewrite `h` using `[← map_lg, ← map_lg, ← map_lg, ← map_add, ← map_pair b (hL _) (hL2 _ _), ← map_pair b (hL _) (hL _), ← map_pair b (hL _) (hL _), ← map_add, simeqW_map_iff]`. Establish `hs : HasSubst ![(X 2 : MvPowerSeries (Fin 3) (MaximalUnramifiedExtension l)), X 0, X 1]` using `hs3 (constantCoeff_X _) (constantCoeff_X _) (constantCoeff_X _)`. Apply the tactic sequence `have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) (Fin 3)).2.2.2.2 (Fin 3) _ _ ![(X 2 : MvPowerSeries (Fin 3) (MaximalUnramifiedExtension l)), X 0, X 1] (by intro i; fin_cases i <;> exact constantCoeff_X _) (by intro i; fin_cases i <;> ex …`.

Rewrite `h'` using `[subst_add hs, subst2_comp hs (hL _) (hL2 _ _), subst2_comp hs (hL _) (hL _), subst2_comp hs (hL _) (hL _), subst_add hs, subst_single_var hs, subst_single_var hs, subst_single_var hs]`. Conclude with `h'`.
-/
theorem biadditive_substLogarithmsIntoParameters_of_logExponent {σ : ℂ_[l] →+* ℂ_[l]} {b : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)} (hb : IsBe0 σ (map (MaximalUnramifiedExtension l).subtype b))
    {F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)} (hF : IsLawOfLog l F) : F1 F (inPar l b) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hL : ∀ i : Fin 3, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0 := fun i => constantCoeff_inVar_eq_zero _ (cc_lgF hl)
  have hL2 : ∀ i j : Fin 3, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l) + at1 j (lgF (MaximalUnramifiedExtension l) l)) = 0 := fun i j => by
    rw [map_add, hL, hL, add_zero]
  have hin : constantCoeff (in3 F) = 0 := by
    unfold in3
    exact constantCoeff_subst_eq_zero (hs2 (by simp) (by simp))
      (by intro i; fin_cases i <;> simp) hF.1
  have hlaw : PowerSeries.subst (in3 F) (lgF (MaximalUnramifiedExtension l) l) = at1 0 (lgF (MaximalUnramifiedExtension l) l) + at1 1 (lgF (MaximalUnramifiedExtension l) l) :=
    log_law hF.1 hF.2.2 (constantCoeff_X _) (constantCoeff_X _)
  refine ⟨divAB_inPar hl fun n hn => ?_, ?_, ?_⟩
  · by_contra h
    have := hb.axes n (by rw [coeff_map]; exact (map_ne_zero _).2 h)
    tauto
  · unfold d1
    rw [subst_inPar hl b hin (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _),
      subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _), hlaw]
    refine simeq_zero ((simeqW_map_iff _ _).1 ?_)
    have h := hb.add₁
    rw [← map_lg, ← map_lg, ← map_lg, ← map_add, ← map_pair b (hL2 _ _) (hL _), ← map_pair b (hL _) (hL _),
      ← map_pair b (hL _) (hL _), ← map_add] at h
    exact h
  · unfold d1
    rw [subst_swap2 hin (constantCoeff_X _), subst_swap2 (constantCoeff_X _) (constantCoeff_X _),
      subst_swap2 (constantCoeff_X _) (constantCoeff_X _),
      subst_inPar hl b (constantCoeff_X _) hin, subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _),
      subst_inPar hl b (constantCoeff_X _) (constantCoeff_X _), hlaw]
    refine simeq_zero ?_
    have h := hb.add₂
    rw [← map_lg, ← map_lg, ← map_lg, ← map_add, ← map_pair b (hL _) (hL2 _ _), ← map_pair b (hL _) (hL _),
      ← map_pair b (hL _) (hL _), ← map_add, simeqW_map_iff] at h
    have hs : HasSubst ![(X 2 : MvPowerSeries (Fin 3) (MaximalUnramifiedExtension l)), X 0, X 1] :=
      hs3 (constantCoeff_X _) (constantCoeff_X _) (constantCoeff_X _)
    have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) (Fin 3)).2.2.2.2 (Fin 3) _ _
      ![(X 2 : MvPowerSeries (Fin 3) (MaximalUnramifiedExtension l)), X 0, X 1]
      (by intro i; fin_cases i <;> exact constantCoeff_X _)
      (by intro i; fin_cases i <;> exact KernelCokernelKilling.integral_X' _) h
    rw [subst_add hs, subst2_comp hs (hL _) (hL2 _ _), subst2_comp hs (hL _) (hL _), subst2_comp hs (hL _) (hL _),
      subst_add hs, subst_single_var hs, subst_single_var hs, subst_single_var hs] at h'
    exact h'

/- English proof (translation)
Unfold `at1`. Rewrite using `[ps_comp (constantCoeff_X _) he.1, he.2, PowerSeries.subst_mul (PowerSeries.HasSubst.X k)]`. Use `congr 1`. Conclude with `PowerSeries.subst_C c`.
-/
theorem subst_lubinTateLog_of_isMul {K κ : Type} [Field K] {l : ℕ} {c : K} {e : PowerSeries K} (he : IsMul l c e) (k : κ) :
    PowerSeries.subst (at1 k e) (lgF K l) = C c * at1 k (lgF K l) := by
  unfold at1
  rw [ps_comp (constantCoeff_X _) he.1, he.2, PowerSeries.subst_mul (PowerSeries.HasSubst.X k)]
  congr 1
  exact PowerSeries.subst_C c

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hL : ∀ i : Fin 2, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0` using `fun i => constantCoeff_inVar_eq_zero _ (cc_lgF hl)`. Establish `hLc : ∀ (c : MaximalUnramifiedExtension l) (i : Fin 2), constantCoeff (C c * at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0` using `fun c i => by`. Rewrite using `[map_mul, hL, mul_zero]`. Introduce `α hα hfix e e' he he'`.

Rewrite using `[subst_inPar hl b (constantCoeff_inVar_eq_zero _ he.1) (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) (constantCoeff_inVar_eq_zero _ he'.1), subst_lubinTateLog_of_isMul he, subst_lubinTateLog_of_isMul he']`. Establish `h` using `hb.conj ((MaximalUnramifiedExtension l).subtype α) (mem_Wp_of_kur α.2 hα) (by rw [← hτ, ← hτ, hfix])`. Rewrite `h` using `[← hτ, ← map_lg, ← map_lg, ← map_C, ← map_C, ← map_mul, ← map_mul, ← map_pair b (hLc _ _) (hL _), ← map_pair b (hL _) (hLc _ _), simeqW_map_iff]`. Conclude with `h`.
-/
theorem adjoint_substLogarithmsIntoParameters_of_logExponent {σ : ℂ_[l] →+* ℂ_[l]} {τ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l}
    (hτ : ∀ x, (MaximalUnramifiedExtension l).subtype (τ x) = σ ((MaximalUnramifiedExtension l).subtype x))
    {b : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)} (hb : IsBe0 σ (map (MaximalUnramifiedExtension l).subtype b)) : F2 l τ (inPar l b) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hL : ∀ i : Fin 2, constantCoeff (at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0 := fun i => constantCoeff_inVar_eq_zero _ (cc_lgF hl)
  have hLc : ∀ (c : MaximalUnramifiedExtension l) (i : Fin 2), constantCoeff (C c * at1 i (lgF (MaximalUnramifiedExtension l) l)) = 0 := fun c i => by
    rw [map_mul, hL, mul_zero]
  intro α hα hfix e e' he he'
  rw [subst_inPar hl b (constantCoeff_inVar_eq_zero _ he.1) (constantCoeff_X _), subst_inPar hl b (constantCoeff_X _) (constantCoeff_inVar_eq_zero _ he'.1),
    subst_lubinTateLog_of_isMul he, subst_lubinTateLog_of_isMul he']
  have h := hb.conj ((MaximalUnramifiedExtension l).subtype α) (mem_Wp_of_kur α.2 hα) (by rw [← hτ, ← hτ, hfix])
  rw [← hτ, ← map_lg, ← map_lg, ← map_C, ← map_C, ← map_mul, ← map_mul, ← map_pair b (hLc _ _) (hL _),
    ← map_pair b (hL _) (hLc _ _), simeqW_map_iff] at h
  exact h

/- English proof (translation)
Establish `h1 : (∑ s : ZMod d, if s.val % 2 = 0 then f s.val else 0) = ∑ i ∈ Finset.range d, if i % 2 = 0 then f i else 0`. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => if i % 2 = 0 then f i else 0) (n + 1)`. Rewrite using `[h1]`. Take `⟨m, rfl⟩` from `hd`.

Establish `h2 : (m + m) / 2 = m` using `by omega`. Rewrite using `[h2]`. Use `clear h1 h2`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Establish `e : m + 1 + (m + 1) = m + m + 1 + 1` using `by omega`. Rewrite using `[e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, if_pos (by omega), if_neg (by omega), add_zero, two_mul, ih]`.
-/
theorem sum_even {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (hd : Even d) (f : ℕ → M) :
    (∑ s : ZMod d, if s.val % 2 = 0 then f s.val else 0) = ∑ i ∈ Finset.range (d / 2), f (2 * i) := by
  have h1 : (∑ s : ZMod d, if s.val % 2 = 0 then f s.val else 0) =
      ∑ i ∈ Finset.range d, if i % 2 = 0 then f i else 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    exact Fin.sum_univ_eq_sum_range (fun i => if i % 2 = 0 then f i else 0) (n + 1)
  rw [h1]
  obtain ⟨m, rfl⟩ := hd
  have h2 : (m + m) / 2 = m := by omega
  rw [h2]
  clear h1 h2
  induction m with
  | zero => simp
  | succ m ih =>
    have e : m + 1 + (m + 1) = m + m + 1 + 1 := by omega
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, if_pos (by omega), if_neg (by omega),
      add_zero, two_mul, ih]

/- English proof (translation)
Rewrite using `[RingHom.coe_pow]`. Conclude with `(Function.Semiconj.iterate_right (f := (MaximalUnramifiedExtension l).subtype) hτ n x)`.
-/
theorem map_iterate {σ : ℂ_[l] →+* ℂ_[l]} {τ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l}
    (hτ : ∀ x, (MaximalUnramifiedExtension l).subtype (τ x) = σ ((MaximalUnramifiedExtension l).subtype x)) (n : ℕ) (x : MaximalUnramifiedExtension l) :
    (MaximalUnramifiedExtension l).subtype (τ^[n] x) = (σ ^ n) ((MaximalUnramifiedExtension l).subtype x) := by
  rw [RingHom.coe_pow]
  exact (Function.Semiconj.iterate_right (f := (MaximalUnramifiedExtension l).subtype) hτ n x)

def toSum (ρ : Type) : Bool × ρ ≃ ρ ⊕ ρ := Equiv.boolProdEquivSum ρ

/- English proof (translation)
Establish `hl : 2 ≤ l` using `by omega`. Establish `h2 : 2 ≤ d`. Use `NeZero.ne d` as an intermediate fact. Take `⟨m, rfl⟩` from `hd`. Use linear arithmetic over natural numbers and integers.

Take `⟨τ, hτ, hU⟩` from `exists_restrict h5 hσ`. Take `⟨b, rfl⟩ : ∃ b : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), map (MaximalUnramifiedExtension l).subtype b = b0` from `⟨fun n => ⟨coeff n b0, kur_of_inWf (hb.coef n)⟩, by ext n; rfl⟩`. Take `⟨o, rfl⟩ : ∃ o : Fin (d / 2) → MaximalUnramifiedExtension l, (fun r => (MaximalUnramifiedExtension l).subtype (o r)) = om` from `⟨fun r => ⟨om r, Wp_subset_Kur (hD.mem r).1⟩, rfl⟩`. Take `⟨o', rfl⟩ : ∃ o : Fin (d / 2) → MaximalUnramifiedExtension l, (fun r => (MaximalUnramifiedExtension l).subtype (o r)) = om'` from `⟨fun r => ⟨om' r, Wp_subset_Kur (hD.mem r).2⟩, rfl⟩`. Establish `hinj` using `(MaximalUnramifiedExtension l).subtype.injective`.

Establish `hOw : OwOK d τ o o'` using `⟨fun r => ⟨GlobalTheory.UnitModel.norm_le_one_of_mem_Wp (hD.mem r).1, GlobalTheory.UnitModel.norm_le_one_of_mem_Wp (hD.mem r).2⟩, fun r => ⟨hinj (by rw [map_iterate hτ]; exact (hD.fix r).1), hinj (by rw [map_iterate hτ]; exact (hD.fix r).2)⟩⟩`. Establish `hTr : TrDual d τ o o'`. Use `⟨hD.card, fun r r' => hinj ?_⟩` and prove the remaining obligations. Rewrite using `[sum_even d hd (fun n => τ^[n] (o r * o' r')), map_sum]`. Simplify using `only [map_iterate hτ, map_mul (MaximalUnramifiedExtension l).subtype]`.

Rewrite using `[hD.dual r r']`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨F, hF⟩` from `(Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hU.1 hU.2.2.1).1`. Take `⟨ζ, hζ⟩` from `kurRoots l (l ^ d - 1) (by have := Nat.one_lt_pow (NeZero.ne d) (show 1 < l by omega); omega) (by`. Introduce `h`.

Establish `h1 : l ∣ l ^ d` using `dvd_pow_self l (NeZero.ne d)`. Establish `h3` using `(Nat.dvd_sub h1 h)`. Rewrite `h3` using `[Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))]`. Use `Nat.le_of_dvd one_pos h3` as an intermediate fact. Use the proof step `omega)`.

Establish `hF1` using `biadditive_substLogarithmsIntoParameters_of_logExponent hb hF`. Establish `hF2` using `adjoint_substLogarithmsIntoParameters_of_logExponent hτ hb`. Take `⟨T, Xi, hT, hXi, hlog, -, hinv, -, -⟩` from `bMinus1 (MaximalUnramifiedExtension l) l d τ hU h2 hd _ o o' hOw hTr`. Establish `hS` using `(meanSimeq (MaximalUnramifiedExtension l) l d τ hU h2 hd F hF _ hF1 hF2 _ o o' hOw hTr ζ hζ).2`. Establish `hc` using `Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow (biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d τ hU h2 hd F hF _ hF1 _ o o' hOw ζ hζ).2.2.1`.

Take `⟨R, hR⟩ : ∃ R : Bool × Fin (d / 2) → MvPowerSeries (Fin (d / 2) ⊕ Fin (d / 2)) (MaximalUnramifiedExtension l), R = fun y => X (toSum _ y)` from `⟨_, rfl⟩`. Establish `hR0 : ∀ y, constantCoeff (R y) = 0` using `fun y => by rw [hR]; exact constantCoeff_X _`. Establish `hRs : HasSubst R` using `hasSubst_of_constantCoeff_zero hR0`. Establish `hTs : HasSubst T` using `hasSubst_of_constantCoeff_zero fun s => (hT s).1`. Establish `hRT0 : ∀ s, constantCoeff (subst R (T s)) = 0` using `fun s => constantCoeff_subst_eq_zero hRs hR0 (hT s).1`.

Establish `hRT : HasSubst fun s => subst R (T s)` using `hasSubst_of_constantCoeff_zero hRT0`. Establish `hz0` using `TranslateJetMomentLawAnyIdempotentLevel.cc_zXY (d := d) hl τ o o'`. Establish `hzs : HasSubst (zXY (d` using `d) l τ o o') := hasSubst_of_constantCoeff_zero hz0`. Establish `hRz : HasSubst fun s : ZMod d => subst R (zXY l τ o o' s)` using `hasSubst_of_constantCoeff_zero fun s => constantCoeff_subst_eq_zero hRs hR0 (hz0 s)`. Establish `hRat : ∀ y, subst R (at1 y (lgF (MaximalUnramifiedExtension l) l)) = at1 (toSum _ y) (lgF (MaximalUnramifiedExtension l) l)` using `fun y => by`.

Rewrite using `[subst_single_var hRs, hR]`. Both sides reduce to the same expression. Establish `hz : ∀ s : ZMod d, map (MaximalUnramifiedExtension l).subtype (subst R (zXY l τ o o' s)) = zOm σ (fun r => (MaximalUnramifiedExtension l).subtype (o r)) (fun r => (MaximalUnramifiedExtension l).subtype (o' r)) s` using `fun s => by`. Unfold `zXY zOm`. Distinguish the cases in `hs : s.val % 2 = 0`.

Rewrite using `[if_pos hs, if_pos (Nat.even_iff.2 hs), subst_sum hRs, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[subst_mul hRs, subst_C, hRat, map_mul, map_C, map_lg, map_iterate hτ]`. Both sides reduce to the same expression. Rewrite using `[if_neg hs, if_neg (fun h => hs (Nat.even_iff.1 h)), subst_sum hRs, map_sum]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[subst_mul hRs, subst_C, hRat, map_mul, map_C, map_lg, map_iterate hτ]`. Both sides reduce to the same expression. Establish `hXs : HasSubst fun r => Xi ((toSum (Fin (d / 2))).symm r)` using `hasSubst_of_constantCoeff_zero fun r => (hXi _).1`. Use `⟨GlobalTheory.KerStd.beOf l d τ (inPar l b) o o' ζ, fun s => map (MaximalUnramifiedExtension l).subtype (subst R (T s)), fun r => map (MaximalUnramifiedExtension l).subtype (Xi ((toSum _).symm r)), GlobalTheory.KerStd.bHyps_of_beStd l d _ h5 h2 hd ⟨τ, F, _, o, o', ζ, ⟨hU, hF, hF1 …` and prove the remaining obligations.

Unfold `GlobalTheory.KerStd.beOf`. Rewrite using `[constantCoeff_map, hc, map_zero]`. Establish `h` using `(simeqW_map_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) (Bool × Fin (d / 2))).2.2.2.2 _ _ _ R hR0 (fun y => by rw [hR]; exact KernelCokernelKilling.integral_X' _) hS)`. Rewrite `h` using `[subst_comp_subst_apply hzs hRs, map_subst hRz]`. Simplify using `only [hz] at h`.

Use `h using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Unfold `beXY`. Rewrite using `[subst_sum hRs, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[subst2_comp hRs (constantCoeff_X _) (constantCoeff_X _), subst_X hRs, subst_X hRs, subst_inPar hl b (hR0 _) (hR0 _), map_pair b (cc_ps (hR0 _) (cc_lgF hl)) (cc_ps (hR0 _) (cc_lgF hl)), ← map_lg, ← map_lg, hR]`. Both sides reduce to the same expression. Rewrite using `[constantCoeff_map, hRT0, map_zero]`. Rewrite using `[constantCoeff_map, (hXi _).1, map_zero]`. Rewrite using `[← letLog_eq, ← GlobalTheory.KerStd.CofactorConverse.map_letLog l (MaximalUnramifiedExtension l).subtype, ← map_subst hRT, ← subst_comp_subst_apply hTs hRs, hlog, hz]`.

Rewrite using `[← map_subst hXs, subst_comp_subst_apply hRs hXs]`. Establish `e : (fun y => subst (fun r => Xi ((toSum (Fin (d / 2))).symm r)) (R y)) = Xi`. Use function extensionality and compare the values at `y`. Rewrite using `[hR]`. Use `show subst _ (X _) = _`.

Rewrite using `[subst_X hXs, Equiv.symm_apply_apply]`. Rewrite using `[e, hinv, map_X]`.
-/
theorem exists_coords_and_series (h5 : 5 ≤ l) {σ : ℂ_[l] →+* ℂ_[l]} (hσ : IsFrob σ) {b0 : MvPowerSeries (Fin 2) ℂ_[l]}
    (hb : IsBe0 σ b0) (d : ℕ) [NeZero d] (hd : Even d) (om om' : Fin (d / 2) → ℂ_[l]) (hD : DualOm σ d om om') :
    ∃ (bv : MvPowerSeries (ZMod d) ℂ_[l]) (t : ZMod d → MvPowerSeries (Fin (d / 2) ⊕ Fin (d / 2)) ℂ_[l])
      (x : Fin (d / 2) ⊕ Fin (d / 2) → MvPowerSeries (ZMod d) ℂ_[l]),
      (Formalism.MainNotions.product_zeroth_first_parts.B1 l d bv ∧ Formalism.MainNotions.product_zeroth_first_parts.B2 l d bv ∧ Formalism.MainNotions.product_zeroth_first_parts.B3 l d bv ∧ Formalism.MainNotions.product_zeroth_first_parts.B4 l d bv) ∧ constantCoeff bv = 0 ∧
      SimeqW (subst (fun s : ZMod d => zOm σ om om' s) bv)
        (∑ r : Fin (d / 2), at2 b0 (lg (Sum.inl r)) (lg (Sum.inr r))) ∧
      (∀ s, constantCoeff (t s) = 0) ∧ (∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) ∧
      (∀ s, subst t (laS l d s) = zOm σ om om' s) ∧ ∀ s, subst x (t s) = X s := by
  have hl : 2 ≤ l := by omega
  have h2 : 2 ≤ d := by
    have := NeZero.ne d
    obtain ⟨m, rfl⟩ := hd
    omega
  obtain ⟨τ, hτ, hU⟩ := exists_restrict h5 hσ
  obtain ⟨b, rfl⟩ : ∃ b : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), map (MaximalUnramifiedExtension l).subtype b = b0 :=
    ⟨fun n => ⟨coeff n b0, kur_of_inWf (hb.coef n)⟩, by ext n; rfl⟩
  obtain ⟨o, rfl⟩ : ∃ o : Fin (d / 2) → MaximalUnramifiedExtension l, (fun r => (MaximalUnramifiedExtension l).subtype (o r)) = om :=
    ⟨fun r => ⟨om r, Wp_subset_Kur (hD.mem r).1⟩, rfl⟩
  obtain ⟨o', rfl⟩ : ∃ o : Fin (d / 2) → MaximalUnramifiedExtension l, (fun r => (MaximalUnramifiedExtension l).subtype (o r)) = om' :=
    ⟨fun r => ⟨om' r, Wp_subset_Kur (hD.mem r).2⟩, rfl⟩
  have hinj := (MaximalUnramifiedExtension l).subtype.injective
  have hOw : OwOK d τ o o' :=
    ⟨fun r => ⟨GlobalTheory.UnitModel.norm_le_one_of_mem_Wp (hD.mem r).1, GlobalTheory.UnitModel.norm_le_one_of_mem_Wp (hD.mem r).2⟩,
      fun r => ⟨hinj (by rw [map_iterate hτ]; exact (hD.fix r).1), hinj (by rw [map_iterate hτ]; exact (hD.fix r).2)⟩⟩
  have hTr : TrDual d τ o o' := by
    refine ⟨hD.card, fun r r' => hinj ?_⟩
    rw [sum_even d hd (fun n => τ^[n] (o r * o' r')), map_sum]
    simp only [map_iterate hτ, map_mul (MaximalUnramifiedExtension l).subtype]
    rw [hD.dual r r']
    split_ifs <;> simp
  obtain ⟨F, hF⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hU.1 hU.2.2.1).1
  obtain ⟨ζ, hζ⟩ := kurRoots l (l ^ d - 1) (by have := Nat.one_lt_pow (NeZero.ne d) (show 1 < l by omega); omega) (by
    intro h
    have h1 : l ∣ l ^ d := dvd_pow_self l (NeZero.ne d)
    have h3 := (Nat.dvd_sub h1 h)
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h3
    have := Nat.le_of_dvd one_pos h3
    omega)
  have hF1 := biadditive_substLogarithmsIntoParameters_of_logExponent hb hF
  have hF2 := adjoint_substLogarithmsIntoParameters_of_logExponent hτ hb
  obtain ⟨T, Xi, hT, hXi, hlog, -, hinv, -, -⟩ := bMinus1 (MaximalUnramifiedExtension l) l d τ hU h2 hd _ o o' hOw hTr
  have hS := (meanSimeq (MaximalUnramifiedExtension l) l d τ hU h2 hd F hF _ hF1 hF2 _ o o' hOw hTr ζ hζ).2
  have hc := Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow (biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d τ hU h2 hd F hF _ hF1 _ o o' hOw ζ hζ).2.2.1
  obtain ⟨R, hR⟩ : ∃ R : Bool × Fin (d / 2) → MvPowerSeries (Fin (d / 2) ⊕ Fin (d / 2)) (MaximalUnramifiedExtension l),
      R = fun y => X (toSum _ y) := ⟨_, rfl⟩
  have hR0 : ∀ y, constantCoeff (R y) = 0 := fun y => by rw [hR]; exact constantCoeff_X _
  have hRs : HasSubst R := hasSubst_of_constantCoeff_zero hR0
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero fun s => (hT s).1
  have hRT0 : ∀ s, constantCoeff (subst R (T s)) = 0 := fun s => constantCoeff_subst_eq_zero hRs hR0 (hT s).1
  have hRT : HasSubst fun s => subst R (T s) := hasSubst_of_constantCoeff_zero hRT0
  have hz0 := TranslateJetMomentLawAnyIdempotentLevel.cc_zXY (d := d) hl τ o o'
  have hzs : HasSubst (zXY (d := d) l τ o o') := hasSubst_of_constantCoeff_zero hz0
  have hRz : HasSubst fun s : ZMod d => subst R (zXY l τ o o' s) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_subst_eq_zero hRs hR0 (hz0 s)
  have hRat : ∀ y, subst R (at1 y (lgF (MaximalUnramifiedExtension l) l)) = at1 (toSum _ y) (lgF (MaximalUnramifiedExtension l) l) := fun y => by
    rw [subst_single_var hRs, hR]
    rfl
  have hz : ∀ s : ZMod d, map (MaximalUnramifiedExtension l).subtype (subst R (zXY l τ o o' s)) =
      zOm σ (fun r => (MaximalUnramifiedExtension l).subtype (o r)) (fun r => (MaximalUnramifiedExtension l).subtype (o' r)) s := fun s => by
    unfold zXY zOm
    by_cases hs : s.val % 2 = 0
    · rw [if_pos hs, if_pos (Nat.even_iff.2 hs), subst_sum hRs, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [subst_mul hRs, subst_C, hRat, map_mul, map_C, map_lg, map_iterate hτ]
      rfl
    · rw [if_neg hs, if_neg (fun h => hs (Nat.even_iff.1 h)), subst_sum hRs, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [subst_mul hRs, subst_C, hRat, map_mul, map_C, map_lg, map_iterate hτ]
      rfl
  have hXs : HasSubst fun r => Xi ((toSum (Fin (d / 2))).symm r) := hasSubst_of_constantCoeff_zero fun r => (hXi _).1
  refine ⟨GlobalTheory.KerStd.beOf l d τ (inPar l b) o o' ζ, fun s => map (MaximalUnramifiedExtension l).subtype (subst R (T s)),
    fun r => map (MaximalUnramifiedExtension l).subtype (Xi ((toSum _).symm r)),
    GlobalTheory.KerStd.bHyps_of_beStd l d _ h5 h2 hd ⟨τ, F, _, o, o', ζ, ⟨hU, hF, hF1, hF2, hOw, hTr, hζ⟩, rfl⟩,
    ?_, ?_, fun s => ?_, fun r => ⟨(integralW_map_iff _).2 (hXi _).2, ?_⟩, fun s => ?_, fun s => ?_⟩
  · unfold GlobalTheory.KerStd.beOf
    rw [constantCoeff_map, hc, map_zero]
  · have h := (simeqW_map_iff _ _).2 ((Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) (Bool × Fin (d / 2))).2.2.2.2 _ _ _ R hR0
      (fun y => by rw [hR]; exact KernelCokernelKilling.integral_X' _) hS)
    rw [subst_comp_subst_apply hzs hRs, map_subst hRz] at h
    simp only [hz] at h
    convert h using 1
    · rfl
    unfold beXY
    rw [subst_sum hRs, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [subst2_comp hRs (constantCoeff_X _) (constantCoeff_X _), subst_X hRs, subst_X hRs, subst_inPar hl b (hR0 _) (hR0 _),
      map_pair b (cc_ps (hR0 _) (cc_lgF hl)) (cc_ps (hR0 _) (cc_lgF hl)), ← map_lg, ← map_lg, hR]
    rfl
  · rw [constantCoeff_map, hRT0, map_zero]
  · rw [constantCoeff_map, (hXi _).1, map_zero]
  · rw [← letLog_eq, ← GlobalTheory.KerStd.CofactorConverse.map_letLog l (MaximalUnramifiedExtension l).subtype, ← map_subst hRT,
      ← subst_comp_subst_apply hTs hRs, hlog, hz]
  · rw [← map_subst hXs, subst_comp_subst_apply hRs hXs]
    have e : (fun y => subst (fun r => Xi ((toSum (Fin (d / 2))).symm r)) (R y)) = Xi := by
      funext y
      rw [hR]
      show subst _ (X _) = _
      rw [subst_X hXs, Equiv.symm_apply_apply]
    rw [e, hinv, map_X]

end GlobalTheory.OnePlace.Unr

end
