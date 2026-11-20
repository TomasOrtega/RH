import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormSubLtOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InerQl

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one`. Consider the case `exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one`. Consider the case `(apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)`.
-/
theorem root_eq_of_near {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m)
    {ζ η : Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  first
  | exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)

/- English proof (translation)
Set `Fx : Subgroup ↥(GK K)` to `{ carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c} one_mem' := fun c _ => rfl mul_mem' := fun {a b} ha hb c hc => by show (a : GQ l) ((b : GQ l) c) = c`. Rewrite using `[hb c hc, ha c hc]`. Use the proof step `inv_mem' := fun {a} ha c hc => by show ((a : GQ l)⁻¹) c = c`. Rewrite using `[AlgEquiv.aut_inv]`. Use `conv_lhs => rw [← ha c hc]`.

Conclude with `AlgEquiv.symm_apply_apply _ _ }`. Establish `hle : IK K ≤ Fx`. Unfold `IK`. Rewrite using `[Subgroup.closure_le]`. Introduce `σ hσ c hc`.

Unfold `MaximalUnramifiedExtension at hc`. Proceed by induction on `hc using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, hlm, hxm⟩` from `hx`. Establish `hxn : ‖x‖ ≤ 1`.

Establish `: ‖x‖ ^ m = 1` using `by rw [← norm_pow, hxm, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le`. Conclude with `root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)`. Consider the case `algebraMap x => exact (σ : GQ l).commutes x`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`.

Consider the case `inv x _ hx => rw [map_inv₀, hx]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`. Conclude with `hle hg c hc`.
-/
theorem IK_fixes_Kur {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) {g : ↥(GK K)} (hg : g ∈ IK K)
    {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : (g : GQ l) c = c := by
  let Fx : Subgroup ↥(GK K) :=
    { carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun {a b} ha hb c hc => by
        show (a : GQ l) ((b : GQ l) c) = c
        rw [hb c hc, ha c hc]
      inv_mem' := fun {a} ha c hc => by
        show ((a : GQ l)⁻¹) c = c
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← ha c hc]
        exact AlgEquiv.symm_apply_apply _ _ }
  have hle : IK K ≤ Fx := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ c hc
    unfold MaximalUnramifiedExtension at hc
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, hlm, hxm⟩ := hx
      have hxn : ‖x‖ ≤ 1 := by
        have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le
      exact root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)
    | algebraMap x => exact (σ : GQ l).commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  exact hle hg c hc

/- English proof (translation)
Introduce `l _ Pl K' h hN hF hS g hg c`. Use `show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c`. Rewrite using `[Pl.PD_actB]`. Establish `hc : (c : Om l) ∈ MaximalUnramifiedExtension l` using `(IntermediateField.mem_inf.1 c.2).2`. Conclude with `Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)`.
-/
theorem IK_mem_Iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl K' h hN hF hS g hg c
  show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c
  rw [Pl.PD_actB]
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  exact Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)

end GlobalTheory.InerQl
