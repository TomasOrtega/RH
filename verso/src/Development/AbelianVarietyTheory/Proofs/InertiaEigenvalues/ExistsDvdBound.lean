import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Take `⟨r, hr⟩` from `bk.str.surjective (Ideal.Quotient.mk _ s)`. Rewrite using `[GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.RingIface.sigO_coe]`. Express the relevant statement in the definitionally equal form `Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])`.

Rewrite using `[GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]`.
-/
theorem θ_σA_ev (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]
  apply Subtype.ext
  rw [GlobalTheory.RingIface.sigO_coe]
  change Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]`.
-/
theorem dvd_σA_ev_sub (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev bk.E ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]

/- English proof (translation)
Establish `hu' : 0 < ‖(u : ℂ_[l])‖` using `norm_pos_iff.2 (fun h => hu (Subtype.ext h))`. Take `⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖` from `((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually (gt_mem_nhds hu')).exists`. Use `⟨a, fun x y n h han => ?_⟩` and prove the remaining obligations. Establish `hl0 : 0 < ‖(l : ℂ_[l])‖` using `norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero`. Establish `hy : ‖(y : ℂ_[l])‖ ≤ 1` using `(GlobalTheory.RingBasics.mem_OC _).1 y.2`.

Establish `h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖`. Use `congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h` as an intermediate fact. Simplify `this` using `[norm_mul, norm_pow]`. Establish `hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a`. Rewrite using `[← pow_add, Nat.sub_add_cancel han]`.

Establish `hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a)`. Establish `hpa : 0 < ‖(l : ℂ_[l])‖ ^ a` using `pow_pos hl0 a`. Establish `hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a)` using `pow_nonneg hl0.le _`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `: ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖` using `mul_lt_mul'' hc ha hpn hpa.le`. Establish `h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n` using `mul_le_of_le_one_right (pow_nonneg hl0.le n) hy`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm` using `(GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx`. Rewrite `hm` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`.

Take `⟨b, hb⟩` from `hm`. Conclude with `⟨b, by rw [← hb, mul_comm]⟩`.
-/
theorem exists_dvd_bound (u : OC l) (hu : u ≠ 0) : ∃ a : ℕ, ∀ (x y : OC l) (n : ℕ),
    x * u = (l : OC l) ^ n * y → a ≤ n → ∃ y' : OC l, x = (l : OC l) ^ (n - a) * y' := by
  have hu' : 0 < ‖(u : ℂ_[l])‖ := norm_pos_iff.2 (fun h => hu (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually
      (gt_mem_nhds hu')).exists
  refine ⟨a, fun x y n h han => ?_⟩
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hy : ‖(y : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 y.2
  have h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ := by
    have := congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h
    simpa [norm_mul, norm_pow] using this
  have hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel han]
  have hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := by
    have hpa : 0 < ‖(l : ℂ_[l])‖ ^ a := pow_pos hl0 a
    have hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := pow_nonneg hl0.le _
    by_contra hc
    push_neg at hc
    have : ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ :=
      mul_lt_mul'' hc ha hpn hpa.le
    have h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := mul_le_of_le_one_right (pow_nonneg hl0.le n) hy
    linarith
  have hm := (GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, by rw [← hb, mul_comm]⟩

end GlobalTheory.BKLim.BetaBd

end
