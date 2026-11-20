import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hlt : Fintype.card (UIdx r) = (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card` using `Fintype.card_subtype _`. Establish `hgt : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card = (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)).card`. Use `Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `using hp`.

Introduce `p _ q _ h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext h.2 h.1`. Introduce `q hq`. Conclude with `⟨(q.2, q.1), by simpa using hq, rfl⟩`.

Establish `heq : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)).card = r + 1`. Establish `: Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) = Finset.univ.map ⟨fun a : Fin (r + 1) => (a, a), fun a b h => by simpa using h⟩`. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨p.1, Prod.ext rfl h⟩`. Introduce and unpack `⟨a, rfl⟩`. Both sides reduce to the same expression. Rewrite using `[this, Finset.card_map, Finset.card_univ, Fintype.card_fin]`.

Establish `h1` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))) (fun p => p.1 < p.2)`. Establish `h2` using `Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2)) (fun p => p.2 < p.1)`. Rewrite `h2` using `[Finset.filter_filter, Finset.filter_filter]`. Establish `e1 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ p.2 < p.1) = Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)` using `Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩)`. Establish `e2 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) = Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)` using `Finset.filter_congr (fun p _ => ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1), fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩)`.

Rewrite `h2` using `[e1, e2, heq]`. Rewrite `h1` using `[Finset.card_univ, Fintype.card_prod, Fintype.card_fin]`. Establish `hsq : (r + 1) * (r + 1) = r * (r + 1) + (r + 1)` using `by ring`. Use linear arithmetic over natural numbers and integers.
-/
theorem volU_two_card_uidx (r : ℕ) : 2 * Fintype.card (UIdx r) = r * (r + 1) := by
  classical
  have hlt : Fintype.card (UIdx r) =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card :=
    Fintype.card_subtype _
  have hgt : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      exact ⟨(q.2, q.1), by simpa using hq, rfl⟩
  have heq : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)).card = r + 1 := by
    have : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) =
        Finset.univ.map ⟨fun a : Fin (r + 1) => (a, a), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
      · rintro ⟨a, rfl⟩; rfl
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))) (fun p => p.1 < p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2)) (fun p => p.2 < p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1) :=
    Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩)
  have e2 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) :=
    Finset.filter_congr (fun p _ => ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1),
      fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩)
  rw [e1, e2, heq] at h2
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  have hsq : (r + 1) * (r + 1) = r * (r + 1) + (r + 1) := by ring
  omega

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
Unfold `gAt`. Use `split_ifs`. Conclude with `(D.host.g_prime 0).pos`. Conclude with `(D.host.g_prime 1).pos`.
-/
theorem volU_gAt_pos (v : PlX X) : 0 < gAt X v := by
  unfold gAt
  split_ifs
  · exact (D.host.g_prime 0).pos
  · exact (D.host.g_prime 1).pos

def VolUHyp : Prop :=
  IsCharAF X.B.I.F ψ ∧ IsStdChar ψ ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]

/- English proof (translation)
Rewrite using `[hU, hZ]`. Establish `hg : (gAt X v : ℝ) ≠ 0` using `by exact_mod_cast (volU_gAt_pos X v).ne'`. Rewrite using `[← zpow_sub₀ hg, ← zpow_natCast]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem volU_ratio (v : PlX X) (hZ : VolTZZAt X u u' ψ v) (hU : VolumeDeepCongruenceSubgroup X ψ v) :
    localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) := by
  rw [hU, hZ]
  have hg : (gAt X v : ℝ) ≠ 0 := by exact_mod_cast (volU_gAt_pos X v).ne'
  rw [← zpow_sub₀ hg, ← zpow_natCast]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `h1 h2 h3 v hv`. Take `⟨hZ, hU⟩` from `h ⟨h1, h2, h3⟩ v hv`. Conclude with `volU_ratio X u u' ψ v hZ hU`.
-/
theorem volTypV_of' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTZZAt X u u' ψ v ∧ VolumeDeepCongruenceSubgroup X ψ v) :
    VolTypV X u u' ψ := by
  intro h1 h2 h3 v hv
  obtain ⟨hZ, hU⟩ := h ⟨h1, h2, h3⟩ v hv
  exact volU_ratio X u u' ψ v hZ hU

/- English proof (translation)
Unfold `VolTZZAt ZZX volS`. Rewrite using `[if_pos hv]`. Establish `hset : ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v) = {z | (fun p => locZ (E` using `X.B.I.E) v z p.1 p.2) ∈ {w | (fun p => (w p - TFv X u v p.1 p.2) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹) ∈ VolTW X.B.I.cm.sig v (gAt X v) D.R.rS (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)}} := by`. Both sides reduce to the same expression. Rewrite using `[hset, hL, hA, hH _ hC]`.

Simplify using `only [Fintype.card_prod, Fintype.card_fin]`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast, zpow_neg, zpow_natCast, ← mul_inv, ← pow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volUZZAt_of (v : PlX X) (hv : TypAt X v)
    (hA : VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (hL : VolTLocPres (E := X.B.I.E) ψ v D.R.rS)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hC : VolTTFCong X u u' v) : VolTZZAt X u u' ψ v := by
  unfold VolTZZAt ZZX volS
  rw [if_pos hv]
  have hset : ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v) =
      {z | (fun p => locZ (E := X.B.I.E) v z p.1 p.2) ∈
        {w | (fun p => (w p - TFv X u v p.1 p.2) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹) ∈
          VolTW X.B.I.cm.sig v (gAt X v) D.R.rS
            (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)}} := by
    rfl
  rw [hset, hL, hA, hH _ hC]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, zpow_neg, zpow_natCast, ← mul_inv, ← pow_add]
  congr 2
  ring

/- English proof (translation)
Unfold `VolumeDeepCongruenceSubgroup localVolumeUnit volU`. Rewrite using `[if_pos hv, hE, hP, hO, one_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, volU_two_card_uidx, zpow_neg, zpow_natCast]`.
-/
theorem volume_deep_congruence_of_fubini (v : PlX X) (hv : TypAt X v)
    (hE : VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS)
    (hP : VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS)
    (hO : VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)) : VolumeDeepCongruenceSubgroup X ψ v := by
  unfold VolumeDeepCongruenceSubgroup localVolumeUnit volU
  rw [if_pos hv, hE, hP, hO, one_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    volU_two_card_uidx, zpow_neg, zpow_natCast]

def VolUSteps (v : PlX X) : Prop :=
  VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ∧
      VolTLocPres (E := X.B.I.E) ψ v D.R.rS ∧ VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS ∧
      VolTTFCong X u u' v ∧ VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS ∧
      VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS ∧ VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)

/- English proof (translation)
The claim follows from `volTypV_of' X u u' ψ fun hh v hv => ⟨volUZZAt_of X u u' ψ v hv (h hh v hv).1 (h hh v hv).2.1 (h hh v hv).2.2.1 (h hh v hv).2.2.2.1, volume_deep_congruence_of_fubini X ψ v hv (h hh v hv).2.2.2.2.1 (h hh v hv).2.2.2.2.2.1 (h hh v hv).2.2.2.2.2.2⟩`.
-/
theorem volTypV_of_steps' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolUSteps X u u' ψ v) :
    VolTypV X u u' ψ :=
  volTypV_of' X u u' ψ fun hh v hv =>
    ⟨volUZZAt_of X u u' ψ v hv (h hh v hv).1 (h hh v hv).2.1 (h hh v hv).2.2.1 (h hh v hv).2.2.2.1,
      volume_deep_congruence_of_fubini X ψ v hv (h hh v hv).2.2.2.2.1 (h hh v hv).2.2.2.2.2.1 (h hh v hv).2.2.2.2.2.2⟩

end OfX

end Formalism.L2.SG.Pf.NcVal
