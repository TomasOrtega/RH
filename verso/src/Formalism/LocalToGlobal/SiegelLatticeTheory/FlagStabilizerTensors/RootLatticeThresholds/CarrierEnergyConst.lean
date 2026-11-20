import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def e1 (D : D7) : ℕ := (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) / 3

def rdExp (D : D7) : ℕ := 2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) + e1 D

def Anum (D : D7) : ℝ := D.host.rdE ^ rdExp D * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Kexp (P : Parts X u u') : ℝ := Anum D / P.Gam0

variable (X u u') in

def LemmaMS (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p =
    D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) *
      (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ

/- English proof (translation)
Establish `hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0`. Unfold `Formalism.MainNotions.S.Lat.gS`. Conclude with `Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)`. Establish `key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f)`. Rewrite using `[← pow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Simplify using `only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]`. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem anum_pow : Anum D ^ D.R.f =
    Formalism.L2.SG.MassDataConc.kapN D * (D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3)))) := by
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) =
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) *
        ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f) := by
    rw [← pow_add]
    congr 1
    ring
  rw [key]
  simp only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.rdE`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Establish `h` using `NumberField.discr_ne_zero (K := D.host.E)`. Conclude with `abs_pos.mpr (by exact_mod_cast h)`.
-/
theorem rdE_pos' : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (by exact_mod_cast h)

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev`. Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `l _`. Apply `div_nonneg` to reduce the goal to its premises. Apply `zpow_nonneg` to reduce the goal to its premises.

Unfold `Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd`. Check the signs of the components of the expression. Unfold `Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd`. Check the signs of the components of the expression.
-/
theorem energy_constant_nonneg (P : Parts X u u') : 0 ≤ P.Gam0 := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev
  apply Finset.prod_nonneg
  intro l _
  apply div_nonneg
  · apply zpow_nonneg
    unfold Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd
    positivity
  · unfold Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd
    positivity

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hZZ, hPP, -⟩` from `hC`. Establish `hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0`. Unfold `Formalism.MainNotions.S.Lat.gS`. Conclude with `Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)`. Establish `hrd : 0 < D.host.rdE` using `rdE_pos'`.

Establish `hA : 0 ≤ Anum D`. Unfold `Anum`. Conclude with `mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)`. Establish `hK0 : 0 ≤ Kexp P` using `div_nonneg hA (energy_constant_nonneg P)`. Use `⟨fun _ => hK0, ?_⟩` and prove the remaining obligations.

Establish `hfS : P.S.f = D.R.f`. Rewrite using `[← hf, ← Fintype.card_fin P.S.f]`. Conclude with `Fintype.card_congr P.τ`. Establish `hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f`. Rewrite using `[Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]`.

Establish `hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ` using `hZZ`. Establish `hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP` using `by show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v`. Conclude with `Finset.prod_pos (fun l _ => (hPP l).2)`. Establish `hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0`. Unfold `Formalism.L2.SG.MassDataConc.kapN`.

Conclude with `mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))`. Establish `hM : D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)`. Rewrite using `[hprod, anum_pow, hMS, hfS]`. Clear the denominators using the available nonvanishing facts.
-/
theorem constPin_of (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : LemmaMS X u u' ψ)
    (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f) :
    ConstPin P ψ (fun _ => Kexp P) := by
  obtain ⟨-, -, -, -, -, -, hZZ, hPP, -⟩ := hC
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hrd : 0 < D.host.rdE := rdE_pos'
  have hA : 0 ≤ Anum D := by
    unfold Anum
    exact mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hK0 : 0 ≤ Kexp P := div_nonneg hA (energy_constant_nonneg P)
  refine ⟨fun _ => hK0, ?_⟩
  have hfS : P.S.f = D.R.f := by
    rw [← hf, ← Fintype.card_fin P.S.f]
    exact Fintype.card_congr P.τ
  have hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f := by
    rw [Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]
  have hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ := hZZ
  have hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos (fun l _ => (hPP l).2)
  have hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
    unfold Formalism.L2.SG.MassDataConc.kapN
    exact mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))
  have hM : D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)
  rw [hprod, anum_pow, hMS, hfS]
  field_simp

end Formalism.L2.SG.Pf.Carrier.EnergyConst
