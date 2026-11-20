import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairingStatement

open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr`. Take `⟨g₀, hg₀i, hg₀u, hg₀z⟩` from `GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr`. Establish `hstep` using `GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh`. Take `⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩` from `hU`. Use `set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef`.

Establish `hJi : ∀ i j, J i j ∈ intL L`. Take `⟨k0, hk0⟩` from `hJ`. Introduce `i j`. Rewrite using `[hJdef, ← hk0]`. Conclude with `((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2`.

Set `P : ℕ → Matrix (Fin n') (Fin n') L → Prop` to `fun k g => (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)`. Establish `hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L, P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j)`. Introduce `k g`. Distinguish the cases in `hP : P k g`. Take `⟨g', h1, h2, h3⟩` from `hstep k g hP.1 hP.2`.

Conclude with `⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩`. Conclude with `⟨g, fun h => absurd h hP⟩`. Use `choose F hF using hex`. Set `f : ℕ → Matrix (Fin n') (Fin n') L` to `fun k => Nat.rec g₀ (fun k g => F k g) k`. Establish `hf0 : f 0 = g₀` using `rfl`.

Establish `hfs : ∀ k, f (k + 1) = F k (f k)` using `fun k => rfl`. Establish `hfP : ∀ k, P k (f k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨hg₀i, hg₀u⟩`.

Consider the case `succ k ih => rw [hfs]`. Conclude with `(hF k (f k) ih).1`. Establish `hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j)`. Introduce `k i j`. Rewrite using `[hfs]`.

Conclude with `(hF k (f k) (hfP k)).2 i j`. Establish `hlim` using `fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)`. Use `choose b hb using hlim`. Set `h : Matrix (Fin n') (Fin n') L` to `Matrix.of b`. Establish `hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j)` using `fun k i j => hb i j k`.

Establish `hϖi : ϖ ∈ intL L` using `by show Valued.v ϖ ≤ 1`. Rewrite using `[hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)`. Establish `hhi : ∀ i j, h i j ∈ intL L`. Introduce `i j`. Establish `e : h i j = (h - f 0) i j + f 0 i j` using `by simp`.

Rewrite using `[e]`. Conclude with `add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)`. Establish `hunit : cT σ h * J * h = J`. Use extensionality with `i j`. Establish `hz0 : (cT σ h * J * h - J) i j = 0`.

Use `eq_zero_of_forall_dvdPow hϖv fun k => ?_` and prove the remaining obligations. Establish `e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) + (cT σ (f k) * J * f k - J)`. Rewrite using `[cT_sub]`. Simplify using `only [sub_mul, mul_sub, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, Matrix.add_apply, Matrix.add_apply]`. Use `dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)` and prove the remaining obligations. Conclude with `mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j`.

Rewrite `hz0` using `[Matrix.sub_apply]`. Conclude with `sub_eq_zero.1 hz0`. Use `set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef`. Establish `hJiJ : Ji * J = 1` using `by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hleft : (Ji * cT σ h * J) * h = 1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]`. Establish `hright : h * (Ji * cT σ h * J) = 1` using `mul_eq_one_comm.1 hleft`. Set `hG : GL (Fin n') L` to `⟨h, Ji * cT σ h * J, hright, hleft⟩`. Establish `hmem : hG ∈ UJ σ J` using `hunit`. Use `⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩` and prove the remaining obligations.

Use `show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)`. Establish `e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r)`. Simplify using `[Matrix.sub_mulVec]`. Rewrite using `[e]`. Use `dvdPow_add ?_ (hg₀z i r)` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `dvdPow_sum _ _ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `dvdPow_mul_int (hhk 0 r s) (hz i s)`.
-/
theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
