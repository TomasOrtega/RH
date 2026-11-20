import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct Matrix

namespace GlobalTheory.RowLev

open Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin IsDedekindDomain

/- English proof (translation)
Introduce `I N p w fr x hx M hM`. Establish `hp : p.Prime` using `fr.prime`. Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Establish `hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p` using `(Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)`. Establish `h1 : ∀ u ∈ lamAf (F` using `I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by`.

Use `fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu` and prove the remaining obligations. Rewrite using `[DictLat.iv_smulE]`. Conclude with `Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)`. Establish `h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F` using `I.F) (wLat0 I w) := by`. Introduce `u hu`.

Use `Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')` and prove the remaining obligations. Use `Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha` and prove the remaining obligations. Introduce and unpack `z ⟨b, hb, e⟩ show (z : I.E ⊗[I.F] Af I.F) • v ∈ _`. Rewrite using `[e]`. Conclude with `smul_mem I w hb hv`.

Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Rewrite using `[add_smul]`. Conclude with `add_mem ha hb`. Introduce `s a _ ha`.

Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ s ha`. Establish `hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F` using `I.F) (wLat0 I w) := fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩`. Use `choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)`. Use `choose b hbL hb using fun i => dense I w hp hcard (y i).2`.

Set `B : Fin N → I.Lf` to `fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩`. Establish `hB : ∀ i, fr.c (B i) = Pi.single i 1`. Introduce `i`. Establish `e : fr.c (y i - B i) = 0` using `(hz _).2 (hb i)`. Rewrite `e` using `[map_sub, sub_eq_zero]`.

Rewrite using `[← e, hy]`. Establish `hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u`. Introduce `n u`. Rewrite using `[map_smulₛₗ, map_intCast]`. Establish `hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u`.

Introduce `n u`. Rewrite using `[map_smulₛₗ, map_natCast]`. Use `⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Set `Z : I.Lf` to `⟨iv I z, DictLat.iv_mem I hz'⟩`. Set `c : Fin N → ℤ` to `fun j => ((fr.c Z j).val : ℤ)`.

Use `⟨c, inter I w ?_⟩` and prove the remaining obligations. Rewrite using `[iv_lin]`. Establish `e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Simplify using `only [hci, hB]`.

Use function extensionality and compare the values at `k`. Simplify using `[c, Finset.sum_apply, Pi.single_apply]`. Establish `e1` using `(hz _).1 e0`. Use `e1 using 1` and compare the differences between its conclusion and the goal. Simplify using `[Z, B, Submodule.coe_sum]`.

Both sides reduce to the same expression. Set `V : I.Lf` to `⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩`. Establish `hV : fr.c V = M *ᵥ Pi.single i 1` using `by rw [← hB i]; exact hM (B i) V.2`. Establish `e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero, hV]`.

Simplify using `only [hcn, hB, ZMod.natCast_zmod_val]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]`. Establish `e1` using `(hz _).1 e0`. Use `e1 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Submodule.coe_sub, Submodule.coe_sum]`. Use `congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Use `show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)`. Rewrite using `[SubringClass.coe_natCast]`. Both sides reduce to the same expression.
-/
theorem redMat0_of_actsAs : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  intro I N p w fr x hx M hM
  have hp : p.Prime := fr.prime
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p :=
    (Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)
  have h1 : ∀ u ∈ lamAf (F := I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by
    refine fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu
    rw [DictLat.iv_smulE]
    exact Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)
  have h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')
    refine Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha
    · rintro z ⟨b, hb, e⟩
      show (z : I.E ⊗[I.F] Af I.F) • v ∈ _
      rw [e]
      exact smul_mem I w hb hv
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]; exact add_mem ha hb
    · intro s a _ ha
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s ha
  have hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F := I.F) (wLat0 I w) :=
    fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩
  choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)
  choose b hbL hb using fun i => dense I w hp hcard (y i).2
  let B : Fin N → I.Lf := fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩
  have hB : ∀ i, fr.c (B i) = Pi.single i 1 := by
    intro i
    have e : fr.c (y i - B i) = 0 := (hz _).2 (hb i)
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  have hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_intCast]
  have hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_natCast]
  refine ⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩
  · let Z : I.Lf := ⟨iv I z, DictLat.iv_mem I hz'⟩
    let c : Fin N → ℤ := fun j => ((fr.c Z j).val : ℤ)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero]
      simp only [hci, hB]
      funext k
      simp [c, Finset.sum_apply, Pi.single_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    simp [Z, B, Submodule.coe_sum]
    rfl
  · let V : I.Lf := ⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩
    have hV : fr.c V = M *ᵥ Pi.single i 1 := by rw [← hB i]; exact hM (B i) V.2
    have e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero, hV]
      simp only [hcn, hB, ZMod.natCast_zmod_val]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)
    rw [SubringClass.coe_natCast]
    rfl

end GlobalTheory.RowLev
