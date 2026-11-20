import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq

open Formalism.L2.PairingIndexBounds.Eq.Sq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Introduce `N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG`. Take `⟨A, A', hP⟩` from `hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4`. Distinguish the cases in `hG0 : G = 0`. Substitute `hG0` using the available equality. Use function extensionality and compare the values at `v`.

Simplify using `[TaylorLogMetric.Iop, TaylorLogMetric.U]`. Establish `hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L'), F ≠ 0` using `⟨G, fun x hx z => hG.2 x hx z, hG0⟩`. Establish `hT1` using `tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)`. Establish `hT2` using `tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)`. Take `⟨S₂, S₃, hS₂, hS₃, hμ⟩` from `mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF`.

Take `⟨T₂, T₃, hT₂, hT₃, hν⟩` from `mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF`. Use function extensionality and compare the values at `v`. Establish `e1` using `tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v`. Establish `e2` using `tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v`. Rewrite `e1` using `[hμ, one_mul]`.

Rewrite `e2` using `[hν, one_mul]`. Conclude with `e1.trans e2.symm`.
-/
theorem sqP_of {B : Cd.Base D cc δ} (hL : B.LatAll) (hS : SqSplit B) : SqP D B.tor := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG
  obtain ⟨A, A', hP⟩ := hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  by_cases hG0 : G = 0
  · subst hG0
    funext v
    simp [TaylorLogMetric.Iop, TaylorLogMetric.U]
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L'), F ≠ 0 := ⟨G, fun x hx z => hG.2 x hx z, hG0⟩
  have hT1 := tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)
  have hT2 := tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ :=
    mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF
  obtain ⟨T₂, T₃, hT₂, hT₃, hν⟩ :=
    mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF
  funext v
  have e1 := tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  have e2 := tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at e1
  rw [hν, one_mul] at e2
  exact e1.trans e2.symm

/- English proof (translation)
The claim follows from `J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR`.
-/
theorem eqP_of_split (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSp : SqSplit B) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq
