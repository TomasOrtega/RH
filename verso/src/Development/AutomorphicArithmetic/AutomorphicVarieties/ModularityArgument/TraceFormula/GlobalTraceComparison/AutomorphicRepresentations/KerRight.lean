import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open NumberField PositivityTheory.Rg.BcB.E MeasureTheory

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1`.
-/
private theorem ker_left (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ (γ * x) y = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1

/- English proof (translation)
The claim follows from `((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2`.
-/
private theorem ker_right (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ x (γ * y) = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2

/- English proof (translation)
The claim follows from `Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)`.
-/
private theorem th_mul' (x y : H E n 0) :
    PositivityTheory.Rg.BcB.E1.th (x * y) = PositivityTheory.Rg.BcB.E1.th x * PositivityTheory.Rg.BcB.E1.th y :=
  Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)

/- English proof (translation)
Take `⟨γ, rfl⟩` from `hδ`. Use `⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩` and prove the remaining obligations. Conclude with `Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm`.
-/
private theorem th_rat {δ : H E n 0} (hδ : δ ∈ ratH E n 0) : PositivityTheory.Rg.BcB.E1.th δ ∈ ratH E n 0 := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩
  exact Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm
    ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `E _ _ _ n ι _ s`. Use `⟨fun γ x => ?_, fun γ x => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `ext_inner_right ℂ fun u => ?_` and prove the remaining obligations. Rewrite using `[s.vecs.rep₁, s.vecs.rep₁]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [ker_left s.D (s.t₁ i j) γ.2]`. Use function extensionality and compare the values at `i`. Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Rewrite using `[s.vecs.rep₂, s.vecs.rep₂]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.kInv_pf :
    KInv := by
  intro E _ _ _ n ι _ s
  refine ⟨fun γ x => ?_, fun γ x => ?_⟩
  · funext i
    refine ext_inner_right ℂ fun u => ?_
    rw [s.vecs.rep₁, s.vecs.rep₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ker_left s.D (s.t₁ i j) γ.2]
  · funext i
    refine ext_inner_left ℂ fun u => ?_
    rw [s.vecs.rep₂, s.vecs.rep₂]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]
