import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWG
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

/- English proof (translation)
Introduce `_ hG hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω`. Establish `hHaar : μ.IsAddHaarMeasure`. Take `⟨_, h, -⟩` from `hμ`. Conclude with `h`. Take `⟨S1, hS1⟩` from `LFixW.fixN V hψ`.

Take `⟨S2, hS2⟩` from `LFixW.fixWc V hψ`. Take `⟨S3, hS3⟩` from `LFixW.unit_triv D χ hχ`. Take `⟨S4, hS4⟩` from `hG D n`. Use `⟨S1 ∪ S2 ∪ S3 ∪ S4, fun S hS e he Φ hΦ u hu => ?_⟩` and prove the remaining obligations. Establish `h1 : S1 ⊆ S` using `fun x hx => hS (by simp [hx])`.

Establish `h2 : S2 ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `h3 : S3 ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `h4 : S4 ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hcont` using `(hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω Φ).1`. Establish `hA : IsClosed {g : G D n | ω g Φ = Φ}`.

Establish `hEq : {g : G D n | ω g Φ = Φ} = ⋂ x, {g : G D n | (ω g Φ).1 x = Φ.1 x}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`.

Rewrite using `[h]`. Introduce `h`. Conclude with `Subtype.ext (funext h)`. Rewrite using `[hEq]`. Conclude with `isClosed_iInter fun x => isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const`.

Establish `h1A : (1 : G D n) ∈ {g : G D n | ω g Φ = Φ}` using `by show ω 1 Φ = Φ`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Establish `key` using `hS4 S h4 {g : G D n | ω g Φ = Φ} hA h1A (by`. Introduce `g hg hcases x hx`.

Establish `hx' : ω x Φ = Φ` using `hx`. Use `show ω (g * x) Φ = Φ`. Rewrite using `[map_mul]`. Use `show ω g (ω x Φ) = Φ`. Rewrite using `[hx']`.

Break down `hcases with hN | hM | ⟨w, u', hw, hu', hu'K, rfl⟩` into its components or cases. Conclude with `hS1 S h1 n θ μ ω χ hω g hg hN Φ (fun y hy => by rw [hΦ y, if_neg hy])`. Conclude with `LFixW.fixM V hω he (hS3 S h3) hg hM Φ hΦ`. Conclude with `hS2 S h2 e he n θ μ ω χ hω hHaar w u' hw hu' hu'K Φ hΦ)`. Conclude with `key hu`.
-/
theorem fixW : IdemEx → GenK → WMaj → FixW := by
  classical
  intro _ hG hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω
  have hHaar : μ.IsAddHaarMeasure := by
    obtain ⟨_, h, -⟩ := hμ
    exact h
  obtain ⟨S1, hS1⟩ := LFixW.fixN V hψ
  obtain ⟨S2, hS2⟩ := LFixW.fixWc V hψ
  obtain ⟨S3, hS3⟩ := LFixW.unit_triv D χ hχ
  obtain ⟨S4, hS4⟩ := hG D n
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4, fun S hS e he Φ hΦ u hu => ?_⟩
  have h1 : S1 ⊆ S := fun x hx => hS (by simp [hx])
  have h2 : S2 ⊆ S := fun x hx => hS (by simp [hx])
  have h3 : S3 ⊆ S := fun x hx => hS (by simp [hx])
  have h4 : S4 ⊆ S := fun x hx => hS (by simp [hx])
  have hcont := (hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω Φ).1
  have hA : IsClosed {g : G D n | ω g Φ = Φ} := by
    have hEq : {g : G D n | ω g Φ = Φ} = ⋂ x, {g : G D n | (ω g Φ).1 x = Φ.1 x} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h x
        rw [h]
      · intro h
        exact Subtype.ext (funext h)
    rw [hEq]
    exact isClosed_iInter fun x =>
      isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have h1A : (1 : G D n) ∈ {g : G D n | ω g Φ = Φ} := by
    show ω 1 Φ = Φ
    rw [map_one]
    rfl
  have key := hS4 S h4 {g : G D n | ω g Φ = Φ} hA h1A (by
    intro g hg hcases x hx
    have hx' : ω x Φ = Φ := hx
    show ω (g * x) Φ = Φ
    rw [map_mul]
    show ω g (ω x Φ) = Φ
    rw [hx']
    rcases hcases with hN | hM | ⟨w, u', hw, hu', hu'K, rfl⟩
    · exact hS1 S h1 n θ μ ω χ hω g hg hN Φ (fun y hy => by rw [hΦ y, if_neg hy])
    · exact LFixW.fixM V hω he (hS3 S h3) hg hM Φ hΦ
    · exact hS2 S h2 e he n θ μ ω χ hω hHaar w u' hw hu' hu'K Φ hΦ)
  exact key hu

end PositivityTheory.Rg.Rsw.L

end
