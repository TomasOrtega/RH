import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacAnn

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Introduce `F _ _ _ δ O N hN m`. Take `⟨hmono, hx, -⟩` from `UpperTheory.ConvolutionTheory.R2.Fo.fkBasic F O`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `w i φ hφ`.

Establish `hφ' : φ ∈ N` using `hφ`. Rewrite using `[UpperTheory.ConvolutionTheory.R2.Fo.vacAnn F δ O φ (hN hφ') w i]`. Conclude with `Submodule.smul_mem _ _ (hx N 0 w i φ hφ)`. Consider the case `succ m ih`. Introduce `w i`.

Establish `hle : O.Fk N (m + 1) ≤ (O.Fk N (m + 1 + 1)).comap (O.d w i)`. Express the relevant statement in the definitionally equal form `O.Fk N m ⊔ ⨆ w', ⨆ j, (O.Fk N m).map (O.x w' j) ≤ _`. Use `sup_le ?_ (iSup_le fun w' => iSup_le fun j => ?_)` and prove the remaining obligations. Introduce `ψ hψ`. Conclude with `hmono N N le_rfl (m + 1) (m + 1 + 1) (Nat.le_succ _) (ih w i ψ hψ)`.

Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `ψ hψ`. Express the relevant statement in the definitionally equal form `O.d w i (O.x w' j ψ) ∈ O.Fk N (m + 1 + 1)`. Establish `hc` using `congrArg (fun T : Module.End ℂ (S4 F) => T ψ) (UpperTheory.ConvolutionTheory.R2.Fo.weyl F O w w' i j).2`. Establish `hc' : O.d w i (O.x w' j ψ) = O.x w' j (O.d w i ψ) + (if w = w' ∧ i = j then (1 : Module.End ℂ (S4 F)) else 0) ψ` using `hc`.

Rewrite using `[hc']`. Use `Submodule.add_mem _ (hx N (m + 1) w' j _ (ih w i ψ hψ)) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hmono N N le_rfl m (m + 1 + 1) (by omega) hψ`. Conclude with `Submodule.zero_mem _`.

Conclude with `fun φ hφ => hle hφ`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.fkD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (N : Submodule ℂ (S4 F)), N ≤ Vac δ → ∀ m w i, ∀ φ ∈ O.Fk N m, O.d w i φ ∈ O.Fk N (m + 1) := by
  intro F _ _ _ δ O N hN m
  obtain ⟨hmono, hx, -⟩ := UpperTheory.ConvolutionTheory.R2.Fo.fkBasic F O
  induction m with
  | zero =>
    intro w i φ hφ
    have hφ' : φ ∈ N := hφ
    rw [UpperTheory.ConvolutionTheory.R2.Fo.vacAnn F δ O φ (hN hφ') w i]
    exact Submodule.smul_mem _ _ (hx N 0 w i φ hφ)
  | succ m ih =>
    intro w i
    have hle : O.Fk N (m + 1) ≤ (O.Fk N (m + 1 + 1)).comap (O.d w i) := by
      change O.Fk N m ⊔ ⨆ w', ⨆ j, (O.Fk N m).map (O.x w' j) ≤ _
      refine sup_le ?_ (iSup_le fun w' => iSup_le fun j => ?_)
      · intro ψ hψ
        exact hmono N N le_rfl (m + 1) (m + 1 + 1) (Nat.le_succ _) (ih w i ψ hψ)
      · rw [Submodule.map_le_iff_le_comap]
        intro ψ hψ
        change O.d w i (O.x w' j ψ) ∈ O.Fk N (m + 1 + 1)
        have hc := congrArg (fun T : Module.End ℂ (S4 F) => T ψ) (UpperTheory.ConvolutionTheory.R2.Fo.weyl F O w w' i j).2
        have hc' : O.d w i (O.x w' j ψ) = O.x w' j (O.d w i ψ) + (if w = w' ∧ i = j then (1 : Module.End ℂ (S4 F)) else 0) ψ := hc
        rw [hc']
        refine Submodule.add_mem _ (hx N (m + 1) w' j _ (ih w i ψ hψ)) ?_
        split_ifs
        · exact hmono N N le_rfl m (m + 1 + 1) (by omega) hψ
        · exact Submodule.zero_mem _
    exact fun φ hφ => hle hφ
