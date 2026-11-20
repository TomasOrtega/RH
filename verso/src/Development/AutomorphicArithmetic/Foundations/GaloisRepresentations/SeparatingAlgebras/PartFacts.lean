import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `E _ _ _ a W C P`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Take `⟨I, F, h1, h2, rfl⟩` from `GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W C 1 f (fun c v g => by simpa using hf c.1 c.2 v g)`. Use `Submodule.sum_mem _ fun π hπ => ?_` and prove the remaining obligations.

Establish `hfix : F π ∈ fixedBy W C` using `fun k hk v g => by simpa using h2 π hπ ⟨k, hk⟩ v g`. Distinguish the cases in `hP : P π.V`. Conclude with `Submodule.mem_sup_left (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))`. Conclude with `Submodule.mem_sup_right (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))`. Conclude with `iSup₂_le fun π _ => inf_le_right`.

Introduce `K hK`. Use `iSup₂_mono fun π _ => inf_le_inf_left _ ?_` and prove the remaining obligations. Introduce `f hf k hk v g`. Conclude with `hf k (hK hk) v g`. Introduce `x hx f hf`.

Establish `hle : part W C P ≤ (part W C P).comap (algRep W x)`. Use `iSup₂_le fun π hP f hf => ?_` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `AutSub.mem_finPart.2 fun v => π.isAut.stable x.1 _ (AutSub.mem_finPart.1 hf.1 v)`. Introduce `c hc v g`.

Express the relevant statement in the definitionally equal form `f.1 v (g * c * x.1) = f.1 v (g * x.1)`. Establish `e : g * c * x.1 = g * x.1 * (x.1⁻¹ * c * x.1)` using `by group`. Rewrite using `[e]`. Conclude with `hf.2 _ (hx c hc) v _`. Conclude with `hle hf`.

Introduce `G hG`. Take `⟨F, hF, rfl⟩` from `(Submodule.mem_iSup_iff_exists_finsupp (fun π : AutSub E a => ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C) G).1 hG`. Use `⟨F.support, F, fun π hπ => ?_, rfl⟩` and prove the remaining obligations. Establish `h0 : F π ≠ 0` using `Finsupp.mem_support_iff.1 hπ`. Establish `hm : F π ∈ ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C` using `hF π`.

Distinguish the cases in `hP : P π.V`. Rewrite `hm` using `[iSup_pos hP]`. Conclude with `⟨hP, hm.1, hm.2, h0⟩`. Rewrite `hm` using `[iSup_neg hP]`. Conclude with `absurd ((Submodule.mem_bot _).1 hm) h0`.
-/
theorem UpperTheory.Gal.Gen.partFacts_pf :
    UpperTheory.Gal.Gen.PartFacts := by
  intro E _ _ _ a W C P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨I, F, h1, h2, rfl⟩ := GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W C 1 f (fun c v g => by simpa using hf c.1 c.2 v g)
    refine Submodule.sum_mem _ fun π hπ => ?_
    have hfix : F π ∈ fixedBy W C := fun k hk v g => by simpa using h2 π hπ ⟨k, hk⟩ v g
    by_cases hP : P π.V
    · exact Submodule.mem_sup_left
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
  · exact iSup₂_le fun π _ => inf_le_right
  · intro K hK
    refine iSup₂_mono fun π _ => inf_le_inf_left _ ?_
    intro f hf k hk v g
    exact hf k (hK hk) v g
  · intro x hx f hf
    have hle : part W C P ≤ (part W C P).comap (algRep W x) := by
      refine iSup₂_le fun π hP f hf => ?_
      refine Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨?_, ?_⟩)
      · exact AutSub.mem_finPart.2 fun v => π.isAut.stable x.1 _ (AutSub.mem_finPart.1 hf.1 v)
      · intro c hc v g
        change f.1 v (g * c * x.1) = f.1 v (g * x.1)
        have e : g * c * x.1 = g * x.1 * (x.1⁻¹ * c * x.1) := by group
        rw [e]
        exact hf.2 _ (hx c hc) v _
    exact hle hf
  · intro G hG
    obtain ⟨F, hF, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp
      (fun π : AutSub E a => ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C) G).1 hG
    refine ⟨F.support, F, fun π hπ => ?_, rfl⟩
    have h0 : F π ≠ 0 := Finsupp.mem_support_iff.1 hπ
    have hm : F π ∈ ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C := hF π
    by_cases hP : P π.V
    · rw [iSup_pos hP] at hm
      exact ⟨hP, hm.1, hm.2, h0⟩
    · rw [iSup_neg hP] at hm
      exact absurd ((Submodule.mem_bot _).1 hm) h0
