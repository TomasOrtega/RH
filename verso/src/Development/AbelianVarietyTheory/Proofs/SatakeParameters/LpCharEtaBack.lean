import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsoLocAppendSingleton
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne

noncomputable section

namespace GlobalTheory.GoodDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

/- English proof (translation)
Introduce `w a b χ s hχ`. Take `⟨h1, h2, -⟩` from `hT w a b χ χ s hχ hχ`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Establish `h` using `(hT w (D.naut.lpZero w) (D.naut.lpZero w) χ χ 0 hχ hχ).1`. Rewrite `h` using `[D.naut.lpSum_zero]`.

Use `hc w _ _ (D.naut.lpChar (D.naut.lpZero w) χ) ?_` and prove the remaining obligations. Rewrite using `[← h, D.naut.lpSum_comm, D.naut.lpSum_zero]`.
-/
theorem charSum_of_tie (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut)
    (hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b) :
    GlobalTheory.LiftLeaf.CharSum D.nd D.naut := by
  intro w a b χ s hχ
  obtain ⟨h1, h2, -⟩ := hT w a b χ χ s hχ hχ
  refine ⟨h1, h2, ?_⟩
  have h := (hT w (D.naut.lpZero w) (D.naut.lpZero w) χ χ 0 hχ hχ).1
  rw [D.naut.lpSum_zero] at h
  refine hc w _ _ (D.naut.lpChar (D.naut.lpZero w) χ) ?_
  rw [← h, D.naut.lpSum_comm, D.naut.lpSum_zero]

/- English proof (translation)
Establish `hu` using `D.naut.etaT_unr w`. Take `⟨hu', he⟩` from `D.naut.etaTinv_def w`. Establish `hcard` using `D.naut.frobEig_card _ hu`. Rewrite `hcard` using `[D.naut.locG_dim]`. Take `⟨c, hc⟩` from `Multiset.card_eq_one.1 hcard`.

Establish `hc0 : c ≠ 0`. Introduce `h0`. Apply `D.naut.frobEig_ne_zero _ hu` to reduce the goal to its premises. Rewrite using `[hc, h0]`. Conclude with `Multiset.mem_singleton_self _`.

Rewrite `he` using `[hc, Multiset.map_singleton]`. Establish `key` using `GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c hu' hu (D.naut.locG_dim _ w) he hc (inv_mul_cancel₀ hc0)`. Take `⟨-, -, -, h4, h5, -⟩` from `hT w a a (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)`. Rewrite using `[h4, key, h5]`.
-/
theorem lpChar_eta_back (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) (w : PlE D.host) (a : D.naut.LP w) :
    D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a := by
  have hu := D.naut.etaT_unr w
  obtain ⟨hu', he⟩ := D.naut.etaTinv_def w
  have hcard := D.naut.frobEig_card _ hu
  rw [D.naut.locG_dim] at hcard
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hc0 : c ≠ 0 := by
    intro h0
    apply D.naut.frobEig_ne_zero _ hu
    rw [hc, h0]
    exact Multiset.mem_singleton_self _
  rw [hc, Multiset.map_singleton] at he
  have key := GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c hu' hu (D.naut.locG_dim _ w) he hc
    (inv_mul_cancel₀ hc0)
  obtain ⟨-, -, -, h4, h5, -⟩ := hT w a a (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0
    (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)
  rw [h4, key, h5]

/- English proof (translation)
Introduce `D hT hA h41 _ a x hx Sig hSig k v`. Take `⟨-, Sig', hSig', hgood⟩` from `hx`. Establish `hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b` using `hA.2.2`. Establish `hL` using `charSum_of_tie D hT.1 hc`. Take `⟨P, hP, hB⟩` from `hSig`.

Take `⟨P', hP', hB'⟩` from `id hSig'`. Establish `hperm` using `((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'`. Establish `e1` using `GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)`. Rewrite `e1` using `[GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL]`. Establish `e2` using `congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1`.

Simplify using `only [lpChar_eta_back D hT.1] at e2`. Rewrite `e2` using `[GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton]`. Rewrite using `[hc _ _ _ _ e2]`. Conclude with `GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v`.
-/
theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.Conclusion41 D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v

end GlobalTheory.GoodDepthZero
