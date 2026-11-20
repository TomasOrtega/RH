import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatake
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.IsoComp
open GlobalTheory.CompRed
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
/- English proof (translation)
Introduce `hL D P i x f' hf' hf0 sp c hc`. Establish `hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV => (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite`. Introduce `ϖ hϖ k`. Take `⟨N, hN, hNJ⟩` from `(P.M.loc i).J_open`. Conclude with `GlobalTheory.T.finite_image_heckeSet_split_place_cosets D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ`.

Unfold `eigC at hf'`. Rewrite `hf'` using `[Submodule.mem_iSup_iff_exists_finsupp]`. Take `⟨g, hgmem, hgsum⟩` from `hf'`. Establish `hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q`. Introduce `Q hQ`.

Distinguish the cases in `h : D.naut.ptV i Q = some x`. Use `⟨h, ?_⟩` and prove the remaining obligations. Use `hgmem Q` as an intermediate fact. Rewrite `this` using `[iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)]`. Then use the resulting hypothesis. It suffices to derive a contradiction.

Use `hgmem Q` as an intermediate fact. Rewrite `this` using `[iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot]`. Conclude with `hQ this`. Choose the witnesses or unpack the hypotheses as in `⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]`. Use `set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef`. Establish `hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q`.

Rewrite using `[← hgsum, Finsupp.sum, map_sum]`. Establish `hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q)`. Introduce `Q hQ`. Establish `hy` using `(hg' Q (Finsupp.mem_support_iff.1 hQ)).2`. Rewrite `hy` using `[P.H.av.typeV]`.

Conclude with `hy`. Establish `hind` using `isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)`. Establish `hQ0s : Q0 ∈ g.support` using `Finsupp.mem_support_iff.2 hQ0`. Use `⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (P.M.loc i).real_range]`.

Conclude with `⟨g Q0, rfl⟩`. Introduce `h`. Conclude with `hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))`. Introduce `ϖ hϖ k hk set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef`. Establish `htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q)` using `fun Q hQ => Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ)) (Submodule.smul_mem _ _ (hGiso Q hQ))`.

Establish `htsum : ∑ Q ∈ g.support, t Q = 0`. Simplify using `only [t]`. Rewrite using `[Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk, sub_self]`. Establish `hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q`. Rewrite using `[eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]`.

Establish `hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)`. Rewrite using `[hrest]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)` and prove the remaining obligations. Take `⟨hne, hQs⟩` from `Finset.mem_erase.1 hQ`. Conclude with `(le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne) (htmem Q hQs)`.

Establish `h0 : t Q0 = 0` using `Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  intro hL D P i x f' hf' hf0 sp c hc
  classical
  have hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV =>
      (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite := by
    intro ϖ hϖ k
    obtain ⟨N, hN, hNJ⟩ := (P.M.loc i).J_open
    exact GlobalTheory.T.finite_image_heckeSet_split_place_cosets D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ
  unfold eigC at hf'
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hf'
  obtain ⟨g, hgmem, hgsum⟩ := hf'
  have hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q := by
    intro Q hQ
    by_cases h : D.naut.ptV i Q = some x
    · refine ⟨h, ?_⟩
      have := hgmem Q
      rwa [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)] at this
    · exfalso
      have := hgmem Q
      rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot] at this
      exact hQ this
  obtain ⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]
  set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef
  have hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q := by
    rw [← hgsum, Finsupp.sum, map_sum]
  have hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro Q hQ
    have hy := (hg' Q (Finsupp.mem_support_iff.1 hQ)).2
    rw [P.H.av.typeV] at hy
    exact hy
  have hind := isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)
  have hQ0s : Q0 ∈ g.support := Finsupp.mem_support_iff.2 hQ0
  refine ⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩
  · rw [← (P.M.loc i).real_range]
    exact ⟨g Q0, rfl⟩
  · intro h
    exact hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
  · intro ϖ hϖ k hk
    set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k
    set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
      fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef
    have htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun Q hQ =>
      Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ))
        (Submodule.smul_mem _ _ (hGiso Q hQ))
    have htsum : ∑ Q ∈ g.support, t Q = 0 := by
      simp only [t]
      rw [Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk,
        sub_self]
    have hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]
    have hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j) := by
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)
      obtain ⟨hne, hQs⟩ := Finset.mem_erase.1 hQ
      exact (le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne)
        (htmem Q hQs)
    have h0 : t Q0 = 0 := Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2
    exact sub_eq_zero.1 h0
end GlobalTheory.IsoComp
end
end
