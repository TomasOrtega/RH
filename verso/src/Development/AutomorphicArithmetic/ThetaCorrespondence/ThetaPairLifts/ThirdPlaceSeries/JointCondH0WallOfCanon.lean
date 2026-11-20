import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0WallOfCanon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepcongr

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
/- English proof (translation)
Introduce `_ D L HW R X hX F hJ h41 hFont`. Take `⟨⟨ep, hJa⟩, hJb, hJc, -, hJe, hJf, -⟩` from `hJ`. Use `⟨hOf L, hOf L, ?_⟩` and prove the remaining obligations. Introduce `i _ _ hsplit u hu π hπ`. Establish `hnI : ¬ TwistedPlaces.InertK D (D.nd.l i)`.

Introduce `h2`. Unfold `TwistedPlaces.SplitK at hsplit`. Unfold `TwistedPlaces.InertK at h2`. Rewrite `h2` using `[hsplit]`. Apply the tactic sequence `rcases h2 with h2 | h2 <;> cases h2`.

Rewrite `hu` using `[hX.dc i hnI]`. Unfold `dcOf at hu`. Use `split_ifs at hu with hS`. Use `swap`. Simplify using `[KillingConditions.allRows] at hu`.

Take `⟨_, h5, hq, hd, hg, _⟩` from `hS.1`. Establish `hu' : u ∈ placesOver D.host.E (D.nd.l i)` using `((Exists.choose hS.2).cover u).1 (Or.inr hu)`. Establish `hl2 : D.nd.l i ≠ 2` using `by omega`. Establish `hsm : D.nd.l i ∉ D.host.small` using `fun h => by`. Establish `h' : primeClass D.host.toHostRaw (D.nd.l i) = PrimeClass.splitK` using `hsplit`.

Simplify using `[primeClass, h] at h'`. Establish `hKur` using `GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hsm hq hd u hu'`. Establish `hgood : Good (D.nbr i u hu').Kw 1 (D.nbr i u hu').LL` using `(D.self_good i u hu').good_one (D.nbr i u hu').LL_split hl2 (GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hKur)`. Establish `hZ : π ∈ D.nd.Z i` using `Formalism.MainNotions.LargeLevelLemmas.zgoodSubsetZ i hπ`. Establish `hfam` using `hX.fam`.

Establish `hdec` using `(GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hfam i π hZ).2.2.2`. Establish `hgr` using `hfam.good i`. Establish `hcont` using `hfam.cont i π`. Establish `hWc : Continuous (WpO D.nd i (X.ρ i) π)`. Establish `h1 : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)`.

Use `((D.nd.chi_cont i 1).comp continuous_inv).congr fun g => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[MonoidHom.inv_apply, ← map_inv]`. Conclude with `h1.smul hcont`. Establish `hLc` using `GlobalTheory.WordJumpsCompare.continuous_loc D i u hu' _ hWc`.

Establish `hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu') ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v` using `fun v => hLc.matrix_mulVec continuous_const`. Establish `hJW` using `fun τ => GlobalTheory.T.decomposition_local_above D L ep hJa hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgr hZ hdec u hu' (TruncatedSeriesCountingIdentities.CoefExt.self i u hu') τ (WpO D.nd i (X.ρ i) π) (Or.inl rfl)`. Establish `hrn : D.R.r ≤ D.R.nV` using `Nat.le_add_right _ _`. Establish `hnV : 1 ≤ D.R.nV` using `le_trans D.R.t_odd.pos (Nat.le_add_left _ _)`. Establish `hH` using `GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i u hu').Kw (D.nbr i u hu').LL hgood (hOf L) D.R.nV (4 * D.R.n) (wLat D i (X.ρ i) π u hu' hc) hKur (GlobalTheory.bridge_finrank_le D i u hu') hnV (fun τ => by`.

Take `⟨U, hU1, hU2, hU3⟩` from `(hJW τ).1`. Conclude with `⟨U, hU1.trans hrn, hU2, hU3⟩)`. Use `⟨hu', 1, hgood, hc, ?_, hH.1, fun τ => (hJW τ).2, ?_⟩` and prove the remaining obligations. Conclude with `(_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hFont i) hgr hcont hdec (hg 0) (hg 1) u hu' (TruncatedSeriesCountingIdentities.CoefExt.self i u hu')).2.2.1`. Rewrite using `[hX.c0]`.

Conclude with `hH.2`.
-/
theorem jointCond_H0Wall_of_canon_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ∀ F : FonOf D.loc D.locA HW, AdmissibleParameterJ.JumpConditions L → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0 := by
  intro _ D L HW R X hX F hJ h41 hFont
  obtain ⟨⟨ep, hJa⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ
  refine ⟨hOf L, hOf L, ?_⟩
  intro i _ _ hsplit u hu π hπ
  have hnI : ¬ TwistedPlaces.InertK D (D.nd.l i) := by
    intro h2
    unfold TwistedPlaces.SplitK at hsplit
    unfold TwistedPlaces.InertK at h2
    rw [hsplit] at h2
    rcases h2 with h2 | h2 <;> cases h2
  rw [hX.dc i hnI] at hu
  unfold dcOf at hu
  split_ifs at hu with hS
  swap
  · simp [KillingConditions.allRows] at hu
  obtain ⟨_, h5, hq, hd, hg, _⟩ := hS.1
  have hu' : u ∈ placesOver D.host.E (D.nd.l i) := ((Exists.choose hS.2).cover u).1 (Or.inr hu)
  have hl2 : D.nd.l i ≠ 2 := by omega
  have hsm : D.nd.l i ∉ D.host.small := fun h => by
    have h' : primeClass D.host.toHostRaw (D.nd.l i) = PrimeClass.splitK := hsplit
    simp [primeClass, h] at h'
  have hKur := GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hsm hq hd u hu'
  have hgood : Good (D.nbr i u hu').Kw 1 (D.nbr i u hu').LL :=
    (D.self_good i u hu').good_one (D.nbr i u hu').LL_split hl2 (GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hKur)
  have hZ : π ∈ D.nd.Z i := Formalism.MainNotions.LargeLevelLemmas.zgoodSubsetZ i hπ
  have hfam := hX.fam
  have hdec := (GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hfam i π hZ).2.2.2
  have hgr := hfam.good i
  have hcont := hfam.cont i π
  have hWc : Continuous (WpO D.nd i (X.ρ i) π) := by
    have h1 : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
      refine ((D.nd.chi_cont i 1).comp continuous_inv).congr fun g => ?_
      simp only [Function.comp_apply]
      rw [MonoidHom.inv_apply, ← map_inv]
    exact h1.smul hcont
  have hLc := GlobalTheory.WordJumpsCompare.continuous_loc D i u hu' _ hWc
  have hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu') ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v :=
    fun v => hLc.matrix_mulVec continuous_const
  have hJW := fun τ => GlobalTheory.T.decomposition_local_above D L ep hJa hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgr hZ hdec u hu'
    (TruncatedSeriesCountingIdentities.CoefExt.self i u hu') τ (WpO D.nd i (X.ρ i) π) (Or.inl rfl)
  have hrn : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hnV : 1 ≤ D.R.nV := le_trans D.R.t_odd.pos (Nat.le_add_left _ _)
  have hH := GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i u hu').Kw (D.nbr i u hu').LL hgood (hOf L) D.R.nV
    (4 * D.R.n) (wLat D i (X.ρ i) π u hu' hc) hKur (GlobalTheory.bridge_finrank_le D i u hu') hnV
    (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := (hJW τ).1
      exact ⟨U, hU1.trans hrn, hU2, hU3⟩)
  refine ⟨hu', 1, hgood, hc, ?_, hH.1, fun τ => (hJW τ).2, ?_⟩
  · exact (_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hFont i) hgr hcont hdec (hg 0) (hg 1) u hu'
      (TruncatedSeriesCountingIdentities.CoefExt.self i u hu')).2.2.1
  · rw [hX.c0]
    exact hH.2
end GlobalTheory.HubX
end
