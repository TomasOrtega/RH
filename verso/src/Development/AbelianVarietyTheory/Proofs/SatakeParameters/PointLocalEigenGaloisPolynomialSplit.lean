import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFielStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig
open Formalism.L2

/- English proof (translation)
Introduce `hmem`. Take `⟨w', hover, hw'⟩` from `hmem`. Take `⟨-, e2⟩` from `(D.nd.locs_mem j w i).1 h`. Establish `hl : D.nd.l i = D.what₂.places.resChar w` using `by rw [← D.nd.w_l i, e2]`. Establish `hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p`.

Introduce `p hp`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ w'.asIdeal` using `by rw [map_natCast]; exact hp`. Establish `h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal`. Rewrite using `[← hover]`. Conclude with `h1`.

Establish `h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, s.w_under]`. Conclude with `h2`. Rewrite `h3` using `[map_natCast]`. Conclude with `(hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3`.

Break down `hw' with hQ | ⟨kk, hg⟩ | hpd` into its components or cases. Rewrite `hQ` using `[T.Q_eq j w i h]`. Establish `hsw : s.w ∈ T.B.Qc j w` using `T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩`. Conclude with `hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)`. Apply `hvk.2.2.1` to reduce the goal to its premises.

Use `⟨?_, hvk.2.1⟩` and prove the remaining obligations. Establish `hv` using `hp _ hg`. Use `fin_cases kk`. Conclude with `Or.inl hv`. Conclude with `Or.inr (Or.inl hv)`.

Apply `hvk.2.2.1` to reduce the goal to its premises. Use `⟨?_, hvk.2.1⟩` and prove the remaining obligations. Rewrite `hpd` using `[hl]`. Conclude with `Or.inr (Or.inr (hp _ hpd))`.
-/
theorem not_bad_of_genAt {D : D7} {M : Formalism.L2.MtFam D} (T : Formalism.L2.NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl)
    (i : D.nd.Loc) (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ Formalism.L2.badPl D i := by
  intro hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

/- English proof (translation)
Introduce `D M HT HR AV NL i hyp P x hcong`. Establish `tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0`. Introduce `s ϖ k`. Use extensionality with `g`. Simplify using `[Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]`.

Distinguish the cases in `hP0 : D.naut.typeV i P = ⊥`. Use `⟨x, (AV.ptV i P x).2 ?_⟩` and prove the remaining obligations. Introduce `v k s ϖ _ _ _ _ _ y hy`. Rewrite `hy` using `[hP0, Submodule.mem_bot]`. Substitute `hy` using the available equality.

Rewrite using `[map_zero, smul_zero, tN0]`. Take `⟨y0, hy0, hy0ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Establish `h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i)` using `(D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩`. Set `lamF : PlE D.host → ℕ → ℂ` to `fun v => if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0`. Establish `hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv)` using `fun v hv => dif_pos hv`.

Establish `hinjO : Function.Injective (iotaO D.nd D.naut i)`. Unfold `iotaO`. Simplify using `only [RingHom.coe_comp]`. Conclude with `(D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))`. Establish `hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i, iotaO D.nd D.naut i a = lamF v k ∧ IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)`.

Introduce `v k hv hk1 hk2`. Take `⟨p, hp1, hp2⟩` from `hcong v hv`. Establish `e1` using `(Classical.choose_spec (hyp P v hv)).1`. Rewrite `e1` using `[← hlamF v hv]`. Conclude with `coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v) (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2`.

Set `aF : PlE D.host → ℕ → D.nd.O i` to `fun v k => if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0`. Establish `haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧ IsLocalRing.residue (D.nd.O i) (aF v k) = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)`. Introduce `v k hv`. Simplify using `only [aF, dif_pos hv]`. Conclude with `Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)`.

Establish `hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z)` using `NL.iotaC_coh _ _ i h`. Establish `hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i))`. Introduce `a b hab`. Establish `e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b` using `hinjO (by`. Rewrite using `[hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.

Conclude with `hab)`. Simplify using `using congrArg (NL.phO _ _ i h) e2`. Set `φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ` to `IsFractionRing.lift hinjC`. Establish `hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z` using `fun z => IsFractionRing.lift_algebraMap hinjC z`. Establish `hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)`.

Apply `IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))` to reduce the goal to its premises. Use extensionality with `z`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]`. Rewrite using `[← hiotaC]`. Both sides reduce to the same expression.

Establish `hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y`. Introduce `y`. Rewrite using `[← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]`. Conclude with `congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK`. Set `κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i))` to `fun v k => algebraMap _ _ (NL.phO _ _ i h (aF v k))`.

Establish `hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k`. Introduce `v k hv hk1 hk2`. Simplify using `only [κ, hφalg]`. Rewrite using `[← hiotaC]`. Conclude with `(haF v k ⟨hv, hk1, hk2⟩).1`.

Take `⟨e, hene, he⟩` from `GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1 (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by`. Introduce `v k hvk`. Take `⟨hv, hk1, hk2⟩` from `(Formalism.L2.genAt_iff NL h v k).2 hvk`. Take `⟨s, ϖ, hc, hu⟩` from `GlobalTheory.T.splitEx_every_datum D v hv.1`. Establish `hbad : s.v ∉ Formalism.L2.badPl D i` using `not_bad_of_genAt NL _ _ i h v k s hvk hc`.

Establish `hfin` using `GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i) s ϖ k hbad hu`. Use `⟨s, ϖ, hc, hu, ?_, ?_⟩` and prove the remaining obligations. Introduce `c f f' show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'`. Simplify using `only [Formalism.L2.NG.tN]`. Rewrite using `[heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]`.

Rewrite using `[hκ v k hv hk1 hk2]`. Establish `e3` using `(Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0`. Rewrite `e3` using `[← hlamF v hv]`. Conclude with `e3)`. Establish `hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i)) (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i))))` using `IsFractionRing.injective _ _`.

Take `⟨ψ, hψ, hψW⟩` from `pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by`. Introduce and unpack `_ ⟨v, k, hvk, rfl⟩`. Conclude with `⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)`. Establish `hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k), ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k)`. Introduce `v k hvk`.

Apply `hinjK` to reduce the goal to its premises. Establish `h1` using `hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩`. Establish `h2` using `he v k hvk`. Express the relevant statement in the definitionally equal form `NL.B.hK _ _ v k e = _ at h1`. Rewrite `h1` using `[h2]`.

Conclude with `(smul_left_injective _ hene h1).symm`. Establish `hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i`. Use `(cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1` and prove the remaining obligations. Introduce and unpack `_ ⟨v, k, hvk, rfl⟩`. Rewrite using `[hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]`.

Take `⟨hv, hk1, hk2⟩` from `(Formalism.L2.genAt_iff NL h v k).2 hvk`. Conclude with `residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2`. Establish `hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥`. Introduce `h0`. Apply `hene` to reduce the goal to its premises.

Establish `h3` using `hψW`. Rewrite `h3` using `[h0]`. Conclude with `(Submodule.mem_bot _).1 h3`. Use `⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩` and prove the remaining obligations. Introduce `v k s ϖ hv hc hu hk1 hk2 y hy`.

Establish `hvk` using `(Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩`. Establish `e1` using `(Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy`. Rewrite `e1` using `[← hlamF v hv]`. Rewrite using `[e1]`. Use `congr 1`.

Use `show lamF v k = iotaO D.nd D.naut i _`. Rewrite using `[hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]`. Use `show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)`. Rewrite using `[hψv v k hvk, ← hiotaC]`. Conclude with `(haF v k ⟨hv, hk1, hk2⟩).1.symm`.
-/
theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro D M HT HR AV NL i hyp P x hcong
  classical
  have tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
      Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    intro s ϖ k; ext g; simp [Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]
  by_cases hP0 : D.naut.typeV i P = ⊥
  · refine ⟨x, (AV.ptV i P x).2 ?_⟩
    intro v k s ϖ _ _ _ _ _ y hy
    rw [hP0, Submodule.mem_bot] at hy
    subst hy
    rw [map_zero, smul_zero, tN0]
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  let lamF : PlE D.host → ℕ → ℂ := fun v =>
    if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0
  have hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv) := fun v hv => dif_pos hv
  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i,
      iotaO D.nd D.naut i a = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv hk1 hk2
    obtain ⟨p, hp1, hp2⟩ := hcong v hv
    have e1 := (Classical.choose_spec (hyp P v hv)).1
    rw [← hlamF v hv] at e1
    exact coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v)
      (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2
  let aF : PlE D.host → ℕ → D.nd.O i := fun v k =>
    if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0
  have haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) (aF v k) =
        IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv
    simp only [aF, dif_pos hv]
    exact Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK
  let κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) := fun v k =>
    algebraMap _ _ (NL.phO _ _ i h (aF v k))
  have hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k := by
    intro v k hv hk1 hk2
    simp only [κ, hφalg]
    rw [← hiotaC]
    exact (haF v k ⟨hv, hk1, hk2⟩).1
  obtain ⟨e, hene, he⟩ := GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1
    (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.T.splitEx_every_datum D v hv.1
      have hbad : s.v ∉ Formalism.L2.badPl D i := not_bad_of_genAt NL _ _ i h v k s hvk hc
      have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i)
        s ϖ k hbad hu
      refine ⟨s, ϖ, hc, hu, ?_, ?_⟩
      · intro c f f'
        show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') =
          c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'
        simp only [Formalism.L2.NG.tN]
        rw [heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
      · rw [hκ v k hv hk1 hk2]
        have e3 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0
        rw [← hlamF v hv] at e3
        exact e3)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)
  have hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k) := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i := by
    refine (cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]
    obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
    exact residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2
  have hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  refine ⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩
  intro v k s ϖ hv hc hu hk1 hk2 y hy
  have hvk := (Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩
  have e1 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy
  rw [← hlamF v hv] at e1
  rw [e1]
  congr 1
  show lamF v k = iotaO D.nd D.naut i _
  rw [hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]
  show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk, ← hiotaC]
  exact (haF v k ⟨hv, hk1, hk2⟩).1.symm

end GlobalTheory.PtLocalEig
