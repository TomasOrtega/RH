import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

/- English proof (translation)
Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `i S _ ih`. Rewrite using `[Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]`.
-/
private theorem iInf_pre {X X' : Scheme.{0}} (g : X' ⟶ X) {n : ℕ} (U : Fin n → X.Opens)
    (S : Finset (Fin n)) : (⨅ i ∈ S, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨅ i ∈ S, U i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S _ ih
    rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

/- English proof (translation)
Use `letI := algΓ s`. Use `letI := algΓ s'`. Take `⟨n, U, hc, hU⟩` from `pV k X s`. Use `haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h`. Establish `hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤`.

Rewrite using `[← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]`. Establish `hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i)`. Introduce `S hS`. Rewrite using `[iInf_pre]`. Conclude with `IsAffineHom.isAffine_preimage _ (hU S hS)`.

Establish `hcube : IsBC e ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b)`. Apply `pC k k' J e (Fin n)` to reduce the goal to its premises. Introduce `S hS`. Establish `hA : IsAffineOpen (cechOpen ⊤ U S)`. Rewrite using `[cechOpen, top_inf_eq]`.

Conclude with `hU S hS`. Use `pE k k' J e _ _ _ _ (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S)) (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_ (pO k k' J e X X' s s' g h a _ hA)` and prove the remaining obligations. Introduce `x`. Conclude with `(sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm`. Use `pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube` and prove the remaining obligations.

Introduce `x`. Take `⟨y, rfl⟩` from `(cechHEquivCoh k hc hU (Omega s a) b).surjective x`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y`.
-/
private theorem pull_isBC (pE : P_equiv) (pC : P_cube) (pA : P_affine) (pV : P_cover)
    (pO : P_omega) (pH : P_cech) {k k' : Type} [Field k] [Field k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) [IsProper s] (a b : ℕ) :
    IsBC e (hodgePullS h.w a b) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨n, U, hc, hU⟩ := pV k X s
  haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h
  have hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  have hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i) := by
    intro S hS
    rw [iInf_pre]
    exact IsAffineHom.isAffine_preimage _ (hU S hS)
  have hcube : IsBC e
      ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b) := by
    apply pC k k' J e (Fin n)
    intro S hS
    have hA : IsAffineOpen (cechOpen ⊤ U S) := by
      rw [cechOpen, top_inf_eq]
      exact hU S hS
    refine pE k k' J e _ _ _ _
      (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S))
      (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_
      (pO k k' J e X X' s s' g h a _ hA)
    intro x
    exact (sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm
  refine pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm
    (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube
  intro x
  obtain ⟨y, rfl⟩ := (cechHEquivCoh k hc hU (Omega s a) b).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y

/- English proof (translation)
Introduce `pB pE pC pA pV pO pH pT k k' _ _ φ`. Use `⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩` and prove the remaining obligations. Introduce `X X' s s' g h _ a b I c`. Use `letI : Algebra k k' := φ.toAlgebra`. Establish `h₀ : IsPullback g s' s (spMap (algebraMap k k'))` using `h`.

Conclude with `pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b) (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c`. Introduce `X X' Y Y' s s' g h r r' e he f hf f' hf' w a b`. Conclude with `⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x, fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩`.
-/
theorem UpperTheory.Gal.G3.jHBC :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cech → (∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y)) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC := by
  intro pB pE pC pA pV pO pH pT k k' _ _ φ
  refine ⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩
  · intro X X' s s' g h _ a b I c
    letI : Algebra k k' := φ.toAlgebra
    have h₀ : IsPullback g s' s (spMap (algebraMap k k')) := h
    exact pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b)
      (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c
  · intro X X' Y Y' s s' g h r r' e he f hf f' hf' w a b
    exact ⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x,
      fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩
