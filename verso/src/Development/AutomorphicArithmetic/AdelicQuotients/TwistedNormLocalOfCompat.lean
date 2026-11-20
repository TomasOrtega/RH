import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem twNorm_hom' {G G' : Type} [Group G] [Group G'] (f : G →* G') (θ : Monoid.End G)
    (θ' : Monoid.End G') (h : ∀ x, f (θ x) = θ' (f x)) (m : ℕ) (δ : G) :
    f (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = PositivityTheory.Rg.Tf.Loc.twNorm θ' m (f δ) := by
  have hp : ∀ (i : ℕ) (x : G), f ((θ ^ i) x) = (θ' ^ i) (f x) := fun i => by
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', PositivityTheory.Rg.Tf.Loc.pow_succ_apply', h, ih]
  induction m with
  | zero => simp
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, PositivityTheory.Rg.Tf.Loc.twNorm_succ, map_mul, ih, hp]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.twistedNorm_local_of_compat :
    Compat → LocNorm := by
  intro hC F E _ _ _ _ _ _ σ _ n _ δ γ hδ
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := hC F E σ n
  have hdiag : GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ) =
      mapGL n (GroundTheory.Global.AdeleBaseChange.adeleMap F E) (GroundTheory.Automorphic.AdelicGLn.diagonal F n γ) := by
    rw [hδ, h8]
  constructor
  · have key := twNorm_hom' ((pI E n).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galInf σ)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h1]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pI E n (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h3]
  · intro v
    have key := twNorm_hom' ((pE E n v).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galFin σ v)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h2]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pE E n v (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h4]
    rfl
