import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Establish `hp : ∀ (i : ℕ) (x : G), f ((θ ^ i) x) = (θ' ^ i) (f x)` using `fun i => by`. Proceed by induction on `i with`. Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ i ih`.

Introduce `x`. Rewrite using `[PositivityTheory.Rg.Tf.Loc.pow_succ_apply', PositivityTheory.Rg.Tf.Loc.pow_succ_apply', h, ih]`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, PositivityTheory.Rg.Tf.Loc.twNorm_succ, map_mul, ih, hp]`.
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
Introduce `hC F E _ _ _ _ _ _ σ _ n _ δ γ hδ`. Take `⟨h1, h2, h3, h4, -, -, h7, h8⟩` from `hC F E σ n`. Establish `hdiag : GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ) = mapGL n (GroundTheory.Global.AdeleBaseChange.adeleMap F E) (GroundTheory.Automorphic.AdelicGLn.diagonal F n γ)`. Rewrite using `[hδ, h8]`. Prove the components needed by the constructor for the conclusion.

Establish `key` using `twNorm_hom' ((pI E n).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) (mapGL n (galInf σ)) (fun x => by`. Simplify using `only [MonoidHom.comp_apply]`. Rewrite using `[← h7, h1]`. Use the proof step `rfl) (Module.finrank F E) δ`. Simplify using `only [MonoidHom.comp_apply] at key`.

Rewrite using `[← key]`. Express the relevant statement in the definitionally equal form `pI E n (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _`. Rewrite using `[hdiag, h3]`. Introduce `v`. Establish `key` using `twNorm_hom' ((pE E n v).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) (mapGL n (galFin σ v)) (fun x => by`.

Simplify using `only [MonoidHom.comp_apply]`. Rewrite using `[← h7, h2]`. Use the proof step `rfl) (Module.finrank F E) δ`. Simplify using `only [MonoidHom.comp_apply] at key`. Rewrite using `[← key]`.

Express the relevant statement in the definitionally equal form `pE E n v (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _`. Rewrite using `[hdiag, h4]`. Both sides reduce to the same expression.
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
