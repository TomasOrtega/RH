import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.SemiLocal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem centralSection_val (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) :
    ∃ u : GroundTheory.Global.IdeleGroup K, (∀ v, ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2 v = 1) ∧
      ((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K) := by
  refine ⟨posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s), fun v => ?_, ?_⟩
  · rw [posIdeleHom_apply]
    exact posIdele_finite _ _ v
  · rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.centralSection_local_scalar :
    CentLoc := by
  intro K _ _ n s
  obtain ⟨u, hf, hu⟩ := centralSection_val K n s
  have hI : ∀ i j, ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j =
      (Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j := by
    intro i j
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).1 = _
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      rfl
  have hI' : ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :=
    Matrix.ext hI
  have hF : ∀ (i j : Fin n), (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 =
      ((1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 := by
    intro i j
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext K hf
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  refine ⟨⟨Units.map (RingHom.toMonoidHom (α := AdeleRing (𝓞 K) K) (β := InfiniteAdeleRing K) (RingHom.fst _ _)) u, fun g => ?_⟩,
    fun g => ?_, fun v => ?_, fun F _ _ _ v => ?_⟩
  · rw [Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul]
    rfl
  · refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [pF_apply]
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 v = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 w.1 = (1 : Matrix (Fin n) (Fin n) (CompletionsOver K v)) i j w
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
