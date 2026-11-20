import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.SemiLocal

/- English proof (translation)
Use `⟨posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s), fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[posIdeleHom_apply]`. Conclude with `posIdele_finite _ _ v`. Rewrite using `[centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]`.
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
Introduce `K _ _ n s`. Take `⟨u, hf, hu⟩` from `centralSection_val K n s`. Establish `hI : ∀ i j, ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j = (Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j`. Introduce `i j`. Express the relevant statement in the definitionally equal form `(((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).1 = _`.

Rewrite using `[hu]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]`.

Both sides reduce to the same expression. Establish `hI' : ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) = Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1` using `Matrix.ext hI`. Establish `hF : ∀ (i j : Fin n), (((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 = ((1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2`. Introduce `i j`. Rewrite using `[hu]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Conclude with `FiniteAdeleRing.ext K hf`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]`.

Use `⟨⟨Units.map (RingHom.toMonoidHom (α := AdeleRing (𝓞 K) K) (β := InfiniteAdeleRing K) (RingHom.fst _ _)) u, fun g => ?_⟩, fun g => ?_, fun v => ?_, fun F _ _ _ v => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, hI']`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul]`. Both sides reduce to the same expression.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, hI']`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Rewrite using `[pF_apply]`. Express the relevant statement in the definitionally equal form `(((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 v = (1 : Matrix (Fin n) (Fin n) _) i j`. Rewrite using `[hF]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression. Use `Units.ext (Matrix.ext fun i j => funext fun w => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 w.1 = (1 : Matrix (Fin n) (Fin n) (CompletionsOver K v)) i j w`. Rewrite using `[hF]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression.
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
