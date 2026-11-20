import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

/- English proof (translation)
Introduce `F E _ _ _ _ _ n q`. Set `f : AdelicGLn.AdelicGL E n → HeightOneSpectrum (𝓞 E) → ℝ` to `fun x w => if below F w ≠ q then AutomorphicForm.locHeight (finAt w x) else 1`. Establish `hoff : ∀ x : AdelicGLn.AdelicGL E n, heightOff q x = (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w x) ^ w.mult) * ∏ᶠ w, f x w`. Introduce `x`. Unfold `heightOff`.

Use `congr 1`. Conclude with `finprod_congr fun w => finprod_eq_if`. Establish `hone : ∀ x w, 1 ≤ f x w`. Introduce `x w`. Simplify using `only [f]`.

Use `split_ifs`. Conclude with `AutomorphicForm.one_le_locHeight _`. Conclude with `le_rfl`. Establish `hsupp : ∀ x, (Function.mulSupport (f x)).Finite`. Introduce `x`.

Use `(AutomorphicForm.finite_mulSupport_locHeight_finAt x).subset ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Function.mem_mulSupport, f] at hw ⊢`. Introduce `h`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Establish `hfi1 : ∀ x, 1 ≤ ∏ᶠ w, f x w` using `fun x => finprod_induction (fun y : ℝ => 1 ≤ y) le_rfl (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) (hone x)`. Use `⟨fun g => ?_, ?_, fun g h => ?_⟩` and prove the remaining obligations. Rewrite using `[hoff]`.

Conclude with `one_le_mul_of_one_le_of_one_le (AutomorphicForm.one_le_prod_locHeight g) (hfi1 g)`. Establish `h1 : ∀ w, f 1 w = 1`. Introduce `w`. Simplify using `[f, AutomorphicForm.locHeight_one]`. Rewrite using `[hoff, finprod_eq_one_of_forall_eq_one h1]`.

Simplify using `[AutomorphicForm.locHeight_one]`. Use `set s := ((hsupp g).union (hsupp h)).union (hsupp (g * h))`. Establish `hfin : ∀ x : AdelicGLn.AdelicGL E n, x = g ∨ x = h ∨ x = g * h → ∏ᶠ w, f x w = ∏ w ∈ s.toFinset, f x w`. Introduce `x hx`. Use `finprod_eq_prod_of_mulSupport_subset _ ?_` and prove the remaining obligations.

Introduce `v hv`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_union]`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `Or.inl (Or.inl hv)`. Conclude with `Or.inl (Or.inr hv)`.

Conclude with `Or.inr hv`. Establish `hf : ∏ᶠ w, f (g * h) w ≤ (∏ᶠ w, f g w) * ∏ᶠ w, f h w`. Rewrite using `[hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)), ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun v _ => le_trans zero_le_one (hone _ v)) fun v _ => ?_` and prove the remaining obligations. Simplify using `only [f]`.

Use `split_ifs`. Rewrite using `[finAt_mul]`. Conclude with `AutomorphicForm.locHeight_mul_le_of_ultrametric _ _`. Simplify using the standard rewrite rules. Establish `hi : (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) ≤ AutomorphicForm.heightConst E n * (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) * ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult`.

Rewrite using `[AutomorphicForm.heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun w _ => by have := AutomorphicForm.locHeight_pos (infAt w (g * h)); positivity) fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, ← mul_pow, infAt_mul]`. Conclude with `pow_le_pow_left₀ (AutomorphicForm.locHeight_pos _).le (AutomorphicForm.locHeight_mul_le _ _) _`. Rewrite using `[hoff, hoff, hoff]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.one_le_heightOff_and_submultiplicative :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : HeightOneSpectrum (𝓞 F)),
        (∀ g : AdelicGLn.AdelicGL E n, 1 ≤ heightOff q g) ∧ heightOff q (1 : AdelicGLn.AdelicGL E n) = 1 ∧
        ∀ g h : AdelicGLn.AdelicGL E n, heightOff q (g * h) ≤ AutomorphicForm.heightConst E n * heightOff q g * heightOff q h := by
  classical
  intro F E _ _ _ _ _ n q
  let f : AdelicGLn.AdelicGL E n → HeightOneSpectrum (𝓞 E) → ℝ := fun x w =>
    if below F w ≠ q then AutomorphicForm.locHeight (finAt w x) else 1
  have hoff : ∀ x : AdelicGLn.AdelicGL E n, heightOff q x =
      (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w x) ^ w.mult) * ∏ᶠ w, f x w := by
    intro x
    unfold heightOff
    congr 1
    exact finprod_congr fun w => finprod_eq_if
  have hone : ∀ x w, 1 ≤ f x w := by
    intro x w
    simp only [f]
    split_ifs
    · exact AutomorphicForm.one_le_locHeight _
    · exact le_rfl
  have hsupp : ∀ x, (Function.mulSupport (f x)).Finite := by
    intro x
    refine (AutomorphicForm.finite_mulSupport_locHeight_finAt x).subset ?_
    intro w hw
    simp only [Function.mem_mulSupport, f] at hw ⊢
    intro h
    apply hw
    rw [h]
    simp
  have hfi1 : ∀ x, 1 ≤ ∏ᶠ w, f x w := fun x =>
    finprod_induction (fun y : ℝ => 1 ≤ y) le_rfl
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) (hone x)
  refine ⟨fun g => ?_, ?_, fun g h => ?_⟩
  · rw [hoff]
    exact one_le_mul_of_one_le_of_one_le (AutomorphicForm.one_le_prod_locHeight g) (hfi1 g)
  · have h1 : ∀ w, f 1 w = 1 := by
      intro w
      simp [f, AutomorphicForm.locHeight_one]
    rw [hoff, finprod_eq_one_of_forall_eq_one h1]
    simp [AutomorphicForm.locHeight_one]
  · set s := ((hsupp g).union (hsupp h)).union (hsupp (g * h))
    have hfin : ∀ x : AdelicGLn.AdelicGL E n, x = g ∨ x = h ∨ x = g * h →
        ∏ᶠ w, f x w = ∏ w ∈ s.toFinset, f x w := by
      intro x hx
      refine finprod_eq_prod_of_mulSupport_subset _ ?_
      intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_union]
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    have hf : ∏ᶠ w, f (g * h) w ≤ (∏ᶠ w, f g w) * ∏ᶠ w, f h w := by
      rw [hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun v _ => le_trans zero_le_one (hone _ v)) fun v _ => ?_
      simp only [f]
      split_ifs
      · rw [finAt_mul]
        exact AutomorphicForm.locHeight_mul_le_of_ultrametric _ _
      · simp
    have hi : (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) ≤
        AutomorphicForm.heightConst E n *
          (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
          ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult := by
      rw [AutomorphicForm.heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod
        (fun w _ => by have := AutomorphicForm.locHeight_pos (infAt w (g * h)); positivity)
        fun w _ => ?_
      rw [← mul_pow, ← mul_pow, infAt_mul]
      exact pow_le_pow_left₀ (AutomorphicForm.locHeight_pos _).le
        (AutomorphicForm.locHeight_mul_le _ _) _
    rw [hoff, hoff, hoff]
    calc (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) *
          ∏ᶠ w, f (g * h) w
        ≤ (AutomorphicForm.heightConst E n *
            (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
            ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult) *
          ((∏ᶠ w, f g w) * ∏ᶠ w, f h w) :=
          mul_le_mul hi hf (le_trans zero_le_one (hfi1 _))
            (mul_nonneg (mul_nonneg (le_trans zero_le_one AutomorphicForm.one_le_heightConst)
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight g)))
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight h)))
      _ = _ := by ring
