import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((0 : ℕ) : ℤ) * ν i) = 1` using `Units.ext (by simp [Cartan.coe_diagPow])`. Rewrite using `[h, locHeight_one, pow_zero]`. Consider the case `succ j ih`.

Establish `h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((j + 1 : ℕ) : ℤ) * ν i) = Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) * Cartan.diagPow (w.adicCompletion E) n ν`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Cartan.coe_diagPow, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `push_cast`. Rewrite using `[add_mul, one_mul, zpow_add₀ (Cartan.uniformizer_ne_zero _)]`. Rewrite using `[h, pow_succ]`. Conclude with `(locHeight_mul_le_of_ultrametric _ _).trans (mul_le_mul_of_nonneg_right ih (locHeight_pos _).le)`.
-/
private theorem locHeight_diagPow_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ν : Fin n → ℤ) (j : ℕ) :
    locHeight (Cartan.diagPow (w.adicCompletion E) n fun i => (j : ℤ) * ν i) ≤
      locHeight (Cartan.diagPow (w.adicCompletion E) n ν) ^ j := by
  induction j with
  | zero =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((0 : ℕ) : ℤ) * ν i) = 1 :=
      Units.ext (by simp [Cartan.coe_diagPow])
    rw [h, locHeight_one, pow_zero]
  | succ j ih =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((j + 1 : ℕ) : ℤ) * ν i) =
        Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) *
          Cartan.diagPow (w.adicCompletion E) n ν := by
      refine Units.ext ?_
      rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Cartan.coe_diagPow,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      push_cast
      rw [add_mul, one_mul, zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    rw [h, pow_succ]
    exact (locHeight_mul_le_of_ultrametric _ _).trans
      (mul_le_mul_of_nonneg_right ih (locHeight_pos _).le)

/- English proof (translation)
The claim follows from `locHeight_eq_one_of_mem_integralGL (GLnLocal.iwahori_le_integralGL _ _ ha)`.
-/
private theorem locHeight_iwahori {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {a : GL (Fin n) (w.adicCompletion E)} (ha : a ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    locHeight a = 1 :=
  locHeight_eq_one_of_mem_integralGL (GLnLocal.iwahori_le_integralGL _ _ ha)

/- English proof (translation)
Introduce `F E _ _ _ _ _ n q w₀ ν`. Use `⟨locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν), one_le_locHeight _, ?_⟩` and prove the remaining obligations. Introduce `j Y f hS g hg`. Take `⟨h1, h2, h3⟩` from `hS g hg`. Establish `hfin` using `finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL E n)`.

Establish `hbelow : ∀ x : HeightOneSpectrum (𝓞 E), x.asIdeal.LiesOver q.asIdeal → AdeleBaseChange.below F x = q`. Introduce `x hx`. Use `HeightOneSpectrum.ext ?_` and prove the remaining obligations. Establish `e1` using `(AdeleBaseChange.liesOver_below (K := F) x).over`. Establish `e2` using `hx.over`.

Conclude with `e1.trans e2.symm`. Establish `split : (∏ᶠ w : HeightOneSpectrum (𝓞 E), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) = (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w …`. Establish `h` using `finprod_mem_union' (f := fun w : HeightOneSpectrum (𝓞 E) => locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) (s := {w | AdeleBaseChange.below F w ≠ q}) (t := {w | AdeleBaseChange.below F w = q}) (Set.disjoint_left.2 fun w h₁ h₂ => h₁ h₂) (hfin.inter_of_right _) (hfin.inter_of_ri …`. Establish `hu : {w : HeightOneSpectrum (𝓞 E) | AdeleBaseChange.below F w ≠ q} ∪ {w | AdeleBaseChange.below F w = q} = Set.univ`. Use extensionality with `w`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Conclude with `(em _).symm`. Rewrite `h` using `[hu, finprod_mem_univ]`. Conclude with `h`. Establish `hC : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) ≤ locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν) ^ j`.

Rewrite using `[finprod_eq_single _ w₀.1 ?_, finprod_eq_if, if_pos (hbelow _ w₀.2)]`. Take `⟨a, ha, b, hb, e⟩` from `h2`. Rewrite using `[e]`. Use `(locHeight_mul_le_of_ultrametric _ _).trans ?_` and prove the remaining obligations. Rewrite using `[locHeight_iwahori hb, mul_one]`.

Use `(locHeight_mul_le_of_ultrametric _ _).trans ?_` and prove the remaining obligations. Rewrite using `[locHeight_iwahori ha, one_mul]`. Conclude with `locHeight_diagPow_le _ _ _ _`. Introduce `x hx`. Rewrite using `[finprod_eq_if]`.

Use `split_ifs with hq`. Establish `hl : x.asIdeal.LiesOver q.asIdeal` using `hq ▸ AdeleBaseChange.liesOver_below x`. Conclude with `locHeight_iwahori (h3 ⟨x, hl⟩ fun h => hx (congrArg Subtype.val h))`. Both sides reduce to the same expression. Establish `hB : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))` using `finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le`.

Establish `hC0 : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))` using `finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le`. Establish `hoff : 0 ≤ heightOff q (g : AdelicGLn.AdelicGL E n)` using `mul_nonneg (zero_le_one.trans (one_le_prod_locHeight _)) hB`. Establish `key : AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) = heightOff q (g : AdelicGLn.AdelicGL E n) * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))`. Rewrite using `[AutomorphicForm.height, split, heightOff, mul_assoc]`. Rewrite using `[key]`.

Conclude with `mul_le_mul h1 hC hC0 (hoff.trans h1)`.
-/
theorem UpperTheory.ConvolutionTheory.GM.htTot :
    HtTot := by
  classical
  intro F E _ _ _ _ _ n q w₀ ν
  refine ⟨locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν), one_le_locHeight _, ?_⟩
  intro j Y f hS g hg
  obtain ⟨h1, h2, h3⟩ := hS g hg
  have hfin := finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL E n)
  have hbelow : ∀ x : HeightOneSpectrum (𝓞 E), x.asIdeal.LiesOver q.asIdeal →
      AdeleBaseChange.below F x = q := by
    intro x hx
    refine HeightOneSpectrum.ext ?_
    have e1 := (AdeleBaseChange.liesOver_below (K := F) x).over
    have e2 := hx.over
    exact e1.trans e2.symm
  have split : (∏ᶠ w : HeightOneSpectrum (𝓞 E), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) =
      (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) *
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    have h := finprod_mem_union' (f := fun w : HeightOneSpectrum (𝓞 E) =>
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)))
      (s := {w | AdeleBaseChange.below F w ≠ q}) (t := {w | AdeleBaseChange.below F w = q})
      (Set.disjoint_left.2 fun w h₁ h₂ => h₁ h₂) (hfin.inter_of_right _) (hfin.inter_of_right _)
    have hu : {w : HeightOneSpectrum (𝓞 E) | AdeleBaseChange.below F w ≠ q} ∪
        {w | AdeleBaseChange.below F w = q} = Set.univ := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (em _).symm
    rw [hu, finprod_mem_univ] at h
    exact h
  have hC : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) ≤
      locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν) ^ j := by
    rw [finprod_eq_single _ w₀.1 ?_, finprod_eq_if, if_pos (hbelow _ w₀.2)]
    · obtain ⟨a, ha, b, hb, e⟩ := h2
      rw [e]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori hb, mul_one]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori ha, one_mul]
      exact locHeight_diagPow_le _ _ _ _
    · intro x hx
      rw [finprod_eq_if]
      split_ifs with hq
      · have hl : x.asIdeal.LiesOver q.asIdeal := hq ▸ AdeleBaseChange.liesOver_below x
        exact locHeight_iwahori (h3 ⟨x, hl⟩ fun h => hx (congrArg Subtype.val h))
      · rfl
  have hB : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hC0 : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hoff : 0 ≤ heightOff q (g : AdelicGLn.AdelicGL E n) :=
    mul_nonneg (zero_le_one.trans (one_le_prod_locHeight _)) hB
  have key : AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) =
      heightOff q (g : AdelicGLn.AdelicGL E n) *
        ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
          locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    rw [AutomorphicForm.height, split, heightOff, mul_assoc]
  rw [key]
  exact mul_le_mul h1 hC hC0 (hoff.trans h1)
