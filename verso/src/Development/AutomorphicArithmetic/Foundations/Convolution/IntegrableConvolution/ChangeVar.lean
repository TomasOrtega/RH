import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `δ`. Establish `h` using `measurePreserving_piFinSuccAbove (fun _ : Fin 1 => μ) 0`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `i.elim0`. Consider the case `succ m ih`.

Introduce `δ`. Establish `h1` using `measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => μ) 0`. Establish `h2` using `(MeasurePreserving.id μ).prod (ih (Fin.tail δ))`. Establish `h3 : MeasurePreserving (fun p : G × (G × (Fin m → G)) => (id p.1, (p.1⁻¹ * δ 0 * p.2.1, p.2.2))) (μ.prod (μ.prod (Measure.pi fun _ => μ))) (μ.prod (μ.prod (Measure.pi fun _ => μ)))`. Use `MeasurePreserving.skew_product (g := fun (a : G) (q : G × (Fin m → G)) => (a⁻¹ * δ 0 * q.1, q.2)) (MeasurePreserving.id μ) ?_ (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Unfold `Function.uncurry fun_prop`. Conclude with `((measurePreserving_mul_left μ (a⁻¹ * δ 0)).prod (MeasurePreserving.id _)).map_eq`. Establish `h4` using `(MeasurePreserving.id μ).prod (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm`. Establish `h` using `h4.comp (h3.comp (h2.comp h1))`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[MeasurableEquiv.piFinSuccAbove, Fin.tail]`.

Simplify using `[MeasurableEquiv.piFinSuccAbove, Fin.tail]`.
-/
private theorem measurePreserving_chainCoords {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (m : ℕ) :
    ∀ δ : Fin m → G,
    MeasurePreserving (fun x : Fin (m + 1) → G => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) := by
  induction m with
  | zero =>
    intro δ
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin 1 => μ) 0
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    exact i.elim0
  | succ m ih =>
    intro δ
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => μ) 0
    have h2 := (MeasurePreserving.id μ).prod (ih (Fin.tail δ))
    have h3 : MeasurePreserving
        (fun p : G × (G × (Fin m → G)) => (id p.1, (p.1⁻¹ * δ 0 * p.2.1, p.2.2)))
        (μ.prod (μ.prod (Measure.pi fun _ => μ))) (μ.prod (μ.prod (Measure.pi fun _ => μ))) := by
      refine MeasurePreserving.skew_product (g := fun (a : G) (q : G × (Fin m → G)) => (a⁻¹ * δ 0 * q.1, q.2))
        (MeasurePreserving.id μ) ?_ (Filter.Eventually.of_forall fun a => ?_)
      · unfold Function.uncurry
        fun_prop
      · exact ((measurePreserving_mul_left μ (a⁻¹ * δ 0)).prod (MeasurePreserving.id _)).map_eq
    have h4 := (MeasurePreserving.id μ).prod
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have h := h4.comp (h3.comp (h2.comp h1))
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro δ x`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `δ x`.

Establish `h` using `ih (fun i => δ i.succ) (fun i => x i.succ)`. Simplify using `only [List.ofFn_succ, List.prod_cons, ← Fin.succ_castSucc]`. Rewrite using `[h]`. Simplify using `[mul_assoc]`.
-/
private theorem tele {G : Type} [Group G] (m : ℕ) : ∀ (δ : Fin m → G) (x : Fin (m + 1) → G),
    (List.ofFn fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ).prod =
      (x 0)⁻¹ * (List.ofFn δ).prod * x (Fin.last m) := by
  induction m with
  | zero => intro δ x; simp
  | succ m ih =>
    intro δ x
    have h := ih (fun i => δ i.succ) (fun i => x i.succ)
    simp only [List.ofFn_succ, List.prod_cons, ← Fin.succ_castSucc]
    rw [h]
    simp [mul_assoc]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ m δ`. Use `⟨measurePreserving_chainCoords μ m (fun i => δ i.castSucc), fun x => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Unfold `UpperTheory.ConvolutionTheory.L1.fib`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Rewrite using `[Fin.snoc_last, tele m (fun i => δ i.castSucc) x, List.ofFn_succ' δ]`. Simplify using `[mul_assoc]`. Rewrite using `[Fin.snoc_castSucc, Fin.coeSucc_eq_succ]`.
-/
theorem UpperTheory.ConvolutionTheory.L1.changeVar :
    UpperTheory.ConvolutionTheory.L1.ChangeVar := by
  intro G _ _ _ _ _ _ _ _ μ _ m δ
  refine ⟨measurePreserving_chainCoords μ m (fun i => δ i.castSucc), fun x => ?_⟩
  funext i
  unfold UpperTheory.ConvolutionTheory.L1.fib
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, tele m (fun i => δ i.castSucc) x, List.ofFn_succ' δ]
    simp [mul_assoc]
  · rw [Fin.snoc_castSucc, Fin.coeSucc_eq_succ]
