import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Set `ev : X → Module.Dual ℂ E` to `fun u => (LinearMap.proj u).comp E.subtype`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Apply `Submodule.span_eq_top_of_ne_zero` to reduce the goal to its premises. Introduce `z hz`. Assume the negation of the conclusion as `h`.

Apply `hz` to reduce the goal to its premises. Use extensionality with `u`. Assume the negation of the conclusion as `hu`. Conclude with `h ⟨ev u, ⟨u, rfl⟩, hu⟩`. Take `⟨κ, c, -, hc, hli⟩` from `exists_linearIndependent' ℂ ev`.

Use `haveI : Finite κ := hli.finite`. Take `⟨a, ⟨e⟩⟩` from `Finite.exists_equiv_fin κ`. Set `b0 : Module.Basis κ ℂ (Module.Dual ℂ E)` to `Module.Basis.mk hli (by rw [hc, hspan])`. Set `b : Module.Basis (Fin a) ℂ (Module.Dual ℂ E)` to `b0.reindex e`. Establish `hb : ∀ i, b i = ev (c (e.symm i))`.

Introduce `i`. Simplify using `[b, b0]`. Use `⟨a, fun i => ((Module.evalEquiv ℂ E).symm (b.coord i) : E), fun i => c (e.symm i), fun i => Subtype.property _, ?_⟩` and prove the remaining obligations. Introduce `f hf u`. Establish `h1` using `b.sum_repr (ev u)`.

Establish `h2` using `congrArg (fun l : Module.Dual ℂ E => l ⟨f, hf⟩) h1`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h2`. Establish `h3 : ∀ i, (((Module.evalEquiv ℂ E).symm (b.coord i) : E) : X → ℂ) u = b.repr (ev u) i`. Introduce `i`. Establish `: ev u ((Module.evalEquiv ℂ E).symm (b.coord i)) = b.coord i (ev u)` using `Module.apply_evalEquiv_symm_apply ℂ E _ _`.

Conclude with `this`. Express the relevant statement in the definitionally equal form `ev u ⟨f, hf⟩ = _`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← h3, mul_comm]`.

Both sides reduce to the same expression.
-/
private theorem tens_interp {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (a : ℕ) (φ : Fin a → X → ℂ) (x : Fin a → X), (∀ i, φ i ∈ E) ∧
      ∀ f ∈ E, ∀ u, f u = ∑ i, f (x i) * φ i u := by
  classical
  let ev : X → Module.Dual ℂ E := fun u => (LinearMap.proj u).comp E.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext u
    by_contra hu
    exact h ⟨ev u, ⟨u, rfl⟩, hu⟩
  obtain ⟨κ, c, -, hc, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  obtain ⟨a, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ ℂ (Module.Dual ℂ E) := Module.Basis.mk hli (by rw [hc, hspan])
  let b : Module.Basis (Fin a) ℂ (Module.Dual ℂ E) := b0.reindex e
  have hb : ∀ i, b i = ev (c (e.symm i)) := by
    intro i
    simp [b, b0]
  refine ⟨a, fun i => ((Module.evalEquiv ℂ E).symm (b.coord i) : E), fun i => c (e.symm i),
    fun i => Subtype.property _, ?_⟩
  intro f hf u
  have h1 := b.sum_repr (ev u)
  have h2 := congrArg (fun l : Module.Dual ℂ E => l ⟨f, hf⟩) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h2
  have h3 : ∀ i, (((Module.evalEquiv ℂ E).symm (b.coord i) : E) : X → ℂ) u = b.repr (ev u) i := by
    intro i
    have : ev u ((Module.evalEquiv ℂ E).symm (b.coord i)) = b.coord i (ev u) :=
      Module.apply_evalEquiv_symm_apply ℂ E _ _
    exact this
  change ev u ⟨f, hf⟩ = _
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h3, mul_comm]
  rfl

/- English proof (translation)
Introduce `X Y E₁ E₂ _ _`. Take `⟨a, φ, x, hφ, hx⟩` from `tens_interp E₁`. Take `⟨b, ψ, y, hψ, hy⟩` from `tens_interp E₂`. Use `⟨a, b, φ, ψ, fun _ p => x p, fun _ q => y q, fun i p => if p = i then 1 else 0, fun j q => if q = j then 1 else 0, hφ, hψ, ?_⟩` and prove the remaining obligations. Introduce `Φ h1 h2 u v`.

Establish `hs : ∀ i j, (∑ p, ∑ q, (if p = i then (1 : ℂ) else 0) * (if q = j then (1 : ℂ) else 0) * Φ (x p) (y q)) = Φ (x i) (y j)`. Introduce `i j`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `q _ hq`.

Simplify using `[hq]`. Simplify using the standard rewrite rules. Introduce `p _ hp`. Simplify using `[hp]`. Simplify using the standard rewrite rules.

Simplify using `only [hs]`. Rewrite using `[hx _ (h1 v) u]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hy _ (h2 (x i)) v, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tens :
    ∀ {X Y : Type} (E₁ : Submodule ℂ (X → ℂ)) (E₂ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂],
      ∃ (a b : ℕ) (φ : Fin a → X → ℂ) (ψ : Fin b → Y → ℂ) (x : Fin a → Fin a → X) (y : Fin b → Fin b → Y) (s : Fin a → Fin a → ℂ) (t : Fin b → Fin b → ℂ),
        (∀ i, φ i ∈ E₁) ∧ (∀ j, ψ j ∈ E₂) ∧ ∀ Φ : X → Y → ℂ, (∀ v, (fun u => Φ u v) ∈ E₁) → (∀ u, Φ u ∈ E₂) →
          ∀ u v, Φ u v = ∑ i, ∑ j, (∑ p, ∑ q, s i p * t j q * Φ (x i p) (y j q)) * φ i u * ψ j v := by
  intro X Y E₁ E₂ _ _
  obtain ⟨a, φ, x, hφ, hx⟩ := tens_interp E₁
  obtain ⟨b, ψ, y, hψ, hy⟩ := tens_interp E₂
  refine ⟨a, b, φ, ψ, fun _ p => x p, fun _ q => y q, fun i p => if p = i then 1 else 0,
    fun j q => if q = j then 1 else 0, hφ, hψ, ?_⟩
  intro Φ h1 h2 u v
  have hs : ∀ i j, (∑ p, ∑ q, (if p = i then (1 : ℂ) else 0) * (if q = j then (1 : ℂ) else 0) *
      Φ (x p) (y q)) = Φ (x i) (y j) := by
    intro i j
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [hq]
    · simp
    · intro p _ hp; simp [hp]
    · simp
  simp only [hs]
  rw [hx _ (h1 v) u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy _ (h2 (x i)) v, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
