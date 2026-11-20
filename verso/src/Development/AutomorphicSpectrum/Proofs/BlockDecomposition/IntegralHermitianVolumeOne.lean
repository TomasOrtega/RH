import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodHerm

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.SiegelWeilFormula.Gunr PositivityTheory.PfSWUS.Loc Topology
open scoped TensorProduct

/- English proof (translation)
Take `⟨hH, hinv⟩` from `hμ`. Use `haveI := hH`. Establish `hmeas : MeasurableSet (L : Set V)` using `hO.measurableSet`. Establish `hclosed : IsClosed (L : Set V)` using `AddSubgroup.isClosed_of_isOpen L hO`. Establish `hfin : μ L ≠ ⊤` using `hC.measure_lt_top.ne`.

Establish `hpos : μ L ≠ 0` using `(hO.measure_pos μ ⟨0, L.zero_mem⟩).ne'`. Use `set c : ℂ := ((μ.real (L : Set V) : ℝ) : ℂ) with hc`. Set `Φ : V → ℂ` to `(L : Set V).indicator fun _ => 1`. Establish `hΦc : Continuous Φ` using `IsClopen.continuous_indicator ⟨hclosed, hO⟩ continuous_const`. Establish `hΦs : HasCompactSupport Φ` using `HasCompactSupport.intro hC fun x hx => Set.indicator_of_notMem hx _`.

Establish `hIΦ : ∫ x, Φ x ∂μ = c`. Simplify using `only [Φ]`. Rewrite using `[integral_indicator_const _ hmeas]`. Simplify using `[hc]`. Establish `hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => c) y`.

Introduce `y`. Distinguish the cases in `hy : y ∈ L`. Rewrite using `[Set.indicator_of_mem (show y ∈ (L : Set V) from hy), ← hIΦ]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ L`.

Simplify using `[Φ, (hann y).2 hy x hx, show x ∈ (L : Set V) from hx]`. Simplify using `[Φ, show x ∉ (L : Set V) from hx]`. Rewrite using `[Set.indicator_of_notMem (show y ∉ (L : Set V) from hy)]`. Establish `hex : ∃ x₀ ∈ L, χ x₀ y ≠ 1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hy ((hann y).1 hcon)`. Take `⟨x₀, hx₀, hne⟩` from `hex`. Establish `htr : ∫ x, Φ (x₀ + x) * χ (x₀ + x) y ∂μ = ∫ x, Φ x * χ x y ∂μ` using `integral_add_left_eq_self (fun x => Φ x * χ x y) x₀`. Establish `hsh : ∀ x, Φ (x₀ + x) = Φ x`.

Introduce `x`. Establish `: x₀ + x ∈ L ↔ x ∈ L` using `L.add_mem_cancel_left hx₀`. Distinguish the cases in `hx : x ∈ L`. Simplify using `[Φ, show x ∈ (L : Set V) from hx, show x₀ + x ∈ (L : Set V) from this.2 hx]`. Simplify using `[Φ, show x ∉ (L : Set V) from hx, show x₀ + x ∉ (L : Set V) from fun h => hx (this.1 h)]`.

Establish `h2 : ∫ x, Φ (x₀ + x) * χ (x₀ + x) y ∂μ = χ x₀ y * ∫ x, Φ x * χ x y ∂μ`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `show Φ (x₀ + x) * χ (x₀ + x) y = χ x₀ y * (Φ x * χ x y)`. Rewrite using `[hsh, hadd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[htr]`. Establish `h3 : (1 - χ x₀ y) * ∫ x, Φ x * χ x y ∂μ = 0`. Rewrite using `[sub_mul, one_mul, ← h2, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne.symm)`.

Establish `hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ`. Establish `: (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => c)` using `funext hI`. Rewrite using `[this, integrable_indicator_iff hmeas]`. Conclude with `integrableOn_const hfin`. Establish `hout` using `hinv Φ hΦc hΦs hint 0`.

Establish `hL : ∫ y, (∫ x, Φ x * χ x y ∂μ) * χ y 0 ∂μ = c * c`. Establish `: ∀ y, (∫ x, Φ x * χ x y ∂μ) * χ y 0 = (L : Set V).indicator (fun _ => c) y`. Introduce `y`. Rewrite using `[hI]`. Distinguish the cases in `hy : y ∈ L`.

Simplify using `[show y ∈ (L : Set V) from hy, (hann 0).2 L.zero_mem y hy]`. Simplify using `[show y ∉ (L : Set V) from hy]`. Simplify using `only [this]`. Rewrite using `[integral_indicator_const _ hmeas]`. Simplify using `[hc]`.

Establish `h1 : Φ (-0) = 1` using `by simp [Φ]`. Rewrite `hout` using `[hL, h1]`. Establish `h2 : (μ.real (L : Set V)) * (μ.real (L : Set V)) = 1`. Establish `: (((μ.real (L : Set V)) * (μ.real (L : Set V)) : ℝ) : ℂ) = ((1 : ℝ) : ℂ)` using `by push_cast; simpa [hc] using hout`. Conclude with `this` after adjusting the coercions.

Establish `h3 : μ.real (L : Set V) = 1`. Establish `h0 : 0 ≤ μ.real (L : Set V)` using `measureReal_nonneg`. Use polynomial arithmetic with `[sq_nonneg (μ.real (L : Set V) - 1), sq_nonneg (μ.real (L : Set V) + 1)]`. Establish `h4 : (μ L).toReal = 1` using `h3`. Conclude with `(ENNReal.toReal_eq_one_iff _).1 h4`.
-/
theorem measure_eq_one_of_selfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (L : AddSubgroup V)
    (hO : IsOpen (L : Set V)) (hC : IsCompact (L : Set V)) (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hcont : ∀ y, Continuous fun x => χ x y) (hann : ∀ y, (∀ x ∈ L, χ x y = 1) ↔ y ∈ L) : μ L = 1 := by
  classical
  obtain ⟨hH, hinv⟩ := hμ
  haveI := hH
  have hmeas : MeasurableSet (L : Set V) := hO.measurableSet
  have hclosed : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hO
  have hfin : μ L ≠ ⊤ := hC.measure_lt_top.ne
  have hpos : μ L ≠ 0 := (hO.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  set c : ℂ := ((μ.real (L : Set V) : ℝ) : ℂ) with hc
  let Φ : V → ℂ := (L : Set V).indicator fun _ => 1
  have hΦc : Continuous Φ := IsClopen.continuous_indicator ⟨hclosed, hO⟩ continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hC fun x hx => Set.indicator_of_notMem hx _
  have hIΦ : ∫ x, Φ x ∂μ = c := by
    simp only [Φ]
    rw [integral_indicator_const _ hmeas]
    simp [hc]
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ L
    · rw [Set.indicator_of_mem (show y ∈ (L : Set V) from hy), ← hIΦ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ L
      · simp [Φ, (hann y).2 hy x hx, show x ∈ (L : Set V) from hx]
      · simp [Φ, show x ∉ (L : Set V) from hx]
    · rw [Set.indicator_of_notMem (show y ∉ (L : Set V) from hy)]
      have hex : ∃ x₀ ∈ L, χ x₀ y ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hy ((hann y).1 hcon)
      obtain ⟨x₀, hx₀, hne⟩ := hex
      have htr : ∫ x, Φ (x₀ + x) * χ (x₀ + x) y ∂μ = ∫ x, Φ x * χ x y ∂μ :=
        integral_add_left_eq_self (fun x => Φ x * χ x y) x₀
      have hsh : ∀ x, Φ (x₀ + x) = Φ x := by
        intro x
        have : x₀ + x ∈ L ↔ x ∈ L := L.add_mem_cancel_left hx₀
        by_cases hx : x ∈ L
        · simp [Φ, show x ∈ (L : Set V) from hx, show x₀ + x ∈ (L : Set V) from this.2 hx]
        · simp [Φ, show x ∉ (L : Set V) from hx, show x₀ + x ∉ (L : Set V) from fun h => hx (this.1 h)]
      have h2 : ∫ x, Φ (x₀ + x) * χ (x₀ + x) y ∂μ = χ x₀ y * ∫ x, Φ x * χ x y ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show Φ (x₀ + x) * χ (x₀ + x) y = χ x₀ y * (Φ x * χ x y)
        rw [hsh, hadd]; ring
      rw [htr] at h2
      have h3 : (1 - χ x₀ y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h2, sub_self]
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne.symm)
  have hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => c) := funext hI
    rw [this, integrable_indicator_iff hmeas]
    exact integrableOn_const hfin
  have hout := hinv Φ hΦc hΦs hint 0
  have hL : ∫ y, (∫ x, Φ x * χ x y ∂μ) * χ y 0 ∂μ = c * c := by
    have : ∀ y, (∫ x, Φ x * χ x y ∂μ) * χ y 0 = (L : Set V).indicator (fun _ => c) y := by
      intro y
      rw [hI]
      by_cases hy : y ∈ L
      · simp [show y ∈ (L : Set V) from hy, (hann 0).2 L.zero_mem y hy]
      · simp [show y ∉ (L : Set V) from hy]
    simp only [this]
    rw [integral_indicator_const _ hmeas]
    simp [hc]
  have h1 : Φ (-0) = 1 := by simp [Φ]
  rw [hL, h1] at hout
  have h2 : (μ.real (L : Set V)) * (μ.real (L : Set V)) = 1 := by
    have : (((μ.real (L : Set V)) * (μ.real (L : Set V)) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast; simpa [hc] using hout
    exact_mod_cast this
  have h3 : μ.real (L : Set V) = 1 := by
    have h0 : 0 ≤ μ.real (L : Set V) := measureReal_nonneg
    nlinarith [sq_nonneg (μ.real (L : Set V) - 1), sq_nonneg (μ.real (L : Set V) + 1)]
  have h4 : (μ L).toReal = 1 := h3
  exact (ENNReal.toReal_eq_one_iff _).1 h4

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModTop_Fv (v : HeightOneSpectrum (𝓞 F)) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def sigEquiv (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    (Fv F v ⊗[F] E) ≃ₐ[Fv F v] (Fv F v ⊗[F] E) :=
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite bs
  Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[Fv F v] Fv F v)
    (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ))

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [sigEquiv, sigR]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigEquiv_apply (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) : sigEquiv bs σ v x = sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigEquiv, sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Rewrite using `[← sigEquiv_apply bs, Algebra.trace_eq_of_algEquiv]`.
-/
theorem trace_sigR (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ x) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x := by
  rw [← sigEquiv_apply bs, Algebra.trace_eq_of_algEquiv]

/- English proof (translation)
Use `haveI := isModTop_Fv (E := E) v`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _`. Use `haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _`. Establish `h` using `IsModuleTopology.continuous_of_linearMap (sigEquiv bs σ v).toLinearMap`. Establish `e : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (sigEquiv bs σ v).toLinearMap`.

Use function extensionality and compare the values at `x`. Conclude with `(sigEquiv_apply bs σ v x).symm`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem continuous_sigR_Fv (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) := by
  haveI := isModTop_Fv (E := E) v
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have h := IsModuleTopology.continuous_of_linearMap (sigEquiv bs σ v).toLinearMap
  have e : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (sigEquiv bs σ v).toLinearMap := by
    funext x
    exact (sigEquiv_apply bs σ v x).symm
  rw [e]
  exact h

/- English proof (translation)
Use `haveI := isModTop_Fv (E := E) v`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _`. Use `haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _`. Set `L` to `(Algebra.TensorProduct.basis (Fv F v) bs).equivFun`. Use `⟨⟨L.toEquiv, IsModuleTopology.continuous_of_linearMap L.toLinearMap, IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩, fun x k => ?_⟩` and prove the remaining obligations.

Both sides reduce to the same expression.
-/
theorem exists_coord_homeo (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v), ∀ x k, e x k = (Algebra.TensorProduct.basis (Fv F v) bs).repr x k := by
  haveI := isModTop_Fv (E := E) v
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let L := (Algebra.TensorProduct.basis (Fv F v) bs).equivFun
  refine ⟨⟨L.toEquiv, IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩, fun x k => ?_⟩
  rfl

/- English proof (translation)
Use `haveI := isModTop_Fv (E := E) v`. Conclude with `IsModuleTopology.topologicalAddGroup (Fv F v) _`.
-/
theorem isTopAdd_tens (v : HeightOneSpectrum (𝓞 F)) : IsTopologicalAddGroup (Fv F v ⊗[F] E) := by
  haveI := isModTop_Fv (E := E) v
  exact IsModuleTopology.topologicalAddGroup (Fv F v) _

/- English proof (translation)
Take `⟨e, -⟩` from `exists_coord_homeo bs v`. Conclude with `e.isEmbedding.t2Space`.
-/
theorem t2_tensor_product (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : T2Space (Fv F v ⊗[F] E) := by
  obtain ⟨e, -⟩ := exists_coord_homeo bs v
  exact e.isEmbedding.t2Space

/- English proof (translation)
Use `haveI := t2_tensor_product bs v`. Establish `: (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) = ⋂ a, ⋂ b, {X | sigR (Fv F v) σ (X b a) = X a b}`. Use extensionality with `X`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]`. Conclude with `Iff.rfl`.

Rewrite using `[this]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ((continuous_sigR_Fv bs σ v).comp ((continuous_apply a).comp (continuous_apply b))) ((continuous_apply b).comp (continuous_apply a))`.
-/
theorem isClosed_herm (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    IsClosed (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  haveI := t2_tensor_product bs v
  have : (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) =
      ⋂ a, ⋂ b, {X | sigR (Fv F v) σ (X b a) = X a b} := by
    ext X
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigR_Fv bs σ v).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

/- English proof (translation)
Take `⟨e, he⟩` from `exists_coord_homeo bs v`. Establish `hO : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v)))` using `Valued.isOpen_integer _`. Establish `h : Rv bs v = e ⁻¹' (Set.pi Set.univ fun _ : Fin d => (v.adicCompletionIntegers F : Set (Fv F v)))`. Use extensionality with `x`. Simplify using `only [Rv, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, he, SetLike.mem_coe]`.

Rewrite using `[h]`. Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage e.continuous`.
-/
theorem isOpen_Rv (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : IsOpen (Rv bs v) := by
  obtain ⟨e, he⟩ := exists_coord_homeo bs v
  have hO : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have h : Rv bs v = e ⁻¹' (Set.pi Set.univ fun _ : Fin d => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp only [Rv, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, he, SetLike.mem_coe]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage e.continuous

/- English proof (translation)
Take `⟨e, he⟩` from `exists_coord_homeo bs v`. Establish `hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v)))` using `PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`. Establish `h : Rv bs v = e ⁻¹' (Set.pi Set.univ fun _ : Fin d => (v.adicCompletionIntegers F : Set (Fv F v)))`. Use extensionality with `x`. Simplify using `only [Rv, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, he, SetLike.mem_coe]`.

Rewrite using `[h]`. Conclude with `e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi fun _ => hO)`.
-/
theorem isCompact_Rv (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : IsCompact (Rv bs v) := by
  obtain ⟨e, he⟩ := exists_coord_homeo bs v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have h : Rv bs v = e ⁻¹' (Set.pi Set.univ fun _ : Fin d => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp only [Rv, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, he, SetLike.mem_coe]
  rw [h]
  exact e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi fun _ => hO)

/- English proof (translation)
Introduce `k`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `mul_mem hc (hx k)`.
-/
theorem smul_mem_Rv {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E} (hx : x ∈ Rv bs v) :
    c • x ∈ Rv bs v := by
  intro k
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hc (hx k)

def boxS (S : Subring (Fv F v ⊗[F] E)) (n : ℕ) : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
  Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (S : Set (Fv F v ⊗[F] E))

/- English proof (translation)
Use extensionality with `b`. Prove the components needed by the constructor for the conclusion. Introduce `h i _ j _`. Conclude with `h i j`. Introduce `h i j`.

Conclude with `h i trivial j trivial`.
-/
theorem coe_integral_hermitian_box (S : Subring (Fv F v ⊗[F] E)) (σ : E →ₐ[F] E) (n : ℕ) :
    (H0 S σ n : Set (HermR (Fv F v) σ n)) = Subtype.val ⁻¹' boxS S n := by
  ext b
  constructor
  · intro h i _ j _
    exact h i j
  · intro h i j
    exact h i trivial j trivial

/- English proof (translation)
Rewrite using `[coe_integral_hermitian_box]`. Use `IsOpen.preimage continuous_subtype_val ?_` and prove the remaining obligations. Establish `hS : IsOpen (S : Set (Fv F v ⊗[F] E))` using `by rw [hG.carrier]; exact isOpen_Rv bs v`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hS`.
-/
theorem isOpen_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : IsOpen (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
  rw [coe_integral_hermitian_box]
  refine IsOpen.preimage continuous_subtype_val ?_
  have hS : IsOpen (S : Set (Fv F v ⊗[F] E)) := by rw [hG.carrier]; exact isOpen_Rv bs v
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hS

/- English proof (translation)
Rewrite using `[coe_integral_hermitian_box]`. Establish `hS : IsCompact (S : Set (Fv F v ⊗[F] E))` using `by rw [hG.carrier]; exact isCompact_Rv bs v`. Conclude with `(isClosed_herm bs σ v n).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hS)`.
-/
theorem isCompact_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : IsCompact (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
  rw [coe_integral_hermitian_box]
  have hS : IsCompact (S : Set (Fv F v ⊗[F] E)) := by rw [hG.carrier]; exact isCompact_Rv bs v
  exact (isClosed_herm bs σ v n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hS)

namespace GoodAt

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

/- English proof (translation)
Establish `h` using `hG.sig ⟨s, hs⟩`. Simplify using `only at h`. Rewrite using `[← h]`. Conclude with `(σS ⟨s, hs⟩).2`.
-/
theorem sig_mem {s : Fv F v ⊗[F] E} (hs : s ∈ S) : sigR (Fv F v) σ s ∈ S := by
  have h := hG.sig ⟨s, hs⟩
  simp only at h
  rw [← h]
  exact (σS ⟨s, hs⟩).2

/- English proof (translation)
Establish `h1` using `hG.sig ⟨s, hs⟩`. Establish `h2` using `hG.sig (σS ⟨s, hs⟩)`. Establish `h3` using `hG.quad.inv ⟨s, hs⟩`. Simplify using `only at h1`. Rewrite `h2` using `[h3, h1]`.

Conclude with `h2.symm`.
-/
theorem sig_sig {s : Fv F v ⊗[F] E} (hs : s ∈ S) : sigR (Fv F v) σ (sigR (Fv F v) σ s) = s := by
  have h1 := hG.sig ⟨s, hs⟩
  have h2 := hG.sig (σS ⟨s, hs⟩)
  have h3 := hG.quad.inv ⟨s, hs⟩
  simp only at h1
  rw [h3, h1] at h2
  exact h2.symm

/- English proof (translation)
Establish `h : ∀ x, x ∈ S ↔ x ∈ Rv bs v` using `fun x => by rw [← hG.carrier]; rfl`. Conclude with `(h _).2 (smul_mem_Rv hc ((h _).1 hs))`.
-/
theorem smul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {s : Fv F v ⊗[F] E} (hs : s ∈ S) : c • s ∈ S := by
  have h : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by rw [← hG.carrier]; rfl
  exact (h _).2 (smul_mem_Rv hc ((h _).1 hs))

end GoodAt

def testMat (σ : E →ₐ[F] E) (a b : Fin n) (s : Fv F v ⊗[F] E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  fun i j => (if i = a ∧ j = b then s else 0) + (if i = b ∧ j = a then sigR (Fv F v) σ s else 0)

/- English proof (translation)
Introduce `i j`. Simplify using `only [testMat, map_add, apply_ite (sigR (Fv F v) σ), map_zero, GoodAt.sig_sig hG hs]`. Rewrite using `[add_comm]`. Simplify using `only [and_comm]`.
-/
theorem testMat_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a b : Fin n) {s : Fv F v ⊗[F] E} (hs : s ∈ S) :
    testMat σ a b s ∈ HermR (Fv F v) σ n := by
  intro i j
  simp only [testMat, map_add, apply_ite (sigR (Fv F v) σ), map_zero, GoodAt.sig_sig hG hs]
  rw [add_comm]
  simp only [and_comm]

/- English proof (translation)
Simplify using `only [testMat, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `key : ∀ (p q : Fin n) (t : Fv F v ⊗[F] E), (∑ x, ∑ x_1, if x = p then if x_1 = q then t * Y x_1 x else 0 else 0) = t * Y q p`. Introduce `p q t`. Rewrite using `[Finset.sum_eq_single p (fun x _ hx => by simp [hx]) (by simp), Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]`. Simplify using the standard rewrite rules.

Rewrite using `[key, key]`.
-/
theorem sum_testMat (σ : E →ₐ[F] E) (a b : Fin n) (s : Fv F v ⊗[F] E) (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    ∑ i, ∑ j, testMat σ a b s i j * Y j i = s * Y b a + sigR (Fv F v) σ s * Y a b := by
  simp only [testMat, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ (p q : Fin n) (t : Fv F v ⊗[F] E),
      (∑ x, ∑ x_1, if x = p then if x_1 = q then t * Y x_1 x else 0 else 0) = t * Y q p := by
    intro p q t
    rw [Finset.sum_eq_single p (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [key, key]

/- English proof (translation)
Establish `hy : (y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = sigR (Fv F v) σ ((y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b a)` using `(y.2 a b).symm`. Establish `hh : algebraMap F (Fv F v) (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]`. Evaluate the numerical expressions. Unfold `pairHerm`.

Use `show algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ i, ∑ j, testMat σ a b s i j * (y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i) = _`. Rewrite using `[sum_testMat, hy, ← map_mul, map_add, trace_sigR bs, ← two_mul, ← mul_assoc, hh, one_mul]`.
-/
theorem pair_testMat (bs : Module.Basis (Fin d) F E) (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a b : Fin n)
    {s : Fv F v ⊗[F] E} (hs : s ∈ S) (y : HermR (Fv F v) σ n) :
    pairHerm (Fv F v) σ n ⟨testMat σ a b s, testMat_mem hG a b hs⟩ y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (s * (y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b a) := by
  have hy : (y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b =
      sigR (Fv F v) σ ((y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b a) := (y.2 a b).symm
  have hh : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  unfold pairHerm
  show algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
    (∑ i, ∑ j, testMat σ a b s i j * (y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i) = _
  rw [sum_testMat, hy, ← map_mul, map_add, trace_sigR bs, ← two_mul, ← mul_assoc, hh, one_mul]

/- English proof (translation)
Simplify using `only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]`.
-/
theorem pair_add (x x' y : HermR (Fv F v) σ n) :
    pairHerm (Fv F v) σ n (x + x') y = pairHerm (Fv F v) σ n x y + pairHerm (Fv F v) σ n x' y := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

/- English proof (translation)
Use `haveI := isModTop_Fv (E := E) v`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _`. Use `haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _`. Use `haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)`. Unfold `pairHerm`.

Use `continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp ?_)` and prove the remaining obligations. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `(IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (Fv F v) ((y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b a))).comp ((continuous_apply_apply a b).comp continuous_subtype_val)`.
-/
theorem continuous_pair (y : HermR (Fv F v) σ n) (bs : Module.Basis (Fin d) F E) :
    Continuous fun x : HermR (Fv F v) σ n => pairHerm (Fv F v) σ n x y := by
  haveI := isModTop_Fv (E := E) v
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  unfold pairHerm
  refine continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp ?_)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact (IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (Fv F v)
    ((y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b a))).comp
      ((continuous_apply_apply a b).comp continuous_subtype_val)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a b`. Use `(hG.trace_dual _).1 fun s hs => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `(hG.psi_cond _).1 fun c hc => ?_` and prove the remaining obligations.

Establish `hcs : c • s ∈ S` using `GoodAt.smul_mem hG hc hs`. Establish `hx : (⟨testMat σ b a (c • s), testMat_mem hG b a hcs⟩ : HermR (Fv F v) σ n) ∈ H0 S σ n`. Introduce `i j`. Use `show testMat σ b a (c • s) i j ∈ S`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `hcs`. Conclude with `zero_mem _`. Use `split_ifs`. Conclude with `GoodAt.sig_mem hG hcs`.

Conclude with `zero_mem _`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[pair_testMat bs hG b a hcs y, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]`. Conclude with `this`. Introduce `hy x hx`.

Use `hG.psi_of_mem ?_` and prove the remaining obligations. Unfold `pairHerm`. Establish `hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F`. Establish `: algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹`. Rewrite using `[one_div, map_inv₀, map_ofNat]`.

Rewrite using `[this]`. Conclude with `hG.half_mem`. Use `mul_mem hh (hG.trace_mem ?_)` and prove the remaining obligations. Conclude with `sum_mem fun i _ => sum_mem fun j _ => mul_mem (hx i j) (hy j i)`.
-/
theorem annihilator (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (y : HermR (Fv F v) σ n) :
    (∀ x ∈ H0 S σ n, ψv (pairHerm (Fv F v) σ n x y) = 1) ↔ y ∈ H0 S σ n := by
  constructor
  · intro h a b

    refine (hG.trace_dual _).1 fun s hs => ?_
    rw [mul_comm]
    refine (hG.psi_cond _).1 fun c hc => ?_
    have hcs : c • s ∈ S := GoodAt.smul_mem hG hc hs
    have hx : (⟨testMat σ b a (c • s), testMat_mem hG b a hcs⟩ : HermR (Fv F v) σ n) ∈ H0 S σ n := by
      intro i j
      show testMat σ b a (c • s) i j ∈ S
      refine add_mem ?_ ?_
      · split_ifs
        · exact hcs
        · exact zero_mem _
      · split_ifs
        · exact GoodAt.sig_mem hG hcs
        · exact zero_mem _
    have := h _ hx
    rw [pair_testMat bs hG b a hcs y, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm] at this
    exact this
  · intro hy x hx
    refine hG.psi_of_mem ?_
    unfold pairHerm
    have hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F := by
      have : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
        rw [one_div, map_inv₀, map_ofNat]
      rw [this]
      exact hG.half_mem
    refine mul_mem hh (hG.trace_mem ?_)
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (hx i j) (hy j i)

end Local

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG νv hν`. Use `haveI := isTopAdd_tens (E := E) v`. Use `haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩`. Use `measure_eq_one_of_selfDual νv _ hν (H0 S σ n) (isOpen_integral_hermitian hG) (isCompact_integral_hermitian hG) ?_ ?_ (annihilator hG)` and prove the remaining obligations. Introduce `x x' y`.

Rewrite using `[pair_add, hG.psi_add]`. Introduce `y`. Conclude with `hG.psi_cont.comp (continuous_pair y bs)`.
-/
theorem volume_integral_hermitian_one : HermitianLatticeVolumeOne := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG νv hν
  haveI := isTopAdd_tens (E := E) v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  refine measure_eq_one_of_selfDual νv _ hν (H0 S σ n) (isOpen_integral_hermitian hG) (isCompact_integral_hermitian hG) ?_ ?_ (annihilator hG)
  · intro x x' y
    rw [pair_add, hG.psi_add]
  · intro y
    exact hG.psi_cont.comp (continuous_pair y bs)

end GlobalTheory.CompanionTheory.GoodHerm
end
