import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.PolFin
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Unfold `UpperTheory.ConvolutionTheory.G3.lpol`. Rewrite using `[GlobalTheory.BCT.ThBasic.nrmL_twist hU]`. Simplify using `using Matrix.charpoly_units_conj g⁻¹ (nrmL n w x).val`.
-/
private theorem UpperTheory.ConvolutionTheory.G2.lpol_twist {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ)
    (w : Pl E) (g x : GLw n w) :
    UpperTheory.ConvolutionTheory.G3.lpol w (g⁻¹ * x * thL n w g) = UpperTheory.ConvolutionTheory.G3.lpol w x := by
  unfold UpperTheory.ConvolutionTheory.G3.lpol
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hU]
  simpa using Matrix.charpoly_units_conj g⁻¹ (nrmL n w x).val

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Apply `h` to reduce the goal to its premises. Unfold `stTw2 clSum`. Use `finsum_eq_zero_of_forall_eq_zero fun c => ?_` and prove the remaining obligations. Use `split_ifs with hc`.

Rewrite using `[UpperTheory.ConvolutionTheory.G3.orbZero _ _ _ _ _ ?_, mul_zero]`. Introduce and unpack `y ⟨g, hg⟩`. Assume the negation of the conclusion as `hy`. Establish `h1 : y.1 = g.1⁻¹ * c.rep.1 * thL a w g.1` using `by rw [hg]; rfl`. Establish `h2 : y.2 = g.2⁻¹ * c.rep.2 * thL b w g.2` using `by rw [hg]; rfl`.

Use `hno ⟨y, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]`. Conclude with `hc.1`. Rewrite using `[h2, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]`. Conclude with `hc.2`.

Both sides reduce to the same expression.
-/
private theorem UpperTheory.ConvolutionTheory.G2.exists_supp {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (a b : ℕ)
    (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y : GLw a w × GLw b w, φ y ≠ 0 ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.1 = Q₁ ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.2 = Q₂ := by
  by_contra hno
  apply h
  unfold stTw2 clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hc
  · rw [UpperTheory.ConvolutionTheory.G3.orbZero _ _ _ _ _ ?_, mul_zero]
    rintro y ⟨g, hg⟩
    by_contra hy
    have h1 : y.1 = g.1⁻¹ * c.rep.1 * thL a w g.1 := by rw [hg]; rfl
    have h2 : y.2 = g.2⁻¹ * c.rep.2 * thL b w g.2 := by rw [hg]; rfl
    refine hno ⟨y, hy, ?_, ?_⟩
    · rw [h1, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.1
    · rw [h2, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.2
  · rfl

/- English proof (translation)
Use `closure_minimal ?_ ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.isClosed.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2.isClosed)` and prove the remaining obligations. Introduce `y hy`. Assume the negation of the conclusion as `hn`. Conclude with `hy (Set.indicator_of_notMem hn _)`.
-/
private theorem UpperTheory.ConvolutionTheory.G2.tsupport_unit2 {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) :
    tsupport (UpperTheory.ConvolutionTheory.G2.unit2 a b w) ⊆ (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := by
  refine closure_minimal ?_ ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.isClosed.prod
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2.isClosed)
  intro y hy
  by_contra hn
  exact hy (Set.indicator_of_notMem hn _)

/- English proof (translation)
Introduce `E _ _ _ hU a b S hS φ hc hae`. Establish `f₁` using `UpperTheory.ConvolutionTheory.G3.polFin E hU a S hS (fun w => Prod.fst '' tsupport (φ w)) (fun w => (hc w).image continuous_fst) (hae.mono fun w hw => by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite `hy` using `[hw]`. Conclude with `(UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).1)`.

Establish `f₂` using `UpperTheory.ConvolutionTheory.G3.polFin E hU b S hS (fun w => Prod.snd '' tsupport (φ w)) (fun w => (hc w).image continuous_snd) (hae.mono fun w hw => by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite `hy` using `[hw]`. Conclude with `(UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).2)`. Use `(f₁.prod f₂).subset ?_` and prove the remaining obligations.

Introduce and unpack `⟨P₁, P₂⟩ ⟨h₁, h₂, h⟩`. Use `⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩` and prove the remaining obligations. Take `⟨y, hy, e₁, -⟩` from `UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)`. Conclude with `⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, e₁⟩`. Take `⟨y, hy, -, e₂⟩` from `UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)`.

Conclude with `⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, e₂⟩`.
-/
theorem UpperTheory.ConvolutionTheory.G2.finP :
    UpperTheory.ConvolutionTheory.G2.FinP := by
  intro E _ _ _ hU a b S hS φ hc hae
  have f₁ := UpperTheory.ConvolutionTheory.G3.polFin E hU a S hS (fun w => Prod.fst '' tsupport (φ w))
    (fun w => (hc w).image continuous_fst) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).1)
  have f₂ := UpperTheory.ConvolutionTheory.G3.polFin E hU b S hS (fun w => Prod.snd '' tsupport (φ w))
    (fun w => (hc w).image continuous_snd) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).2)
  refine (f₁.prod f₂).subset ?_
  rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, e₂⟩
