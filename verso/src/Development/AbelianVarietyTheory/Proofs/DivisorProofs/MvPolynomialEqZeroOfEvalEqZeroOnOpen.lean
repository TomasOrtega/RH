import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

/- English proof (translation)
Establish `hspan : Submodule.span ℝ s = ⊤` using `Submodule.span_eq_top_of_ne_zero hs`. Establish `hall : ∀ φ : V →ₗ[ℝ] ℝ, ∃ L, Filter.Tendsto (fun R => φ (G R)) Filter.atTop (nhds L)`. Introduce `φ`. Establish `hφ : φ ∈ Submodule.span ℝ s` using `by rw [hspan]; trivial`. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `mem f hf => exact hG f hf`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add f g _ _ hf hg`. Take `⟨a, ha⟩` from `hf`. Take `⟨b, hb⟩` from `hg`.

Conclude with `⟨a + b, by simpa using ha.add hb⟩`. Consider the case `smul c f _ hf`. Take `⟨a, ha⟩` from `hf`. Conclude with `⟨c * a, by simpa using ha.const_mul c⟩`. Set `b` to `Module.finBasis ℝ V`.

Use `choose L hL using fun i => hall (b.coord i)`. Use `⟨∑ i, L i • b i, fun φ => ?_⟩` and prove the remaining obligations. Establish `h1 : (fun R => φ (G R)) = fun R => ∑ i, b.coord i (G R) * φ (b i)`. Use function extensionality and compare the values at `R`. Use `conv_lhs => rw [← b.sum_repr (G R), map_sum]`.

Simplify using `only [map_smul, smul_eq_mul, Module.Basis.coord_apply]`. Rewrite using `[h1, map_sum]`. Use `tendsto_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `(hL i).mul_const _`.
-/
theorem exists_weak_limit_of_separating {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (s : Set (V →ₗ[ℝ] ℝ)) (hs : ∀ z : V, z ≠ 0 → ∃ f ∈ s, f z ≠ 0)
    (G : ℝ → V) (hG : ∀ f ∈ s, ∃ L, Filter.Tendsto (fun R => f (G R)) Filter.atTop (nhds L)) :
    ∃ P : V, ∀ φ : V →ₗ[ℝ] ℝ, Filter.Tendsto (fun R => φ (G R)) Filter.atTop (nhds (φ P)) := by
  have hspan : Submodule.span ℝ s = ⊤ := Submodule.span_eq_top_of_ne_zero hs
  have hall : ∀ φ : V →ₗ[ℝ] ℝ, ∃ L, Filter.Tendsto (fun R => φ (G R)) Filter.atTop (nhds L) := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ s := by rw [hspan]; trivial
    induction hφ using Submodule.span_induction with
    | mem f hf => exact hG f hf
    | zero => exact ⟨0, by simp⟩
    | add f g _ _ hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      exact ⟨a + b, by simpa using ha.add hb⟩
    | smul c f _ hf =>
      obtain ⟨a, ha⟩ := hf
      exact ⟨c * a, by simpa using ha.const_mul c⟩
  let b := Module.finBasis ℝ V
  choose L hL using fun i => hall (b.coord i)
  refine ⟨∑ i, L i • b i, fun φ => ?_⟩
  have h1 : (fun R => φ (G R)) = fun R => ∑ i, b.coord i (G R) * φ (b i) := by
    funext R
    conv_lhs => rw [← b.sum_repr (G R), map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  rw [h1, map_sum]
  refine tendsto_finsetSum _ fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact (hL i).mul_const _

/- English proof (translation)
Take `⟨x, hx⟩` from `hne`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.1 hU x hx`. Use `MvPolynomial.funext_set (fun i => Set.Ioo (x i - ε) (x i + ε)) (fun i => Set.Ioo_infinite (by linarith)) fun y hy => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `hp y (hb ?_)` and prove the remaining obligations.

Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hε]`. Introduce `i`. Use `hy i (Set.mem_univ i)` as an intermediate fact. Rewrite using `[Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.
-/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open {σ : Type*} [Fintype σ]
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) (p : MvPolynomial σ ℝ)
    (hp : ∀ x ∈ U, eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine MvPolynomial.funext_set (fun i => Set.Ioo (x i - ε) (x i + ε))
    (fun i => Set.Ioo_infinite (by linarith)) fun y hy => ?_
  rw [map_zero]
  refine hp y (hb ?_)
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  have := hy i (Set.mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [this.1, this.2]

/- English proof (translation)
Introduce `σ _ _ d F U hU hne hd hlim`. Set `V` to `restrictTotalDegree σ ℝ d`. Set `ev : (σ → ℝ) → (V →ₗ[ℝ] ℝ)` to `fun x => (aeval x).toLinearMap ∘ₗ V.subtype`. Establish `hev : ∀ x (z : V), ev x z = eval x (z : MvPolynomial σ ℝ)` using `fun x z => by`. Simplify using `[ev]`.

Set `G : ℝ → V` to `fun R => ⟨F R, (mem_restrictTotalDegree σ d _).2 (hd R)⟩`. Take `⟨P, hP⟩` from `exists_weak_limit_of_separating (ev '' U) (fun z hz => by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hz` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use `mvPolynomial_eq_zero_of_eval_eq_zero_on_open hU hne _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hev]`. Conclude with `h _ ⟨x, hx, rfl⟩) G (by`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Simplify `hlim x hx)` using `only [hev]`. Use `⟨P, (mem_restrictTotalDegree σ d _).1 P.2, fun m => ?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `hP (lcoeff ℝ m ∘ₗ V.subtype)`. Simplify `hP (ev x)` using `only [hev]`.
-/
theorem exists_poly_limit_of_tendsto_on_open :
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) (F : ℝ → MvPolynomial σ ℝ) (U : Set (σ → ℝ)), IsOpen U → U.Nonempty → (∀ R, (F R).totalDegree ≤ d) → (∀ x ∈ U, ∃ L, Filter.Tendsto (fun R => eval x (F R)) Filter.atTop (nhds L)) → ∃ P : MvPolynomial σ ℝ, P.totalDegree ≤ d ∧ (∀ m, Filter.Tendsto (fun R => (F R).coeff m) Filter.atTop (nhds (P.coeff m))) ∧ ∀ x, Filter.Tendsto (fun R => eval x (F R)) Filter.atTop (nhds (eval x P)) := by
  intro σ _ _ d F U hU hne hd hlim
  let V := restrictTotalDegree σ ℝ d
  let ev : (σ → ℝ) → (V →ₗ[ℝ] ℝ) := fun x => (aeval x).toLinearMap ∘ₗ V.subtype
  have hev : ∀ x (z : V), ev x z = eval x (z : MvPolynomial σ ℝ) := fun x z => by
    simp [ev]
  let G : ℝ → V := fun R => ⟨F R, (mem_restrictTotalDegree σ d _).2 (hd R)⟩
  obtain ⟨P, hP⟩ := exists_weak_limit_of_separating (ev '' U) (fun z hz => by
      by_contra h
      push Not at h
      apply hz
      apply Subtype.ext
      refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hU hne _ fun x hx => ?_
      rw [← hev]
      exact h _ ⟨x, hx, rfl⟩) G (by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [hev] using hlim x hx)
  refine ⟨P, (mem_restrictTotalDegree σ d _).1 P.2, fun m => ?_, fun x => ?_⟩
  · exact hP (lcoeff ℝ m ∘ₗ V.subtype)
  · simpa only [hev] using hP (ev x)

end GlobalTheory
