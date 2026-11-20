import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

/- English proof (translation)
Establish `h : (x : A) • y = (y : A) • x` using `by ext; simp [mul_comm]`. Use `congrArg f h` as an intermediate fact. Simplify using `only [map_smul, smul_eq_mul] at this`. Rewrite using `[mul_comm, this, mul_comm]`.
-/
theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

/- English proof (translation)
Take `⟨t, ht⟩` from `(Module.Invertible.bijective (R := A) (M := ↥I)).2 1`. Rewrite using `[← ht]`. Use `clear ht`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `Ideal.add_mem _ ha hb`.
-/
theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | zero => simp
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal

open GlobalTheory.BSP.ZarPrincipal in

/- English proof (translation)
Introduce `A _ I hI`. Use `set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS`. Establish `h1 : (1 : A) ∈ Ideal.span S` using `one_mem_span_values I`. Take `⟨T, hTS, hT⟩` from `Submodule.mem_span_finite_of_mem_span h1`. Establish `hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A)` using `fun a => hTS a.2`.

Use `choose f y hfy using hmem`. Set `e` to `T.equivFin`. Use `⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`. Use `Submodule.span_mono ?_ hT` and prove the remaining obligations.

Introduce `a ha`. Conclude with `⟨e ⟨a, ha⟩, by simp⟩`. Introduce `i`. Use `⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩` and prove the remaining obligations. Use `show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)`.

Rewrite using `[← hfy (e.symm i)]`. Conclude with `form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩`.
-/
theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
