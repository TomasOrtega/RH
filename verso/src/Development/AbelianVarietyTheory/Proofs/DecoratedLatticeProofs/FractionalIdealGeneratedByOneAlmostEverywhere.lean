import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.IdeleGen

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `I.isFractional`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hbot : (I : Submodule (𝓞 E) E) ≠ ⊥`. Introduce `h`. Apply `hI` to reduce the goal to its premises.

Conclude with `FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)`. Take `⟨x, hxI, hx0⟩` from `(Submodule.ne_bot_iff _).1 hbot`. Take `⟨j, hj⟩` from `hint x hxI`. Establish `hj' : (j : E) = (a : E) * x`. Simplify `hj` using `[Algebra.smul_def]`.

Establish `haE : (a : E) ≠ 0` using `by exact_mod_cast ha0`. Establish `hj0 : j ≠ 0`. Introduce `h`. Rewrite `hj'` using `[h]`. Simplify using `at hj'`.

Break down `hj' with h1 | h1` into its components or cases. Apply the tactic sequence `first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm`. Apply the tactic sequence `first | exact hx0 h1 | exact hx0 h1.symm`. Use `set Nd := Ideal.absNorm (Ideal.span {a}) with hNd`. Use `set Nj := Ideal.absNorm (Ideal.span {j}) with hNj`.

Establish `hNd0 : Nd ≠ 0`. Rewrite using `[hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `ha0`. Establish `hNj0 : Nj ≠ 0`. Rewrite using `[hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hj0`. Take `⟨o₁, ho₁⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))`. Take `⟨o₂, ho₂⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))`. Establish `ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E)` using `by rw [← ho₁]; push_cast; ring`. Establish `ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E)` using `by rw [← ho₂]; push_cast; ring`.

Use `⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x`. Rewrite using `[Algebra.smul_def]`. Establish `e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E)` using `by push_cast; ring`. Rewrite using `[e1, ho₂E]`.

Establish `hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E)` using `fun _ => rfl`. Rewrite using `[hal]`. Use `push_cast`. Take the linear combination `((Nd : E) * (o₂ : E)) * hj'`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hxI`. Introduce `b hb`. Take `⟨y, hy⟩` from `hint b hb`. Establish `hy' : (y : E) = (a : E) * b` using `by simpa [Algebra.smul_def] using hy`. Use `⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩` and prove the remaining obligations.

Establish `e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E)` using `by push_cast; ring`. Rewrite using `[e1, ho₁E]`. Use `push_cast`. Take the linear combination `(-((Nj : E) * (o₁ : E))) * hy'`.
-/
theorem exists_nat_mem_mul_integral {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 E, (N : E) * b = (o : E) := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h
    apply hI
    exact FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨j, hj⟩ := hint x hxI
  have hj' : (j : E) = (a : E) * x := by
    simpa [Algebra.smul_def] using hj
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj'; simp at hj'
    rcases hj' with h1 | h1
    · first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm
    · first | exact hx0 h1 | exact hx0 h1.symm
  set Nd := Ideal.absNorm (Ideal.span {a}) with hNd
  set Nj := Ideal.absNorm (Ideal.span {j}) with hNj
  have hNd0 : Nd ≠ 0 := by
    rw [hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha0
  have hNj0 : Nj ≠ 0 := by
    rw [hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hj0
  obtain ⟨o₁, ho₁⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  obtain ⟨o₂, ho₂⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))
  have ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E) := by rw [← ho₁]; push_cast; ring
  have ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E) := by rw [← ho₂]; push_cast; ring
  refine ⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩
  · have : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x := by
      rw [Algebra.smul_def]
      have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
      rw [e1, ho₂E]
      have hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun _ => rfl
      rw [hal]
      push_cast
      linear_combination ((Nd : E) * (o₂ : E)) * hj'
    rw [this]
    exact Submodule.smul_mem _ _ hxI
  · intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    have hy' : (y : E) = (a : E) * b := by simpa [Algebra.smul_def] using hy
    refine ⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩
    have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
    rw [e1, ho₁E]
    push_cast
    linear_combination (-((Nj : E) * (o₁ : E))) * hy'

/- English proof (translation)
Introduce `D I hI`. Take `⟨N, hN0, hNI, hNb⟩` from `exists_nat_mem_mul_integral I hI`. Establish `hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN0` after adjusting the coercions.

Establish `hfin` using `Ideal.finite_factors hc0`. Use `⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `hmem`. Apply `hv` to reduce the goal to its premises. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hmem`. Establish `: (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E)` using `by push_cast; rfl`. Rewrite using `[this]`. Conclude with `hNI`. Establish `: (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E)` using `by push_cast; rfl`.

Rewrite using `[this]`. Conclude with `hNb`.
-/
theorem aeGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  intro D I hI
  obtain ⟨N, hN0, hNI, hNb⟩ := exists_nat_mem_mul_integral I hI
  have hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hc0
  refine ⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩
  · intro hmem
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNI
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNb

end GlobalTheory.IdeleGen
