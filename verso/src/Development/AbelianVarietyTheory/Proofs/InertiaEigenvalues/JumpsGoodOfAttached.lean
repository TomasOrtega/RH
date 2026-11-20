import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨b, hb⟩` from `R.m_even`. Establish `h2` using `R.two_le_m`. Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`.
-/
theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

/- English proof (translation)
Rewrite using `[Multiset.map_map]`. Use `conv_rhs => rw [← Multiset.map_id S]`. Use `Multiset.map_congr rfl fun z hz => ?_` and prove the remaining obligations. Take `⟨n, rfl⟩` from `h z hz`. Simplify using the standard rewrite rules.
-/
theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

/- English proof (translation)
Introduce and unpack `D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩`. Set `S : (D.host.E →+* ℂ) → Multiset ℂ` to `fun τc => (D.naut.infG π τc).map fun z => -z - ((((1 - (D.R.t : ℝ)) / 2 : ℝ)) : ℂ)`. Establish `hint : ∀ τc, ∀ w ∈ S τc, ∃ n : ℤ, w = (n : ℂ)`. Introduce `τc w hw`. Take `⟨z, hz, rfl⟩` from `Multiset.mem_map.1 hw`.

Take `⟨n, rfl⟩` from `(((D.naut.ralg_def π).1 hR.ralg) τc).2 z hz`. Take `⟨a, ha⟩` from `odd_rank D.R`. Take `⟨b, hb⟩` from `D.R.t_odd`. Use `⟨-n - a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective (fun n : ℤ => (n : ℂ))` using `Int.cast_injective`. Establish `hcast : ∀ τc, ((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S τc` using `fun τc => map_round_cast _ (hint τc)`. Use `⟨ι, fun τc => (S τc).map fun z => ⌊z.re⌋, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv τ τc hτ a`. Rewrite using `[hA.jumps v hv τ τc hτ a]`. Use `Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) ((S τc).map fun z => ⌊z.re⌋) hinj a` as an intermediate fact. Rewrite `this` using `[hcast]`. Rewrite using `[← this]`.

Introduce `τc`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [S, Multiset.card_map, D.naut.infG_card]`. Apply `Multiset.map_injective hinj` to reduce the goal to its premises. Rewrite using `[hcast]`.

Establish `: (((S τc).map fun z => ⌊z.re⌋).map (fun a => (D.R.t : ℤ) - 1 - a)).map (fun n : ℤ => (n : ℂ)) = (((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ))).map (fun w => (D.R.t : ℂ) - 1 - w)`. Simplify using `only [Multiset.map_map, Function.comp_def]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[this, hcast]`.

Simplify using `only [S, hR.anti τc, Multiset.map_map, Function.comp_def]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `a ha`.

Establish `h1 : (a : ℂ) ∈ S τc`. Rewrite using `[← hcast τc]`. Conclude with `Multiset.mem_map_of_mem _ ha`. Take `⟨z, hz, hza⟩` from `Multiset.mem_map.1 h1`. Use `hR.window τc z hz a ?_` and prove the remaining obligations.

Rewrite using `[← hza]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_jumpsAre_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J := by
  classical
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩
  let S : (D.host.E →+* ℂ) → Multiset ℂ := fun τc =>
    (D.naut.infG π τc).map fun z => -z - ((((1 - (D.R.t : ℝ)) / 2 : ℝ)) : ℂ)
  have hint : ∀ τc, ∀ w ∈ S τc, ∃ n : ℤ, w = (n : ℂ) := by
    intro τc w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hw
    obtain ⟨n, rfl⟩ := (((D.naut.ralg_def π).1 hR.ralg) τc).2 z hz
    obtain ⟨a, ha⟩ := odd_rank D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨-n - a + b, ?_⟩
    rw [ha, hb]
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℤ => (n : ℂ)) := Int.cast_injective
  have hcast : ∀ τc, ((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S τc :=
    fun τc => map_round_cast _ (hint τc)
  refine ⟨ι, fun τc => (S τc).map fun z => ⌊z.re⌋, ?_, ?_⟩
  · intro v hv τ τc hτ a
    rw [hA.jumps v hv τ τc hτ a]
    have := Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) ((S τc).map fun z => ⌊z.re⌋) hinj a
    rw [hcast] at this
    rw [← this]
  · intro τc
    refine ⟨?_, ?_, ?_⟩
    · simp only [S, Multiset.card_map, D.naut.infG_card]
    · apply Multiset.map_injective hinj
      rw [hcast]
      have : (((S τc).map fun z => ⌊z.re⌋).map (fun a => (D.R.t : ℤ) - 1 - a)).map (fun n : ℤ => (n : ℂ))
          = (((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ))).map (fun w => (D.R.t : ℂ) - 1 - w) := by
        simp only [Multiset.map_map, Function.comp_def]
        push_cast
        rfl
      rw [this, hcast]
      simp only [S, hR.anti τc, Multiset.map_map, Function.comp_def]
      refine Multiset.map_congr rfl fun z _ => ?_
      push_cast
      ring
    · intro a ha
      have h1 : (a : ℂ) ∈ S τc := by
        rw [← hcast τc]
        exact Multiset.mem_map_of_mem _ ha
      obtain ⟨z, hz, hza⟩ := Multiset.mem_map.1 h1
      refine hR.window τc z hz a ?_
      rw [← hza]
      push_cast
      ring

end GlobalTheory.TripleGal.Jumps
