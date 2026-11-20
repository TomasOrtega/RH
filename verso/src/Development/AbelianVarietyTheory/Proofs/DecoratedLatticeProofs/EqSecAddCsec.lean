import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

/- English proof (translation)
Establish `h` using `(idem_iff q a).1 ha`. Rewrite using `[q.sec_pr, q.sec_pr, map_mul, cA_cA]`. Use `conv_lhs => rw [← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  have h := (idem_iff q a).1 ha
  rw [q.sec_pr, q.sec_pr, map_mul, cA_cA]
  conv_lhs => rw [← h]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[q.sec_pr, RingHom.map_mul]`. Conclude with `mul_mem_intAE (e_mem_intAt q).2 h.2`.

Rewrite using `[q.sec_pr, RingHom.map_mul]`. Conclude with `mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sec_add_csec q ha, RingHom.map_add]`.

Conclude with `add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))`.
-/
theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 h.2
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [eq_sec_add_csec q ha, RingHom.map_add]
    exact add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))

/- English proof (translation)
Establish `he` using `e_mem_intAt q`. Establish `hpe : q.pr q.e = 1` using `by rw [← sec_one q, q.pr_sec]`. Establish `h1` using `((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1`. Establish `h2` using `((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1`. Rewrite `h1`, `h2` using `[map_mul, hpe, mul_one]`.

Establish `hne : D.host.xi0 ≠ 0` using `GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero`. Establish `hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1`. Rewrite using `[← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]`. Express the relevant statement in the definitionally equal form `valuation k (q.pr (incA D D.host.xi0)) = 1`. Establish `v1` using `(Valuation.mem_integer_iff _ _).1 h1`.

Establish `v2` using `(Valuation.mem_integer_iff _ _).1 h2`. Establish `v3` using `congrArg (valuation k) hprod`. Rewrite `v3` using `[map_mul, map_one]`. Use `le_antisymm v1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Use `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one` as an intermediate fact. Rewrite `this` using `[v3, mul_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
