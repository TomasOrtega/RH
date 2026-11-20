import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

open Ideal WittVector

namespace GlobalTheory.PadicComplQuot

/- English proof (translation)
Rewrite using `[← AdicCompletion.ker_evalOneₐ_eq_map _ hI, RingHom.mem_ker]`. Both sides reduce to the same expression.
-/
theorem mem_map_iff_evalOne {A : Type} [CommRing A] (I : Ideal A) (hI : I.FG) (x : AdicCompletion I A) :
    x ∈ I.map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.evalOneₐ I x = 0 := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hI, RingHom.mem_ker]
  rfl

/- English proof (translation)
Use `set I : Ideal A := Ideal.span {(p : A)} with hIdef`. Establish `hfg : I.FG` using `Submodule.fg_span_singleton _`. Establish `hspan : Ideal.span {(p : AdicCompletion I A)} = I.map (algebraMap A (AdicCompletion I A))`. Rewrite using `[hIdef, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hcomm : ∀ a : A, AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a` using `fun a => (AdicCompletion.evalOneₐ I).commutes a`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I r)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq, hspan, mem_map_iff_evalOne I hfg, map_sub, hcomm, ha, sub_self]`. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, mem_map_iff_evalOne I hfg, hcomm, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem quot_completion (p : ℕ) (A : Type) [CommRing A] (_hp : IsSMulRegular A (p : A)) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  set I : Ideal A := Ideal.span {(p : A)} with hIdef
  have hfg : I.FG := Submodule.fg_span_singleton _
  have hspan : Ideal.span {(p : AdicCompletion I A)} = I.map (algebraMap A (AdicCompletion I A)) := by
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hcomm : ∀ a : A, AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a :=
    fun a => (AdicCompletion.evalOneₐ I).commutes a
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I r)
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hspan, mem_map_iff_evalOne I hfg, map_sub, hcomm, ha, sub_self]
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, mem_map_iff_evalOne I hfg, hcomm,
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.PadicComplQuot
