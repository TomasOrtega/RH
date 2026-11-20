import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hF`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z S p _ w w' h1 h2`. Unfold `IsWt at *`. Introduce `A φ hφ`.

Take `⟨ψ1, hψ1, e1⟩` from `h1 A φ hφ`. Take `⟨ψ2, hψ2, e2⟩` from `h2 A φ hφ`. Use `⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ x`. Use `haveI := A.finite`.

Establish `hfin` using `hF A.r Ω x`. Rewrite using `[Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]`. Use `finsum_congr fun z => finsum_congr fun _ => ?_` and prove the remaining obligations. Use `show _ = (w Ω _ + w' Ω _) * _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `Z S p _ d w h1`. Unfold `IsWt at *`. Introduce `A φ hφ`. Take `⟨ψ1, hψ1, e1⟩` from `h1 A φ hφ`. Use `⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩` and prove the remaining obligations.

Introduce `Ω _ _ x`. Rewrite using `[Function.comp_apply, e1, mul_finsum_mem]`. Use `finsum_congr fun z => finsum_congr fun _ => ?_` and prove the remaining obligations. Use `show _ = d * w Ω _ * _`. Expand and normalize the polynomial expressions, which then agree.

Introduce `Z S p _ d`. Unfold `IsWt`. Introduce `A φ hφ`. Use `haveI : IsIso A.r := by`. Rewrite using `[← A.pb.isoPullback_hom_snd]`.

Use `infer_instance`. Use `⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ x`. Establish `hs : fib A.r x = {x ≫ inv A.r}`. Use extensionality with `z`.

Use `show z ≫ A.r = x ↔ z = x ≫ inv A.r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Introduce and unpack `rfl`.

Simplify using the standard rewrite rules. Rewrite using `[hs, finsum_mem_singleton, pt_comp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtLin_of :
    FibFin → WtLin := by
  intro hF
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' h1 h2
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    obtain ⟨ψ2, hψ2, e2⟩ := h2 A φ hφ
    refine ⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩
    intro Ω _ _ x
    haveI := A.finite
    have hfin := hF A.r Ω x
    rw [Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = (w Ω _ + w' Ω _) * _
    ring
  · intro Z S p _ d w h1
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    refine ⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩
    intro Ω _ _ x
    rw [Function.comp_apply, e1, mul_finsum_mem]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = d * w Ω _ * _
    ring
  · intro Z S p _ d
    unfold IsWt
    intro A φ hφ
    haveI : IsIso A.r := by
      rw [← A.pb.isoPullback_hom_snd]
      infer_instance
    refine ⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩
    intro Ω _ _ x
    have hs : fib A.r x = {x ≫ inv A.r} := by
      ext z
      show z ≫ A.r = x ↔ z = x ≫ inv A.r
      constructor
      · rintro rfl
        simp
      · rintro rfl
        simp
    rw [hs, finsum_mem_singleton, pt_comp]
    rfl
