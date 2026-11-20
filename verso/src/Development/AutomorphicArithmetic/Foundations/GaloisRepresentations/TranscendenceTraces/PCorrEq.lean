import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hIF hTR hTP hWP q _ n i S Y B bS bY _ _ ι _ c m hc hq D hD hcyc y`. Take `⟨G, pG, fG, h, hpG, hh, hp, hf, hmono⟩` from `hIF bS bY ι (fun a => (c a).Z) (fun a => (c a).p) (fun a => (c a).f) (fun a => (c a).fin) hc`. Use `haveI := hpG`. Establish `hwt : ∀ a, IsWt (h a ≫ pG) (c a).w`. Introduce `a`.

Rewrite using `[hp a]`. Conclude with `(c a).wt`. Establish `key : ∀ a, (c a).op q n i y = tr pG (Wt.push (h a) (c a).w) q n i (pull (ZMod q) (sch.map fG) (tw q i) n y)`. Introduce `a`. Use `haveI := hh a`.

Rewrite using `[← hTP q n i (h a) pG (c a).w (hwt a) hq, ← pull_comp, ← Functor.map_comp, hf a]`. Simplify using `only [Corr.op, AddMonoidHom.comp_apply]`. Rewrite using `[hp a]`. Simplify using `only [key]`. Use `hTR q n i pG ι (fun a => Wt.push (h a) (c a).w) m (fun a => by haveI := hh a; exact hWP (h a) pG (c a).w (hwt a)) hq D hD ?_ _` and prove the remaining obligations.

Introduce `Ω _ _ z hz`. Rewrite using `[← hcyc Ω (z ≫ pG) (z ≫ fG) hz]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hs : fib (h a) z = {z' | z' ≫ (c a).p = z ≫ pG ∧ z' ≫ (c a).f = z ≫ fG}`.

Use extensionality with `z'`. Simplify using `only [fib, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨by rw [Category.assoc, hp a], by rw [Category.assoc, hf a]⟩`.

Introduce and unpack `⟨h1, h2⟩`. Apply `hmono` to reduce the goal to its premises. Rewrite using `[Category.assoc, hp a, h1]`. Rewrite using `[Category.assoc, hf a, h2]`. Simplify using `only [Wt.push, Corr.cyc]`.

Rewrite using `[hs]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.corrEq_of :
    ImageFin → TrRel → TrPush → WtPush → CorrEq := by
  intro hIF hTR hTP hWP q _ n i S Y B bS bY _ _ ι _ c m hc hq D hD hcyc y
  obtain ⟨G, pG, fG, h, hpG, hh, hp, hf, hmono⟩ :=
    hIF bS bY ι (fun a => (c a).Z) (fun a => (c a).p) (fun a => (c a).f) (fun a => (c a).fin) hc
  haveI := hpG
  have hwt : ∀ a, IsWt (h a ≫ pG) (c a).w := by
    intro a
    rw [hp a]
    exact (c a).wt
  have key : ∀ a, (c a).op q n i y =
      tr pG (Wt.push (h a) (c a).w) q n i (pull (ZMod q) (sch.map fG) (tw q i) n y) := by
    intro a
    haveI := hh a
    rw [← hTP q n i (h a) pG (c a).w (hwt a) hq, ← pull_comp, ← Functor.map_comp, hf a]
    simp only [Corr.op, AddMonoidHom.comp_apply]
    rw [hp a]
  simp only [key]
  refine hTR q n i pG ι (fun a => Wt.push (h a) (c a).w) m
    (fun a => by haveI := hh a; exact hWP (h a) pG (c a).w (hwt a)) hq D hD ?_ _
  intro Ω _ _ z hz
  rw [← hcyc Ω (z ≫ pG) (z ≫ fG) hz]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hs : fib (h a) z = {z' | z' ≫ (c a).p = z ≫ pG ∧ z' ≫ (c a).f = z ≫ fG} := by
    ext z'
    simp only [fib, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact ⟨by rw [Category.assoc, hp a], by rw [Category.assoc, hf a]⟩
    · rintro ⟨h1, h2⟩
      apply hmono
      · rw [Category.assoc, hp a, h1]
      · rw [Category.assoc, hf a, h2]
  simp only [Wt.push, Corr.cyc]
  rw [hs]
