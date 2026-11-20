import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

/- English proof (translation)
Introduce `R _ F E E' f`. Take `⟨-, cl, hsurj, heq, hzero, hpull⟩` from `GlobalTheory.EtC.HCElements.main R F`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Use `⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `(hf n).2 (cl E n z hz)`. Take `⟨c, hc, rfl⟩` from `hsurj E' n x`. Take `⟨h, hp⟩` from `hpull E E' f n c hc`. Rewrite `hx` using `[hp, heq]`. Take `⟨y, hy⟩` from `hx`.

Conclude with `⟨c, y, hc, hy⟩`. Take `⟨h, hp⟩` from `hpull E E' f n c hc`. Establish `h0 : cl E n (((HC R F).map f.op).f n c) h = 0` using `(hzero E n _ h).2 ⟨y, hy⟩`. Rewrite `h0` using `[← hp]`. Establish `: cl E' n c hc = 0` using `(hf n).1 (h0.trans (map_zero _).symm)`.

Take `⟨b, hb⟩` from `(hzero E' n c hc).1 this`. Conclude with `⟨b, hb.symm⟩`. Introduce and unpack `⟨hS, hI⟩ n`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨c, hc, rfl⟩` from `hsurj E' n x`. Take `⟨h, hp⟩` from `hpull E E' f n c hc`. Rewrite `hx` using `[hp, hzero]`. Take `⟨b, hb⟩` from `hI n c hc hx`.

Conclude with `(hzero E' n c hc).2 ⟨b, hb.symm⟩`. Introduce `x`. Take `⟨z, hz, rfl⟩` from `hsurj E n x`. Take `⟨c, y, hc, hcy⟩` from `hS n z hz`. Take `⟨h, hp⟩` from `hpull E E' f n c hc`.

Use `⟨cl E' n c hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, heq]`. Conclude with `⟨y, hcy⟩`.
-/
theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
