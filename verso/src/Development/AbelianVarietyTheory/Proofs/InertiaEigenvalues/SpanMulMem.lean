import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development

namespace GlobalTheory.SpanMulInertiaEigenvalues

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Unfold `Formalism.L2.SG.LocVol.OEv at *`. Rewrite `*` using `[SetLike.mem_coe]`. Use `set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ with hS`. Establish `hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S`. Introduce and unpack `_ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩`.

Use `⟨x * y, Set.mem_univ _, ?_⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _`. Rewrite using `[map_mul, map_mul]`. Establish `key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S, x * y ∈ Submodule.span (v.adicCompletionIntegers F) S`. Introduce `x hx y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (hSmul x hx y hy)`. Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => rw [mul_add]`. Conclude with `Submodule.add_mem _ h1 h2`.

Consider the case `smul c y _ h => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c h`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact key x hx b hb`. Consider the case `zero => simp`.

Consider the case `add x z _ _ h1 h2 => rw [add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c h`.
-/
theorem span_mul_mem {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (ha : a ∈ Formalism.L2.SG.LocVol.OEv v) (hb : b ∈ Formalism.L2.SG.LocVol.OEv v) :
    a * b ∈ Formalism.L2.SG.LocVol.OEv v := by
  unfold Formalism.L2.SG.LocVol.OEv at *
  rw [SetLike.mem_coe] at *
  set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ
    with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    refine ⟨x * y, Set.mem_univ _, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _
    rw [map_mul, map_mul]
  have key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S,
      x * y ∈ Submodule.span (v.adicCompletionIntegers F) S := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hSmul x hx y hy)
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  induction ha using Submodule.span_induction with
  | mem x hx => exact key x hx b hb
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/- English proof (translation)
Introduce `v _ _ ha hb` and use `span_mul_mem v ha hb`.
-/
theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}, a ∈ Formalism.L2.SG.LocVol.OEv v → b ∈ Formalism.L2.SG.LocVol.OEv v → a * b ∈ Formalism.L2.SG.LocVol.OEv v :=
  fun v _ _ ha hb => span_mul_mem v ha hb

end GlobalTheory.SpanMulInertiaEigenvalues
