import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.ScRefExists.LG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `v`. Use `show ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `v.valuation_le_one r`.
-/
theorem int_mem_intAd (r : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro v
  show ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

/- English proof (translation)
Use `HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_` and prove the remaining obligations. Establish `hv : ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F` using `h v`. Rewrite `hv` using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Then use the resulting hypothesis.
-/
theorem int_of_mem_intAd (x : F) (h : algebraMap F (Af F) x ∈ Formalism.UG.intAd F) :
    x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  have hv : ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := h v
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv

def lam (a : E) : E →ₗ[F] F := (Algebra.trace F E) ∘ₗ (LinearMap.mulLeft F a)

def Phi (a : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map (lam a) LinearMap.id

/- English proof (translation)
Simplify using `[Phi, lam, Algebra.smul_def]`.
-/
theorem Phi_tmul (a x : E) (c : Af F) :
    Phi a (x ⊗ₜ[F] c) = algebraMap F (Af F) (Algebra.trace F E (a * x)) * c := by
  simp [Phi, lam, Algebra.smul_def]

def Gens : Submonoid (E ⊗[F] Af F) where
  carrier := {x | ∃ o : 𝓞 E, ∃ c ∈ Formalism.UG.intAd F, x = (algebraMap (𝓞 E) E o) ⊗ₜ[F] c}
  one_mem' := ⟨1, 1, one_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  mul_mem' := by
    rintro _ _ ⟨o, c, hc, rfl⟩ ⟨o', c', hc', rfl⟩
    exact ⟨o * o', c * c', mul_mem hc hc', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

/- English proof (translation)
Establish `hy' : y ∈ AddSubgroup.closure ((Submonoid.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪ Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) : Set _))` using `Subring.mem_closure_iff.mp hy`. Establish `hle : Submonoid.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪ Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) ≤ (Gens : Submonoid _)`. Rewrite using `[Submonoid.closure_le]`. Introduce and unpack `_ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)`. Conclude with `⟨o, 1, one_mem _, rfl⟩`.

Conclude with `⟨1, c, hc, by simp⟩`. Establish `hy2` using `AddSubgroup.closure_mono hle hy'`. Use `clear hy hy' hle`. Proceed by induction on `hy2 using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨o, c, hc, rfl⟩` from `hx`. Rewrite using `[Phi_tmul]`. Take `⟨r, hr⟩` from `ha o`. Rewrite using `[← hr]`. Conclude with `mul_mem (int_mem_intAd r) hc`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`.

Conclude with `neg_mem hx`.
-/
theorem Phi_mem (a : E) (ha : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
    (algebraMap (𝓞 F) F).range) {y : E ⊗[F] Af F} (hy : y ∈ IntAf F E) :
    Phi a y ∈ Formalism.UG.intAd F := by
  have hy' : y ∈ AddSubgroup.closure ((Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) : Set _)) :=
    Subring.mem_closure_iff.mp hy
  have hle : Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) ≤ (Gens : Submonoid _) := by
    rw [Submonoid.closure_le]
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact ⟨o, 1, one_mem _, rfl⟩
    · exact ⟨1, c, hc, by simp⟩
  have hy2 := AddSubgroup.closure_mono hle hy'
  clear hy hy' hle
  induction hy2 using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, c, hc, rfl⟩ := hx
    rw [Phi_tmul]
    obtain ⟨r, hr⟩ := ha o
    rw [← hr]
    exact mul_mem (int_mem_intAd r) hc
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
Establish `h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`. Establish `hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero (𝓞 F) F h1`. Establish `hmem : t ∈ FractionalIdeal.dual (𝓞 F) F (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E))`. Rewrite using `[FractionalIdeal.mem_dual hd]`. Introduce `a ha`.

Rewrite `ha` using `[FractionalIdeal.mem_dual h1]`. Establish `ha' : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈ (algebraMap (𝓞 F) F).range`. Introduce `o`. Use `ha (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).mpr ⟨o, rfl⟩)` as an intermediate fact. Simplify `this` using `[Algebra.traceForm_apply]`.

Establish `hP` using `Phi_mem a ha' ht`. Establish `hx : Phi a (Formalism.UG.inclE (F` using `F) (Af F) t) = algebraMap F (Af F) (Algebra.trace F E (a * t)) := by`. Simplify using `[Formalism.UG.inclE, Phi_tmul]`. Rewrite `hP` using `[hx]`. Use `int_of_mem_intAd _ hP` as an intermediate fact.

Simplify `this` using `[Algebra.traceForm_apply, mul_comm]`. Rewrite `hmem` using `[FractionalIdeal.dual_dual]`. Conclude with `(FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp hmem`.
-/
theorem locGlob_gen (t : E) (ht : Formalism.UG.inclE (F := F) (Af F) t ∈ IntAf F E) :
    ∃ s : 𝓞 E, algebraMap (𝓞 E) E s = t := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 F) F h1
  have hmem : t ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    have ha' : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
        (algebraMap (𝓞 F) F).range := by
      intro o
      have := ha (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).mpr ⟨o, rfl⟩)
      simpa [Algebra.traceForm_apply] using this
    have hP := Phi_mem a ha' ht
    have hx : Phi a (Formalism.UG.inclE (F := F) (Af F) t) =
        algebraMap F (Af F) (Algebra.trace F E (a * t)) := by
      simp [Formalism.UG.inclE, Phi_tmul]
    rw [hx] at hP
    have := int_of_mem_intAd _ hP
    simpa [Algebra.traceForm_apply, mul_comm] using this
  rw [FractionalIdeal.dual_dual] at hmem
  exact (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp hmem

end Gen

/- English proof (translation)
Introduce `I t ht`. Conclude with `locGlob_gen t ht`.
-/
theorem local_global_principle_alt : PI.ScRefExists.Sk.LocGlob := by
  intro I t ht
  exact locGlob_gen t ht

end PI.ScRefExists.LG
