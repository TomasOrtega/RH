import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPlaceEmb

/- English proof (translation)
Introduce `hf`. Use `haveI := hf.isDomain`. Establish `h0 : z * (z - 1) = 0` using `by rw [mul_sub, hz, mul_one, sub_self]`. Break down `mul_eq_zero.1 h0 with h' | h'` into its components or cases. Rewrite `h` using `[h', σ.map_zero, zero_add]`.

Conclude with `zero_ne_one h`. Rewrite `h` using `[sub_eq_zero.1 h', σ.map_one]`. Conclude with `one_ne_zero (add_eq_left.1 h)`.
-/
theorem not_isField_of_idem {A : Type} [CommRing A] (σ : A →+* A) {z : A} (hz : z * z = z) (h : z + σ z = 1) :
    ¬ IsField A := by
  intro hf
  haveI := hf.isDomain
  have h0 : z * (z - 1) = 0 := by rw [mul_sub, hz, mul_one, sub_self]
  rcases mul_eq_zero.1 h0 with h' | h'
  · rw [h', σ.map_zero, zero_add] at h
    exact zero_ne_one h
  · rw [sub_eq_zero.1 h', σ.map_one] at h
    exact one_ne_zero (add_eq_left.1 h)

/- English proof (translation)
Establish `h2 : Module.finrank K (K ⊗[F] E) = 2` using `by rw [Module.finrank_baseChange, hE]`. Take `⟨φ⟩` from `GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := K) h2 (not_isField_of_idem (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom hz h)`. Conclude with `⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩`.
-/
theorem nonempty_algHom_of_idem {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) {z : K ⊗[F] E} (hz : z * z = z)
    (h : z + (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom z = 1) : Nonempty (E →ₐ[F] K) := by
  have h2 : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, hE]
  obtain ⟨φ⟩ := GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := K) h2
    (not_isField_of_idem (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom hz h)
  exact ⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩

/- English proof (translation)
Set `Φ : R ⊗[F] E →+* K ⊗[F] E` to `(Algebra.TensorProduct.map ψ (AlgHom.id F E)).toRingHom`. Set `τ : K ⊗[F] E →+* K ⊗[F] E` to `(Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom`. Establish `hcomm : ∀ x, Φ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom x) = τ (Φ x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a b => rfl`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `nonempty_algHom_of_idem hE σ (z := Φ e) (by rw [← map_mul, he]) ?_` and prove the remaining obligations. Use `congrArg Φ hs` as an intermediate fact.

Rewrite `this` using `[map_add, hcomm]`. Rewrite using `[this, Algebra.TensorProduct.algebraMap_apply]`. Express the relevant statement in the definitionally equal form `ψ ε ⊗ₜ[F] (1 : E) = 1`. Rewrite using `[hψ]`. Both sides reduce to the same expression.
-/
theorem nonempty_algHom_of_idem_map {F E K R : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [CommRing R] [Algebra F R] (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) (ψ : R →ₐ[F] K) {e : R ⊗[F] E}
    {ε : R} (he : e * e = e) (hs : e + (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom e = algebraMap R _ ε)
    (hψ : ψ ε = 1) : Nonempty (E →ₐ[F] K) := by
  let Φ : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ψ (AlgHom.id F E)).toRingHom
  let τ : K ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom
  have hcomm : ∀ x, Φ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom x) = τ (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine nonempty_algHom_of_idem hE σ (z := Φ e) (by rw [← map_mul, he]) ?_
  have := congrArg Φ hs
  rw [map_add, hcomm] at this
  rw [this, Algebra.TensorProduct.algebraMap_apply]
  change ψ ε ⊗ₜ[F] (1 : E) = 1
  rw [hψ]
  rfl

/- English proof (translation)
Introduce `D v ε hε hn`. Choose the witnesses or unpack the hypotheses as in `⟨e, ⟨he, -, -⟩, hsum⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap _ _ ε := by`. Assume the negation of the conclusion as `h`. Conclude with `hn ⟨hε, h⟩`. Take `⟨α, rfl, h1, -⟩` from `hε`.

Conclude with `nonempty_algHom_of_idem_map (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 D.sp.cm.sig ((evalV D.host.F v).comp (sndA D.host.F)) he hsum h1`.
-/
theorem nonempty_algHom_of_not_nonSplitAt :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  intro D v ε hε hn
  obtain ⟨e, ⟨he, -, -⟩, hsum⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap _ _ ε := by
    by_contra h
    exact hn ⟨hε, h⟩
  obtain ⟨α, rfl, h1, -⟩ := hε
  exact nonempty_algHom_of_idem_map (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 D.sp.cm.sig
    ((evalV D.host.F v).comp (sndA D.host.F)) he hsum h1

end GlobalTheory.SplitPlaceEmb

end
