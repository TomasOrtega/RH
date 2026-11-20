import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite `hx`, the goal using `[Submodule.mem_one]`. Take `⟨y, rfl⟩` from `hx`. Establish `hy : IsIntegral ℤ (e (algebraMap (𝓞 E) E y))` using `(RingOfIntegers.isIntegral_coe y).map (e : E →+* E).toIntAlgHom`. Conclude with `⟨⟨_, hy⟩, rfl⟩`.
-/
theorem ringEquiv_mem_one (e : E ≃+* E) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    e x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_one] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  have hy : IsIntegral ℤ (e (algebraMap (𝓞 E) E y)) :=
    (RingOfIntegers.isIntegral_coe y).map (e : E →+* E).toIntAlgHom
  exact ⟨⟨_, hy⟩, rfl⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]`. Introduce `a ha`. Establish `ha' : e.symm a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite `ha`, the goal using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]`. Conclude with `ringEquiv_mem_one e.symm ha`.

Establish `h` using `hx _ ha'`. Set `f : E ≃ₐ[ℚ] E` to `AlgEquiv.ofRingEquiv (f := e) (fun q => map_ratCast e q)`. Establish `key : Algebra.traceForm ℚ E (e x) a = Algebra.traceForm ℚ E x (e.symm a)`. Simplify using `only [Algebra.traceForm_apply]`. Establish `: e x * a = f (x * e.symm a)`.

Rewrite using `[map_mul]`. Use `show e x * a = e x * e (e.symm a)`. Rewrite using `[RingEquiv.apply_symm_apply]`. Rewrite using `[this, Algebra.trace_eq_of_algEquiv]`. Rewrite using `[key]`.

Conclude with `h`.
-/
theorem ringEquiv_mem_dual (e : E ≃+* E) {x : E}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    e x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have ha' : e.symm a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at ha ⊢
    exact ringEquiv_mem_one e.symm ha
  have h := hx _ ha'
  let f : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := e) (fun q => map_ratCast e q)
  have key : Algebra.traceForm ℚ E (e x) a = Algebra.traceForm ℚ E x (e.symm a) := by
    simp only [Algebra.traceForm_apply]
    have : e x * a = f (x * e.symm a) := by
      rw [map_mul]
      show e x * a = e x * e (e.symm a)
      rw [RingEquiv.apply_symm_apply]
    rw [this, Algebra.trace_eq_of_algEquiv]
  rw [key]; exact h

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro x hx`. Rewrite `hx`, the goal using `[pow_zero]`. Conclude with `ringEquiv_mem_one e hx`.

Consider the case `succ j ih`. Introduce `x hx`. Rewrite `hx`, the goal using `[pow_succ]`. Use `Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `Submodule.mul_mem_mul (ih m hm) (hM n hn)`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`.
-/
theorem ringEquiv_mem_pow (e : E ≃+* E) (M : Submodule (𝓞 E) E) (hM : ∀ x ∈ M, e x ∈ M) :
    ∀ (j : ℕ) (x : E), x ∈ M ^ j → e x ∈ M ^ j := by
  intro j
  induction j with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact ringEquiv_mem_one e hx
  | succ j ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (ih m hm) (hM n hn)
    · rw [map_add]; exact Submodule.add_mem _ ha hb

/- English proof (translation)
Establish `hd : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ = FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]`. Rewrite `hx`, the goal using `[dInv, hd, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]`. Conclude with `ringEquiv_mem_pow e _ (fun y hy => ringEquiv_mem_dual e hy) j x hx`.
-/
theorem ringEquiv_mem_dInv (e : E ≃+* E) (j : ℕ) (x : E) (hx : x ∈ dInv E j) : e x ∈ dInv E j := by
  have hd : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  rw [dInv, hd, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow] at hx ⊢
  exact ringEquiv_mem_pow e _ (fun y hy => ringEquiv_mem_dual e hy) j x hx

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ j x hx`. Establish `hb : Function.Bijective ((σ : E →+* E).toRatAlgHom)` using `AlgHom.bijective _`. Conclude with `ringEquiv_mem_dInv (RingEquiv.ofBijective (σ : E →+* E) hb) j x hx`.
-/
theorem conj_mem_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  intro F E _ _ _ _ _ σ _ j x hx
  have hb : Function.Bijective ((σ : E →+* E).toRatAlgHom) := AlgHom.bijective _
  exact ringEquiv_mem_dInv (RingEquiv.ofBijective (σ : E →+* E) hb) j x hx

end GlobalTheory.SnMass.VolN
