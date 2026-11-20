import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.EigenlineBaseChange

/- English proof (translation)
The claim follows from `isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective`.
-/
theorem isIntegral_coe_iff {M : IntermediateField ℚ ℂ} (x : M) : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm`. Establish `hsm : s ∈ TaylorLogMetric.ellT D M τ` using `hs ▸ Submodule.mem_span_singleton_self s`. Rewrite `hsm` using `[GlobalTheory.Glob.mem_ellT_iff hM]`. Set `g : ∀ y ∈ D.host.AA0, 𝓞 M` to `fun y hy => ⟨s * ⟨_, hM τ (D.host.conj y)⟩, (isIntegral_coe_iff _).1 (hsm y hy)⟩`. Use `set I : Ideal (𝓞 M) := Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} with hI`.

Establish `hg : ∀ y hy, g y hy ∈ I` using `fun y hy => Ideal.subset_span ⟨y, hy, rfl⟩`. Assume the negation of the conclusion as `hI1`. Establish `hI0 : I ≠ ⊥`. Introduce `h`. Establish `h1` using `hg 1 (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D)`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Establish `h2 : (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj 1) = 0` using `congrArg (fun a : 𝓞 M => ((a : M) : ℂ)) h1`. Rewrite `h2` using `[map_one, map_one, mul_one]`. Conclude with `hs0 (Subtype.ext h2)`. Take `⟨x, hx, hx1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := M) hI0 hI1`.

Rewrite `hx` using `[FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)]`. Establish `hxs : x * s ∈ TaylorLogMetric.ellT D M τ`. Rewrite using `[GlobalTheory.Glob.mem_ellT_iff hM]`. Introduce `y hy`. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 (hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hg y hy)))`.

Establish `h1 : IsIntegral ℤ (((c : M) : ℂ))` using `(isIntegral_coe_iff _).2 c.isIntegral_coe`. Establish `h2 : ((c : M) : ℂ) = (x : ℂ) * ((s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y))` using `congrArg (fun a : M => (a : ℂ)) hc`. Rewrite `h1` using `[h2, ← mul_assoc]`. Conclude with `h1`. Rewrite `hxs` using `[hs, Submodule.mem_span_singleton]`.

Take `⟨c, hc⟩` from `hxs`. Use `hx1 ((FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩)` and prove the remaining obligations. Conclude with `mul_right_cancel₀ hs0 hc`.
-/
theorem span_eq_top {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M) (τ : D.what₂.Tau) (s : M)
    (hs : TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}) :
    Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} = ⊤ := by
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hsm : s ∈ TaylorLogMetric.ellT D M τ := hs ▸ Submodule.mem_span_singleton_self s
  rw [GlobalTheory.Glob.mem_ellT_iff hM] at hsm
  let g : ∀ y ∈ D.host.AA0, 𝓞 M := fun y hy =>
    ⟨s * ⟨_, hM τ (D.host.conj y)⟩, (isIntegral_coe_iff _).1 (hsm y hy)⟩
  set I : Ideal (𝓞 M) := Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
    ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} with hI
  have hg : ∀ y hy, g y hy ∈ I := fun y hy => Ideal.subset_span ⟨y, hy, rfl⟩
  by_contra hI1
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := hg 1 (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D)
    rw [h, Ideal.mem_bot] at h1
    have h2 : (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj 1) = 0 :=
      congrArg (fun a : 𝓞 M => ((a : M) : ℂ)) h1
    rw [map_one, map_one, mul_one] at h2
    exact hs0 (Subtype.ext h2)
  obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := M) hI0 hI1
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)] at hx
  have hxs : x * s ∈ TaylorLogMetric.ellT D M τ := by
    rw [GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
      (hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hg y hy)))
    have h1 : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
    have h2 : ((c : M) : ℂ) = (x : ℂ) * ((s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)) :=
      congrArg (fun a : M => (a : ℂ)) hc
    rw [h2, ← mul_assoc] at h1
    exact h1
  rw [hs, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  refine hx1 ((FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩)
  exact mul_right_cancel₀ hs0 hc

/- English proof (translation)
Introduce `D M M' _ _ hle hM τ s hs`. Establish `hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M'` using `fun τ x => hle (hM τ x)`. Establish `hs0 : s ≠ 0` using `GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm`. Establish `hs0' : (s : ℂ) ≠ 0` using `fun h => hs0 (Subtype.ext h)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[GlobalTheory.Glob.mem_ellT_iff hM']`. Establish `key : ∀ a ∈ Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)}, IsIntegral ℤ ((x : ℂ) * (s : ℂ)⁻¹ * ((a : M) : ℂ))`. Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem a ha`. Take `⟨y, hy, e⟩` from `ha`. Rewrite using `[e, mul_assoc, inv_mul_cancel_left₀ hs0']`. Conclude with `hx y hy`. Consider the case `zero => simpa using isIntegral_zero`.

Consider the case `add a b _ _ ha hb`. Establish `e : (((a + b : 𝓞 M) : M) : ℂ) = ((a : M) : ℂ) + ((b : M) : ℂ)` using `rfl`. Rewrite using `[e, mul_add]`. Conclude with `ha.add hb`. Consider the case `smul c a _ ha`.

Establish `hc : IsIntegral ℤ (((c : M) : ℂ))` using `(isIntegral_coe_iff _).2 c.isIntegral_coe`. Establish `e : (((c • a : 𝓞 M) : M) : ℂ) = ((c : M) : ℂ) * ((a : M) : ℂ)` using `rfl`. Rewrite using `[e, mul_left_comm]`. Conclude with `hc.mul ha`. Establish `h1` using `key 1 (by rw [span_eq_top hM τ s hs]; trivial)`.

Establish `e : (((1 : 𝓞 M) : M) : ℂ) = 1` using `rfl`. Rewrite `h1` using `[e, mul_one]`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨⟨x * (⟨(s : ℂ), hle s.2⟩ : M')⁻¹, (isIntegral_coe_iff _).1 h1⟩, ?_⟩` and prove the remaining obligations. Conclude with `inv_mul_cancel_right₀ (fun h => hs0' (congrArg (fun a : M' => (a : ℂ)) h)) x`.

Rewrite using `[Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM']`. Conclude with `(GlobalTheory.Glob.mem_ellT_iff hM τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)`.
-/
theorem ellT_eq_span_of_le : ∀ (D : D7) (M M' : IntermediateField ℚ ℂ) [NumberField M] [NumberField M'] (hle : M ≤ M'), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s} → TaylorLogMetric.ellT D M' τ = Submodule.span (𝓞 M') {(⟨(s : ℂ), hle s.2⟩ : M')} := by
  intro D M M' _ _ hle hM τ s hs
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M' := fun τ x => hle (hM τ x)
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hs0' : (s : ℂ) ≠ 0 := fun h => hs0 (Subtype.ext h)
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM'] at hx
    have key : ∀ a ∈ Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
        ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)},
        IsIntegral ℤ ((x : ℂ) * (s : ℂ)⁻¹ * ((a : M) : ℂ)) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, hy, e⟩ := ha
        rw [e, mul_assoc, inv_mul_cancel_left₀ hs0']
        exact hx y hy
      | zero => simpa using isIntegral_zero
      | add a b _ _ ha hb =>
        have e : (((a + b : 𝓞 M) : M) : ℂ) = ((a : M) : ℂ) + ((b : M) : ℂ) := rfl
        rw [e, mul_add]
        exact ha.add hb
      | smul c a _ ha =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
        have e : (((c • a : 𝓞 M) : M) : ℂ) = ((c : M) : ℂ) * ((a : M) : ℂ) := rfl
        rw [e, mul_left_comm]
        exact hc.mul ha
    have h1 := key 1 (by rw [span_eq_top hM τ s hs]; trivial)
    have e : (((1 : 𝓞 M) : M) : ℂ) = 1 := rfl
    rw [e, mul_one] at h1
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨(s : ℂ), hle s.2⟩ : M')⁻¹, (isIntegral_coe_iff _).1 h1⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hs0' (congrArg (fun a : M' => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM']
    exact (GlobalTheory.Glob.mem_ellT_iff hM τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)

end GlobalTheory.EigenlineBaseChange
