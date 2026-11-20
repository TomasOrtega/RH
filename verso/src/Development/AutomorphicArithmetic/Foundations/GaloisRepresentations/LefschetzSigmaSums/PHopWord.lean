import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.G3 (Tower Th)

variable {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ] (X : Tower B Γ) (T : Th.{0} B ℂ)

/- English proof (translation)
Establish `h` using `(hL X T hT j 0 0 0 hz hz).2`. Simplify using `using h`.
-/
private theorem hecke_zero (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ)) :
    X.hecke T j 0 = 0 := by
  have h := (hL X T hT j 0 0 0 hz hz).2
  simpa using h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨by simpa using hz, by simpa using hecke_zero X T hL hT j hz⟩`. Consider the case `insert a s ha ih`. Take `⟨h1, h2⟩` from `ih fun i hi => hf i (Finset.mem_insert_of_mem hi)`. Establish `h3` using `hsm (c a) (f a) (hf a (Finset.mem_insert_self a s))`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `⟨hadd _ _ h3 h1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hL X T hT j _ _ 0 h3 h1).1, h2, (hL X T hT j (f a) (f a) (c a) (hf a (Finset.mem_insert_self a s)) (hf a (Finset.mem_insert_self a s))).2]`.
-/
private theorem hecke_sum (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ))
    (hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f'))
    (hsm : ∀ (c : ℂ) (f : Γ → ℂ), X.IsFn j f → X.IsFn j (c • f))
    {I : Type} (s : Finset I) (f : I → Γ → ℂ) (c : I → ℂ) (hf : ∀ i ∈ s, X.IsFn j (f i)) :
    X.IsFn j (∑ i ∈ s, c i • f i) ∧ X.hecke T j (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • X.hecke T j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using hz, by simpa using hecke_zero X T hL hT j hz⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 := hsm (c a) (f a) (hf a (Finset.mem_insert_self a s))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hadd _ _ h3 h1, ?_⟩
    rw [(hL X T hT j _ _ 0 h3 h1).1, h2,
      (hL X T hT j (f a) (f a) (c a) (hf a (Finset.mem_insert_self a s)) (hf a (Finset.mem_insert_self a s))).2]

end UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `hR hL hM B Γ _ X T hT j`. Take `⟨-, hz, hfg, hsm⟩` from `hR X ℂ j`. Establish `hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f')` using `fun f f' a b => (hfg f f' a b).1`. Use `⟨fun m f c hf => hecke_sum X T hL hT j hz hadd hsm Finset.univ f c fun i _ => hf i, ?_⟩` and prove the remaining obligations. Introduce `J ψ f hψ hf`.

Establish `hw : ∀ w : List J, X.IsFn j (wordFn (X.K j) ψ w f) ∧ X.hecke T j (wordFn (X.K j) ψ w f) = (w.map fun i => X.hecke T j (ψ i)).prod * X.hecke T j f`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => exact ⟨hf, by simp [wordFn]⟩`. Consider the case `cons i w ih`.

Take `⟨h1, h2⟩` from `ih`. Establish `e : wordFn (X.K j) ψ (i :: w) f = UpperTheory.Gal.G3.conv (X.K j) (ψ i) (wordFn (X.K j) ψ w f)` using `rfl`. Rewrite using `[e]`. Use `⟨(hfg _ _ (hψ i) h1).2, ?_⟩` and prove the remaining obligations. Rewrite using `[hM X T hT j _ _ (hψ i) h1, h2, List.map_cons, List.prod_cons, mul_assoc]`.

Use `⟨hw, fun s => ?_⟩` and prove the remaining obligations. Establish `hs` using `hecke_sum X T hL hT j hz hadd hsm s.support (fun w => wordFn (X.K j) ψ w f) s fun w _ => (hw w).1`. Establish `e : polyFn (X.K j) ψ s f = ∑ w ∈ s.support, s w • wordFn (X.K j) ψ w f` using `rfl`. Rewrite using `[e]`. Use `⟨hs.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs.2]`. Unfold `UpperTheory.Gal.CertificateRingHomMap.wop Finsupp.sum`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(hw w).2, smul_mul_assoc]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.hopWord_of :
    UpperTheory.Gal.G3.FnRing → UpperTheory.Gal.G3.HopLin.{0} → UpperTheory.Gal.G3.HopMul.{0} → HopWord := by
  intro hR hL hM B Γ _ X T hT j
  obtain ⟨-, hz, hfg, hsm⟩ := hR X ℂ j
  have hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f') := fun f f' a b => (hfg f f' a b).1
  refine ⟨fun m f c hf => hecke_sum X T hL hT j hz hadd hsm Finset.univ f c fun i _ => hf i, ?_⟩
  intro J ψ f hψ hf
  have hw : ∀ w : List J, X.IsFn j (wordFn (X.K j) ψ w f) ∧
      X.hecke T j (wordFn (X.K j) ψ w f) = (w.map fun i => X.hecke T j (ψ i)).prod * X.hecke T j f := by
    intro w
    induction w with
    | nil => exact ⟨hf, by simp [wordFn]⟩
    | cons i w ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : wordFn (X.K j) ψ (i :: w) f = UpperTheory.Gal.G3.conv (X.K j) (ψ i) (wordFn (X.K j) ψ w f) := rfl
      rw [e]
      refine ⟨(hfg _ _ (hψ i) h1).2, ?_⟩
      rw [hM X T hT j _ _ (hψ i) h1, h2, List.map_cons, List.prod_cons, mul_assoc]
  refine ⟨hw, fun s => ?_⟩
  have hs := hecke_sum X T hL hT j hz hadd hsm s.support (fun w => wordFn (X.K j) ψ w f) s fun w _ => (hw w).1
  have e : polyFn (X.K j) ψ s f = ∑ w ∈ s.support, s w • wordFn (X.K j) ψ w f := rfl
  rw [e]
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  unfold UpperTheory.Gal.CertificateRingHomMap.wop Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [(hw w).2, smul_mul_assoc]

end
