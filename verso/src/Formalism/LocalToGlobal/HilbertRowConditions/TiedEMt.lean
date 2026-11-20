import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Rows

structure EMtTied (D : D7) (C : Formalism.L2.Forms.ColsTiedSym D) {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D}
    {tp : Formalism.L2.Host.TupTied D cf nch} {Tw : TwForms D} (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp C Tw) : Prop where

  mu0 : ∀ (u : D.what₂.Word) (F G : (D.mem u).P.Mt),
    inner ℂ (D.eMt u F) (D.eMt u G) = (D.fm u).ipP ((C.forms u).jM G) ((C.forms u).jM F)

  tw : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (F G : (D.PTw u μ).Mt),
    inner ℂ (D.eMtTw u μ F) (D.eMtTw u μ G) = (Tw.fm u μ).ipP (tw.ptE.jM u μ G) (tw.ptE.jM u μ F)

def IsoWith {M A : Type} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (e : M →ₗ[ℂ] A) (B : M → M → ℂ) : Prop :=
  ∀ F G, inner ℂ (e F) (e G) = B F G

/- English proof (translation)
Take `⟨F, hF⟩` from `hne`. Establish `h1` using `ht F F`. Rewrite `h1` using `[← he F F]`. Simplify using `only [LinearMap.smul_apply, inner_smul_left, inner_smul_right] at h1`. Establish `hz : inner ℂ (e F) (e F) ≠ 0` using `inner_self_ne_zero.mpr hF`.

Establish `h3 : (starRingEnd ℂ) t * t = 1`. Apply `mul_right_cancel₀ hz` to reduce the goal to its premises. Take the linear combination `h1`. Establish `h2 : ((Complex.normSq t : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Conclude with `h3`. Conclude with `h2` after adjusting the coercions.
-/
theorem IsoWith.scale_normSq {M A : Type} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {e : M →ₗ[ℂ] A} {B : M → M → ℂ} (he : IsoWith e B) {t : ℂ} (ht : IsoWith (t • e) B) (hne : ∃ F, e F ≠ 0) :
    Complex.normSq t = 1 := by
  obtain ⟨F, hF⟩ := hne
  have h1 := ht F F
  rw [← he F F] at h1
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right] at h1
  have hz : inner ℂ (e F) (e F) ≠ 0 := inner_self_ne_zero.mpr hF
  have h3 : (starRingEnd ℂ) t * t = 1 := by
    apply mul_right_cancel₀ hz
    linear_combination h1
  have h2 : ((Complex.normSq t : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h3
  exact_mod_cast h2

/- English proof (translation)
Introduce `F G` and use `h.tw u μ hμ F G`.
-/
theorem EMtTied.isoWith_tw {D : D7} {C : Formalism.L2.Forms.ColsTiedSym D} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D}
    {tp : Formalism.L2.Host.TupTied D cf nch} {Tw : TwForms D} {tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp C Tw} (h : EMtTied D C tw)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) :
    IsoWith (D.eMtTw u μ).toLinearMap (fun F G => (Tw.fm u μ).ipP (tw.ptE.jM u μ G) (tw.ptE.jM u μ F)) :=
  fun F G => h.tw u μ hμ F G

/- English proof (translation)
Introduce `F G` and use `h.mu0 u F G`.
-/
theorem EMtTied.isometry_at_base_tuple {D : D7} {C : Formalism.L2.Forms.ColsTiedSym D} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D}
    {tp : Formalism.L2.Host.TupTied D cf nch} {Tw : TwForms D} {tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp C Tw} (h : EMtTied D C tw)
    (u : D.what₂.Word) :
    IsoWith (D.eMt u).toLinearMap (fun F G => (D.fm u).ipP ((C.forms u).jM G) ((C.forms u).jM F)) :=
  fun F G => h.mu0 u F G

end Formalism.L2.Rows

end
