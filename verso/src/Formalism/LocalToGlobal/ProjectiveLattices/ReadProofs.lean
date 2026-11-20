import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TestRd (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
    ∃ (k : (U σ).Comp) (x : ((U σ).X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
      cvalR σ (ψ (f p y)) = u * rdU (U σ) f k x.1

def BCEx (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ z : FrPt Xo c (CAt σ), FrMap ψ y z

def WtC (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)),
    FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

/- English proof (translation)
Introduce `a n hd p y ψ`. Take `⟨z, hz⟩` from `hB p y ψ`. Take `⟨-, -, hcov, -⟩` from `hU`. Take `⟨k, x, t, ht⟩` from `hcov z`. Use `⟨k, x, toC (wchar (ex Dw a n) t), fun f hf => ?_⟩` and prove the remaining obligations.

Establish `hft : FromTest (K` using `c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩`. Establish `e2` using `hW f hf.1`. Establish `hev : evR Xo c f z = ψ (f p y)`. Unfold `evR evalAt`. Rewrite using `[dif_pos hft]`.

Conclude with `e2 _ _ _ _ _ _ _ _ hft.choose_spec.choose_spec.choose_spec hz`. Establish `hwt` using `hC a n hd f hf t ((U σ).un k x) z ht`. Establish `hr : rdU (U σ) f k x.1 = toC (evR Xo c f ((U σ).un k x))`. Simplify using `only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, Subtype.coe_eta]`. Rewrite using `[hr, ← hev, hwt]`.

Apply the tactic sequence `all_goals rfl`.
-/
theorem testRd_of (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hU : IsUnf (U σ))
    (hB : BCEx Xo c σ) (hC : WtC Xo c σ) : TestRd Xo c U σ := by
  intro a n hd p y ψ
  obtain ⟨z, hz⟩ := hB p y ψ
  obtain ⟨-, -, hcov, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := hcov z
  refine ⟨k, x, toC (wchar (ex Dw a n) t), fun f hf => ?_⟩
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
  have e2 := hW f hf.1
  have hev : evR Xo c f z = ψ (f p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact e2 _ _ _ _ _ _ _ _ hft.choose_spec.choose_spec.choose_spec hz
  have hwt := hC a n hd f hf t ((U σ).un k x) z ht
  have hr : rdU (U σ) f k x.1 = toC (evR Xo c f ((U σ).un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, Subtype.coe_eta]
  rw [hr, ← hev, hwt]
  all_goals rfl

/- English proof (translation)
Introduce `a n hd σ hσ f hf h0`. Use function extensionality and compare the values at `p y`. Use `show f p y = 0`. Use `eq_zero_of_cpts σ p _ fun ψ => ?_` and prove the remaining obligations. Take `⟨k, x, u, hk⟩` from `h σ hσ a n hd p y ψ`.

Establish `e` using `hk f (cusp_le_sec Xo c U a n hf)`. Rewrite `e` using `[h0 k x.1 x.2, mul_zero]`. Conclude with `e`.
-/
theorem rdDomInj_of (h : ∀ σ, GoodEmb c σ → TestRd Xo c U σ) : RdDomInj Xo c U := by
  intro a n hd σ hσ f hf h0
  funext p y
  show f p y = 0
  refine eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨k, x, u, hk⟩ := h σ hσ a n hd p y ψ
  have e := hk f (cusp_le_sec Xo c U a n hf)
  rw [h0 k x.1 x.2, mul_zero] at e
  exact e

/- English proof (translation)
Use `haveI : CharZero c.F := RingHom.charZero σ`. Introduce `a k hd n b hb hli`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `w hw`. Establish `hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0`.

Introduce `θ`. Establish `hz : ∑ i, θ (toCAt σ (w i)) • b i = 0`. Use function extensionality and compare the values at `p y`. Establish `hpt` using `descend_cpts σ p (fun i => b i p y) w (fun ψ => by`. Take `⟨k', x, u, hk⟩` from `h a k hd p y ψ`.

Establish `e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU (U σ) (b i) k' x.1)`. Introduce `i`. Rewrite using `[hk (b i) (hb i)]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `congrFun (congrFun hw k') x.1`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2`. Repeatedly rewrite using `[e1]`. Rewrite using `[← Finset.mul_sum, e2, mul_zero]) θ`. Simplify `hpt` using `[Finset.sum_apply]`. Conclude with `fun i => Fintype.linearIndependent_iff.1 hli _ hz i`.

Introduce `i`. Conclude with `(Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i`.
-/
theorem rdIndep_of (σ : c.F →+* ℂ) (h : TestRd Xo c U σ) : RdIndep Xo c U σ := by
  haveI : CharZero c.F := RingHom.charZero σ
  intro a k hd n b hb hli
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
    intro θ
    have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
      funext p y
      have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
        obtain ⟨k', x, u, hk⟩ := h a k hd p y ψ
        have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU (U σ) (b i) k' x.1) := by
          intro i; rw [hk (b i) (hb i)]; ring
        have e2 := congrFun (congrFun hw k') x.1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
        simp_rw [e1]
        rw [← Finset.mul_sum, e2, mul_zero]) θ
      simpa [Finset.sum_apply] using hpt
    exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
  intro i
  exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

/- English proof (translation)
Establish `hbinv : frInv b ∈ Bor X.Ψ r`. Introduce `τ`. Take `⟨hdet, htri⟩` from `hb τ`. Establish `hu : IsUnit (mat b τ).det` using `isUnit_iff_ne_zero.2 hdet`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mat_frInv]`. Conclude with `(Matrix.isUnit_nonsing_inv_det_iff.2 hu).ne_zero`. Introduce `i j hij haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu`. Establish `hBT : (mat b τ).BlockTriangular id` using `fun i' j' h' => htri i' j' h'`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hBT hij`.

Establish `hrm : rmul (rmul (lact γ x) b) (frInv b) = lact γ x`. Use function extensionality and compare the values at `τ`. Use `show mat (rmul (lact γ x) b) τ * mat (frInv b) τ = mat (lact γ x) τ`. Rewrite using `[mat_rmul, mat_frInv, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]`. Establish `h1 : P (lact γ x) = 0`.

Establish `h2` using `hB _ hz (frInv b) hbinv`. Rewrite `h2` using `[hrm, h0, mul_zero]`. Conclude with `h2`. Rewrite `h1` using `[hΓ γ hγ x hx]`. Take `⟨n, hn, hχ⟩` from `X.χ_fin la`.

Establish `hne : X.χ la γ ≠ 0`. Introduce `h`. Establish `h3` using `hχ γ hγ`. Rewrite `h3` using `[h, zero_pow hn.ne']`. Conclude with `zero_ne_one h3`.

Conclude with `(mul_eq_zero.1 h1).resolve_left hne`.
-/
theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    obtain ⟨hdet, htri⟩ := hb τ
    have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 hdet
    refine ⟨?_, ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 hu).ne_zero
    · intro i j hij
      haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
      have hBT : (mat b τ).BlockTriangular id := fun i' j' h' => htri i' j' h'
      exact Matrix.blockTriangular_inv_of_blockTriangular hBT hij
  have hrm : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    show mat (rmul (lact γ x) b) τ * mat (frInv b) τ = mat (lact γ x) τ
    rw [mat_rmul, mat_frInv, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]
  have h1 : P (lact γ x) = 0 := by
    have h2 := hB _ hz (frInv b) hbinv
    rw [hrm, h0, mul_zero] at h2
    exact h2
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have h3 := hχ γ hγ
    rw [h, zero_pow hn.ne'] at h3
    exact zero_ne_one h3
  exact (mul_eq_zero.1 h1).resolve_left hne

/- English proof (translation)
Use `replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem Q hQ`. Establish `hQ' : IsHolCusp X la Q` using `hQ`. Conclude with `⟨fun k x hx b hb => (hQ' k).1.1.2.1 x hx b hb, fun k γ hγ x hx => (hQ' k).1.1.2.2 γ hγ x hx⟩`.

Consider the case `zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩`. Consider the case `add Q R _ _ hQ hR`. Use `⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Rewrite using `[hQ.1 k x hx b hb, hR.1 k x hx b hb]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.add_apply]`. Rewrite using `[hQ.2 k γ hγ x hx, hR.2 k γ hγ x hx]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a Q _ hQ`.

Use `⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hQ.1 k x hx b hb]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[hQ.2 k γ hγ x hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    have hQ' : IsHolCusp X la Q := hQ
    exact ⟨fun k x hx b hb => (hQ' k).1.1.2.1 x hx b hb, fun k γ hγ x hx => (hQ' k).1.1.2.2 γ hγ x hx⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add Q R _ _ hQ hR =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hQ.1 k x hx b hb, hR.1 k x hx b hb]
      ring
    · simp only [Pi.add_apply]
      rw [hQ.2 k γ hγ x hx, hR.2 k γ hγ x hx]
      ring
  | smul a Q _ hQ =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.1 k x hx b hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.2 k γ hγ x hx]
      ring

variable {D : D7} {Comp : Type} {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

/- English proof (translation)
Use `replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem Q hQ => exact h la Q hQ`. Consider the case `zero`. Use `⟨fun γ _ g => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_zero, Pi.zero_apply]`. Rewrite using `[map_zero]`. Conclude with `continuous_const`. Consider the case `add Q R _ _ hQ hR`. Use `⟨fun γ hγ g => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, Pi.add_apply, hQ.1 γ hγ g, hR.1 γ hγ g]`. Rewrite using `[map_add]`. Conclude with `hQ.2.add hR.2`. Consider the case `smul a Q _ hQ`. Use `⟨fun γ hγ g => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_smul, Pi.smul_apply, hQ.1 γ hγ g]`. Rewrite using `[map_smul]`. Conclude with `hQ.2.const_smul a`.
-/
theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact h la Q hQ
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_⟩
    · simp only [map_zero, Pi.zero_apply]
    · rw [map_zero]
      exact continuous_const
  | add Q R _ _ hQ hR =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_add, Pi.add_apply, hQ.1 γ hγ g, hR.1 γ hγ g]
    · rw [map_add]
      exact hQ.2.add hR.2
  | smul a Q _ hQ =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_smul, Pi.smul_apply, hQ.1 γ hγ g]
    · rw [map_smul]
      exact hQ.2.const_smul a

/- English proof (translation)
Use function extensionality and compare the values at `q`. Conclude with `congrArg (Quotient.lift φ _) (Quotient.out_eq q)`.
-/
theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  exact congrArg (Quotient.lift φ _) (Quotient.out_eq q)

/- English proof (translation)
Introduce `la P hP`. Take `⟨hL, hc⟩` from `h la P hP`. Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Rewrite using `[onQ_eq_lift _ hL]`. Use `Measurable.aestronglyMeasurable ?_` and prove the remaining obligations.

Conclude with `measurable_from_quotient.2 hc.measurable`.
-/
theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hc⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hc.measurable

/- English proof (translation)
Introduce `la P hP h0 k x hx`. Establish `hA'` using `adelAut_holSub hA la hP`. Establish `hz : ∀ g, adel V dict mu P g = 0` using `hQ _ hA'.2 hA'.1 h0`. Take `⟨-, -, -, hdom, hsurj, -⟩` from `hd`. Take `⟨g, γ, hγ, b, hb, hg⟩` from `hsurj k x hx`.

Establish `hm : mu g ≠ 0`. Introduce `h`. Establish `h1` using `hmu.2.1 g`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Establish `h1 : mu g * P (dict g).1 (dict g).2 = 0` using `hz g`. Establish `h2 : P (dict g).1 (dict g).2 = 0` using `(mul_eq_zero.1 h1).resolve_left hm`. Establish `h3` using `hdom g`. Rewrite `h2`, `h3` using `[hg]`. Establish `hE` using `eqv_holSub (U σ).X la hP`.

Conclude with `eq_zero_of_orbit ((U σ).X k) (la k) (P k) (hE.1 k) (hE.2 k) hx hγ hb h3 h2`.
-/
theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP h0 k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 h0
  obtain ⟨-, -, -, hdom, hsurj, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hsurj k x hx
  have hm : mu g ≠ 0 := by
    intro h
    have h1 := hmu.2.1 g
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have h1 : mu g * P (dict g).1 (dict g).2 = 0 := hz g
  have h2 : P (dict g).1 (dict g).2 = 0 := (mul_eq_zero.1 h1).resolve_left hm
  have h3 := hdom g
  rw [hg] at h2 h3
  have hE := eqv_holSub (U σ).X la hP
  exact eq_zero_of_orbit ((U σ).X k) (la k) (P k) (hE.1 k) (hE.2 k) hx hγ hb h3 h2

end Adelic

end Formalism.L2.Pj
