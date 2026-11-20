import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocalStatement
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric

/- English proof (translation)
Use `⟨fun z hz y hy => ?_, fun z w hd => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ x in 𝓝[U] z, f x < 2 * y` using `h.1 z hz (2 * y) (by simp only at hy; linarith) filter_upwards [h1] with x hx`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h1, h2⟩` from `h.2 z w hd`. Establish `e : Real.circleAverage (fun ζ : ℂ => f (z + ζ • w) / 2) 0 1 = Real.circleAverage (fun ζ : ℂ => f (z + ζ • w)) 0 1 / 2`.

Use `Real.circleAverage_fun_smul (c := 0) (R := 1) (a := (1 / 2 : ℝ)) (f := fun ζ : ℂ => f (z + ζ • w))` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[show (fun ζ : ℂ => f (z + ζ • w) / 2) = fun ζ : ℂ => 1 / 2 * f (z + ζ • w) by`. Use function extensionality and compare the values at `ζ`. Use the proof step `ring, this]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: CircleIntegrable ((1 / 2 : ℝ) • fun ζ : ℂ => f (z + ζ • w)) 0 1` using `h1.const_smul`. Use `(circleIntegrable_congr (fun ζ _ => ?_)).1 this` and prove the remaining obligations. Simplify using `[div_eq_inv_mul]`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isPsh_half {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (h : IsPsh U f) :
    IsPsh U (fun z => f z / 2) := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, f x < 2 * y := h.1 z hz (2 * y) (by simp only at hy; linarith)
    filter_upwards [h1] with x hx
    linarith
  · obtain ⟨h1, h2⟩ := h.2 z w hd
    have e : Real.circleAverage (fun ζ : ℂ => f (z + ζ • w) / 2) 0 1 =
        Real.circleAverage (fun ζ : ℂ => f (z + ζ • w)) 0 1 / 2 := by
      have := Real.circleAverage_fun_smul (c := 0) (R := 1) (a := (1 / 2 : ℝ)) (f := fun ζ : ℂ => f (z + ζ • w))
      simp only [smul_eq_mul] at this
      rw [show (fun ζ : ℂ => f (z + ζ • w) / 2) = fun ζ : ℂ => 1 / 2 * f (z + ζ • w) by
        funext ζ; ring, this]
      ring
    refine ⟨?_, ?_⟩
    · have : CircleIntegrable ((1 / 2 : ℝ) • fun ζ : ℂ => f (z + ζ • w)) 0 1 := h1.const_smul
      refine (circleIntegrable_congr (fun ζ _ => ?_)).1 this
      simp [div_eq_inv_mul]
    · rw [e]; linarith

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

/- English proof (translation)
Establish `h : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ.ne'`. Use function extensionality and compare the values at `i`. Simplify using `[aff, affInv, Function.comp, h]`.
-/
theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]

/- English proof (translation)
Rewrite `ht` using `[mem_ball, dist_eq_norm, sub_eq_add_neg]`. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff one_pos]`. Introduce `i`. Establish `h1 : ‖(t - t₀) (π.symm i)‖ < ρ`. Establish `: ‖t + -t₀‖ < ρ` using `ht`.

Rewrite `this` using `[pi_norm_lt_iff hρ]`. Simplify `this (π.symm i)` using `[sub_eq_add_neg]`. Simplify using `only [affInv, Function.comp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]`. Rewrite using `[inv_mul_lt_iff₀ hρ]`. Simplify using `using h1`.
-/
theorem norm_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) {t : Fin n → ℂ}
    (ht : t ∈ ball t₀ ρ) : affInv t₀ ρ π t ∈ ball 0 1 := by
  rw [mem_ball, dist_eq_norm, sub_eq_add_neg] at ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖(t - t₀) (π.symm i)‖ < ρ := by
    have : ‖t + -t₀‖ < ρ := ht
    rw [pi_norm_lt_iff hρ] at this
    simpa [sub_eq_add_neg] using this (π.symm i)
  simp only [affInv, Function.comp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ]
  rw [inv_mul_lt_iff₀ hρ]
  simpa using h1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[affInv, Function.comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem affInv_add {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (z w : Fin n → ℂ) (ζ : ℂ) :
    affInv t₀ ρ π (z + ζ • w) = affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) := by
  funext i
  simp [affInv, Function.comp]
  ring

/- English proof (translation)
Establish `hc : Continuous (affInv t₀ ρ π)`. Unfold `affInv`. Use `fun_prop`. Use `⟨h.1.comp (g := affInv t₀ ρ π) hc.continuousOn (fun t ht => norm_affInv t₀ hρ π ht), fun z w hd => ?_⟩` and prove the remaining obligations. Establish `hd' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) ∈ ball 0 1`.

Introduce `ζ hζ`. Rewrite using `[← affInv_add]`. Conclude with `norm_affInv t₀ hρ π (hd ζ hζ)`. Establish `e : (fun ζ : ℂ => ψ (affInv t₀ ρ π (z + ζ • w))) = fun ζ : ℂ => ψ (affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm))`. Use function extensionality and compare the values at `ζ`.

Rewrite using `[affInv_add]`. Simplify using `only [e]`. Conclude with `h.2 _ _ hd'`.
-/
theorem isPsh_comp_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    {ψ : (Fin n → ℂ) → ℝ} (h : IsPsh (ball 0 1) ψ) : IsPsh (ball t₀ ρ) (fun t => ψ (affInv t₀ ρ π t)) := by
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  refine ⟨h.1.comp (g := affInv t₀ ρ π) hc.continuousOn (fun t ht => norm_affInv t₀ hρ π ht), fun z w hd => ?_⟩
  have hd' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) ∈ ball 0 1 := by
    intro ζ hζ
    rw [← affInv_add]
    exact norm_affInv t₀ hρ π (hd ζ hζ)
  have e : (fun ζ : ℂ => ψ (affInv t₀ ρ π (z + ζ • w))) =
      fun ζ : ℂ => ψ (affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm)) := by
    funext ζ; rw [affInv_add]
  simp only [e]
  exact h.2 _ _ hd'

/- English proof (translation)
Establish `hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀` using `hF.div analyticAt_const h0`. Establish `h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane`. Establish `: F t₀ / F t₀ ∈ Complex.slitPlane` using `by rw [div_self h0]; exact Complex.one_mem_slitPlane`. Conclude with `hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)`. Establish `h2 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ (fun t => F t / F t₀) t` using `hH.eventually_analyticAt`.

Take `⟨r, hr, hb⟩` from `Metric.eventually_nhds_iff_ball.1 (h1.and h2)`. Use `⟨r, hr, fun t => Complex.log (F t / F t₀), fun t ht => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Conclude with `((hb t ht).2.differentiableAt.clog (hb t ht).1).differentiableWithinAt`. Establish `hne : F t / F t₀ ≠ 0` using `Complex.slitPlane_ne_zero (hb t ht).1`. Establish `hFt : F t ≠ 0` using `fun h => hne (by simp [h])`.

Rewrite using `[Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_log_norm {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀) (h0 : F t₀ ≠ 0) :
    ∃ r > (0 : ℝ), ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ball t₀ r) ∧
      ∀ t ∈ ball t₀ r, Real.log ‖F t‖ = (G t).re + Real.log ‖F t₀‖ := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane := by
    have : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
    exact hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)
  have h2 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ (fun t => F t / F t₀) t := hH.eventually_analyticAt
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨r, hr, fun t => Complex.log (F t / F t₀), fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hb t ht).2.differentiableAt.clog (hb t ht).1).differentiableWithinAt
  · have hne : F t / F t₀ ≠ 0 := Complex.slitPlane_ne_zero (hb t ht).1
    have hFt : F t ≠ 0 := fun h => hne (by simp [h])
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]
    ring

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simpa using analyticAt_const`. Consider the case `add p r hp hr`. Establish `e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p + r))) = (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) + fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) r)`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hp.add hr`. Consider the case `mul_X p i hp`. Establish `e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p * MvPolynomial.X i))) = (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) * fun t => q t i`.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hp.mul (hq i)`.
-/
theorem analyticAt_eval {A : Type} {n : ℕ} {q : (Fin n → ℂ) → A → ℂ} {t₀ : Fin n → ℂ}
    (hq : ∀ i, AnalyticAt ℂ (fun t => q t i) t₀) (p : MvPolynomial A ℤ) :
    AnalyticAt ℂ (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) t₀ := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p r hp hr =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p + r))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) +
          fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) r) := by
      funext t; simp
    rw [e]; exact hp.add hr
  | mul_X p i hp =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p * MvPolynomial.X i))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) * fun t => q t i := by
      funext t; simp
    rw [e]; exact hp.mul (hq i)

open scoped ComplexOrder in

/- English proof (translation)
Establish `hH : (R.Hmᵀ).IsHermitian`. Use extensionality with `i j`. Conclude with `R.herm.apply j i`. Establish `hM : (R.Hmᵀ).PosDef`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations.

Establish `h1` using `R.pos x hx`. Establish `e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x`. Rewrite using `[Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]`. Establish `him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0` using `hH.im_star_dotProduct_mulVec_self x`. Rewrite using `[Complex.pos_iff]`.

Conclude with `⟨by rw [e]; exact h1, him.symm⟩`. Set `C : Matrix (Fin g) (Fin m) ℂ` to `(Matrix.of u)ᵀ`. Establish `hC : Function.Injective C.mulVec` using `Matrix.mulVec_injective_iff.2 hu`. Establish `e : R.gram u = Cᴴ * R.Hmᵀ * C`. Use extensionality with `a b`.

Simplify using `only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hp` using `(hM.conjTranspose_mul_mul_same hC).det_pos`. Rewrite `hp` using `[← e]`. Conclude with `(Complex.pos_iff.1 hp).1`.
-/
theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  have hM : (R.Hmᵀ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := R.pos x hx
    have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact h1, him.symm⟩
  let C : Matrix (Fin g) (Fin m) ℂ := (Matrix.of u)ᵀ
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hu
  have e : R.gram u = Cᴴ * R.Hmᵀ * C := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp := (hM.conjTranspose_mul_mul_same hC).det_pos
  rw [← e] at hp
  exact (Complex.pos_iff.1 hp).1

/- English proof (translation)
Take `⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩` from `h`. Take `⟨v', e', d'⟩` from `h3 i`. Take `⟨w', f', g'⟩` from `h3 j`. Conclude with `⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩`.
-/
theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

/- English proof (translation)
Establish `e : offBd D a = ball 0 1 ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)), {t | (i : ℕ) < (D.chart a).a → t i ≠ 0}`. Use extensionality with `t`. Simplify using `only [offBd, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]`. Use `and_congr_right fun ht => ?_` and prove the remaining obligations. Rewrite using `[(D.chart a).boundary t ht]`.

Use `push_neg`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < (D.chart a).a`.

Simplify `isOpen_ne_fun (continuous_apply i) continuous_const` using `[h]`. Simplify using `[h]`.
-/
theorem isOpen_offBd (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) : IsOpen (offBd D a) := by
  have e : offBd D a = ball 0 1 ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)),
      {t | (i : ℕ) < (D.chart a).a → t i ≠ 0} := by
    ext t
    simp only [offBd, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun ht => ?_
    rw [(D.chart a).boundary t ht]
    push_neg
    rfl
  rw [e]
  refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : (i : ℕ) < (D.chart a).a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

end Free

end GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence
