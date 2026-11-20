import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

/- English proof (translation)
The claim follows from `AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ h`.
-/
private theorem rt_inj {c c' : ℚ} (h : (rt c : A ℚ) = rt c') : c = c' :=
  AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `rt_inj (congrFun h i)`.
-/
private theorem rp_inj {ξ ξ' : Fin 4 → ℚ} (h : rp ξ = rp ξ') : ξ = ξ' := by
  funext i
  exact rt_inj (congrFun h i)

/- English proof (translation)
Rewrite using `[map_mul, gl_mul]`.
-/
private theorem gl_ratS_mul {E : Type} [Field E] [NumberField E] (a b : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E (a * b)) = gl (ratS E a) * gl (ratS E b) := by
  rw [map_mul, gl_mul]

/- English proof (translation)
Rewrite using `[map_inv, gl_inv]`.
-/
private theorem gl_ratS_inv {E : Type} [Field E] [NumberField E] (a : Matrix.SpecialLinearGroup (Fin 2) E) :
    (gl (ratS E a))⁻¹ = gl (ratS E a⁻¹) := by
  rw [map_inv, gl_inv]

/- English proof (translation)
Introduce `E _ _ _ D σ Sel hO hσ hS`. Take `⟨h1, h2, h3, h4, -⟩` from `hO E D`. Take `⟨-, -, -, -, -, -, -, -, -, -, hq⟩` from `szLaws E D`. Establish `hpt : ∀ p : ↥Sel × ℚˣ, ∃ ξ : Fin 4 → ℚ, rp ξ = D.act (gl (ratS E (σ p.1.1)))⁻¹ (rp ![0, (p.2 : ℚ), 0, 0])`. Introduce and unpack `⟨r, s⟩`.

Take `⟨ρ, hρ⟩` from `h1 (σ r.1)⁻¹`. Conclude with `⟨ρ ![0, (s : ℚ), 0, 0], by rw [gl_ratS_inv, hρ]⟩`. Use `choose pt hpt using hpt`. Establish `hmem : ∀ p, pt p ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}`. Introduce and unpack `⟨r, s⟩`.

Use `⟨fun h0 => ?_, ?_⟩` and prove the remaining obligations. Establish `hp` using `congrArg (D.act (gl (ratS E (σ r.1)))) (hpt (r, s))`. Rewrite `hp` using `[D.act_act_inv, h0]`. Establish `hz : rp (0 : Fin 4 → ℚ) = 0`. Use function extensionality and compare the values at `i`.

Conclude with `map_zero _`. Rewrite `hp` using `[hz]`. Establish `hz' : D.act (gl (ratS E (σ r.1))) (0 : V4 ℚ) = 0` using `(D.actL (gl (ratS E (σ r.1)))).map_zero`. Rewrite `hp` using `[hz']`. Establish `h1' : (rt (0 : ℚ) : A ℚ) = rt (s : ℚ)` using `(map_zero _).trans (congrFun hp 1)`.

Conclude with `s.ne_zero (rt_inj h1').symm`. Apply `rt_inj` to reduce the goal to its premises. Rewrite using `[← hq, hpt (r, s), gl_ratS_inv, D.quadForm_act, nu_gl, hq]`. Simplify using `[qr]`. Establish `hinj : Function.Injective pt`.

Introduce and unpack `⟨r, s⟩ ⟨r', s'⟩ h`. Establish `hh : D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) = D.act (gl (ratS E (σ r'.1)))⁻¹ (rp ![0, (s' : ℚ), 0, 0])`. Rewrite using `[← hpt (r, s), ← hpt (r', s'), h]`. Take `⟨δ, hδ⟩ : ∃ δ, δ = σ r'.1 * (σ r.1)⁻¹` from `⟨_, rfl⟩`. Establish `hact : D.act (gl (ratS E δ)) (rp ![0, (s : ℚ), 0, 0]) = rp ![0, (s' : ℚ), 0, 0]`.

Rewrite using `[hδ, gl_ratS_mul, ← gl_ratS_inv, D.act_mul, hh, D.act_act_inv]`. Establish `h10` using `h3 δ s s' s.ne_zero hact`. Establish `e1 : σ r'.1 = δ * σ r.1` using `by simp [hδ]`. Establish `hrow : ∀ j, r'.1.1 j = δ 1 1 * r.1.1 j`. Introduce `j`.

Establish `a : (σ r'.1).1 1 j = r'.1.1 j` using `congrFun (hσ r'.1) j`. Establish `b : (σ r.1).1 1 j = r.1.1 j` using `congrFun (hσ r.1) j`. Establish `c : (σ r'.1).1 1 j = (δ * σ r.1).1 1 j` using `by rw [← e1]`. Rewrite using `[← a, c, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, b]`. Establish `h10' : δ.1 1 0 = 0` using `h10`.

Rewrite using `[h10', zero_mul, zero_add]`. Establish `ht0 : δ 1 1 ≠ 0`. Introduce `h`. Apply `r'.1.2` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Rewrite using `[hrow, h, zero_mul]`. Both sides reduce to the same expression. Establish `ht : Units.mk0 _ ht0 = (1 : Eˣ)` using `(hS r.1).unique ⟨r'.1, r'.2, by funext j; exact hrow j⟩ ⟨r.1, r.2, by simp⟩`. Establish `ht1 : δ 1 1 = 1` using `by simpa using congrArg Units.val ht`. Establish `hr : r' = r`.

Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[hrow, ht1, one_mul]`. Substitute `hr` using the available equality. Establish `hss : rp ![0, (s : ℚ), 0, 0] = rp ![0, (s' : ℚ), 0, 0]`.

Use `congrArg (D.act (gl (ratS E (σ r'.1)))) hh` as an intermediate fact. Simplify `this` using `only [D.act_act_inv]`. Establish `h1' : (s : ℚ) = s'` using `rt_inj (congrFun hss 1)`. Rewrite using `[Units.ext h1']`. Establish `hsurj : ∀ ξ ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ∃ p, pt p = ξ`.

Introduce and unpack `ξ ⟨hξ0, hξq⟩`. Take `⟨γ, r0, hr0, hγ⟩` from `h2 ξ hξ0 hξq`. Establish `hrow : (γ⁻¹).1 1 ≠ 0`. Introduce `h`. Establish `hd` using `(γ⁻¹).det_coe`.

Establish `a : (γ⁻¹).1 1 0 = 0` using `congrFun h 0`. Establish `b : (γ⁻¹).1 1 1 = 0` using `congrFun h 1`. Rewrite `hd` using `[Matrix.det_fin_two, a, b]`. Simplify using `at hd`. Take `⟨t, ⟨r', hr', hrt⟩, -⟩` from `hS ⟨_, hrow⟩`.

Establish `ha : ∀ j, (σ r').1 1 j = (t : E) * (γ⁻¹).1 1 j`. Introduce `j`. Rewrite using `[hσ r', hrt]`. Both sides reduce to the same expression. Establish `h10 : (σ r' * γ) 1 0 = 0`.

Establish `hI : (γ⁻¹ * γ).1 1 0 = 0` using `by simp`. Rewrite `hI` using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Express the relevant statement in the definitionally equal form `(σ r' * γ).1 1 0 = 0`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, ha, mul_assoc, mul_assoc, ← mul_add, hI, mul_zero]`. Take `⟨c, hc, hcr⟩` from `h4 _ h10`.

Use `⟨(⟨r', hr'⟩, Units.mk0 (c * r0) (mul_ne_zero hc hr0)), rp_inj ?_⟩` and prove the remaining obligations. Rewrite using `[hpt]`. Express the relevant statement in the definitionally equal form `D.act (gl (ratS E (σ r')))⁻¹ (rp ![0, c * r0, 0, 0]) = rp ξ`. Rewrite using `[← hcr, gl_ratS_mul, D.act_mul, D.act_inv_act, hγ]`. Use `⟨Equiv.ofBijective (fun p => ⟨pt p, hmem p⟩) ⟨?_, ?_⟩, fun r s => hpt (r, s)⟩` and prove the remaining obligations.

Introduce `p p' h`. Conclude with `hinj (congrArg Subtype.val h)`. Introduce and unpack `⟨ξ, hξ⟩`. Take `⟨p, hp⟩` from `hsurj ξ hξ`. Conclude with `⟨p, Subtype.ext hp⟩`.
-/
theorem UpperTheory.exists_equiv_rowSelection_units_isotropicVectors :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E) (Sel : Set {r : Fin 2 → E // r ≠ 0}), Orb1 → M.RowSec σ → (∀ r : {r : Fin 2 → E // r ≠ 0}, ∃! t : Eˣ, ∃ r' ∈ Sel, r'.1 = (t : E) • r.1) → ∃ e : ↥Sel × ℚˣ ≃ ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ∀ r s, rp (e (r, s)).1 = D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) := by
  intro E _ _ _ D σ Sel hO hσ hS
  obtain ⟨h1, h2, h3, h4, -⟩ := hO E D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hq⟩ := szLaws E D
  have hpt : ∀ p : ↥Sel × ℚˣ, ∃ ξ : Fin 4 → ℚ,
      rp ξ = D.act (gl (ratS E (σ p.1.1)))⁻¹ (rp ![0, (p.2 : ℚ), 0, 0]) := by
    rintro ⟨r, s⟩
    obtain ⟨ρ, hρ⟩ := h1 (σ r.1)⁻¹
    exact ⟨ρ ![0, (s : ℚ), 0, 0], by rw [gl_ratS_inv, hρ]⟩
  choose pt hpt using hpt
  have hmem : ∀ p, pt p ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0} := by
    rintro ⟨r, s⟩
    refine ⟨fun h0 => ?_, ?_⟩
    · have hp := congrArg (D.act (gl (ratS E (σ r.1)))) (hpt (r, s))
      rw [D.act_act_inv, h0] at hp
      have hz : rp (0 : Fin 4 → ℚ) = 0 := by
        funext i
        exact map_zero _
      rw [hz] at hp
      have hz' : D.act (gl (ratS E (σ r.1))) (0 : V4 ℚ) = 0 := (D.actL (gl (ratS E (σ r.1)))).map_zero
      rw [hz'] at hp
      have h1' : (rt (0 : ℚ) : A ℚ) = rt (s : ℚ) := (map_zero _).trans (congrFun hp 1)
      exact s.ne_zero (rt_inj h1').symm
    · apply rt_inj
      rw [← hq, hpt (r, s), gl_ratS_inv, D.quadForm_act, nu_gl, hq]
      simp [qr]
  have hinj : Function.Injective pt := by
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    have hh : D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) =
        D.act (gl (ratS E (σ r'.1)))⁻¹ (rp ![0, (s' : ℚ), 0, 0]) := by
      rw [← hpt (r, s), ← hpt (r', s'), h]
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = σ r'.1 * (σ r.1)⁻¹ := ⟨_, rfl⟩
    have hact : D.act (gl (ratS E δ)) (rp ![0, (s : ℚ), 0, 0]) = rp ![0, (s' : ℚ), 0, 0] := by
      rw [hδ, gl_ratS_mul, ← gl_ratS_inv, D.act_mul, hh, D.act_act_inv]
    have h10 := h3 δ s s' s.ne_zero hact
    have e1 : σ r'.1 = δ * σ r.1 := by simp [hδ]
    have hrow : ∀ j, r'.1.1 j = δ 1 1 * r.1.1 j := by
      intro j
      have a : (σ r'.1).1 1 j = r'.1.1 j := congrFun (hσ r'.1) j
      have b : (σ r.1).1 1 j = r.1.1 j := congrFun (hσ r.1) j
      have c : (σ r'.1).1 1 j = (δ * σ r.1).1 1 j := by rw [← e1]
      rw [← a, c, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, b]
      have h10' : δ.1 1 0 = 0 := h10
      rw [h10', zero_mul, zero_add]
    have ht0 : δ 1 1 ≠ 0 := by
      intro h
      apply r'.1.2
      funext j
      rw [hrow, h, zero_mul]
      rfl
    have ht : Units.mk0 _ ht0 = (1 : Eˣ) := (hS r.1).unique
      ⟨r'.1, r'.2, by funext j; exact hrow j⟩ ⟨r.1, r.2, by simp⟩
    have ht1 : δ 1 1 = 1 := by simpa using congrArg Units.val ht
    have hr : r' = r := by
      refine Subtype.ext (Subtype.ext ?_)
      funext j
      rw [hrow, ht1, one_mul]
    subst hr
    have hss : rp ![0, (s : ℚ), 0, 0] = rp ![0, (s' : ℚ), 0, 0] := by
      have := congrArg (D.act (gl (ratS E (σ r'.1)))) hh
      simpa only [D.act_act_inv] using this
    have h1' : (s : ℚ) = s' := rt_inj (congrFun hss 1)
    rw [Units.ext h1']
  have hsurj : ∀ ξ ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ∃ p, pt p = ξ := by
    rintro ξ ⟨hξ0, hξq⟩
    obtain ⟨γ, r0, hr0, hγ⟩ := h2 ξ hξ0 hξq
    have hrow : (γ⁻¹).1 1 ≠ 0 := by
      intro h
      have hd := (γ⁻¹).det_coe
      have a : (γ⁻¹).1 1 0 = 0 := congrFun h 0
      have b : (γ⁻¹).1 1 1 = 0 := congrFun h 1
      rw [Matrix.det_fin_two, a, b] at hd
      simp at hd
    obtain ⟨t, ⟨r', hr', hrt⟩, -⟩ := hS ⟨_, hrow⟩
    have ha : ∀ j, (σ r').1 1 j = (t : E) * (γ⁻¹).1 1 j := by
      intro j
      rw [hσ r', hrt]
      rfl
    have h10 : (σ r' * γ) 1 0 = 0 := by
      have hI : (γ⁻¹ * γ).1 1 0 = 0 := by simp
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hI
      change (σ r' * γ).1 1 0 = 0
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, ha, mul_assoc, mul_assoc,
        ← mul_add, hI, mul_zero]
    obtain ⟨c, hc, hcr⟩ := h4 _ h10
    refine ⟨(⟨r', hr'⟩, Units.mk0 (c * r0) (mul_ne_zero hc hr0)), rp_inj ?_⟩
    rw [hpt]
    change D.act (gl (ratS E (σ r')))⁻¹ (rp ![0, c * r0, 0, 0]) = rp ξ
    rw [← hcr, gl_ratS_mul, D.act_mul, D.act_inv_act, hγ]
  refine ⟨Equiv.ofBijective (fun p => ⟨pt p, hmem p⟩) ⟨?_, ?_⟩, fun r s => hpt (r, s)⟩
  · intro p p' h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨ξ, hξ⟩
    obtain ⟨p, hp⟩ := hsurj ξ hξ
    exact ⟨p, Subtype.ext hp⟩
