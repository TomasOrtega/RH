import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder

def topDens {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  maDensity (fun _ : Fin D => fun y => ψ y / 2) z

def DetMono.Hyp {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A'.PosSemidef ∧ (A - A').PosSemidef

def DetMono.Statement : Prop :=
  ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℂ), DetMono.Hyp A A' → A'.det.re ≤ A.det.re

def MACompact.Hyp {D : ℕ} (Ω : Set (Fin D → ℂ)) (φ v : (Fin D → ℂ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v Ω ∧
    HasCompactSupport v ∧ tsupport v ⊆ Ω

def MACompact.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (φ v : (Fin D → ℂ) → ℝ), MACompact.Hyp Ω φ v →
    ∫ z in Ω, (topDens (φ + v) z - topDens φ z) = 0

def MAComparison.Hyp {D : ℕ} (Ω : Set (Fin D → ℂ)) (φ a b : (Fin D → ℂ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ Ω ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a Ω ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b Ω ∧
    (∀ z ∈ Ω, ∀ w, 0 ≤ leviForm (φ + a) z w) ∧ (∀ z ∈ Ω, ∀ w, 0 ≤ leviForm (φ + b) z w) ∧
    ∀ k : ℝ, IsCompact {z | z ∈ Ω ∧ -k ≤ b z - a z}

def MAComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (φ a b : (Fin D → ℂ) → ℝ), MAComparison.Hyp Ω φ a b →
    ∫⁻ z in Ω, ENNReal.ofReal (topDens (φ + b) z) ≤ ∫⁻ z in Ω, ENNReal.ofReal (topDens (φ + a) z)

def CoverMass.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.ncard {x | x ∈ M ∧ z x = w} = δ

def CoverMass.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ

def LocBddRatio {A : Type*} [CommRing A] [Algebra ℂ A] (p q : A) : Prop :=
  ∀ x : A →ₐ[ℂ] ℂ, ∃ (s : Finset A) (ε : ℝ), 0 < ε ∧ ∃ M : ℝ, ∀ y : A →ₐ[ℂ] ℂ,
    (∀ a ∈ s, ‖y a - x a‖ < ε) → y q ≠ 0 → ‖y p‖ ≤ M * ‖y q‖

def RiemannExt.Hyp (A : Type*) [CommRing A] [Algebra ℂ A] (p q : A) : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧ q ≠ 0 ∧ LocBddRatio p q

def RiemannExt.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] (p q : A), RiemannExt.Hyp A p q → ∃ r : A, p = q * r

def IntegralAtPoints {A : Type*} [CommRing A] (h a : A) (N : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (y : A →+* K), (∀ b, ‖y b‖ ≤ 1) → y h ≠ 0 → ‖y a‖ ≤ ‖(N : K)‖

def Normality.Hyp (A : Type*) [CommRing A] (h a : A) (N : ℕ) : Prop :=
  Algebra.FiniteType ℤ A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧ (∀ m : ℤ, m ≠ 0 → (m : A) ≠ 0) ∧
    h ≠ 0 ∧ 0 < N ∧ IntegralAtPoints h a N

def Normality.Statement : Prop :=
  ∀ (A : Type) [CommRing A] (h a : A) (N : ℕ), Normality.Hyp A h a N → ∃ b : A, a = N * b

/- English proof (translation)
Assemble the required witnesses or components as `⟨Matrix.PosSemidef.zero, by rw [sub_zero]; exact (Matrix.PosDef.one).posSemidef⟩`.
-/
theorem DetMono.hyp_inhabited : DetMono.Hyp (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 :=
  ⟨Matrix.PosSemidef.zero, by rw [sub_zero]; exact (Matrix.PosDef.one).posSemidef⟩

/- English proof (translation)
Use `⟨isOpen_univ, contDiff_const.contDiffOn, ?_, ?_, Set.subset_univ _⟩` and prove the remaining obligations. Conclude with `(ContDiffBump.contDiff _).contDiffOn`. Conclude with `ContDiffBump.hasCompactSupport _`.
-/
theorem MACompact.hyp_inhabited :
    MACompact.Hyp (Set.univ : Set (Fin 1 → ℂ)) 0
      (⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : Fin 1 → ℂ))) := by
  refine ⟨isOpen_univ, contDiff_const.contDiffOn, ?_, ?_, Set.subset_univ _⟩
  · exact (ContDiffBump.contDiff _).contDiffOn
  · exact ContDiffBump.hasCompactSupport _

/- English proof (translation)
Establish `hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG (D` using `1)) := by`. Unfold `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG`. Conclude with `contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))`. Establish `h` using `(hG.log fun y => (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG_pos y).ne').div_const 2`. Establish `e : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D` using `1) = fun y => Real.log (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG y) / 2 :=`.

Use function extensionality and compare the values at `fun y => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot_eq y`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem gbPot_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG (D := 1)) := by
    unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG
    exact contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
  have h := (hG.log fun y => (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG_pos y).ne').div_const 2
  have e : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1) =
      fun y => Real.log (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG y) / 2 :=
    funext fun y => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot_eq y
  rw [e]
  exact h

/- English proof (translation)
Establish `hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z = 1 + (z 0).re ^ 2 + (z 0).im ^ 2`. Simplify using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < 1 + (z 0).re ^ 2 + (z 0).im ^ 2` using `by positivity`. Simplify using `only [leviForm, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv_fderiv_gbPot_apply, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbBil_apply, hG, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviForm_gbPot_one (z w : Fin 1 → ℂ) :
    leviForm (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) z w =
      ((w 0).re ^ 2 + (w 0).im ^ 2) / (2 * (1 + (z 0).re ^ 2 + (z 0).im ^ 2) ^ 2) := by
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z = 1 + (z 0).re ^ 2 + (z 0).im ^ 2 := by
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG, Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < 1 + (z 0).re ^ 2 + (z 0).im ^ 2 := by positivity
  simp only [leviForm, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv_fderiv_gbPot_apply, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbBil_apply,
    hG, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  field_simp
  ring

/- English proof (translation)
Establish `hcont : Continuous (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D` using `1)) := gbPot_contDiff.continuous`. Use `⟨isOpen_univ, contDiff_const.contDiffOn, gbPot_contDiff.contDiffOn, contDiff_const.contDiffOn, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z _ w`. Rewrite using `[zero_add, leviForm_gbPot_one]`. Check the signs of the components of the expression.

Introduce `z _ w`. Simplify using `[leviForm]`. Introduce `k`. Establish `hset : {z | z ∈ (Set.univ : Set (Fin 1 → ℂ)) ∧ -k ≤ (0 : (Fin 1 → ℂ) → ℝ) z - ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot z} = {z | ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot z ≤ k}`. Use extensionality with `z`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Pi.zero_apply, zero_sub]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Rewrite using `[hset]`. Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (0 : Fin 1 → ℂ)) (r := Real.exp k)).subset ?_` and prove the remaining obligations.

Introduce `z hz`. Simplify using `only [Set.mem_ofPred_eq] at hz`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `(pi_norm_le_iff_of_nonneg (Real.exp_pos k).le).2 fun i => ?_` and prove the remaining obligations. Establish `hG` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG_pos z`.

Establish `hlog : Real.log (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z) ≤ 2 * k`. Rewrite `hz` using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot_eq]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z ≤ Real.exp (2 * k)` using `(Real.log_le_iff_le_exp hG).1 hlog`. Establish `hi : ‖z i‖ ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z`.

Unfold `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG`. Use `Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : Real.exp (2 * k) = Real.exp k ^ 2` using `by rw [← Real.exp_nat_mul]; ring_nf`. Establish `h2 : ‖z i‖ ^ 2 ≤ Real.exp k ^ 2` using `by linarith`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos k).le two_ne_zero).1 h2`.
-/
theorem MAComparison.hyp_inhabited :
    MAComparison.Hyp (Set.univ : Set (Fin 1 → ℂ)) 0 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot 0 := by
  have hcont : Continuous (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) := gbPot_contDiff.continuous
  refine ⟨isOpen_univ, contDiff_const.contDiffOn, gbPot_contDiff.contDiffOn,
    contDiff_const.contDiffOn, ?_, ?_, ?_⟩
  · intro z _ w
    rw [zero_add, leviForm_gbPot_one]
    positivity
  · intro z _ w
    simp [leviForm]
  · intro k
    have hset : {z | z ∈ (Set.univ : Set (Fin 1 → ℂ)) ∧ -k ≤ (0 : (Fin 1 → ℂ) → ℝ) z -
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot z} = {z | ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot z ≤ k} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Pi.zero_apply, zero_sub]
      constructor <;> intro h <;> linarith
    rw [hset]
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 1 → ℂ)) (r := Real.exp k)).subset ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos k).le).2 fun i => ?_
    have hG := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG_pos z
    have hlog : Real.log (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z) ≤ 2 * k := by
      rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot_eq] at hz; linarith
    have hle : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z ≤ Real.exp (2 * k) := (Real.log_le_iff_le_exp hG).1 hlog
    have hi : ‖z i‖ ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z := by
      unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG
      have := Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
      linarith
    have he : Real.exp (2 * k) = Real.exp k ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : ‖z i‖ ^ 2 ≤ Real.exp k ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos k).le two_ne_zero).1 h2

/- English proof (translation)
Use `⟨isOpen_univ, measure_empty, differentiableOn_id, fun x _ => by simp, ?_, ?_⟩` and prove the remaining obligations. Use `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn ?_ ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_univ.isClosedMap_subtype_val`. Introduce `w _`. Use `Set.Subsingleton.finite fun a ha b hb => Subtype.ext ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, id] at ha hb`. Rewrite using `[ha, hb]`. Conclude with `(isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.1 isOpen_univ.isOpenEmbedding_subtypeVal.isLocalHomeomorph).mono (Set.subset_univ _)`. Introduce `w _`. Establish `: {x | x ∈ (Set.univ : Set (Fin 1 → ℂ)) ∧ id x = w} = {w}` using `by ext x; simp`.

Rewrite using `[this, Set.ncard_singleton]`.
-/
theorem CoverMass.hyp_inhabited :
    CoverMass.Hyp (Set.univ : Set (Fin 1 → ℂ)) ∅ id 1 := by
  refine ⟨isOpen_univ, measure_empty, differentiableOn_id, fun x _ => by simp, ?_, ?_⟩
  · refine IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn ?_ ?_ ?_
    · exact isClosed_univ.isClosedMap_subtype_val
    · intro w _
      refine Set.Subsingleton.finite fun a ha b hb => Subtype.ext ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id] at ha hb
      rw [ha, hb]
    · exact (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.1
        isOpen_univ.isOpenEmbedding_subtypeVal.isLocalHomeomorph).mono (Set.subset_univ _)
  · intro w _
    have : {x | x ∈ (Set.univ : Set (Fin 1 → ℂ)) ∧ id x = w} = {w} := by ext x; simp
    rw [this, Set.ncard_singleton]

/- English proof (translation)
Use `⟨inferInstance, inferInstance, inferInstance, Polynomial.X_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `x`. Use `⟨{Polynomial.X}, 1, one_pos, ‖x Polynomial.X‖ + 1, fun y hy _ => ?_⟩` and prove the remaining obligations. Establish `h1` using `hy Polynomial.X (Finset.mem_singleton_self _)`. Establish `h2 : ‖y Polynomial.X‖ ≤ ‖x Polynomial.X‖ + 1`.

Use `norm_le_norm_add_norm_sub' (y Polynomial.X) (x Polynomial.X)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right h2 (norm_nonneg _)`.
-/
theorem RiemannExt.hyp_inhabited :
    RiemannExt.Hyp (Polynomial ℂ) (Polynomial.X * Polynomial.X) Polynomial.X := by
  refine ⟨inferInstance, inferInstance, inferInstance, Polynomial.X_ne_zero, ?_⟩
  intro x
  refine ⟨{Polynomial.X}, 1, one_pos, ‖x Polynomial.X‖ + 1, fun y hy _ => ?_⟩
  have h1 := hy Polynomial.X (Finset.mem_singleton_self _)
  have h2 : ‖y Polynomial.X‖ ≤ ‖x Polynomial.X‖ + 1 := by
    have := norm_le_norm_add_norm_sub' (y Polynomial.X) (x Polynomial.X)
    linarith
  rw [map_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/- English proof (translation)
Establish `hft : @Algebra.FiniteType ℤ (Polynomial ℤ) _ _ Polynomial.algebraOfAlgebra` using `inferInstance`. Apply the tactic sequence `refine ⟨by convert hft <;> rfl, inferInstance, inferInstance, ?_, one_ne_zero, one_pos, ?_⟩`. Introduce `m hm`. Rewrite using `[← Polynomial.C_eq_intCast]`. Conclude with `Polynomial.C_ne_zero.2 hm`.

Introduce `p _ K _ _ _ y hy _`. Rewrite using `[Nat.cast_one, norm_one]`. Conclude with `hy _`.
-/
theorem Normality.hyp_inhabited :
    Normality.Hyp (Polynomial ℤ) 1 Polynomial.X 1 := by
  have hft : @Algebra.FiniteType ℤ (Polynomial ℤ) _ _ Polynomial.algebraOfAlgebra := inferInstance
  refine ⟨by convert hft <;> rfl, inferInstance, inferInstance, ?_, one_ne_zero, one_pos, ?_⟩
  · intro m hm
    rw [← Polynomial.C_eq_intCast]
    exact Polynomial.C_ne_zero.2 hm
  · intro p _ K _ _ _ y hy _
    rw [Nat.cast_one, norm_one]
    exact hy _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
