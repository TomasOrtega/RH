import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsInStabilizerNilradicalLieTripleMulEqZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointConjMemCongruenceSubgroupOfCongrLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalCenterIntegralCoveringRadiusStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SmallFund

open GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.UG GlobalTheory.NilLie

section Point

variable (I : AutInst)

/- English proof (translation)
Establish `hc : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * b = 1 → (I.P v)⁻¹ * a * I.P v * ((I.P v)⁻¹ * b * I.P v) = 1` using `fun v a b h => by`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun v => ⟨⟨(I.P v)⁻¹ * ex (B v) * I.P v, (I.P v)⁻¹ * ex (-B v) * I.P v, hc v _ _ (ex_mul_ex_neg (hB v)), hc v _ _ (ex_neg_mul_ex (hB v))⟩, ?_⟩, ⟨fun v => ?_, ?_⟩, fun v => rfl⟩` and prove the remaining obligations. Establish `h` using `ex_unitary (hB v)`. Rewrite `h` using `[cT_conj]`.

Use `show ((I.P v)⁻¹ * ex (B v) * I.P v)ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * ex (B v) * I.P v) = Jm (I.ε v)`. Rewrite using `[← I.P_spec v]`. Combine the equalities or inequalities in the displayed calculation. Establish `h : I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹ = ex (B v)`. Combine the equalities or inequalities in the displayed calculation.

Use `show I.InUnipRad _ _ _ (I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹)`. Rewrite using `[h, ← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v]`. Conclude with `ex_unip (hB v)`. Establish `h : I.fmat (1 : I.Gf) = 1` using `by simp [AutInst.fmat]`. Simplify using `only [h, AutInst.InUnipRad, sub_self, Matrix.zero_mulVec]`.

Use `⟨fun _ _ => trivial, fun _ _ => zero_mem _, fun _ => ?_⟩` and prove the remaining obligations. Simplify using `[hform]`.
-/
theorem exists_real (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (B : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) (hB : B ∈ nilReal I R) :
    ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧
      ∀ v, uMat (m v) = (I.P v)⁻¹ * ex (B v) * I.P v := by
  have hc : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * b = 1 →
      (I.P v)⁻¹ * a * I.P v * ((I.P v)⁻¹ * b * I.P v) = 1 := fun v a b h => by
    calc _ = (I.P v)⁻¹ * (a * (I.P v * (I.P v)⁻¹) * b) * I.P v := by simp only [mul_assoc]
      _ = 1 := by rw [P_mul_inv, mul_one, h, mul_one, inv_mul_P]
  refine ⟨fun v => ⟨⟨(I.P v)⁻¹ * ex (B v) * I.P v, (I.P v)⁻¹ * ex (-B v) * I.P v,
    hc v _ _ (ex_mul_ex_neg (hB v)), hc v _ _ (ex_neg_mul_ex (hB v))⟩, ?_⟩, ⟨fun v => ?_, ?_⟩, fun v => rfl⟩
  · have h := ex_unitary (hB v)
    rw [cT_conj] at h
    show ((I.P v)⁻¹ * ex (B v) * I.P v)ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * ex (B v) * I.P v) = Jm (I.ε v)
    rw [← I.P_spec v]
    calc _ = (I.P v)ᴴ * ((ex (B v))ᴴ * (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) *
          ex (B v)) * I.P v := by simp only [conjTranspose_mul, mul_assoc]
      _ = _ := by rw [P_mul_inv, conjTranspose_one, mul_one, mul_one, h]
  · have h : I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹ = ex (B v) := by
      calc _ = (I.P v * (I.P v)⁻¹) * ex (B v) * (I.P v * (I.P v)⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [P_mul_inv, one_mul, mul_one]
    show I.InUnipRad _ _ _ (I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹)
    rw [h, ← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v]
    exact ex_unip (hB v)
  · have h : I.fmat (1 : I.Gf) = 1 := by simp [AutInst.fmat]
    simp only [h, AutInst.InUnipRad, sub_self, Matrix.zero_mulVec]
    refine ⟨fun _ _ => trivial, fun _ _ => zero_mem _, fun _ => ?_⟩
    simp [hform]

/- English proof (translation)
Establish `key : ∀ v, ∃ Y, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) Y ∧ ex Y = I.P v * uMat (ν v) * (I.P v)⁻¹` using `fun v => by`. Establish `h` using `hν.1 v`. Rewrite `h` using `[← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v]`. Use `exists_log ?_ h` and prove the remaining obligations. Establish `hx : (uMat (ν v))ᴴ * Jm (I.ε v) * uMat (ν v) = Jm (I.ε v)` using `(ν v).2`.

Rewrite using `[cT_conj]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, mul_assoc]`. Use `_ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by`. Rewrite using `[I.P_spec, hx, ← I.P_spec]`.

Simplify using `only [conjTranspose_mul, mul_assoc]`. Use `_ = _ := by rw [P_mul_inv, conjTranspose_one, one_mul, mul_one]`. Use `choose Y hY hY' using key`. Use `⟨Y, hY, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hY']`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_real_log (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (ν : I.Ginf)
    (hν : ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E)))) :
    ∃ Y ∈ nilReal I R, ∀ v, uMat (ν v) = (I.P v)⁻¹ * ex (Y v) * I.P v := by
  have key : ∀ v, ∃ Y, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) Y ∧
      ex Y = I.P v * uMat (ν v) * (I.P v)⁻¹ := fun v => by
    have h := hν.1 v
    rw [← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v] at h
    refine exists_log ?_ h
    have hx : (uMat (ν v))ᴴ * Jm (I.ε v) * uMat (ν v) = Jm (I.ε v) := (ν v).2
    rw [cT_conj]
    calc _ = ((I.P v)⁻¹)ᴴ * ((uMat (ν v))ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * uMat (ν v)) * (I.P v)⁻¹ := by
          simp only [conjTranspose_mul, mul_assoc]
      _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          rw [I.P_spec, hx, ← I.P_spec]; simp only [conjTranspose_mul, mul_assoc]
      _ = _ := by rw [P_mul_inv, conjTranspose_one, one_mul, mul_one]
  choose Y hY hY' using key
  refine ⟨Y, hY, fun v => ?_⟩
  rw [hY']
  calc _ = ((I.P v)⁻¹ * I.P v) * uMat (ν v) * ((I.P v)⁻¹ * I.P v) := by rw [inv_mul_P, one_mul, mul_one]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Establish `hJ : IsUnit I.J`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Conclude with `I.J_det`. Establish `hcong : ∀ {Y Z : Matrix (Fin I.n) (Fin I.n) I.E}, Y ∈ nilInt I x R → Z ∈ cenInt I x R → ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (ex ((2 * g : I.E) • Y + (g : I.E) • Z) - 1) *ᵥ y = (g : I.E) • z`. Introduce `Y Z hY hZ y hy`.

Use `⟨2 • (Y *ᵥ y) + (2 * g) • (Y *ᵥ (Y *ᵥ y)) + Z *ᵥ y, ?_, ?_⟩` and prove the remaining obligations. Conclude with `add_mem (add_mem (nsmul_mem (hY.2 y hy) _) (nsmul_mem (hY.2 _ (hY.2 y hy)) _)) (hZ.2 y hy)`. Rewrite using `[ex_add_cen hJ (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1), ex]`. Simplify using `only [add_mulVec, sub_mulVec, smul_mulVec, smul_mul_assoc, mul_smul_comm, one_mulVec, ← mulVec_mulVec]`. Simplify using `only [← Nat.cast_smul_eq_nsmul I.E]`.

Use `push_cast`. Apply the tactic sequence `match_scalars <;> first | ring1 | field_simp`. Establish `hN : InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)` using `nil_add (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1).1`. Set `γ : GL (Fin I.n) I.E` to `⟨ex ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀), ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)), ex_mul_ex_neg hN, ex_neg_mul_ex hN⟩`. Take `⟨a, ha, h1, h2⟩` from `GlobalTheory.T.rational_unipotentRadical_mem_adelic I _ γ (ex_unitary hN) (ex_unip hN)`.

Use `⟨a, ha, GlobalTheory.T.pointConj_mem_congruenceSubgroup_of_congr_lattice I x a g γ h2 (hcong hY hZ) fun y hy => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `hY' : -Y₀ ∈ nilInt I x R` using `⟨nil_neg hY.1, fun u hu => by rw [neg_mulVec]; exact neg_mem (hY.2 u hu)⟩`. Establish `hZ' : -Z₀ ∈ cenInt I x R` using `⟨by simpa using cen_smul (c := -1) (by simp) hZ.1, fun u hu => by rw [neg_mulVec]; exact neg_mem (hZ.2 u hu)⟩`. Take `⟨z, hz, e⟩` from `hcong hY' hZ' y hy`. Rewrite `e` using `[smul_neg, smul_neg, ← neg_add, sub_mulVec, one_mulVec, sub_eq_iff_eq_add]`.

Use `show ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)) *ᵥ y ∈ _`. Rewrite using `[e, Nat.cast_smul_eq_nsmul]`. Conclude with `add_mem (nsmul_mem hz _) hy`. Rewrite using `[h1]`. Use `congr 2`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;>`. Simplify using `[γ, ex, Matrix.mul_apply, Matrix.one_apply, hij, map_ofNat]`.
-/
theorem exists_rat (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    {Y₀ Z₀ : Matrix (Fin I.n) (Fin I.n) I.E} (hY : Y₀ ∈ nilInt I x R) (hZ : Z₀ ∈ cenInt I x R) :
    ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧
      ∀ v, uMat (γ.1 v) = (I.P v)⁻¹ *
        ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) * I.P v := by
  have hJ : IsUnit I.J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]; exact I.J_det
  have hcong : ∀ {Y Z : Matrix (Fin I.n) (Fin I.n) I.E}, Y ∈ nilInt I x R → Z ∈ cenInt I x R →
      ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (ex ((2 * g : I.E) • Y + (g : I.E) • Z) - 1) *ᵥ y = (g : I.E) • z := by
    intro Y Z hY hZ y hy
    refine ⟨2 • (Y *ᵥ y) + (2 * g) • (Y *ᵥ (Y *ᵥ y)) + Z *ᵥ y, ?_, ?_⟩
    · exact add_mem (add_mem (nsmul_mem (hY.2 y hy) _) (nsmul_mem (hY.2 _ (hY.2 y hy)) _)) (hZ.2 y hy)
    · rw [ex_add_cen hJ (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1), ex]
      simp only [add_mulVec, sub_mulVec, smul_mulVec, smul_mul_assoc, mul_smul_comm, one_mulVec,
        ← mulVec_mulVec]
      simp only [← Nat.cast_smul_eq_nsmul I.E]
      push_cast
      match_scalars <;> first | ring1 | field_simp
  have hN : InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀) :=
    nil_add (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1).1
  let γ : GL (Fin I.n) I.E := ⟨ex ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀), ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)),
    ex_mul_ex_neg hN, ex_neg_mul_ex hN⟩
  obtain ⟨a, ha, h1, h2⟩ := GlobalTheory.T.rational_unipotentRadical_mem_adelic I _ γ (ex_unitary hN) (ex_unip hN)
  refine ⟨a, ha, GlobalTheory.T.pointConj_mem_congruenceSubgroup_of_congr_lattice I x a g γ h2 (hcong hY hZ) fun y hy => ?_, fun v => ?_⟩
  · have hY' : -Y₀ ∈ nilInt I x R :=
      ⟨nil_neg hY.1, fun u hu => by rw [neg_mulVec]; exact neg_mem (hY.2 u hu)⟩
    have hZ' : -Z₀ ∈ cenInt I x R :=
      ⟨by simpa using cen_smul (c := -1) (by simp) hZ.1,
        fun u hu => by rw [neg_mulVec]; exact neg_mem (hZ.2 u hu)⟩
    obtain ⟨z, hz, e⟩ := hcong hY' hZ' y hy
    rw [smul_neg, smul_neg, ← neg_add, sub_mulVec, one_mulVec, sub_eq_iff_eq_add] at e
    show ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)) *ᵥ y ∈ _
    rw [e, Nat.cast_smul_eq_nsmul]
    exact add_mem (nsmul_mem hz _) hy
  · rw [h1]
    congr 2
    ext i j
    by_cases hij : i = j <;>
      simp [γ, ex, Matrix.mul_apply, Matrix.one_apply, hij, map_ofNat]

end Point

/- English proof (translation)
Take `⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ f = t ^ 2` from `⟨Real.sqrt f, Real.sqrt_pos.2 hf, (Real.sq_sqrt hf.le).symm⟩`. Establish `h2 : (4 / 3 : ℝ) ≤ Real.sqrt 2` using `Real.le_sqrt_of_sq_le (by norm_num)`. Rewrite using `[Real.sqrt_mul (by norm_num), Real.sqrt_sq ht.le]`. Establish `hc : 0 ≤ N * t * g * rd * rho` using `by positivity`. Establish `e : 2 * g * (N * t ^ 2 / 8 * rd * rho / (Real.sqrt 2 * t)) + g * (N * t ^ 2 * rd * rho / (16 * t)) = N * t * g * rd * rho / (4 * Real.sqrt 2) + N * t * g * rd * rho / 16`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : N * t * g * rd * rho / (4 * Real.sqrt 2) ≤ N * t * g * rd * rho / (4 * (4 / 3))` using `by gcongr`. Rewrite using `[e]`. Generalize the expression as in `N * t * g * rd * rho = c at *`.

Establish `h4 : c / (4 * (4 / 3)) = 3 / 16 * c` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem radius_le (N f g rd rho : ℝ) (hN : 0 ≤ N) (hf : 0 < f) (hg : 0 ≤ g) (hrd : 0 ≤ rd) (hrho : 0 ≤ rho) :
    2 * g * (N * f / 8 * rd * rho / Real.sqrt (2 * f)) + g * (N * f * rd * rho / (16 * Real.sqrt f)) ≤
      N * Real.sqrt f * g * rd * rho / 4 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ f = t ^ 2 := ⟨Real.sqrt f, Real.sqrt_pos.2 hf, (Real.sq_sqrt hf.le).symm⟩
  have h2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ht.le]
  have hc : 0 ≤ N * t * g * rd * rho := by positivity
  have e : 2 * g * (N * t ^ 2 / 8 * rd * rho / (Real.sqrt 2 * t)) + g * (N * t ^ 2 * rd * rho / (16 * t)) =
      N * t * g * rd * rho / (4 * Real.sqrt 2) + N * t * g * rd * rho / 16 := by
    field_simp
    ring
  have h3 : N * t * g * rd * rho / (4 * Real.sqrt 2) ≤ N * t * g * rd * rho / (4 * (4 / 3)) := by
    gcongr
  rw [e]
  generalize N * t * g * rd * rho = c at *
  have h4 : c / (4 * (4 / 3)) = 3 / 16 * c := by ring
  linarith

/- English proof (translation)
Introduce `I x g R lo hi rho hg hsat _ hiso hhi hlarge hlo hhl hh2 ν hν`. Establish `hrho : 0 < rho` using `by nlinarith [sq_pos_of_pos hhi]`. Establish `hlo0 : 0 < lo`. Assume the negation of the conclusion as `h`. Use polynomial arithmetic with `[mul_nonneg hrho.le (neg_nonneg.2 (not_lt.1 h))]`.

Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast hg`. Establish `hgc : ((g : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hg0.ne'`. Establish `hreal : ∀ c : ℝ, starRingEnd ℂ (c : ℂ) = c` using `Complex.conj_ofReal`. Take `⟨-, -, -, hnil, hcen⟩` from `GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R`. Take `⟨Y, hY, hνY⟩` from `exists_real_log I x R ν hν`.

Take `⟨Y₀, hY₀, Z, hZ, hA⟩` from `GlobalTheory.T.nilradical_first_layer_covering_radius_le I x R lo hi rho hsat hiso hhi hlarge hlo hlo0 hhl (fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) (fun v => nil_smul (hreal _) (hY v))`. Establish `hY₀'` using `hnil Y₀ hY₀.1`. Use `set A : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) • ((fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) - diagEmb I Y₀ - Z) v with hAdef`. Establish `hAn : A ∈ nilReal I R` using `fun v => nil_smul (hreal _) (nil_sub (nil_sub (nil_smul (hreal _) (hY v)) (hY₀' v)) (hZ v).1)`. Use `set Z'' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) • Z v + (2 : ℂ)⁻¹ • (A v * (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) - (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) * A v) with hZ''def`.

Establish `hZ''c : Z'' ∈ cenReal I R` using `fun v => cen_add (cen_smul (hreal _) (hZ v)) (cen_smul map_half (cen_comm (hAn v) (nil_smul (hreal _) (hY₀' v))))`. Take `⟨Z₀, hZ₀, hZ'⟩` from `GlobalTheory.T.nilradicalCenter_integral_covering_radius I x R hi rho hsat hiso hhi hlarge hh2 (fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) (fun v => cen_smul (hreal _) (hZ''c v))`. Establish `hZ₀'` using `hcen Z₀ hZ₀.1`. Use `set Z' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((g : ℝ) : ℂ) • ((fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) - diagEmb I Z₀) v with hZ'def`. Establish `hZ'c : Z' ∈ cenReal I R` using `fun v => cen_smul (hreal _) (cen_sub (cen_smul (hreal _) (hZ''c v)) (hZ₀' v))`.

Take `⟨γ, hγ, hγK, hγv⟩` from `exists_rat I x g R hY₀ hZ₀`. Establish `hfac : ∀ v, ex (Y v) = ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) * ex (A v) * ex (Z' v)` using `fun v => by`. Use `ex_factor (isUnit_Jv I v) (nil_smul (hreal (2 * g)) (hY₀' v)) (hAn v) (cen_smul (hreal g) (hZ₀' v)) (hZ'c v)` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 1`.

Establish `e1 : ((g : ℝ) : ℂ) • diagEmb I Z₀ v + Z' v = Z'' v`. Simplify using `only [hZ'def, Pi.sub_apply, smul_sub, smul_smul]`. Rewrite using `[Complex.ofReal_inv, mul_inv_cancel₀ hgc, one_smul]`. Normalize the expressions using the abelian group laws. Establish `e2 : ((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v + A v + ((2 * g : ℝ) : ℂ) • Z v = Y v`.

Simplify using `only [hAdef, Pi.sub_apply, smul_sub, smul_smul]`. Rewrite using `[Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast (by positivity : (2 * g : ℝ) ≠ 0)), one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, ← e2, hZ''def]`. Simplify using `only [add_sub_cancel_right]`.

Establish `hprod : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * (a * a) = 0 → b * (b * b) = 0 → uMat (x.1 v) * NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * a * (I.P v * uMat (x.1 v))) * NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * b * (I.P v * uMat (x.1 v))) = (I.P v)⁻¹ * (ex a * ex b) * …` using `fun v a b ha hb => by`. Rewrite using `[exp_conj (frame_mul I x v) (mul_frame I x v) ha, exp_conj (frame_mul I x v) (mul_frame I x v) hb]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [uMat_mul_inv, frame_mul]; simp only [mul_assoc, one_mul]`.

Use `⟨γ, hγ, hγK, fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)), fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)), fun v => ⟨inG_frame I x v (hAn v), inG_frame I x v (hZ'c v).1⟩, fun v => ?_, ?_, fun s t => ?_⟩` and prove the remaining obligations. Use `hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hAn v) (hAn v) (hAn v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (hZ'c v).1 (hZ'c v).1 (hZ'c v).1)` as an intermediate fact. Rewrite using `[mul_assoc (uMat (γ.1 v)), mul_assoc (uMat (γ.1 v)), this, hνY, hγv, hfac]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[P_mul_inv]`.

Simplify using `only [mul_assoc, one_mul]`. Use `_ = _ := by simp only [mul_assoc]`. Establish `n1 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)))) = normAt I x A` using `by simp only [normAt, mul_assoc]`. Establish `n2 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)))) = normAt I x Z'` using `by simp only [normAt, mul_assoc]`. Rewrite using `[n1, n2, hAdef, hZ'def, normAt_smul I x _ (by positivity), normAt_smul I x _ hg0.le]`.

Establish `hf : (0 : ℝ) < I.f` using `by exact_mod_cast (Module.finrank_pos : 0 < I.f)`. Establish `hrd : 0 ≤ I.rd` using `Real.rpow_nonneg (abs_nonneg _) _`. Use `le_trans ?_ (radius_le ((I.n : ℝ) ^ 2) I.f g I.rd rho (by positivity) hf hg0.le hrd hrho.le)` and prove the remaining obligations. Use `gcongr`. Establish `hs' : ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((s : ℂ) • A v)` using `fun v => nil_smul (hreal s) (hAn v)`.

Establish `ht' : ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((t : ℂ) • Z' v)` using `fun v => cen_smul (hreal t) (hZ'c v)`. Take `⟨m, hm, hmv⟩` from `exists_real I x R (fun v => (s : ℂ) • A v + (t : ℂ) • Z' v) (fun v => nil_add (hs' v) (ht' v).1)`. Use `⟨m, hm, fun v => ?_⟩` and prove the remaining obligations. Use `hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hs' v) (hs' v) (hs' v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (ht' v).1 (ht' v).1 (ht' v).1)` as an intermediate fact. Rewrite `this` using `[ex_mul_ex_cen (isUnit_Jv I v) (hs' v) (ht' v), ← hmv]`.

Rewrite using `[← this]`. Simplify using `only [mul_smul_comm, smul_mul_assoc]`.
-/
theorem small_fundamental_set : ∀ (I : AutInst) (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), 1 ≤ g → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≠ ⊥ → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → hi ≤ rho * lo → hi ^ 2 ≤ rho / 4 → ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) → ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * rho / 4 ∧ ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧ ∀ v, uMat (m v) * uMat (x.1 v) = uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v) := by
  intro I x g R lo hi rho hg hsat _ hiso hhi hlarge hlo hhl hh2 ν hν
  have hrho : 0 < rho := by nlinarith [sq_pos_of_pos hhi]
  have hlo0 : 0 < lo := by
    by_contra h
    nlinarith [mul_nonneg hrho.le (neg_nonneg.2 (not_lt.1 h))]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hgc : ((g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hreal : ∀ c : ℝ, starRingEnd ℂ (c : ℂ) = c := Complex.conj_ofReal
  obtain ⟨-, -, -, hnil, hcen⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  obtain ⟨Y, hY, hνY⟩ := exists_real_log I x R ν hν
  obtain ⟨Y₀, hY₀, Z, hZ, hA⟩ := GlobalTheory.T.nilradical_first_layer_covering_radius_le I x R lo hi rho hsat hiso hhi hlarge hlo hlo0 hhl
    (fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) (fun v => nil_smul (hreal _) (hY v))
  have hY₀' := hnil Y₀ hY₀.1
  set A : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) •
    ((fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) - diagEmb I Y₀ - Z) v with hAdef
  have hAn : A ∈ nilReal I R := fun v =>
    nil_smul (hreal _) (nil_sub (nil_sub (nil_smul (hreal _) (hY v)) (hY₀' v)) (hZ v).1)
  set Z'' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) • Z v +
    (2 : ℂ)⁻¹ • (A v * (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) - (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) * A v)
    with hZ''def
  have hZ''c : Z'' ∈ cenReal I R := fun v =>
    cen_add (cen_smul (hreal _) (hZ v)) (cen_smul map_half (cen_comm (hAn v) (nil_smul (hreal _) (hY₀' v))))
  obtain ⟨Z₀, hZ₀, hZ'⟩ := GlobalTheory.T.nilradicalCenter_integral_covering_radius I x R hi rho hsat hiso hhi hlarge hh2
    (fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) (fun v => cen_smul (hreal _) (hZ''c v))
  have hZ₀' := hcen Z₀ hZ₀.1
  set Z' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((g : ℝ) : ℂ) •
    ((fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) - diagEmb I Z₀) v with hZ'def
  have hZ'c : Z' ∈ cenReal I R := fun v =>
    cen_smul (hreal _) (cen_sub (cen_smul (hreal _) (hZ''c v)) (hZ₀' v))
  obtain ⟨γ, hγ, hγK, hγv⟩ := exists_rat I x g R hY₀ hZ₀
  have hfac : ∀ v, ex (Y v) = ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) *
      ex (A v) * ex (Z' v) := fun v => by
    have := ex_factor (isUnit_Jv I v) (nil_smul (hreal (2 * g)) (hY₀' v)) (hAn v)
      (cen_smul (hreal g) (hZ₀' v)) (hZ'c v)
    refine Eq.trans ?_ this
    congr 1
    have e1 : ((g : ℝ) : ℂ) • diagEmb I Z₀ v + Z' v = Z'' v := by
      simp only [hZ'def, Pi.sub_apply, smul_sub, smul_smul]
      rw [Complex.ofReal_inv, mul_inv_cancel₀ hgc, one_smul]; abel
    have e2 : ((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v + A v + ((2 * g : ℝ) : ℂ) • Z v = Y v := by
      simp only [hAdef, Pi.sub_apply, smul_sub, smul_smul]
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast (by positivity : (2 * g : ℝ) ≠ 0)), one_smul]
      abel
    rw [e1, ← e2, hZ''def]
    simp only [add_sub_cancel_right]
  have hprod : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * (a * a) = 0 → b * (b * b) = 0 →
      uMat (x.1 v) * NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * a * (I.P v * uMat (x.1 v))) *
        NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * b * (I.P v * uMat (x.1 v))) =
      (I.P v)⁻¹ * (ex a * ex b) * I.P v * uMat (x.1 v) := fun v a b ha hb => by
    rw [exp_conj (frame_mul I x v) (mul_frame I x v) ha, exp_conj (frame_mul I x v) (mul_frame I x v) hb]
    calc _ = (uMat (x.1 v) * uMat (x.1 v)⁻¹) * (I.P v)⁻¹ * ex a *
          (I.P v * uMat (x.1 v) * (uMat (x.1 v)⁻¹ * (I.P v)⁻¹)) * ex b * (I.P v * uMat (x.1 v)) := by
          simp only [mul_assoc]
      _ = _ := by rw [uMat_mul_inv, frame_mul]; simp only [mul_assoc, one_mul]
  refine ⟨γ, hγ, hγK, fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)),
    fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)),
    fun v => ⟨inG_frame I x v (hAn v), inG_frame I x v (hZ'c v).1⟩, fun v => ?_, ?_, fun s t => ?_⟩
  · have := hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hAn v) (hAn v) (hAn v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (hZ'c v).1 (hZ'c v).1 (hZ'c v).1)
    rw [mul_assoc (uMat (γ.1 v)), mul_assoc (uMat (γ.1 v)), this, hνY, hγv, hfac]
    calc _ = (I.P v)⁻¹ * ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) *
          (I.P v * (I.P v)⁻¹) * (ex (A v) * ex (Z' v)) * I.P v * uMat (x.1 v) := by
          rw [P_mul_inv]; simp only [mul_assoc, one_mul]
      _ = _ := by simp only [mul_assoc]
  · have n1 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)))) =
        normAt I x A := by simp only [normAt, mul_assoc]
    have n2 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)))) =
        normAt I x Z' := by simp only [normAt, mul_assoc]
    rw [n1, n2, hAdef, hZ'def, normAt_smul I x _ (by positivity), normAt_smul I x _ hg0.le]
    have hf : (0 : ℝ) < I.f := by exact_mod_cast (Module.finrank_pos : 0 < I.f)
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine le_trans ?_ (radius_le ((I.n : ℝ) ^ 2) I.f g I.rd rho (by positivity) hf hg0.le hrd hrho.le)
    gcongr
  · have hs' : ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((s : ℂ) • A v) :=
      fun v => nil_smul (hreal s) (hAn v)
    have ht' : ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((t : ℂ) • Z' v) :=
      fun v => cen_smul (hreal t) (hZ'c v)
    obtain ⟨m, hm, hmv⟩ := exists_real I x R (fun v => (s : ℂ) • A v + (t : ℂ) • Z' v)
      (fun v => nil_add (hs' v) (ht' v).1)
    refine ⟨m, hm, fun v => ?_⟩
    have := hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hs' v) (hs' v) (hs' v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (ht' v).1 (ht' v).1 (ht' v).1)
    rw [ex_mul_ex_cen (isUnit_Jv I v) (hs' v) (ht' v), ← hmv] at this
    rw [← this]
    simp only [mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmallFund
