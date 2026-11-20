import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace LatOnly

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma tsum_sub {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∑' l : Λ, f (l : ℂ) = ∑' l : Λ', f (l : ℂ) := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma tprod_submodule_congr {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∏' l : Λ, f (l : ℂ) = ∏' l : Λ', f (l : ℂ) := by
  subst h
  rfl

variable {L L' : PeriodPair}

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [wZeta]`. Conclude with `tsum_sub h (fun w => 1 / (z - w) + 1 / w + z / w ^ 2)`.
-/
lemma wZeta_eq (h : L.lattice = L'.lattice) : wZeta L = wZeta L' := by
  funext z
  simp only [wZeta]
  exact tsum_sub h (fun w => 1 / (z - w) + 1 / w + z / w ^ 2)

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [wSigma]`. Rewrite using `[tprod_submodule_congr h (fun w => wFactor w z)]`.
-/
lemma wSigma_eq (h : L.lattice = L'.lattice) : wSigma L = wSigma L' := by
  funext z
  simp only [wSigma]
  rw [tprod_submodule_congr h (fun w => wFactor w z)]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [PeriodPair.weierstrassP]`. Conclude with `tsum_sub h (fun w => 1 / (z - w) ^ 2 - 1 / w ^ 2)`.
-/
lemma wp_eq (h : L.lattice = L'.lattice) : L.weierstrassP = L'.weierstrassP := by
  funext z
  simp only [PeriodPair.weierstrassP]
  exact tsum_sub h (fun w => 1 / (z - w) ^ 2 - 1 / w ^ 2)

/- English proof (translation)
Simplify using `only [PeriodPair.G]`. Conclude with `tsum_sub h (fun w => (w ^ n)⁻¹)`.
-/
lemma G_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n := by
  simp only [PeriodPair.G]
  exact tsum_sub h (fun w => (w ^ n)⁻¹)

/- English proof (translation)
Establish `hhalf : L.ω₁ / 2 ∉ L.lattice`. Introduce `hx`. Take `⟨p, q, hpq⟩` from `PeriodPair.mem_lattice.mp hx`. Establish `hli` using `L.indep`. Rewrite `hli` using `[LinearIndependent.pair_iff]`.

Take `⟨h1, h2⟩` from `hli ((p : ℝ) - 1 / 2) (q : ℝ) (by`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `hpq)`. Establish `h3 : (2 : ℝ) * p = 1` using `by linarith`.

Establish `h2p : (2 * p : ℤ) = 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Establish `hω' : ω ∈ L'.lattice` using `by rw [← h]; exact hω`. Establish `hhalf' : L.ω₁ / 2 ∉ L'.lattice` using `by rw [← h]; exact hhalf`. Establish `e1` using `zetaQuasi L ω (L.ω₁ / 2) hω hhalf`.

Establish `e2` using `zetaQuasi L' ω (L.ω₁ / 2) hω' hhalf'`. Rewrite `e1` using `[wZeta_eq h]`. Take the linear combination `e2 - e1`.
-/
lemma wEta_eq_on (h : L.lattice = L'.lattice) {ω : ℂ} (hω : ω ∈ L.lattice) :
    wEta L ω = wEta L' ω := by
  have hhalf : L.ω₁ / 2 ∉ L.lattice := by
    intro hx
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hx
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli ((p : ℝ) - 1 / 2) (q : ℝ) (by
      simp only [Complex.real_smul]
      push_cast
      linear_combination hpq)
    have h3 : (2 : ℝ) * p = 1 := by linarith
    have h2p : (2 * p : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hω' : ω ∈ L'.lattice := by rw [← h]; exact hω
  have hhalf' : L.ω₁ / 2 ∉ L'.lattice := by rw [← h]; exact hhalf
  have e1 := zetaQuasi L ω (L.ω₁ / 2) hω hhalf
  have e2 := zetaQuasi L' ω (L.ω₁ / 2) hω' hhalf'
  rw [wZeta_eq h] at e1
  linear_combination e2 - e1

/- English proof (translation)
Establish `hb0 : L.basis 0 = L.ω₁` using `by first`. Consider the case `exact L.basis_zero`. Consider the case `simp [PeriodPair.basis]`. Establish `hb1 : L.basis 1 = L.ω₂` using `by first`. Consider the case `exact L.basis_one`.

Consider the case `simp [PeriodPair.basis]`. Establish `hω₁ : L.ω₁ ∈ L.lattice` using `PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩`. Establish `hω₂ : L.ω₂ ∈ L.lattice` using `PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩`. Apply `L.basis.ext` to reduce the goal to its premises. Introduce `i`.

Use `fin_cases i`. Use `show wEta L (L.basis 0) = wEta L' (L.basis 0)`. Rewrite using `[hb0]`. Conclude with `wEta_eq_on h hω₁`. Use `show wEta L (L.basis 1) = wEta L' (L.basis 1)`.

Rewrite using `[hb1]`. Conclude with `wEta_eq_on h hω₂`.
-/
lemma wEta_eq (h : L.lattice = L'.lattice) : wEta L = wEta L' := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [PeriodPair.basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have hω₁ : L.ω₁ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩
  have hω₂ : L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩
  apply L.basis.ext
  intro i
  fin_cases i
  · show wEta L (L.basis 0) = wEta L' (L.basis 0)
    rw [hb0]
    exact wEta_eq_on h hω₁
  · show wEta L (L.basis 1) = wEta L' (L.basis 1)
    rw [hb1]
    exact wEta_eq_on h hω₂

/- English proof (translation)
Rewrite using `[etaSplit L 1, etaSplit L Complex.I]`. Simplify using `only [map_one, Complex.conj_I]`. Take the linear combination `((s2 L - (Real.pi : ℂ) / (area L : ℂ)) / 2) * Complex.I_sq`.
-/
lemma quasiPeriodConst_formula (L : PeriodPair) : s2 L = (wEta L 1 - Complex.I * wEta L Complex.I) / 2 := by
  rw [etaSplit L 1, etaSplit L Complex.I]
  simp only [map_one, Complex.conj_I]
  linear_combination ((s2 L - (Real.pi : ℂ) / (area L : ℂ)) / 2) * Complex.I_sq

/- English proof (translation)
Rewrite using `[etaSplit L 1, etaSplit L Complex.I]`. Simplify using `only [map_one, Complex.conj_I]`. Take the linear combination `(((Real.pi : ℂ) / (area L : ℂ) - s2 L) / 2) * Complex.I_sq`.
-/
lemma piA_formula (L : PeriodPair) :
    (Real.pi : ℂ) / (area L : ℂ) = (wEta L 1 + Complex.I * wEta L Complex.I) / 2 := by
  rw [etaSplit L 1, etaSplit L Complex.I]
  simp only [map_one, Complex.conj_I]
  linear_combination (((Real.pi : ℂ) / (area L : ℂ) - s2 L) / 2) * Complex.I_sq

/- English proof (translation)
Rewrite using `[quasiPeriodConst_formula L, quasiPeriodConst_formula L', wEta_eq h]`.
-/
lemma quasiPeriodConst_eq (h : L.lattice = L'.lattice) : s2 L = s2 L' := by
  rw [quasiPeriodConst_formula L, quasiPeriodConst_formula L', wEta_eq h]

/- English proof (translation)
Establish `h1` using `piA_formula L`. Rewrite `h1` using `[wEta_eq h, ← piA_formula L']`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h2 : (area L : ℂ)⁻¹ = (area L' : ℂ)⁻¹`. Rewrite `h1` using `[div_eq_mul_inv, div_eq_mul_inv]`.

Conclude with `mul_left_cancel₀ hpi h1`. Establish `h3 : (area L : ℂ) = area L'` using `inv_inj.mp h2`. Conclude with `h3` after adjusting the coercions.
-/
lemma area_eq (h : L.lattice = L'.lattice) : area L = area L' := by
  have h1 := piA_formula L
  rw [wEta_eq h, ← piA_formula L'] at h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (area L : ℂ)⁻¹ = (area L' : ℂ)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv] at h1
    exact mul_left_cancel₀ hpi h1
  have h3 : (area L : ℂ) = area L' := inv_inj.mp h2
  exact_mod_cast h3

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [sgStar]`. Rewrite using `[wSigma_eq h, quasiPeriodConst_eq h]`.
-/
lemma sgStar_eq (h : L.lattice = L'.lattice) : sgStar L = sgStar L' := by
  funext z
  simp only [sgStar]
  rw [wSigma_eq h, quasiPeriodConst_eq h]

end LatOnly

/- English proof (translation)
Introduce `L L' h`. Use `⟨LatOnly.wZeta_eq h, LatOnly.wSigma_eq h, LatOnly.wEta_eq h, LatOnly.area_eq h, LatOnly.quasiPeriodConst_eq h, LatOnly.sgStar_eq h, LatOnly.wp_eq h, ?_, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `simp only [PeriodPair.g₂, LatOnly.G_eq h]`. Consider the case `(unfold PeriodPair.g₂`.

Rewrite using `[LatOnly.G_eq h])`. Consider the case `(unfold PeriodPair.g₂ done)`. Use `first`. Consider the case `simp only [PeriodPair.g₃, LatOnly.G_eq h]`. Consider the case `(unfold PeriodPair.g₃`.

Rewrite using `[LatOnly.G_eq h])`. Consider the case `(unfold PeriodPair.g₃ done)`.
-/
theorem lattice_only : LatticeOnly := by
  intro L L' h
  refine ⟨LatOnly.wZeta_eq h, LatOnly.wSigma_eq h, LatOnly.wEta_eq h, LatOnly.area_eq h,
    LatOnly.quasiPeriodConst_eq h, LatOnly.sgStar_eq h, LatOnly.wp_eq h, ?_, ?_⟩
  · first
      | simp only [PeriodPair.g₂, LatOnly.G_eq h]
      | (unfold PeriodPair.g₂
         rw [LatOnly.G_eq h])
      | (unfold PeriodPair.g₂
         done)
  · first
      | simp only [PeriodPair.g₃, LatOnly.G_eq h]
      | (unfold PeriodPair.g₃
         rw [LatOnly.G_eq h])
      | (unfold PeriodPair.g₃
         done)

namespace Homog

variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice, PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, hmn⟩`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z at hmn`.

Rewrite using `[← hmn, show c⁻¹ * ((m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂)) = (c⁻¹ * c) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring, inv_mul_cancel₀ hc, one_mul]`. Introduce and unpack `⟨m, n, hmn⟩`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z`. Rewrite using `[show (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = c * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring, hmn, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]`.
-/
lemma mem_scale (z : ℂ) : z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z at hmn
    rw [← hmn, show c⁻¹ * ((m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂))
        = (c⁻¹ * c) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring, inv_mul_cancel₀ hc, one_mul]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z
    rw [show (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = c * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring,
      hmn, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

def scaleEquiv : L.lattice ≃ (scalePair L c hc).lattice where
  toFun l := ⟨c * (l : ℂ), (mem_scale L c hc _).2 (by rw [inv_mul_cancel_left₀ hc]; exact l.2)⟩
  invFun l := ⟨c⁻¹ * (l : ℂ), (mem_scale L c hc _).1 l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [hc]

/- English proof (translation)
The claim follows from `(Equiv.tsum_eq (scaleEquiv L c hc) (fun l => f (l : ℂ))).symm`.
-/
lemma tsum_scale (f : ℂ → ℂ) :
    ∑' l : (scalePair L c hc).lattice, f (l : ℂ) = ∑' l : L.lattice, f (c * (l : ℂ)) := (Equiv.tsum_eq (scaleEquiv L c hc) (fun l => f (l : ℂ))).symm

/- English proof (translation)
The claim follows from `(Equiv.tprod_eq (scaleEquiv L c hc) (fun l => f (l : ℂ))).symm`.
-/
lemma tprod_scale (f : ℂ → ℂ) :
    ∏' l : (scalePair L c hc).lattice, f (l : ℂ) = ∏' l : L.lattice, f (c * (l : ℂ)) := (Equiv.tprod_eq (scaleEquiv L c hc) (fun l => f (l : ℂ))).symm

/- English proof (translation)
Simplify using `only [wZeta]`. Rewrite using `[tsum_scale L c hc (fun w => 1 / (c * z - w) + 1 / w + c * z / w ^ 2), ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `try dsimp only`.

Establish `e : c * z - c * (l : ℂ) = c * (z - l)` using `by ring`. Establish `hc2 : c * (c ^ 2)⁻¹ = c⁻¹`. Rewrite using `[pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Rewrite using `[e]`. Simplify using `only [one_div, mul_inv, div_eq_mul_inv, mul_pow]`.

Take the linear combination `(z * ((l : ℂ) ^ 2)⁻¹) * hc2`.
-/
lemma wZeta_scale (z : ℂ) : wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z := by
  simp only [wZeta]
  rw [tsum_scale L c hc (fun w => 1 / (c * z - w) + 1 / w + c * z / w ^ 2), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  have e : c * z - c * (l : ℂ) = c * (z - l) := by ring
  have hc2 : c * (c ^ 2)⁻¹ = c⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [e]
  simp only [one_div, mul_inv, div_eq_mul_inv, mul_pow]
  linear_combination (z * ((l : ℂ) ^ 2)⁻¹) * hc2

omit L in
include hc in
/- English proof (translation)
Unfold `wFactor`. Establish `h1 : c * z / (c * l) = z / l` using `mul_div_mul_left z l hc`. Establish `h2 : (c * z) ^ 2 / (2 * (c * l) ^ 2) = z ^ 2 / (2 * l ^ 2)`. Rewrite using `[show (c * z) ^ 2 = c ^ 2 * z ^ 2 by ring, show 2 * (c * l) ^ 2 = c ^ 2 * (2 * l ^ 2) by ring]`. Conclude with `mul_div_mul_left _ _ (pow_ne_zero 2 hc)`.

Rewrite using `[h1, h2]`.
-/
lemma wFactor_scale (l z : ℂ) : wFactor (c * l) (c * z) = wFactor l z := by
  unfold wFactor
  have h1 : c * z / (c * l) = z / l := mul_div_mul_left z l hc
  have h2 : (c * z) ^ 2 / (2 * (c * l) ^ 2) = z ^ 2 / (2 * l ^ 2) := by
    rw [show (c * z) ^ 2 = c ^ 2 * z ^ 2 by ring, show 2 * (c * l) ^ 2 = c ^ 2 * (2 * l ^ 2) by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)
  rw [h1, h2]

/- English proof (translation)
Simplify using `only [wSigma]`. Rewrite using `[tprod_scale L c hc (fun w => wFactor w (c * z))]`. Apply the tactic sequence `try dsimp only`. Simplify using `only [wFactor_scale c hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma wSigma_scale (z : ℂ) : wSigma (scalePair L c hc) (c * z) = c * wSigma L z := by
  simp only [wSigma]
  rw [tprod_scale L c hc (fun w => wFactor w (c * z))]
  try dsimp only
  simp only [wFactor_scale c hc]
  ring

/- English proof (translation)
Simplify using `only [PeriodPair.weierstrassP]`. Rewrite using `[tsum_scale L c hc (fun w => 1 / (c * z - w) ^ 2 - 1 / w ^ 2), ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[show c * z - c * (l : ℂ) = c * (z - l) by ring]`. Simplify using `only [one_div, mul_inv, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma wp_scale (z : ℂ) :
    (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z := by
  simp only [PeriodPair.weierstrassP]
  rw [tsum_scale L c hc (fun w => 1 / (c * z - w) ^ 2 - 1 / w ^ 2), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [show c * z - c * (l : ℂ) = c * (z - l) by ring]
  simp only [one_div, mul_inv, mul_pow]
  ring

/- English proof (translation)
Simplify using `only [PeriodPair.G]`. Rewrite using `[tsum_scale L c hc (fun w => (w ^ n)⁻¹), ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[mul_pow, mul_inv]`.
-/
lemma G_scale (n : ℕ) : (scalePair L c hc).G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [tsum_scale L c hc (fun w => (w ^ n)⁻¹), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [mul_pow, mul_inv]

/- English proof (translation)
Establish `hb : L.basis 0 = L.ω₁` using `by first`. Consider the case `exact L.basis_zero`. Consider the case `simp [PeriodPair.basis]`. Establish `h1` using `L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0`. Rewrite `h1` using `[hb]`.

Simplify `h1` using `[wEta]`.
-/
lemma wEta_basis₁ (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
  have hb : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [PeriodPair.basis]
  have h1 := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
  rw [hb] at h1
  simpa [wEta] using h1

/- English proof (translation)
Establish `hb : L.basis 1 = L.ω₂` using `by first`. Consider the case `exact L.basis_one`. Consider the case `simp [PeriodPair.basis]`. Establish `h1` using `L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1`. Rewrite `h1` using `[hb]`.

Simplify `h1` using `[wEta]`.
-/
lemma wEta_basis₂ (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have hb : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have h1 := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  rw [hb] at h1
  simpa [wEta] using h1

/- English proof (translation)
Establish `hb0 : L.basis 0 = L.ω₁` using `by first`. Consider the case `exact L.basis_zero`. Consider the case `simp [PeriodPair.basis]`. Establish `hb1 : L.basis 1 = L.ω₂` using `by first`. Consider the case `exact L.basis_one`.

Consider the case `simp [PeriodPair.basis]`. Establish `k1 : wEta (scalePair L c hc) (c * L.ω₁) = c⁻¹ * wEta L L.ω₁`. Establish `h` using `wEta_basis₁ (scalePair L c hc)`. Express the relevant statement in the definitionally equal form `wEta (scalePair L c hc) (c * L.ω₁) = 2 * wZeta (scalePair L c hc) (c * L.ω₁ / 2) at h`. Rewrite using `[h, show c * L.ω₁ / 2 = c * (L.ω₁ / 2) by ring, wZeta_scale L c hc, wEta_basis₁ L]`.

Expand and normalize the polynomial expressions, which then agree. Establish `k2 : wEta (scalePair L c hc) (c * L.ω₂) = c⁻¹ * wEta L L.ω₂`. Establish `h` using `wEta_basis₂ (scalePair L c hc)`. Express the relevant statement in the definitionally equal form `wEta (scalePair L c hc) (c * L.ω₂) = 2 * wZeta (scalePair L c hc) (c * L.ω₂ / 2) at h`. Rewrite using `[h, show c * L.ω₂ / 2 = c * (L.ω₂ / 2) by ring, wZeta_scale L c hc, wEta_basis₂ L]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : (wEta (scalePair L c hc)).comp (LinearMap.mulLeft ℝ c) = (LinearMap.mulLeft ℝ c⁻¹).comp (wEta L)`. Apply `L.basis.ext` to reduce the goal to its premises. Introduce `i`. Use `fin_cases i`.

Use `first`. Consider the case `(show wEta (scalePair L c hc) (c * L.basis 0) = c⁻¹ * wEta L (L.basis 0)`. Rewrite using `[hb0]`. Conclude with `k1)`. Consider the case `(simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.zero_eta, hb0]`.

Conclude with `k1)`. Use `first`. Consider the case `(show wEta (scalePair L c hc) (c * L.basis 1) = c⁻¹ * wEta L (L.basis 1)`. Rewrite using `[hb1]`. Conclude with `k2)`.

Consider the case `(simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.mk_one, hb1]`. Conclude with `k2)`. Conclude with `LinearMap.congr_fun key z`.
-/
lemma wEta_scale (z : ℂ) : wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [PeriodPair.basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have k1 : wEta (scalePair L c hc) (c * L.ω₁) = c⁻¹ * wEta L L.ω₁ := by
    have h := wEta_basis₁ (scalePair L c hc)
    change wEta (scalePair L c hc) (c * L.ω₁) = 2 * wZeta (scalePair L c hc) (c * L.ω₁ / 2) at h
    rw [h, show c * L.ω₁ / 2 = c * (L.ω₁ / 2) by ring, wZeta_scale L c hc, wEta_basis₁ L]
    ring
  have k2 : wEta (scalePair L c hc) (c * L.ω₂) = c⁻¹ * wEta L L.ω₂ := by
    have h := wEta_basis₂ (scalePair L c hc)
    change wEta (scalePair L c hc) (c * L.ω₂) = 2 * wZeta (scalePair L c hc) (c * L.ω₂ / 2) at h
    rw [h, show c * L.ω₂ / 2 = c * (L.ω₂ / 2) by ring, wZeta_scale L c hc, wEta_basis₂ L]
    ring
  have key : (wEta (scalePair L c hc)).comp (LinearMap.mulLeft ℝ c)
      = (LinearMap.mulLeft ℝ c⁻¹).comp (wEta L) := by
    apply L.basis.ext
    intro i
    fin_cases i
    · first
        | (show wEta (scalePair L c hc) (c * L.basis 0) = c⁻¹ * wEta L (L.basis 0)
           rw [hb0]
           exact k1)
        | (simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.zero_eta, hb0]
           exact k1)
    · first
        | (show wEta (scalePair L c hc) (c * L.basis 1) = c⁻¹ * wEta L (L.basis 1)
           rw [hb1]
           exact k2)
        | (simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.mk_one, hb1]
           exact k2)
  exact LinearMap.congr_fun key z

/- English proof (translation)
Simplify using `only [area]`. Express the relevant statement in the definitionally equal form `|(conj (c * L.ω₁) * (c * L.ω₂)).im| = ‖c‖ ^ 2 * |(conj L.ω₁ * L.ω₂).im|`. Establish `hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `e : conj (c * L.ω₁) * (c * L.ω₂) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (conj L.ω₁ * L.ω₂)`.

Rewrite using `[map_mul, hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `first`. Consider the case `rw [Complex.im_ofReal_mul]`.

Consider the case `simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]`. Rewrite using `[abs_mul, abs_of_nonneg (by positivity)]`.
-/
lemma area_scale : area (scalePair L c hc) = ‖c‖ ^ 2 * area L := by
  simp only [area]
  change |(conj (c * L.ω₁) * (c * L.ω₂)).im| = ‖c‖ ^ 2 * |(conj L.ω₁ * L.ω₂).im|
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e : conj (c * L.ω₁) * (c * L.ω₂) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (conj L.ω₁ * L.ω₂) := by
    rw [map_mul, hn]
    ring
  rw [e]
  first
    | rw [Complex.im_ofReal_mul]
    | simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [abs_mul, abs_of_nonneg (by positivity)]

/- English proof (translation)
Establish `hcc : conj c ≠ 0` using `(map_ne_zero _).mpr hc`. Simplify using `only [s2]`. Express the relevant statement in the definitionally equal form `(wEta (scalePair L c hc) (c * L.ω₁) * conj (c * L.ω₂) - wEta (scalePair L c hc) (c * L.ω₂) * conj (c * L.ω₁)) / (c * L.ω₁ * conj (c * L.ω₂) - c * L.ω₂ * conj (c * L.ω₁)) = _`. Rewrite using `[wEta_scale L c hc, wEta_scale L c hc, map_mul, map_mul]`. Rewrite using `[show c⁻¹ * wEta L L.ω₁ * (conj c * conj L.ω₂) - c⁻¹ * wEta L L.ω₂ * (conj c * conj L.ω₁) = (c⁻¹ * conj c) * (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) by ring, show c * L.ω₁ * (conj c * conj L.ω₂) - c * L.ω₂ * (conj c * conj L.ω₁) = (c * conj c) * (L.ω₁ * conj L.ω₂ - L. …`.

Use `congr 1`. Use `first`. Consider the case `(field_simp done)`. Consider the case `(field_simp ring)`. Consider the case `(rw [div_eq_iff (mul_ne_zero hc hcc)]`.

Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.
-/
lemma quasiPeriodConst_scale : s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L := by
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  simp only [s2]
  change (wEta (scalePair L c hc) (c * L.ω₁) * conj (c * L.ω₂)
      - wEta (scalePair L c hc) (c * L.ω₂) * conj (c * L.ω₁))
      / (c * L.ω₁ * conj (c * L.ω₂) - c * L.ω₂ * conj (c * L.ω₁)) = _
  rw [wEta_scale L c hc, wEta_scale L c hc, map_mul, map_mul]
  rw [show c⁻¹ * wEta L L.ω₁ * (conj c * conj L.ω₂) - c⁻¹ * wEta L L.ω₂ * (conj c * conj L.ω₁)
      = (c⁻¹ * conj c) * (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) by ring,
    show c * L.ω₁ * (conj c * conj L.ω₂) - c * L.ω₂ * (conj c * conj L.ω₁)
      = (c * conj c) * (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁) by ring,
    mul_div_mul_comm]
  congr 1
  first
    | (field_simp
       done)
    | (field_simp
       ring)
    | (rw [div_eq_iff (mul_ne_zero hc hcc)]
       field_simp
       ring)

/- English proof (translation)
Simplify using `only [sgStar]`. Rewrite using `[wSigma_scale L c hc, quasiPeriodConst_scale L c hc]`. Establish `hcc : (c ^ 2)⁻¹ * c ^ 2 = 1` using `inv_mul_cancel₀ (pow_ne_zero 2 hc)`. Establish `he : -((c ^ 2)⁻¹ * s2 L) * (c * z) ^ 2 / 2 = -(s2 L) * z ^ 2 / 2`. Take the linear combination `(-(s2 L) * z ^ 2 / 2) * hcc`.

Rewrite using `[he]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sgStar_scale (z : ℂ) : sgStar (scalePair L c hc) (c * z) = c * sgStar L z := by
  simp only [sgStar]
  rw [wSigma_scale L c hc, quasiPeriodConst_scale L c hc]
  have hcc : (c ^ 2)⁻¹ * c ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hc)
  have he : -((c ^ 2)⁻¹ * s2 L) * (c * z) ^ 2 / 2 = -(s2 L) * z ^ 2 / 2 := by
    linear_combination (-(s2 L) * z ^ 2 / 2) * hcc
  rw [he]
  ring

/- English proof (translation)
Simplify using `only [herm, area_scale L c hc]`. Establish `hA : (area L : ℂ) ≠ 0` using `by exact_mod_cast (areaPos L).ne'`. Establish `hcc : conj c ≠ 0` using `(map_ne_zero _).mpr hc`. Establish `hn : ((‖c‖ ^ 2 * area L : ℝ) : ℂ) = c * conj c * (area L : ℂ)`. Rewrite using `[Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Rewrite using `[hn, map_mul, div_eq_div_iff (mul_ne_zero (mul_ne_zero hc hcc) hA) hA]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_scale (z w : ℂ) : herm (scalePair L c hc) (c * z) (c * w) = herm L z w := by
  simp only [herm, area_scale L c hc]
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (areaPos L).ne'
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : ((‖c‖ ^ 2 * area L : ℝ) : ℂ) = c * conj c * (area L : ℂ) := by
    rw [Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, map_mul, div_eq_div_iff (mul_ne_zero (mul_ne_zero hc hcc) hA) hA]
  ring

/- English proof (translation)
Simplify using `only [opU]`. Rewrite using `[show c * z + c * t = c * (z + t) by ring, sgStar_scale L c hc, herm_scale L c hc, herm_scale L c hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma opU_scale (t z : ℂ) :
    opU (scalePair L c hc) (c * t) (sgStar (scalePair L c hc)) (c * z)
      = c * opU L t (sgStar L) z := by
  simp only [opU]
  rw [show c * z + c * t = c * (z + t) by ring, sgStar_scale L c hc, herm_scale L c hc,
    herm_scale L c hc]
  ring

/- English proof (translation)
Simplify using `only [th0]`. Establish `h0` using `opU_scale L c hc t 0`. Rewrite `h0` using `[mul_zero]`. Rewrite using `[opU_scale L c hc t z, h0]`. Conclude with `mul_div_mul_left _ _ hc`.
-/
lemma normalizedTheta_scale (t z : ℂ) : th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z := by
  simp only [th0]
  have h0 := opU_scale L c hc t 0
  rw [mul_zero] at h0
  rw [opU_scale L c hc t z, h0]
  exact mul_div_mul_left _ _ hc

end Homog

/- English proof (translation)
Introduce `L c hc`. Use `⟨Homog.mem_scale L c hc, Homog.wZeta_scale L c hc, Homog.wSigma_scale L c hc, Homog.wp_scale L c hc, Homog.wEta_scale L c hc, Homog.area_scale L c hc, Homog.quasiPeriodConst_scale L c hc, Homog.sgStar_scale L c hc, Homog.normalizedTheta_scale L c hc, ?_, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(simp only [PeriodPair.g₂, Homog.G_scale L c hc] ring)`. Consider the case `(unfold PeriodPair.g₂ done)`.

Use `first`. Consider the case `(simp only [PeriodPair.g₃, Homog.G_scale L c hc] ring)`. Consider the case `(unfold PeriodPair.g₃ done)`.
-/
theorem homogeneity_thm : Homogeneity := by
  intro L c hc
  refine ⟨Homog.mem_scale L c hc, Homog.wZeta_scale L c hc, Homog.wSigma_scale L c hc,
    Homog.wp_scale L c hc, Homog.wEta_scale L c hc, Homog.area_scale L c hc, Homog.quasiPeriodConst_scale L c hc,
    Homog.sgStar_scale L c hc, Homog.normalizedTheta_scale L c hc, ?_, ?_⟩
  · first
      | (simp only [PeriodPair.g₂, Homog.G_scale L c hc]
         ring)
      | (unfold PeriodPair.g₂
         done)
  · first
      | (simp only [PeriodPair.g₃, Homog.G_scale L c hc]
         ring)
      | (unfold PeriodPair.g₃
         done)

end Formalism.L2.Th1.F
