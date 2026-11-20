import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricIntertwinerOfMatrixCoeffEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOneStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HolDict

/- English proof (translation)
Take `⟨ha, q, hq, hS⟩` from `h`. Take `⟨ha', q', hq', hS'⟩` from `h'`. Establish `k1 : ∀ a, ∃ b, q' b = q a ∧ e' b = e a` using `fun a => by`. Establish `: (q a, e a) ∈ S` using `hS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Rewrite `this` using `[hS']`.

Take `⟨b, -, hb⟩` from `Finset.mem_image.1 this`. Conclude with `⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩`. Establish `k2 : ∀ a, ∃ b, q b = q' a` using `fun a => by`. Establish `: (q' a, e' a) ∈ S` using `hS' ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Rewrite `this` using `[hS]`.

Take `⟨b, -, hb⟩` from `Finset.mem_image.1 this`. Conclude with `⟨b, congrArg Prod.fst hb⟩`. Establish `hl : l = l'`. Use `(StrictAnti.range_inj ha ha').1 ?_` and prove the remaining obligations. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Take `⟨b, hb, -⟩` from `k1 a`. Conclude with `⟨b, by rw [hq', hq, hb]⟩`. Introduce and unpack `⟨a, rfl⟩`.

Take `⟨b, hb⟩` from `k2 a`. Conclude with `⟨b, by rw [hq', hq, hb]⟩`. Use `⟨hl, funext fun a => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, he⟩` from `k1 a`. Establish `: l' b = l' a` using `by rw [hq', hb, ← hq, hl]`.

Rewrite using `[← he, ha'.injective this]`.
-/
theorem isEnum_unique {n : ℕ} {S : SPar} {l l' : Fin n → ℝ} {e e' : Fin n → Bool}
    (h : IsEnum S l e) (h' : IsEnum S l' e') : l = l' ∧ e = e' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have k1 : ∀ a, ∃ b, q' b = q a ∧ e' b = e a := fun a => by
    have : (q a, e a) ∈ S := hS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have k2 : ∀ a, ∃ b, q b = q' a := fun a => by
    have : (q' a, e' a) ∈ S := hS' ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb⟩
  have hl : l = l' := by
    refine (StrictAnti.range_inj ha ha').1 ?_
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb, -⟩ := k1 a
      exact ⟨b, by rw [hq', hq, hb]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := k2 a
      exact ⟨b, by rw [hq', hq, hb]⟩
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := k1 a
  have : l' b = l' a := by rw [hq', hb, ← hq, hl]
  rw [← he, ha'.injective this]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det h.2`. Rewrite `h1` using `[det_mul, det_mul, det_diagonal]`. Establish `h2 : (∏ a : Fin n, -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations. Unfold `ReciprocityTheory.ChartRestriction.G.FD.sgn`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h2` using `[← h1]`. Conclude with `⟨right_ne_zero_of_mul h2, right_ne_zero_of_mul (left_ne_zero_of_mul h2)⟩`.
-/
theorem OrthFr.dets {n : ℕ} {Hm x : Mt n} {q : ℕ} (h : OrthFr Hm q x) : x.det ≠ 0 ∧ Hm.det ≠ 0 := by
  have h1 := congrArg Matrix.det h.2
  rw [det_mul, det_mul, det_diagonal] at h1
  have h2 : (∏ a : Fin n, -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  rw [← h1] at h2
  exact ⟨right_ne_zero_of_mul h2, right_ne_zero_of_mul (left_ne_zero_of_mul h2)⟩

end GlobalTheory.HolDict

namespace GlobalTheory.HolDict

section
variable {n : ℕ} {Hm : Mt n}

/- English proof (translation)
Establish `h1 : (gᴴ * Hm * g).det = Hm.det` using `congrArg Matrix.det hg`. Rewrite `h1` using `[det_mul]`. Conclude with `isUnit_iff_ne_zero.2 (right_ne_zero_of_mul (h1 ▸ hH))`.
-/
theorem uh_det_isUnit (hH : Hm.det ≠ 0) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) : IsUnit g.det := by
  have h1 : (gᴴ * Hm * g).det = Hm.det := congrArg Matrix.det hg
  rw [det_mul] at h1
  exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul (h1 ▸ hH))

/- English proof (translation)
Simplify using `[Formalism.QuantumDeterminants.UH]`.
-/
theorem uh_one : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  simp [Formalism.QuantumDeterminants.UH]

/- English proof (translation)
Establish `ha' : aᴴ * Hm * a = Hm` using `ha`. Establish `hb' : bᴴ * Hm * b = Hm` using `hb`. Use `show (a * b)ᴴ * Hm * (a * b) = Hm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hm := by rw [ha', hb']`.
-/
theorem uh_mul {a b : Mt n} (ha : a ∈ Formalism.QuantumDeterminants.UH Hm) (hb : b ∈ Formalism.QuantumDeterminants.UH Hm) : a * b ∈ Formalism.QuantumDeterminants.UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

/- English proof (translation)
Establish `h1` using `mul_nonsing_inv g (uh_det_isUnit hH hg)`. Establish `hg' : gᴴ * Hm * g = Hm` using `hg`. Use `show g⁻¹ᴴ * Hm * g⁻¹ = Hm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hm := by rw [h1]; simp`.
-/
theorem uh_inv (hH : Hm.det ≠ 0) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) : g⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  have h1 := mul_nonsing_inv g (uh_det_isUnit hH hg)
  have hg' : gᴴ * Hm * g = Hm := hg
  show g⁻¹ᴴ * Hm * g⁻¹ = Hm
  calc g⁻¹ᴴ * Hm * g⁻¹ = g⁻¹ᴴ * (gᴴ * Hm * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hm * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h1]; simp

/- English proof (translation)
Establish `h1` using `mul_nonsing_inv x (isUnit_iff_ne_zero.2 hx)`. Use `show (y * x⁻¹)ᴴ * Hm * (y * x⁻¹) = Hm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = (x * x⁻¹)ᴴ * Hm * (x * x⁻¹) := by`. Rewrite using `[h, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hm := by rw [h1]; simp`.
-/
theorem uh_of_gram_eq {x y : Mt n} (hx : x.det ≠ 0) (h : yᴴ * Hm * y = xᴴ * Hm * x) : y * x⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  have h1 := mul_nonsing_inv x (isUnit_iff_ne_zero.2 hx)
  show (y * x⁻¹)ᴴ * Hm * (y * x⁻¹) = Hm
  calc (y * x⁻¹)ᴴ * Hm * (y * x⁻¹) = x⁻¹ᴴ * (yᴴ * Hm * y) * x⁻¹ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (x * x⁻¹)ᴴ * Hm * (x * x⁻¹) := by
        rw [h, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h1]; simp

/- English proof (translation)
Use `uh_of_gram_eq h.dets.1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`.

Rewrite using `[h.2, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `h1 : star (Complex.exp ((s a : ℂ) * Complex.I)) * Complex.exp ((s a : ℂ) * Complex.I) = 1`. Rewrite using `[Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]`.

Simplify using the standard rewrite rules. Simplify using `only [Pi.star_apply]`. Take the linear combination `(-((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * h1`.
-/
theorem OrthFr.tor_mem {q : ℕ} {x : Mt n} (h : OrthFr Hm q x) (s : Fin n → ℝ) :
    x * diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) * x⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  refine uh_of_gram_eq h.dets.1 ?_
  calc _ = (diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)))ᴴ * (xᴴ * Hm * x) *
        diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h.2, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext a
        have h1 : star (Complex.exp ((s a : ℂ) * Complex.I)) * Complex.exp ((s a : ℂ) * Complex.I) = 1 := by
          rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp
        simp only [Pi.star_apply]
        linear_combination (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * h1

/- English proof (translation)
Establish `hg' : gᴴ * Hm * g = Hm` using `hg`. Establish `e : (g * x)ᴴ * Hm * (g * x) = xᴴ * Hm * x`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul]`.

Conclude with `mul_ne_zero (uh_det_isUnit hH hg).ne_zero hx.1`. Rewrite using `[e]`. Conclude with `hx.2 i`.
-/
theorem frDom_mul (hH : Hm.det ≠ 0) {q : ℕ} {g x : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    g * x ∈ frDom Hm q := by
  have hg' : gᴴ * Hm * g = Hm := hg
  have e : (g * x)ᴴ * Hm * (g * x) = xᴴ * Hm * x := by
    calc _ = xᴴ * (gᴴ * Hm * g) * x := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg']
  refine ⟨?_, fun i => ?_⟩
  · rw [det_mul]; exact mul_ne_zero (uh_det_isUnit hH hg).ne_zero hx.1
  · rw [e]; exact hx.2 i

end

/- English proof (translation)
Establish `h1` using `(LinearMap.norm_map_iff_inner_map_map A).1 hA v y`. Establish `h2 : ‖c‖ = 1`. Use `hA v` as an intermediate fact. Rewrite `this` using `[hc, norm_smul, hv, mul_one]`. Then use the resulting hypothesis. Rewrite `h1` using `[hc, inner_smul_left]`.

Establish `h3 : c * (starRingEnd ℂ) c = 1` using `by rw [Complex.mul_conj', h2]; simp`. Rewrite using `[← h1, ← mul_assoc, h3, one_mul]`.
-/
theorem inner_eigen_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ y, ‖A y‖ = ‖y‖) {v : H} (hv : ‖v‖ = 1) {c : ℂ} (hc : A v = c • v) (y : H) : ⟪v, A y⟫_ℂ = c * ⟪v, y⟫_ℂ := by
  have h1 := (LinearMap.norm_map_iff_inner_map_map A).1 hA v y
  have h2 : ‖c‖ = 1 := by
    have := hA v
    rwa [hc, norm_smul, hv, mul_one] at this
  rw [hc, inner_smul_left] at h1
  have h3 : c * (starRingEnd ℂ) c = 1 := by rw [Complex.mul_conj', h2]; simp
  rw [← h1, ← mul_assoc, h3, one_mul]

section
variable {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x x' : ι → Mt n} {w : ι → Fin n → ℤ}

/- English proof (translation)
Take `⟨P, ⟨hP1, hP2⟩, hP⟩` from `h`. Take `⟨P', ⟨hP1', hP2'⟩, hP'⟩` from `h'`. Use `⟨fun y => P y - P' y, ⟨hP1.sub hP1', fun y hy b hb => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[hP2 y hy b hb, hP2' y hy b hb, mul_sub]`.

Simplify using `only []`. Rewrite using `[hP u hu, hP' u hu]`.
-/
theorem HolFn.sub {f f' : (ι → Mt n) → ℂ} (h : HolFn Hm q x w f) (h' : HolFn Hm q x w f') :
    HolFn Hm q x w fun u => f u - f' u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hP⟩ := h
  obtain ⟨P', ⟨hP1', hP2'⟩, hP'⟩ := h'
  refine ⟨fun y => P y - P' y, ⟨hP1.sub hP1', fun y hy b hb => ?_⟩, fun u hu => ?_⟩
  · simp only []
    rw [hP2 y hy b hb, hP2' y hy b hb, mul_sub]
  · simp only []
    rw [hP u hu, hP' u hu]

/- English proof (translation)
Take `⟨P, ⟨hP1, hP2⟩, hP⟩` from `h`. Establish `hm : ∀ y ∈ frDoms Hm q, (fun τ => (g τ * Matrix.of (y τ) : Mt n)) ∈ frDoms Hm q` using `fun y hy τ => frDom_mul (hH τ) (hg τ) (hy τ)`. Use `⟨fun y => P fun τ => (g τ * Matrix.of (y τ) : Mt n), ⟨?_, fun y hy b hb => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.comp (F := ι → Fin n → Fin n → ℂ) (f := fun (y : ι → Fin n → Fin n → ℂ) => fun τ a c => (g τ * Matrix.of (y τ) : Mt n) a c) hP1 ?_ hm` and prove the remaining obligations. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations.

Use `differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`. Use `hP2 _ (hm y hy) b hb` as an intermediate fact. Simplify using `only []`.

Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc (g τ) (Matrix.of (y τ)) (b τ)).symm`. Simplify using `only []`.

Rewrite using `[hP _ fun τ => uh_mul (uh_mul (hg τ) (hu τ)) (uh_inv (hH τ) (hg τ))]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Use `show (g τ * u τ * (g τ)⁻¹ * x' τ : Mt n) = g τ * (u τ * x τ)`. Rewrite using `[hx, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (uh_det_isUnit (hH τ) (hg τ)), Matrix.mul_assoc]`.
-/
theorem HolFn.conj (hH : ∀ τ, (Hm τ).det ≠ 0) {g : ι → Mt n} (hg : g ∈ UG Hm) (hx : ∀ τ, x' τ = g τ * x τ)
    {f : (ι → Mt n) → ℂ} (h : HolFn Hm q x' w f) :
    HolFn Hm q x w fun u => f fun τ => g τ * u τ * (g τ)⁻¹ := by
  obtain ⟨P, ⟨hP1, hP2⟩, hP⟩ := h
  have hm : ∀ y ∈ frDoms Hm q, (fun τ => (g τ * Matrix.of (y τ) : Mt n)) ∈ frDoms Hm q :=
    fun y hy τ => frDom_mul (hH τ) (hg τ) (hy τ)
  refine ⟨fun y => P fun τ => (g τ * Matrix.of (y τ) : Mt n), ⟨?_, fun y hy b hb => ?_⟩, fun u hu => ?_⟩
  · refine DifferentiableOn.comp (F := ι → Fin n → Fin n → ℂ)
      (f := fun (y : ι → Fin n → Fin n → ℂ) => fun τ a c => (g τ * Matrix.of (y τ) : Mt n) a c) hP1 ?_ hm
    refine Differentiable.differentiableOn ?_
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  · have := hP2 _ (hm y hy) b hb
    simp only []
    rw [← this]
    congr 1
    funext τ
    exact (Matrix.mul_assoc (g τ) (Matrix.of (y τ)) (b τ)).symm
  · simp only []
    rw [hP _ fun τ => uh_mul (uh_mul (hg τ) (hu τ)) (uh_inv (hH τ) (hg τ))]
    congr 1
    funext τ
    show (g τ * u τ * (g τ)⁻¹ * x' τ : Mt n) = g τ * (u τ * x τ)
    rw [hx, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (uh_det_isUnit (hH τ) (hg τ)), Matrix.mul_assoc]

end

def uhGrp {n : ℕ} (Hm : Mt n) (hH : Hm.det ≠ 0) : Subgroup (Mt n)ˣ where
  carrier := {g | (g : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm}
  mul_mem' ha hb := uh_mul ha hb
  one_mem' := uh_one
  inv_mem' {g} hg := by
    show ((g⁻¹ : (Mt n)ˣ) : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm
    rw [Matrix.coe_units_inv]
    exact uh_inv hH hg

def uhHom {n : ℕ} {Hm : Mt n} (hH : Hm.det ≠ 0) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mt n → (H →L[ℂ] H)} (h : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) : uhGrp Hm hH →* (H →L[ℂ] H) where
  toFun g := σ ((g : (Mt n)ˣ) : Mt n)
  map_one' := h.1.1
  map_mul' a b := h.1.2 _ a.2 _ b.2

/- English proof (translation)
Establish `lift : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∃ a : uhGrp Hm hH, ((a : (Mt n)ˣ) : Mt n) = g` using `fun g hg => ⟨⟨((Matrix.isUnit_iff_isUnit_det g).2 (uh_det_isUnit hH hg)).unit, hg⟩, rfl⟩`. Take `⟨io, hio, hio2⟩` from `GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq (uhGrp Hm hH) H' (uhHom hH h') H (uhHom hH h) (fun g y => h'.2.1 _ g.2 y) (fun g y => h.2.1 _ g.2 y) v' v (by`. Introduce `y hy`. Set `T : Submodule ℂ H'` to `Submodule.span ℂ (Set.range fun g : uhGrp Hm hH => uhHom hH h' g v')`. Establish `hT : T.topologicalClosure = ⊤`.

Use `(hi' T.topologicalClosure T.isClosed_topologicalClosure ?_).resolve_left ?_` and prove the remaining obligations. Introduce `g hg z hz`. Take `⟨a, rfl⟩` from `lift g hg`. Establish `hmap : Set.MapsTo (uhHom hH h' a) (T : Set H') (T : Set H')`. Introduce `z hz`.

Establish `: T.map (uhHom hH h' a : H' →ₗ[ℂ] H') ≤ T`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `Submodule.subset_span ⟨a * b, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`.

Both sides reduce to the same expression. Conclude with `this ⟨z, hz, rfl⟩`. Conclude with `hmap.closure (uhHom hH h' a).continuous hz`. Introduce `hb`. Establish `: v' ∈ T.topologicalClosure` using `T.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)`.

Rewrite `this` using `[hb]`. Conclude with `hv' this`. Establish `h0` using `Submodule.topologicalClosure_eq_top_iff.1 hT`. Establish `: y ∈ Tᗮ`. Rewrite using `[Submodule.mem_orthogonal']`.

Introduce `u hu`. Use `Submodule.span_induction (p := fun u _ => ⟪y, u⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `hy b`. Simplify using the standard rewrite rules.

Introduce `a b _ _ ha hb`. Rewrite using `[inner_add_right, ha, hb, add_zero]`. Introduce `c a _ ha`. Rewrite using `[inner_smul_right, ha, mul_zero]`. Rewrite `this` using `[h0]`.

Conclude with `this) (fun g => hc _ g.2)`. Establish `hint : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ y, io (σ' g y) = σ g (io y)` using `fun g hg y => by`. Take `⟨a, rfl⟩` from `lift g hg`. Conclude with `hio2 a y`. Establish `hr : LinearMap.range io.toLinearMap = ⊤`.

Use `(hi _ io.isometry.isClosedEmbedding.isClosed_range ?_).resolve_left ?_` and prove the remaining obligations. Introduce and unpack `g hg _ ⟨y, rfl⟩`. Conclude with `⟨σ' g y, hint g hg y⟩`. Introduce `hb`. Establish `: v ∈ LinearMap.range io.toLinearMap` using `⟨v', hio⟩`.

Rewrite `this` using `[hb]`. Conclude with `hv this`. Conclude with `⟨LinearIsometryEquiv.ofSurjective io (LinearMap.range_eq_top.1 hr), hint⟩`.
-/
theorem exists_equiv_of_coef_eq {n : ℕ} {Hm : Mt n} (hH : Hm.det ≠ 0) {H H' : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ : Mt n → (H →L[ℂ] H)} {σ' : Mt n → (H' →L[ℂ] H')} (h : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ)
    (h' : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ') (hi : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ) (hi' : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ')
    {v : H} {v' : H'} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ⟪v, σ g v⟫_ℂ = ⟪v', σ' g v'⟫_ℂ) :
    ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ y, U (σ' g y) = σ g (U y) := by
  have lift : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∃ a : uhGrp Hm hH, ((a : (Mt n)ˣ) : Mt n) = g := fun g hg =>
    ⟨⟨((Matrix.isUnit_iff_isUnit_det g).2 (uh_det_isUnit hH hg)).unit, hg⟩, rfl⟩
  obtain ⟨io, hio, hio2⟩ := GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq (uhGrp Hm hH) H' (uhHom hH h') H (uhHom hH h)
    (fun g y => h'.2.1 _ g.2 y) (fun g y => h.2.1 _ g.2 y) v' v (by
      intro y hy
      let T : Submodule ℂ H' := Submodule.span ℂ (Set.range fun g : uhGrp Hm hH => uhHom hH h' g v')
      have hT : T.topologicalClosure = ⊤ := by
        refine (hi' T.topologicalClosure T.isClosed_topologicalClosure ?_).resolve_left ?_
        · intro g hg z hz
          obtain ⟨a, rfl⟩ := lift g hg
          have hmap : Set.MapsTo (uhHom hH h' a) (T : Set H') (T : Set H') := by
            intro z hz
            have : T.map (uhHom hH h' a : H' →ₗ[ℂ] H') ≤ T := by
              rw [Submodule.map_span_le]
              rintro _ ⟨b, rfl⟩
              refine Submodule.subset_span ⟨a * b, ?_⟩
              simp only [map_mul]; rfl
            exact this ⟨z, hz, rfl⟩
          exact hmap.closure (uhHom hH h' a).continuous hz
        · intro hb
          have : v' ∈ T.topologicalClosure := T.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
          rw [hb] at this
          exact hv' this
      have h0 := Submodule.topologicalClosure_eq_top_iff.1 hT
      have : y ∈ Tᗮ := by
        rw [Submodule.mem_orthogonal']
        intro u hu
        refine Submodule.span_induction (p := fun u _ => ⟪y, u⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨b, rfl⟩; exact hy b
        · simp
        · intro a b _ _ ha hb; rw [inner_add_right, ha, hb, add_zero]
        · intro c a _ ha; rw [inner_smul_right, ha, mul_zero]
      rw [h0] at this
      exact this) (fun g => hc _ g.2)
  have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ y, io (σ' g y) = σ g (io y) := fun g hg y => by
    obtain ⟨a, rfl⟩ := lift g hg
    exact hio2 a y
  have hr : LinearMap.range io.toLinearMap = ⊤ := by
    refine (hi _ io.isometry.isClosedEmbedding.isClosed_range ?_).resolve_left ?_
    · rintro g hg _ ⟨y, rfl⟩
      exact ⟨σ' g y, hint g hg y⟩
    · intro hb
      have : v ∈ LinearMap.range io.toLinearMap := ⟨v', hio⟩
      rw [hb] at this
      exact hv this
  exact ⟨LinearIsometryEquiv.ofSurjective io (LinearMap.range_eq_top.1 hr), hint⟩

end GlobalTheory.HolDict

namespace GlobalTheory.HolDict

/- English proof (translation)
Establish `hH : ∀ τ, (Hm τ).det ≠ 0` using `fun τ => (ho τ).dets.2`. Establish `hxu : ∀ τ, IsUnit (x τ).det` using `fun τ => isUnit_iff_ne_zero.2 (ho τ).dets.1`. Take `⟨g, hg, hx⟩ : ∃ g ∈ UG Hm, ∀ τ, x' τ = g τ * x τ` from `⟨fun τ => x' τ * (x τ)⁻¹, fun τ => uh_of_gram_eq (ho τ).dets.1 ((ho' τ).2.trans (ho τ).2.symm), fun τ => (Matrix.nonsing_inv_mul_cancel_right _ _ (hxu τ)).symm⟩`. Establish `hgu : ∀ τ, IsUnit (g τ).det` using `fun τ => uh_det_isUnit (hH τ) (hg τ)`. Establish `hgi : ∀ τ, (g τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Hm τ)` using `fun τ => uh_inv (hH τ) (hg τ)`.

Establish `one : ∀ τ, ⟪v τ, σ τ 1 (v τ)⟫_ℂ = 1` using `fun τ => by`. Rewrite using `[(h τ).1.1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv]`. Simplify using the standard rewrite rules. Establish `one' : ∀ τ, ⟪v' τ, σ' τ (g τ * 1 * (g τ)⁻¹) (v' τ)⟫_ℂ = 1` using `fun τ => by`. Rewrite using `[Matrix.mul_one, Matrix.mul_nonsing_inv _ (hgu τ), (h' τ).1.1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv']`.

Simplify using the standard rewrite rules. Establish `key` using `GlobalTheory.T.holomorphicType_eq_zero_of_torus_law_at_one n ι Hm q x w ho _ (hf.sub (hf'.conj hH hg hx)) (by`. Introduce `u hu s`. Establish `e1 : ∀ τ, ⟪v τ, σ τ ((torEl x s * u) τ) (v τ)⟫_ℂ = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ` using `fun τ => by`. Establish `hm : torEl x s τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)` using `(ho τ).tor_mem (s τ)`.

Rewrite using `[Pi.mul_apply, (h τ).1.2 _ hm _ (hu τ), ContinuousLinearMap.comp_apply]`. Conclude with `inner_eigen_of_norm _ ((h τ).2.1 _ hm) (hv τ) (ht s τ) _`. Establish `e2 : ∀ τ, ⟪v' τ, σ' τ (g τ * (torEl x s * u) τ * (g τ)⁻¹) (v' τ)⟫_ℂ = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪v' τ, σ' τ (g τ * u τ * (g τ)⁻¹) (v' τ)⟫_ℂ` using `fun τ => by`. Establish `hm : torEl x' s τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)` using `(ho' τ).tor_mem (s τ)`. Establish `e : g τ * (torEl x s * u) τ * (g τ)⁻¹ = torEl x' s τ * (g τ * u τ * (g τ)⁻¹)`.

Simplify using `only [Pi.mul_apply, torEl, hx τ, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hgu τ)]`. Rewrite using `[e, (h' τ).1.2 _ hm _ (uh_mul (uh_mul (hg τ) (hu τ)) (hgi τ)), ContinuousLinearMap.comp_apply]`. Conclude with `inner_eigen_of_norm _ ((h' τ).2.1 _ hm) (hv' τ) (ht' s τ) _`. Simplify using `only [e1, e2, Finset.prod_mul_distrib, torCh, mul_sub]) (by`. Simplify using `only [Pi.one_apply, one, one', Finset.prod_const_one, sub_self])`.

Establish `hne : ∀ {E : Type} [NormedAddCommGroup E] {y : E}, ‖y‖ = 1 → y ≠ 0` using `fun {E} _ {y} hy h0 => by`. Simplify using `[h0] at hy`. Use `exists_equiv_of_coef_eq (hH τ) (h τ) (h' τ) (hi τ) (hi' τ) (v := v τ) (v' := σ' τ (g τ)⁻¹ (v' τ)) (hne (hv τ)) (hne (((h' τ).2.1 _ (hgi τ) _).trans (hv' τ))) fun a ha => ?_` and prove the remaining obligations. Establish `hu : Function.update (1 : ι → Mt n) τ a ∈ UG Hm` using `fun ρ => by`. Distinguish the cases in `hρ : ρ = τ`.

Substitute `hρ` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `ha`. Rewrite using `[Function.update_of_ne hρ]`. Conclude with `uh_one`.

Establish `k` using `sub_eq_zero.1 (key _ hu)`. Simplify using `only [] at k`. Rewrite `k` using `[Finset.prod_eq_single τ (fun ρ _ hρ => by rw [Function.update_of_ne hρ]; exact one ρ) (by simp), Finset.prod_eq_single τ (fun ρ _ hρ => by rw [Function.update_of_ne hρ]; exact one' ρ) (by simp), Function.update_self]`. Rewrite using `[k, (h' τ).1.2 _ (uh_mul (hg τ) ha) _ (hgi τ), (h' τ).1.2 _ (hg τ) _ ha, ← (LinearMap.norm_map_iff_inner_map_map (σ' τ (g τ))).1 ((h' τ).2.1 _ (hg τ)) (σ' τ (g τ)⁻¹ (v' τ)), ← ContinuousLinearMap.comp_apply (σ' τ (g τ)) (σ' τ (g τ)⁻¹), ← (h' τ).1.2 _ (hg τ) _ (hgi τ), Matrix.mul_ …`. Both sides reduce to the same expression.
-/
theorem exists_equiv_of_holFn {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x x' : ι → Mt n}
    {w : ι → Fin n → ℤ} {H H' : ι → Type} [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)]
    [∀ τ, CompleteSpace (H τ)] [∀ τ, NormedAddCommGroup (H' τ)] [∀ τ, InnerProductSpace ℂ (H' τ)] [∀ τ, CompleteSpace (H' τ)]
    {σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)} {σ' : ∀ τ, Mt n → (H' τ →L[ℂ] H' τ)}
    (h : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ)) (h' : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ' τ))
    (hi : ∀ τ, IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ)) (hi' : ∀ τ, IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ' τ))
    (ho : ∀ τ, OrthFr (Hm τ) (q τ) (x τ)) (ho' : ∀ τ, OrthFr (Hm τ) (q τ) (x' τ))
    {v : ∀ τ, H τ} {v' : ∀ τ, H' τ} (hv : ∀ τ, ‖v τ‖ = 1) (hv' : ∀ τ, ‖v' τ‖ = 1)
    (hf : HolFn Hm q x w fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ)
    (hf' : HolFn Hm q x' w fun u => ∏ τ, ⟪v' τ, σ' τ (u τ) (v' τ)⟫_ℂ)
    (ht : ∀ s τ, σ τ (torEl x s τ) (v τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • v τ)
    (ht' : ∀ s τ, σ' τ (torEl x' s τ) (v' τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • v' τ) (τ : ι) :
    ∃ U : H' τ ≃ₗᵢ[ℂ] H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, U (σ' τ g y) = σ τ g (U y) := by
  classical
  have hH : ∀ τ, (Hm τ).det ≠ 0 := fun τ => (ho τ).dets.2
  have hxu : ∀ τ, IsUnit (x τ).det := fun τ => isUnit_iff_ne_zero.2 (ho τ).dets.1
  obtain ⟨g, hg, hx⟩ : ∃ g ∈ UG Hm, ∀ τ, x' τ = g τ * x τ :=
    ⟨fun τ => x' τ * (x τ)⁻¹, fun τ => uh_of_gram_eq (ho τ).dets.1 ((ho' τ).2.trans (ho τ).2.symm),
      fun τ => (Matrix.nonsing_inv_mul_cancel_right _ _ (hxu τ)).symm⟩
  have hgu : ∀ τ, IsUnit (g τ).det := fun τ => uh_det_isUnit (hH τ) (hg τ)
  have hgi : ∀ τ, (g τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := fun τ => uh_inv (hH τ) (hg τ)
  have one : ∀ τ, ⟪v τ, σ τ 1 (v τ)⟫_ℂ = 1 := fun τ => by
    rw [(h τ).1.1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv]; simp
  have one' : ∀ τ, ⟪v' τ, σ' τ (g τ * 1 * (g τ)⁻¹) (v' τ)⟫_ℂ = 1 := fun τ => by
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ (hgu τ), (h' τ).1.1, ContinuousLinearMap.one_apply,
      inner_self_eq_norm_sq_to_K, hv']; simp
  have key := GlobalTheory.T.holomorphicType_eq_zero_of_torus_law_at_one n ι Hm q x w ho _ (hf.sub (hf'.conj hH hg hx)) (by
    intro u hu s
    have e1 : ∀ τ, ⟪v τ, σ τ ((torEl x s * u) τ) (v τ)⟫_ℂ =
        (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := fun τ => by
      have hm : torEl x s τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := (ho τ).tor_mem (s τ)
      rw [Pi.mul_apply, (h τ).1.2 _ hm _ (hu τ), ContinuousLinearMap.comp_apply]
      exact inner_eigen_of_norm _ ((h τ).2.1 _ hm) (hv τ) (ht s τ) _
    have e2 : ∀ τ, ⟪v' τ, σ' τ (g τ * (torEl x s * u) τ * (g τ)⁻¹) (v' τ)⟫_ℂ =
        (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪v' τ, σ' τ (g τ * u τ * (g τ)⁻¹) (v' τ)⟫_ℂ := fun τ => by
      have hm : torEl x' s τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := (ho' τ).tor_mem (s τ)
      have e : g τ * (torEl x s * u) τ * (g τ)⁻¹ = torEl x' s τ * (g τ * u τ * (g τ)⁻¹) := by
        simp only [Pi.mul_apply, torEl, hx τ, Matrix.mul_inv_rev, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul_cancel_left _ _ (hgu τ)]
      rw [e, (h' τ).1.2 _ hm _ (uh_mul (uh_mul (hg τ) (hu τ)) (hgi τ)), ContinuousLinearMap.comp_apply]
      exact inner_eigen_of_norm _ ((h' τ).2.1 _ hm) (hv' τ) (ht' s τ) _
    simp only [e1, e2, Finset.prod_mul_distrib, torCh, mul_sub]) (by
    simp only [Pi.one_apply, one, one', Finset.prod_const_one, sub_self])
  have hne : ∀ {E : Type} [NormedAddCommGroup E] {y : E}, ‖y‖ = 1 → y ≠ 0 := fun {E} _ {y} hy h0 => by
    simp [h0] at hy
  refine exists_equiv_of_coef_eq (hH τ) (h τ) (h' τ) (hi τ) (hi' τ) (v := v τ) (v' := σ' τ (g τ)⁻¹ (v' τ)) (hne (hv τ))
    (hne (((h' τ).2.1 _ (hgi τ) _).trans (hv' τ))) fun a ha => ?_
  have hu : Function.update (1 : ι → Mt n) τ a ∈ UG Hm := fun ρ => by
    by_cases hρ : ρ = τ
    · subst hρ; rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne hρ]; exact uh_one
  have k := sub_eq_zero.1 (key _ hu)
  simp only [] at k
  rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [Function.update_of_ne hρ]; exact one ρ) (by simp),
    Finset.prod_eq_single τ (fun ρ _ hρ => by rw [Function.update_of_ne hρ]; exact one' ρ) (by simp),
    Function.update_self] at k
  rw [k, (h' τ).1.2 _ (uh_mul (hg τ) ha) _ (hgi τ), (h' τ).1.2 _ (hg τ) _ ha,
    ← (LinearMap.norm_map_iff_inner_map_map (σ' τ (g τ))).1 ((h' τ).2.1 _ (hg τ)) (σ' τ (g τ)⁻¹ (v' τ)),
    ← ContinuousLinearMap.comp_apply (σ' τ (g τ)) (σ' τ (g τ)⁻¹), ← (h' τ).1.2 _ (hg τ) _ (hgi τ),
    Matrix.mul_nonsing_inv _ (hgu τ), (h' τ).1.1]
  rfl

/- English proof (translation)
Introduce `D θ V S M M' w v v' hθ hs hw hv hv'`. Establish `hl : ∀ τ, M'.lam τ = M.lam τ` using `fun τ => (isEnum_unique (M'.enum τ) (M.enum τ)).1`. Establish `he : ∀ τ, M'.ε τ = M.ε τ` using `fun τ => (isEnum_unique (M'.enum τ) (M.enum τ)).2`. Establish `hs' : HolShape M'` using `fun τ => by rw [hl, he]; exact hs τ`. Establish `hw' : WtIs M' w` using `fun τ c => by`.

Rewrite using `[hw τ c]`. Unfold `extWt`. Rewrite using `[hl, he]`. Take `⟨f1, t1⟩` from `GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType D θ V S M w v hθ hs hw hv`. Take `⟨f2, t2⟩` from `GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType D θ V S M' w v' hθ hs' hw' hv'`.

Establish `m1` using `GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M`. Establish `m2` using `GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M'`. Use `haveI := fun τ => (m1 τ).1`. Use `haveI := fun τ => (m2 τ).1`. Simplify using `only [he] at f2`.

Use `exists_equiv_of_holFn (fun τ => (m1 τ).2.1) (fun τ => (m2 τ).2.1) (fun τ => (m1 τ).2.2.1) (fun τ => (m2 τ).2.2.1) (fun τ => ((m1 τ).2.2.2 hs).1) (fun τ => he τ ▸ ((m2 τ).2.2.2 hs').1) (fun τ => (hv τ).1) (fun τ => (hv' τ).1) f1 f2 t1 t2` as an intermediate fact. Use `choose U hU using this`. Conclude with `⟨U, hU⟩`.
-/
theorem holModel_unique : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M M' : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (v' : M'.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → IsExtVec M' v' → ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, U τ (M'.rep τ g y) = M.rep τ g (U τ y) := by
  intro D θ V S M M' w v v' hθ hs hw hv hv'
  have hl : ∀ τ, M'.lam τ = M.lam τ := fun τ => (isEnum_unique (M'.enum τ) (M.enum τ)).1
  have he : ∀ τ, M'.ε τ = M.ε τ := fun τ => (isEnum_unique (M'.enum τ) (M.enum τ)).2
  have hs' : HolShape M' := fun τ => by rw [hl, he]; exact hs τ
  have hw' : WtIs M' w := fun τ c => by
    rw [hw τ c]; unfold extWt; rw [hl, he]
  obtain ⟨f1, t1⟩ := GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType D θ V S M w v hθ hs hw hv
  obtain ⟨f2, t2⟩ := GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType D θ V S M' w v' hθ hs' hw' hv'
  have m1 := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M
  have m2 := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M'
  haveI := fun τ => (m1 τ).1
  haveI := fun τ => (m2 τ).1
  simp only [he] at f2
  have := exists_equiv_of_holFn (fun τ => (m1 τ).2.1) (fun τ => (m2 τ).2.1) (fun τ => (m1 τ).2.2.1) (fun τ => (m2 τ).2.2.1)
    (fun τ => ((m1 τ).2.2.2 hs).1) (fun τ => he τ ▸ ((m2 τ).2.2.2 hs').1) (fun τ => (hv τ).1) (fun τ => (hv' τ).1) f1 f2 t1 t2
  choose U hU using this
  exact ⟨U, hU⟩

end GlobalTheory.HolDict
