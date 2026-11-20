import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `fsPot`. Rewrite using `[Real.log_pow]`. Evaluate the numerical expressions.
-/
theorem fsPot_eq {n : ℕ} (h : HermNorm n) :
    fsPot h = fun y => 2 * Real.log (h.dualNorm y) := by
  funext y
  unfold fsPot
  rw [Real.log_pow]
  norm_num

/- English proof (translation)
Establish `h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ`. Establish `: (fun w => c * φ w) = c • φ` using `rfl`. Rewrite using `[this, fderiv_const_smul_field]`. Establish `h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ)`. Rewrite using `[h1]`.

Conclude with `fderiv_const_smul_field (f := fderiv ℝ φ) c`. Use extensionality with `i j`. Simplify using `only [ReciprocityTheory.AnForm.hessC, h2, Pi.smul_apply, Matrix.smul_apply, _root_.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_const_mul {D : ℕ} (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.hessC (fun w => c * φ w) z = (c : ℂ) • ReciprocityTheory.AnForm.hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    have : (fun w => c * φ w) = c • φ := rfl
    rw [this, fderiv_const_smul_field]
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]
    exact fderiv_const_smul_field (f := fderiv ℝ φ) c
  ext i j
  simp only [ReciprocityTheory.AnForm.hessC, h2, Pi.smul_apply, Matrix.smul_apply,
    _root_.smul_apply, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.mdisc`. Simplify using `only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun S _ => by ring`.
-/
theorem mdisc_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.maDens`. Simplify using `only [hessC_const_mul, mdisc_smul]`. Rewrite using `[← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_const_mul {D : ℕ} (c : ℝ) (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens (fun k w => c * φ k w) z = c ^ D * ReciprocityTheory.AnForm.maDens φ z := by
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hessC_const_mul, mdisc_smul]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.varInt`. Use `split_ifs with hA`. Unfold `GroundTheory.Heights₂.Heights.chartInt GroundTheory.Heights₂.Heights.chartDens GroundTheory.Heights₂.Heights.sheetSum`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[mul_finsum]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if, finsum_eq_if]`. Use `split_ifs with hx hs`.

Establish `key : ReciprocityTheory.AnForm.maDens (fun k => (fun _ x => c * ψ x : Fin e → (Fin n → ℂ) → ℝ) k ∘ hs.choose) y = c ^ e * ReciprocityTheory.AnForm.maDens (fun k => (fun _ => ψ : Fin e → (Fin n → ℂ) → ℝ) k ∘ hs.choose) y` using `maDens_const_mul c (fun _ => ψ ∘ hs.choose) y dsimp only`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem varInt_const_mul {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (c : ℝ) (ψ : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J e g (fun _ x => c * ψ x) =
      c ^ e * GroundTheory.Heights₂.Heights.varInt J e g (fun _ => ψ) := by
  unfold GroundTheory.Heights₂.Heights.varInt
  split_ifs with hA
  · unfold GroundTheory.Heights₂.Heights.chartInt GroundTheory.Heights₂.Heights.chartDens
      GroundTheory.Heights₂.Heights.sheetSum
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum]
    refine finsum_congr fun x => ?_
    classical
    rw [finsum_eq_if, finsum_eq_if]
    split_ifs with hx hs
    · have key : ReciprocityTheory.AnForm.maDens
          (fun k => (fun _ x => c * ψ x : Fin e → (Fin n → ℂ) → ℝ) k ∘ hs.choose) y =
          c ^ e * ReciprocityTheory.AnForm.maDens (fun k => (fun _ => ψ : Fin e → (Fin n → ℂ) → ℝ) k ∘
            hs.choose) y :=
        maDens_const_mul c (fun _ => ψ ∘ hs.choose) y
      dsimp only
      rw [key]
      ring
    · ring
    · ring
  · ring

/- English proof (translation)
Rewrite using `[fsPot_eq]`. Conclude with `varInt_const_mul J g 2 _`.
-/
theorem varInt_fsPot_eq_two_pow_mul {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (g : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J e g (fun _ => fsPot h) =
      2 ^ e * GroundTheory.Heights₂.Heights.varInt J e g (fun _ x => Real.log (h.dualNorm x)) := by
  rw [fsPot_eq]
  exact varInt_const_mul J g 2 _

/- English proof (translation)
Establish `hP` using `hJ.isPrime`. Establish `hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤`. Introduce `htop`. Establish `h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J` using `GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)`.

Take `⟨p, hp⟩` from `Ideal.nonempty_minimalPrimes hne`. Establish `hpP : p.IsPrime` using `hp.1.1`. Establish `hJp : J ≤ p` using `le_sup_left.trans hp.1.2`. Establish `hht` using `Ideal.map_height_le_one_of_mem_minimalPrimes hp`. Establish `hpm : (p.map (Ideal.Quotient.mk J)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`.

Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ (p.map (Ideal.Quotient.mk J))`. Rewrite `hform` using `[hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)]`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1}))` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2) (Ideal.Quotient.factor_surjective hp.1.2)`. Use `le_trans ?_ hle` and prove the remaining obligations. Establish `key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b`.

Introduce `a b ha hab`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe m`. Proceed by induction on `a using ENat.recTopCoe with`.

Consider the case `top => simp at ha`. Consider the case `coe k`. Establish `h1 : k ≤ 1` using `by exact_mod_cast ha`. Establish `h2 : k + m = e + 1` using `by exact_mod_cast hab`. Conclude with `(by omega : e ≤ m)` after adjusting the coercions.

Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Rewrite `hform` using `[WithBot.add_bot]`.

Conclude with `WithBot.bot_ne_coe hform`. Consider the case `coe b`. Establish `hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞)`. Conclude with `hform` after adjusting the coercions. Conclude with `key _ b hht hab` after adjusting the coercions.
-/
theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

/- English proof (translation)
Set `f` to `(GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom`. Set `P` to `RingHom.ker f`. Set `g : MvPolynomial (Fin d) ℂ ⧸ P →+* MvPolynomial (Fin n) ℂ ⧸ J` to `RingHom.kerLift f`. Establish `hgf : g.comp (Ideal.Quotient.mk P) = f` using `RingHom.ext fun a => RingHom.kerLift_mk f a`. Establish `hg_fin : g.Finite` using `RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk P) (by rw [hgf]; exact hfin)`.

Set `` to `g.toAlgebra`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin d) ℂ ⧸ P) (MvPolynomial (Fin n) ℂ ⧸ J)` using `⟨hg_fin.to_isIntegral⟩`. Establish `h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P)` using `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ _)) fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ ⧸ P) hpq`. Establish `hd : ringKrullDim (MvPolynomial (Fin d) ℂ) = (d : ℕ)`. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`.

Simplify using the standard rewrite rules. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Establish `haP : a ∈ P` using `ha`.

Establish `h2` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0) (Ideal.Quotient.eq_zero_iff_mem.mpr haP)`. Rewrite `h2` using `[hd]`. Establish `h3` using `(add_le_add_left (hJ.trans h1) 1).trans h2`. Establish `h4 : d + 1 ≤ d` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem injective_projHom_of_finite_of_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J))
    (hfin : (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.Finite) :
    Function.Injective (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A) := by
  let f := (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom
  let P := RingHom.ker f
  let g : MvPolynomial (Fin d) ℂ ⧸ P →+* MvPolynomial (Fin n) ℂ ⧸ J := RingHom.kerLift f
  have hgf : g.comp (Ideal.Quotient.mk P) = f :=
    RingHom.ext fun a => RingHom.kerLift_mk f a
  have hg_fin : g.Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk P) (by rw [hgf]; exact hfin)
  let := g.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ ⧸ P) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hg_fin.to_isIntegral⟩
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ _)) fun _ _ hpq =>
      Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ ⧸ P) hpq
  have hd : ringKrullDim (MvPolynomial (Fin d) ℂ) = (d : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have haP : a ∈ P := ha
  have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr haP)
  rw [hd] at h2
  have h3 := (add_le_add_left (hJ.trans h1) 1).trans h2
  have h4 : d + 1 ≤ d := by exact_mod_cast h3
  omega

/- English proof (translation)
Unfold `IsFiniteProj`. Rewrite using `[aeval_linForm_eq_projHom]`. Conclude with `⟨fun h => ⟨injective_projHom_of_finite_of_le hJ h, h⟩, fun h => h.finite⟩`.
-/
theorem isFiniteProj_iff_of_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)) :
    IsFiniteProj J A ↔ GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A := by
  unfold IsFiniteProj
  rw [aeval_linForm_eq_projHom]
  exact ⟨fun h => ⟨injective_projHom_of_finite_of_le hJ h, h⟩, fun h => h.finite⟩

/- English proof (translation)
Establish `hp : (fun A : Matrix (Fin d) (Fin n) ℂ => IsFiniteProj J A) = fun A => GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A`. Use function extensionality and compare the values at `fun A => propext (isFiniteProj_iff_of_le hJ)`. Unfold `varIntegral GroundTheory.Heights₂.Heights.varInt`. Distinguish the cases in `h : ∃ A : Matrix (Fin d) (Fin n) ℂ, GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A`. Establish `h' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A`.

Take `⟨A, hA⟩` from `h`. Conclude with `⟨A, (isFiniteProj_iff_of_le hJ).mpr hA⟩`. Rewrite using `[dif_pos h, dif_pos h', projInt_eq, choose_congr hp h' h]`. Establish `h' : ¬ ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A`. Introduce and unpack `⟨A, hA⟩`.

Conclude with `h ⟨A, (isFiniteProj_iff_of_le hJ).mp hA⟩`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem varIntegral_eq_of_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)) :
    varIntegral J g φ = GroundTheory.Heights₂.Heights.varInt J d g φ := by
  have hp : (fun A : Matrix (Fin d) (Fin n) ℂ => IsFiniteProj J A) =
      fun A => GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A :=
    funext fun A => propext (isFiniteProj_iff_of_le hJ)
  unfold varIntegral GroundTheory.Heights₂.Heights.varInt
  by_cases h : ∃ A : Matrix (Fin d) (Fin n) ℂ,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A
  · have h' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A := by
      obtain ⟨A, hA⟩ := h
      exact ⟨A, (isFiniteProj_iff_of_le hJ).mpr hA⟩
    rw [dif_pos h, dif_pos h', projInt_eq, choose_congr hp h' h]
  · have h' : ¬ ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A := by
      rintro ⟨A, hA⟩
      exact h ⟨A, (isFiniteProj_iff_of_le hJ).mp hA⟩
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Rewrite using `[varIntegral_eq_of_le _ _ _ (le_ringKrullDim_slice hJ hH hℓ), varInt_fsPot_eq_two_pow_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]`.
-/
theorem slice_integral_eq {n e : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {ℓ : Fin n → ℂ} (g : (Fin n → ℂ) → ℝ) (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J)
    (hℓ : linForm ℓ ∉ J) :
    ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h) =
      GroundTheory.Heights₂.Heights.varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g
        (fun _ x => Real.log (h.dualNorm x)) := by
  rw [varIntegral_eq_of_le _ _ _ (le_ringKrullDim_slice hJ hH hℓ), varInt_fsPot_eq_two_pow_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/- English proof (translation)
Use `⟨hJ.isPrime, hH, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hrel`. Simplify using `only [IsRelevant, not_exists, not_not] at hrel`. Establish `hsurj : Function.Surjective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J))`. Introduce `z`.

Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨c, by rw [← Ideal.Quotient.mk_algebraMap]; rfl⟩`. Consider the case `add p q hp hq`. Take `⟨a, ha⟩` from `hp`.

Take `⟨b, hb⟩` from `hq`. Conclude with `⟨a + b, by rw [map_add, ha, hb, map_add]⟩`. Consider the case `mul_X p i _`. Conclude with `⟨0, by rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hrel i), mul_zero]⟩`. Establish `h1` using `ringKrullDim_le_of_surjective _ hsurj`.

Rewrite `h1` using `[hJ.dim, ringKrullDim_eq_zero_of_field]`. Establish `: e + 1 ≤ 0` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem isProjPrime_of_isAffVariety {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) : IsProjPrime J := by
  refine ⟨hJ.isPrime, hH, ?_⟩
  by_contra hrel
  simp only [IsRelevant, not_exists, not_not] at hrel
  have hsurj : Function.Surjective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, by rw [← Ideal.Quotient.mk_algebraMap]; rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p i _ =>
      exact ⟨0, by rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hrel i), mul_zero]⟩
  have h1 := ringKrullDim_le_of_surjective _ hsurj
  rw [hJ.dim, ringKrullDim_eq_zero_of_field] at h1
  have : e + 1 ≤ 0 := by exact_mod_cast h1
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩, fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg GroundTheory.Heights₂.Heights.A …`.
-/
theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

/- English proof (translation)
Establish `hm : Measurable (Set.piecewise {x : Fin n → ℂ | x ≠ 0} g fun _ => g 0)` using `hg.measurable_piecewise continuousOn_const (measurableSet_singleton _).compl`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using `[Set.piecewise]`. Simplify using `[Set.piecewise, hx]`.
-/
theorem measurable_of_continuousOn_ne_zero {n : ℕ} {g : (Fin n → ℂ) → ℝ}
    (hg : ContinuousOn g {x | x ≠ 0}) : Measurable g := by
  classical
  have hm : Measurable (Set.piecewise {x : Fin n → ℂ | x ≠ 0} g fun _ => g 0) :=
    hg.measurable_piecewise continuousOn_const (measurableSet_singleton _).compl
  convert hm using 1
  funext x
  by_cases hx : x = 0
  · subst hx
    simp [Set.piecewise]
  · simp [Set.piecewise, hx]

def ConeToProjectiveContinuous.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → IsHomogIdeal J → linForm ℓ ∉ J →
    ContinuousOn g {x | x ≠ 0} → (∀ c : ℂ, c ≠ 0 → ∀ y, g (c • y) = g y) →
      coneIntegral h J e g =
        ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h)

/- English proof (translation)
Introduce `n e h J ℓ g hA hH hℓ hgc hg` and use `H n e h J ℓ g hA hH hℓ (measurable_of_continuousOn_ne_zero hgc) hg`.
-/
theorem ConeToProjectiveContinuous.kleimanNef_field_of_alt (H : ConeToProjective.Statement) :
    ConeToProjectiveContinuous.Statement :=
  fun n e h J ℓ g hA hH hℓ hgc hg =>
    H n e h J ℓ g hA hH hℓ (measurable_of_continuousOn_ne_zero hgc) hg

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H n e h J ℓ g hA hH hℓ hgc hg`. Establish `hP` using `isProjPrime_of_isAffVariety hA hH`. Take `⟨F, hF⟩` from `(exists_isChowForm_iff (e := e) hP).mpr hA`. Rewrite using `[H n e h J F ℓ g hP hF hℓ (fun t x ht => hg t ht x) hgc, slice_integral_eq h g hA hH hℓ]`.

Introduce `H n e h J F ℓ g hP hF hℓ hg hgc`. Establish `hA : IsAffVariety J (e + 1)` using `(exists_isChowForm_iff hP).mp ⟨F, hF⟩`. Rewrite using `[H n e h J ℓ g hA hP.isHomog hℓ hgc (fun c hc y => hg c y hc), slice_integral_eq h g hA hP.isHomog hℓ]`.
-/
theorem ConeToProjective.iff_continuous :
    GroundTheory.Heights₂.Heights.ConeToProjective.Statement ↔ ConeToProjectiveContinuous.Statement := by
  constructor
  · intro H n e h J ℓ g hA hH hℓ hgc hg
    have hP := isProjPrime_of_isAffVariety hA hH
    obtain ⟨F, hF⟩ := (exists_isChowForm_iff (e := e) hP).mpr hA
    rw [H n e h J F ℓ g hP hF hℓ (fun t x ht => hg t ht x) hgc, slice_integral_eq h g hA hH hℓ]
  · intro H n e h J F ℓ g hP hF hℓ hg hgc
    have hA : IsAffVariety J (e + 1) := (exists_isChowForm_iff hP).mp ⟨F, hF⟩
    rw [H n e h J ℓ g hA hP.isHomog hℓ hgc (fun c hc y => hg c y hc),
      slice_integral_eq h g hA hP.isHomog hℓ]

/- English proof (translation)
The claim follows from `ConeToProjective.iff_continuous.mpr (ConeToProjectiveContinuous.kleimanNef_field_of_alt H)`.
-/
theorem ConeToProjective.kleimanNef_field_of_alt (H : ConeToProjective.Statement) :
    GroundTheory.Heights₂.Heights.ConeToProjective.Statement :=
  ConeToProjective.iff_continuous.mpr (ConeToProjectiveContinuous.kleimanNef_field_of_alt H)

/- English proof (translation)
Take `⟨hA, hH, hℓ, -⟩` from `ConeToProjective.hypotheses_inhabited`. Establish `hpos : ∀ x : Fin 2 → ℂ, x ≠ 0 → ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 ≠ 0`. Introduce `x hx h0`. Apply `hx` to reduce the goal to its premises. Establish `h0' : ‖x 0‖ ^ 2 = 0 ∧ ‖x 1‖ ^ 2 = 0` using `(add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h0`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `using h0'.1`. Simplify using `using h0'.2`. Use `⟨hA, hH, hℓ, ?_, ?_⟩` and prove the remaining obligations.

Use `ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => hpos x hx` and prove the remaining obligations. Introduce `c hc y`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using the standard rewrite rules.

Establish `hc2 : ‖c‖ ^ 2 ≠ 0` using `by positivity`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`. Rewrite using `[← mul_add, mul_div_mul_left _ _ hc2]`.
-/
theorem ConeToProjectiveContinuous.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) ∧
      IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (Pi.single (0 : Fin 2) (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      ContinuousOn (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) {x | x ≠ 0} ∧
      (∀ c : ℂ, c ≠ 0 → ∀ y : Fin 2 → ℂ,
        (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) (c • y) =
          (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) y) := by
  obtain ⟨hA, hH, hℓ, -⟩ := ConeToProjective.hypotheses_inhabited
  have hpos : ∀ x : Fin 2 → ℂ, x ≠ 0 → ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 ≠ 0 := by
    intro x hx h0
    apply hx
    have h0' : ‖x 0‖ ^ 2 = 0 ∧ ‖x 1‖ ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h0
    funext i
    fin_cases i
    · simpa using h0'.1
    · simpa using h0'.2
  refine ⟨hA, hH, hℓ, ?_, ?_⟩
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => hpos x hx
  · intro c hc y
    by_cases hy : y = 0
    · subst hy
      simp
    have hc2 : ‖c‖ ^ 2 ≠ 0 := by positivity
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [← mul_add, mul_div_mul_left _ _ hc2]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
