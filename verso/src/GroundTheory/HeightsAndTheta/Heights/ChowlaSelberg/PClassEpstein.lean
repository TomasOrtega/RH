import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DedekindZetaEqSumRealEisenstein
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassPeriodInvConj
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassReducedParamsNonemptyPf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

/- English proof (translation)
Use extensionality with `z`. Conclude with `Iff.rfl`.
-/
theorem coe_idealLattice (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice σ I : Set ℂ) = σ '' (I : Set K) := by
  ext z
  exact Iff.rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hreal : (InfinitePlace.mk σ).IsReal`. Rewrite using `[InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.mpr (h x)`. Establish `h1 : 0 < InfinitePlace.nrRealPlaces K` using `by classical`. Conclude with `Fintype.card_pos_iff.mpr ⟨⟨_, hreal⟩⟩`. Establish `h2` using `InfinitePlace.card_add_two_mul_card_eq_rank K`.

Rewrite `h2` using `[Algebra.IsQuadraticExtension.finrank_eq_two]`. Establish `h3 : InfinitePlace.nrComplexPlaces K = 0` using `by omega`. Establish `h4` using `sign_discr K`. Rewrite `h4` using `[h3, pow_zero, S.discr_eq]`. Establish `hd` using `S.prime.pos`.

Establish `: (-(S.d : ℤ)).sign = -1` using `Int.sign_eq_neg_one_of_neg (by omega)`. Rewrite `h4` using `[this]`. Conclude with `absurd h4 (by decide)`.
-/
theorem exists_im_ne_zero [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)
    (σ : K →+* ℂ) : ∃ x : K, (σ x).im ≠ 0 := by
  by_contra h
  push Not at h
  have hreal : (InfinitePlace.mk σ).IsReal := by
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (h x)
  have h1 : 0 < InfinitePlace.nrRealPlaces K := by
    classical
    exact Fintype.card_pos_iff.mpr ⟨⟨_, hreal⟩⟩
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  have h3 : InfinitePlace.nrComplexPlaces K = 0 := by omega
  have h4 := sign_discr K
  rw [h3, pow_zero, S.discr_eq] at h4
  have hd := S.prime.pos
  have : (-(S.d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [this] at h4
  exact absurd h4 (by decide)

/- English proof (translation)
Establish `hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain Complex.basisOneI) = 1`. Rewrite using `[← Complex.toBasis_orthonormalBasisOneI, MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _)]`. Rewrite using `[MeasureTheory.measureReal_def, OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]`. Simplify using the standard rewrite rules. Unfold `latticeArea`.

Rewrite using `[ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI, hvol, mul_one, Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `[Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latticeArea_periodPair (L : PeriodPair) :
    latticeArea L.lattice = |L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re| := by
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _)]
    rw [MeasureTheory.measureReal_def, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI, hvol, mul_one,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
  congr 1
  ring

/- English proof (translation)
Establish `hind : LinearIndependent ℝ ![c⁻¹ * (τ : ℂ), c⁻¹]`. Use `LinearIndependent.pair_iff.2 fun a b hab => ?_` and prove the remaining obligations. Use `LinearIndependent.pair_iff.1 (latticeOfTau τ).indep a b ?_` and prove the remaining obligations. Establish `e : a • (latticeOfTau τ).ω₁ + b • (latticeOfTau τ).ω₂ = c * (a • (c⁻¹ * (τ : ℂ)) + b • c⁻¹)`. Simplify using `only [latticeOfTau, Complex.real_smul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e, hab, mul_zero]`. Set `P : PeriodPair` to `⟨c⁻¹ * (τ : ℂ), c⁻¹, hind⟩`. Establish `hmem : ∀ z : ℂ, z ∈ Λ ↔ c * z ∈ Theta.latticeOf (τ : ℂ)`. Introduce `z`.

Rewrite using `[← h]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨y, hy, e⟩`.

Rewrite using `[← mul_left_cancel₀ hc e]` and apply the resulting hypothesis. Establish `hP : P.lattice = Λ`. Use extensionality with `z`. Rewrite using `[PeriodPair.mem_lattice, hmem, Theta.latticeOf, SetLike.mem_coe, Submodule.mem_span_pair]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, n, rfl⟩`. Use `⟨n, m, ?_⟩` and prove the remaining obligations. Simplify using `only [P, zsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨a, b, e⟩`. Use `⟨b, a, mul_left_cancel₀ hc ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Simplify using `only [P, zsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Substitute `hP` using the available equality. Establish `harea : latticeArea P.lattice = ‖c⁻¹‖ ^ 2 * τ.im`. Rewrite using `[latticeArea_periodPair]`. Establish `e : P.ω₁.re * P.ω₂.im - P.ω₁.im * P.ω₂.re = -(Complex.normSq c⁻¹ * τ.im)`.

Simplify using `only [P, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, UpperHalfPlane.coe_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, abs_neg, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) τ.im_pos.le), Complex.normSq_eq_norm_sq]`. Unfold `epsteinSum Theta.realEisenstein`. Rewrite using `[harea, ← P.latticeEquivProd.symm.toEquiv.tsum_eq]`.

Use `tsum_congr fun p => ?_` and prove the remaining obligations. Establish `hcoe : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) = c⁻¹ * ((p.1 : ℂ) * τ + p.2)`. Rewrite using `[LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]`. Simplify using `only [P]`. Expand and normalize the polynomial expressions, which then agree.

Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules. Establish `hne : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) ≠ 0`. Rewrite using `[ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.coe_toEquiv, LinearEquiv.map_eq_zero_iff]`.

Conclude with `hp`. Establish `hz : (p.1 : ℂ) * τ + p.2 ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hcoe, h0, mul_zero]`.

Rewrite using `[if_neg hne, if_neg hp, hcoe, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.mul_rpow (by positivity) τ.im_pos.le, ← Real.rpow_natCast_mul (norm_nonneg _)]`. Establish `ht : 0 < ‖c⁻¹‖ ^ ((2 : ℕ) * s)` using `Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hc)) _`. Move the coercions through the operations in `at ht ⊢`. Rewrite using `[mul_div_mul_left _ _ ht.ne']`.
-/
theorem epsteinSum_eq_realEisenstein {Λ : Submodule ℤ ℂ} {τ : ℍ} {c : ℂ} (hc : c ≠ 0)
    (h : (fun z => c * z) '' (Λ : Set ℂ) = Theta.latticeOf (τ : ℂ)) (s : ℝ) :
    epsteinSum Λ s = Theta.realEisenstein τ s := by
  have hind : LinearIndependent ℝ ![c⁻¹ * (τ : ℂ), c⁻¹] := by
    refine LinearIndependent.pair_iff.2 fun a b hab => ?_
    refine LinearIndependent.pair_iff.1 (latticeOfTau τ).indep a b ?_
    have e : a • (latticeOfTau τ).ω₁ + b • (latticeOfTau τ).ω₂ =
        c * (a • (c⁻¹ * (τ : ℂ)) + b • c⁻¹) := by
      simp only [latticeOfTau, Complex.real_smul]
      field_simp
    rw [e, hab, mul_zero]
  let P : PeriodPair := ⟨c⁻¹ * (τ : ℂ), c⁻¹, hind⟩
  have hmem : ∀ z : ℂ, z ∈ Λ ↔ c * z ∈ Theta.latticeOf (τ : ℂ) := by
    intro z
    rw [← h]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, e⟩
      rwa [← mul_left_cancel₀ hc e]
  have hP : P.lattice = Λ := by
    ext z
    rw [PeriodPair.mem_lattice, hmem, Theta.latticeOf, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨n, m, ?_⟩
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
    · rintro ⟨a, b, e⟩
      refine ⟨b, a, mul_left_cancel₀ hc ?_⟩
      rw [← e]
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
  subst hP
  have harea : latticeArea P.lattice = ‖c⁻¹‖ ^ 2 * τ.im := by
    rw [latticeArea_periodPair]
    have e : P.ω₁.re * P.ω₂.im - P.ω₁.im * P.ω₂.re = -(Complex.normSq c⁻¹ * τ.im) := by
      simp only [P, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, UpperHalfPlane.coe_im]
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) τ.im_pos.le),
      Complex.normSq_eq_norm_sq]
  unfold epsteinSum Theta.realEisenstein
  rw [harea, ← P.latticeEquivProd.symm.toEquiv.tsum_eq]
  refine tsum_congr fun p => ?_
  have hcoe : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) =
      c⁻¹ * ((p.1 : ℂ) * τ + p.2) := by
    rw [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
    simp only [P]
    ring
  by_cases hp : p = 0
  · subst hp
    simp
  · have hne : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) ≠ 0 := by
      rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.coe_toEquiv,
        LinearEquiv.map_eq_zero_iff]
      exact hp
    have hz : (p.1 : ℂ) * τ + p.2 ≠ 0 := by
      intro h0
      apply hne
      rw [hcoe, h0, mul_zero]
    rw [if_neg hne, if_neg hp, hcoe, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      Real.mul_rpow (by positivity) τ.im_pos.le, ← Real.rpow_natCast_mul (norm_nonneg _)]
    have ht : 0 < ‖c⁻¹‖ ^ ((2 : ℕ) * s) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hc)) _
    push_cast at ht ⊢
    rw [mul_div_mul_left _ _ ht.ne']

/- English proof (translation)
Unfold `Theta.realEisenstein`. Rewrite using `[← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Establish `hneg : ((Theta.negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ)` using `rfl`. Establish `him : (Theta.negConj τ).im = τ.im` using `by show ((Theta.negConj τ : ℍ) : ℂ).im = (τ : ℂ).im`.

Rewrite using `[hneg]`. Simplify using the standard rewrite rules. Distinguish the cases in `hp : p = 0`. Substitute `hp` using the available equality. Establish `h00 : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) (0 : ℤ × ℤ) = 0`.

Apply the tactic sequence `ext <;> simp`. Rewrite using `[if_pos h00, if_pos rfl]`. Establish `hp' : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p ≠ 0`. Introduce `h0`. Apply `hp` to reduce the goal to its premises.

Simplify using `only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map, Prod.mk_eq_zero, id, neg_eq_zero] at h0`. Conclude with `Prod.ext h0.1 h0.2`. Rewrite using `[if_neg hp', if_neg hp, him]`. Use `congr 2`. Establish `e : (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).1 : ℂ) * (Theta.negConj τ : ℂ) + (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).2 : ℂ) = -(starRingEnd ℂ) ((p.1 : ℂ) * τ + p.2)`.

Simplify using `only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map, id, hneg, map_add, map_mul, map_intCast, Int.cast_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg, Complex.norm_conj]`.
-/
theorem realEisenstein_negConj (τ : ℍ) (s : ℝ) :
    Theta.realEisenstein (Theta.negConj τ) s = Theta.realEisenstein τ s := by
  unfold Theta.realEisenstein
  rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  refine tsum_congr fun p => ?_
  have hneg : ((Theta.negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have him : (Theta.negConj τ).im = τ.im := by
    show ((Theta.negConj τ : ℍ) : ℂ).im = (τ : ℂ).im
    rw [hneg]
    simp
  by_cases hp : p = 0
  · subst hp
    have h00 : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) (0 : ℤ × ℤ) = 0 := by
      ext <;> simp
    rw [if_pos h00, if_pos rfl]
  · have hp' : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p ≠ 0 := by
      intro h0
      apply hp
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map,
        Prod.mk_eq_zero, id, neg_eq_zero] at h0
      exact Prod.ext h0.1 h0.2
    rw [if_neg hp', if_neg hp, him]
    congr 2
    have e : (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).1 : ℂ) * (Theta.negConj τ : ℂ) +
        (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).2 : ℂ) =
          -(starRingEnd ℂ) ((p.1 : ℂ) * τ + p.2) := by
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map, id, hneg,
        map_add, map_mul, map_intCast, Int.cast_neg]
      ring
    rw [e, norm_neg, Complex.norm_conj]

/- English proof (translation)
Rewrite using `[ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]`. Unfold `partialZeta`. Use `tsum_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _), Real.rpow_neg (Nat.cast_nonneg _)]`.
-/
theorem partialZeta_eq_toReal (A : ClassGroup (𝓞 K)) (s : ℝ) :
    partialZeta A s = (∑' t : (ClassGroup.mk0 ⁻¹' {A} : Set (Ideal (𝓞 K))⁰),
      ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s))).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  unfold partialZeta
  refine tsum_congr fun t => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_neg (Nat.cast_nonneg _)]

/- English proof (translation)
Introduce `σ C 𝔟 hC s hs`. Substitute `hC` using the available equality. Establish `hK : Module.finrank ℚ K = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two ℚ K`. Establish `hσ` using `exists_im_ne_zero S σ`. Take `⟨τ, c, hc, himg⟩` from `Theta.exists_isLatticeParam_fractionalIdeal hK σ hσ 𝔟`.

Take `⟨w, hw, hinv⟩` from `Theta.ClassPeriodInv.exists_inv_eq_conj hK σ hσ 𝔟`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc', himg'⟩ : Theta.IsLatticeParam (σ '' (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K)) (Theta.negConj τ) := by`. Rewrite using `[hinv]`. Conclude with `Theta.ClassPeriodInv.isLatticeParam_conj ⟨c, hc, himg⟩ hw`. Establish `key` using `Theta.projectiveLineClassData.class_sum hK σ hσ 𝔟⁻¹ (Theta.negConj τ) c' hc' himg' hs`.

Establish `hE : epsteinSum (idealLattice σ 𝔟) s = Theta.realEisenstein τ s` using `epsteinSum_eq_realEisenstein hc (by rw [coe_idealLattice]; exact himg) s`. Establish `hD : Real.sqrt |(discr K : ℝ)| = Real.sqrt S.d`. Rewrite using `[S.discr_eq]`. Use `push_cast`. Rewrite using `[abs_neg, Nat.abs_cast]`.

Rewrite `key` using `[realEisenstein_negConj, hD]`. Establish `hw0 : (Units.torsionOrder K : ENNReal) ≠ 0`. Conclude with `Units.torsionOrder_ne_zero K` after adjusting the coercions. Establish `hsum` using `(ENNReal.eq_div_iff hw0 (ENNReal.natCast_ne_top _)).mpr key`. Establish `hcl : ClassGroup.mk K 𝔟 = (ClassGroup.mk K 𝔟⁻¹)⁻¹` using `by rw [map_inv, inv_inv]`.

Rewrite using `[hcl, partialZeta_eq_toReal]`. Use `erw [hsum]`. Rewrite using `[ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (mul_nonneg (by positivity) (Theta.realEisenstein_nonneg _ _)), hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ClassEpstein.proof [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K) :
    ClassEpstein.Statement S := by
  intro σ C 𝔟 hC s hs
  subst hC
  have hK : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hσ := exists_im_ne_zero S σ
  obtain ⟨τ, c, hc, himg⟩ := Theta.exists_isLatticeParam_fractionalIdeal hK σ hσ 𝔟
  obtain ⟨w, hw, hinv⟩ := Theta.ClassPeriodInv.exists_inv_eq_conj hK σ hσ 𝔟
  obtain ⟨c', hc', himg'⟩ : Theta.IsLatticeParam
      (σ '' (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K))
      (Theta.negConj τ) := by
    rw [hinv]
    exact Theta.ClassPeriodInv.isLatticeParam_conj ⟨c, hc, himg⟩ hw
  have key := Theta.projectiveLineClassData.class_sum hK σ hσ 𝔟⁻¹ (Theta.negConj τ) c' hc' himg' hs
  have hE : epsteinSum (idealLattice σ 𝔟) s = Theta.realEisenstein τ s :=
    epsteinSum_eq_realEisenstein hc (by rw [coe_idealLattice]; exact himg) s
  have hD : Real.sqrt |(discr K : ℝ)| = Real.sqrt S.d := by
    rw [S.discr_eq]
    push_cast
    rw [abs_neg, Nat.abs_cast]
  rw [realEisenstein_negConj, hD] at key
  have hw0 : (Units.torsionOrder K : ENNReal) ≠ 0 := by
    exact_mod_cast Units.torsionOrder_ne_zero K
  have hsum := (ENNReal.eq_div_iff hw0 (ENNReal.natCast_ne_top _)).mpr key
  have hcl : ClassGroup.mk K 𝔟 = (ClassGroup.mk K 𝔟⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  rw [hcl, partialZeta_eq_toReal]
  erw [hsum]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (Theta.realEisenstein_nonneg _ _)), hE]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
