import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CurvatureStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CptDifferentiable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BoundOfIneqs
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfDetFderivNeZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExtendByZeroStrictAntiOfPositiveGaps

noncomputable section

namespace GlobalTheory.BigTrdeg

section Alg

open MvPolynomial

def homog {K : Type} [Field K] {n N : ℕ} (j0 : Fin N) (jj : Fin n → Fin N) (d : ℕ) (p : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin N) K :=
  ∑ α ∈ p.support, C (p.coeff α) * X j0 ^ (d - ∑ k, α k) * ∏ k, X (jj k) ^ α k

/- English proof (translation)
Establish `h` using `MvPolynomial.le_totalDegree hα`. Rewrite `h` using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Then use the resulting hypothesis.
-/
theorem sum_le_totalDegree {K : Type} [Field K] {n : ℕ} {p : MvPolynomial (Fin n) K} {α : Fin n →₀ ℕ}
    (hα : α ∈ p.support) : ∑ k, α k ≤ p.totalDegree := by
  have h := MvPolynomial.le_totalDegree hα
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h

/- English proof (translation)
Unfold `homog`. Apply `MvPolynomial.IsHomogeneous.sum` to reduce the goal to its premises. Introduce `α hα`. Establish `hS : ∑ k, α k ≤ d` using `(sum_le_totalDegree hα).trans hd`. Establish `h` using `((MvPolynomial.isHomogeneous_C (σ := Fin N) (p.coeff α)).mul (MvPolynomial.isHomogeneous_X_pow (R := K) j0 (d - ∑ k, α k))).mul (MvPolynomial.IsHomogeneous.prod Finset.univ (fun k => (MvPolynomial.X (jj k) : MvPolynomial (Fin N) K) ^ α k) (fun k => α k) (fun k _ => MvPolynomial.i …`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use linear arithmetic over natural numbers and integers.
-/
theorem homog_isHomogeneous {K : Type} [Field K] {n N : ℕ} (j0 : Fin N) (jj : Fin n → Fin N) {d : ℕ}
    {p : MvPolynomial (Fin n) K} (hd : p.totalDegree ≤ d) : (homog j0 jj d p).IsHomogeneous d := by
  unfold homog
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hS : ∑ k, α k ≤ d := (sum_le_totalDegree hα).trans hd
  have h := ((MvPolynomial.isHomogeneous_C (σ := Fin N) (p.coeff α)).mul
    (MvPolynomial.isHomogeneous_X_pow (R := K) j0 (d - ∑ k, α k))).mul
    (MvPolynomial.IsHomogeneous.prod Finset.univ (fun k => (MvPolynomial.X (jj k) : MvPolynomial (Fin N) K) ^ α k)
      (fun k => α k) (fun k _ => MvPolynomial.isHomogeneous_X_pow _ _))
  convert h using 1
  omega

/- English proof (translation)
Unfold `homog`. Rewrite using `[MvPolynomial.eval₂_eq' φ (fun k => u (jj k) / u j0) p, MvPolynomial.eval₂_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hS : ∑ k, α k ≤ d` using `(sum_le_totalDegree hα).trans hd`. Simplify using `only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[show u j0 ^ d = u j0 ^ (d - ∑ k, α k) * u j0 ^ (∑ k, α k) by rw [← pow_add, Nat.sub_add_cancel hS]]`. Establish `hu' : u j0 ^ (∑ k, α k) ≠ 0` using `pow_ne_zero _ hu`. Clear the denominators using the available nonvanishing facts.
-/
theorem eval₂_homog {K L : Type} [Field K] [Field L] (φ : K →+* L) {n N : ℕ} (j0 : Fin N) (jj : Fin n → Fin N)
    {d : ℕ} {p : MvPolynomial (Fin n) K} (hd : p.totalDegree ≤ d) (u : Fin N → L) (hu : u j0 ≠ 0) :
    eval₂ φ u (homog j0 jj d p) = u j0 ^ d * eval₂ φ (fun k => u (jj k) / u j0) p := by
  unfold homog
  rw [MvPolynomial.eval₂_eq' φ (fun k => u (jj k) / u j0) p, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hS : ∑ k, α k ≤ d := (sum_le_totalDegree hα).trans hd
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [show u j0 ^ d = u j0 ^ (d - ∑ k, α k) * u j0 ^ (∑ k, α k) by rw [← pow_add, Nat.sub_add_cancel hS]]
  have hu' : u j0 ^ (∑ k, α k) ≠ 0 := pow_ne_zero _ hu
  field_simp

/- English proof (translation)
Establish `hind' : AlgebraicIndependent K (fun k : Fin n => v (jj k) / v j0)`. Rewrite using `[algebraicIndependent_iff]`. Introduce `p hp`. Establish `hP` using `homog_isHomogeneous (K := K) j0 jj (d := p.totalDegree + 1) (p := p) (Nat.le_succ _)`. Establish `hv0 : MvPolynomial.aeval v (homog j0 jj (p.totalDegree + 1) p) = 0`.

Rewrite using `[MvPolynomial.aeval_def, eval₂_homog (algebraMap K Ω) j0 jj (Nat.le_succ _) v hv, ← MvPolynomial.aeval_def, hp, mul_zero]`. Establish `hW` using `hrel p.totalDegree _ hP hv0`. Apply `MvPolynomial.map_injective (f := σ) σ.injective` to reduce the goal to its premises. Simplify using `only [map_zero]`. Apply `hind` to reduce the goal to its premises.

Introduce `s hs h0`. Rewrite using `[MvPolynomial.eval_map]`. Establish `h1` using `hW s hs`. Rewrite `h1` using `[eval₂_homog σ j0 jj (Nat.le_succ _) (fun k => W k s) h0]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ h0)`.

Establish `hmem : ∀ k : Fin n, v (jj k) / v j0 ∈ IntermediateField.adjoin K (Set.range fun k => v k / v j0)` using `fun k => IntermediateField.subset_adjoin K _ ⟨jj k, rfl⟩`. Establish `hy : AlgebraicIndependent K (fun k : Fin n => (⟨v (jj k) / v j0, hmem k⟩ : IntermediateField.adjoin K (Set.range fun k => v k / v j0)))` using `AlgebraicIndependent.of_comp (IntermediateField.val _) (by exact hind')`. Establish `h1` using `hy.cardinalMk_le_trdeg`. Establish `h2` using `trdeg_le_of_injective (IntermediateField.val (IntermediateField.adjoin K (Set.range fun k => v k / v j0))) Subtype.val_injective`. Rewrite `h1` using `[Cardinal.mk_fin]`.

Rewrite `h2` using `[hΩ]`. Conclude with `le_antisymm h2 h1`.
-/
theorem trdeg_ratios {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) {n N : ℕ}
    (hΩ : Algebra.trdeg K Ω = n) (v : Fin N → Ω) (j0 : Fin N) (jj : Fin n → Fin N) (hv : v j0 ≠ 0)
    {S : Type} (W : Fin N → S → ℂ) (U : Set S)
    (hrel : ∀ (d : ℕ) (P : MvPolynomial (Fin N) K), P.IsHomogeneous (d + 1) → aeval v P = 0 →
      ∀ s ∈ U, eval₂ σ (fun k => W k s) P = 0)
    (hind : ∀ p : MvPolynomial (Fin n) ℂ,
      (∀ s ∈ U, W j0 s ≠ 0 → eval (fun k => W (jj k) s / W j0 s) p = 0) → p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v j0)) = n := by
  classical
  have hind' : AlgebraicIndependent K (fun k : Fin n => v (jj k) / v j0) := by
    rw [algebraicIndependent_iff]
    intro p hp
    have hP := homog_isHomogeneous (K := K) j0 jj (d := p.totalDegree + 1) (p := p) (Nat.le_succ _)
    have hv0 : MvPolynomial.aeval v (homog j0 jj (p.totalDegree + 1) p) = 0 := by
      rw [MvPolynomial.aeval_def, eval₂_homog (algebraMap K Ω) j0 jj (Nat.le_succ _) v hv,
        ← MvPolynomial.aeval_def, hp, mul_zero]
    have hW := hrel p.totalDegree _ hP hv0
    apply MvPolynomial.map_injective (f := σ) σ.injective
    simp only [map_zero]
    apply hind
    intro s hs h0
    rw [MvPolynomial.eval_map]
    have h1 := hW s hs
    rw [eval₂_homog σ j0 jj (Nat.le_succ _) (fun k => W k s) h0] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ h0)
  have hmem : ∀ k : Fin n, v (jj k) / v j0 ∈ IntermediateField.adjoin K (Set.range fun k => v k / v j0) :=
    fun k => IntermediateField.subset_adjoin K _ ⟨jj k, rfl⟩
  have hy : AlgebraicIndependent K
      (fun k : Fin n => (⟨v (jj k) / v j0, hmem k⟩ : IntermediateField.adjoin K (Set.range fun k => v k / v j0))) :=
    AlgebraicIndependent.of_comp (IntermediateField.val _) (by exact hind')
  have h1 := hy.cardinalMk_le_trdeg
  have h2 := trdeg_le_of_injective (IntermediateField.val (IntermediateField.adjoin K (Set.range fun k => v k / v j0)))
    Subtype.val_injective
  rw [Cardinal.mk_fin] at h1
  rw [hΩ] at h2
  exact le_antisymm h2 h1

end Alg

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `choose M hM using X.signature`. Use `⟨fun τ => M τ, ?_⟩` and prove the remaining obligations. Use `show (fun τ => M τ) ∈ GG X.Ψ X.Gm X.p0`. Introduce `τ`. Use `⟨(hM τ).1, fun i => ?_⟩` and prove the remaining obligations.

Establish `hd : dmin X.Gm (fun τ => M τ) τ i = ((psgn X.p0 i : ℝ) : ℂ)`. Unfold `dmin`. Rewrite using `[show gram τ.1 X.Gm (mat (fun τ => M τ) τ) = _ from (hM τ).2]`. Conclude with `PoinPf.lminor_Jd X i`. Rewrite using `[hd, Complex.ofReal_re]`.

Conclude with `mul_self_pos.mpr (PoinPf.psgn_ne X.p0 i)`.
-/
theorem exists_mem_dom (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose M hM using X.signature
  refine ⟨fun τ => M τ, ?_⟩
  show (fun τ => M τ) ∈ GG X.Ψ X.Gm X.p0
  intro τ
  refine ⟨(hM τ).1, fun i => ?_⟩
  have hd : dmin X.Gm (fun τ => M τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin
    rw [show gram τ.1 X.Gm (mat (fun τ => M τ) τ) = _ from (hM τ).2]
    exact PoinPf.lminor_Jd X i
  rw [hd, Complex.ofReal_re]
  exact mul_self_pos.mpr (PoinPf.psgn_ne X.p0 i)

/- English proof (translation)
Use `⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ hγ x _ => ?_⟩` and prove the remaining obligations. Simplify using `[bchar]`. Establish `h1` using `X.χ_add 0 0 γ hγ`. Take `⟨n, hn, hpow⟩` from `X.χ_fin 0`. Establish `h2` using `hpow γ hγ`.

Rewrite `h1` using `[add_zero]`. Establish `hne : X.χ 0 γ ≠ 0`. Introduce `h`. Rewrite `h2` using `[h, zero_pow hn.ne']`. Conclude with `zero_ne_one h2`.

Establish `h3 : X.χ 0 γ = 1` using `mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)`. Simplify using `[h3]`.
-/
theorem isSec_one (X : Data E r) : X.IsSec 0 (fun _ => 1) := by
  refine ⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ hγ x _ => ?_⟩
  · simp [bchar]
  · have h1 := X.χ_add 0 0 γ hγ
    obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
    have h2 := hpow γ hγ
    rw [add_zero] at h1
    have hne : X.χ 0 γ ≠ 0 := by
      intro h
      rw [h, zero_pow hn.ne'] at h2
      exact zero_ne_one h2
    have h3 : X.χ 0 γ = 1 := mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)
    simp [h3]

def RatiosFree (X : Data E r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) : Prop :=
  ∃ (j0 : Fin N) (jj : Fin (nd X) → Fin N), (∃ x ∈ X.dom, w j0 x ≠ 0) ∧
    ∀ p : MvPolynomial (Fin (nd X)) ℂ,
      (∀ x ∈ X.dom, w j0 x ≠ 0 → MvPolynomial.eval (fun k => w (jj k) x / w j0 x) p = 0) → p = 0

/- English proof (translation)
Establish `hpos : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviM X (phla X (a • L - eW)) x0 z ξ` using `fun x0 _ z hz ξ hξ => (ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.curvature_statement_holds r X (a • L - eW) x0 z hz).2 hdom ξ hξ`. Take `⟨x, hx, j0, jj, hx0, hdet⟩` from `GlobalTheory.ProperImmersionPoint.main E r X L eW N a w et ha hw hw0 het het0 hpos hpr`. Use `⟨j0, jj, ⟨x, hx, hx0⟩, fun p hp => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen X.dom`. Establish `hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ` using `fun τ => continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))`.

Establish `hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ)`. Introduce `τ`. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Simplify using `only [gram, hermC, col, Matrix.of_apply, mat]`. Use `fun_prop`.

Establish `hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i` using `fun τ i => by`. Unfold `dmin lminor`. Conclude with `((hgram τ).matrix_submatrix _ _).matrix_det`. Use `show IsOpen (GG X.Ψ X.Gm X.p0)`. Simplify using `only [GG, Set.setOf_forall, Set.setOf_and]`.

Use `isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations. Conclude with `isOpen_ne_fun (hmat τ).matrix_det continuous_const`. Conclude with `isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))`. Establish `hev : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X x z ∈ X.dom ∧ w j0 (cpt X x z) ≠ 0`. Establish `hmem : X.dom ∩ {y | w j0 y ≠ 0} ∈ 𝓝 x`.

Establish `hc : ContinuousAt (w j0) x` using `((hw j0).1.differentiableAt (hopen.mem_nhds hx)).continuousAt`. Conclude with `Filter.inter_mem (hopen.mem_nhds hx) (hc.eventually_ne hx0)`. Establish `hc0 : ContinuousAt (cpt X x) 0` using `(PoinPf.diff_cpt X x).continuous.continuousAt`. Rewrite `hmem` using `[← PoinPf.cpt_zero X x]`. Conclude with `hc0.preimage_mem_nhds hmem`.

Use `GlobalTheory.JacobianIndependence.eq_zero_of_det_fderiv_ne_zero (nd X) (fun k z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) (fun k => ?_) hdet p ?_` and prove the remaining obligations. Use `filter_upwards [hev] with z hz`. Establish `hd : ∀ m, DifferentiableAt ℂ (fun z => w m (cpt X x z)) z` using `fun m => ((hw m).1.differentiableAt (hopen.mem_nhds hz.1)).comp z ((PoinPf.diff_cpt X x) z)`. Establish `hi : DifferentiableAt ℂ (fun z => (w j0 (cpt X x z))⁻¹) z` using `(differentiableAt_inv (𝕜 := ℂ) hz.2).comp z (hd j0)`. Establish `hq` using `(hd (jj k)).mul hi`.

Establish `he : (fun z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) = fun z => w (jj k) (cpt X x z) * (w j0 (cpt X x z))⁻¹`. Use function extensionality and compare the values at `y`. Conclude with `div_eq_mul_inv _ _`. Use `show DifferentiableAt ℂ (fun z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) z`. Rewrite using `[he]`.

Conclude with `hq`. Use `filter_upwards [hev] with z hz`. Conclude with `hp _ hz.1 hz.2`.
-/
theorem ratiosFree_of_proper (X : Data E r) (L eW : Wt X.Ψ r) {N : ℕ} (a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ)
    (et : Frame X.Ψ r → ℂ) (ha : 0 < a) (hw : ∀ k, X.IsSec L (w k)) (hw0 : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0)
    (het : X.IsSec eW et) (het0 : ∃ x ∈ X.dom, et x ≠ 0) (hdom : IsStrictDom X (a • L - eW))
    (hpr : ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) : RatiosFree X w := by
  have hpos : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (a • L - eW)) x0 z ξ := fun x0 _ z hz ξ hξ =>
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.curvature_statement_holds r X (a • L - eW) x0 z hz).2 hdom ξ hξ
  obtain ⟨x, hx, j0, jj, hx0, hdet⟩ :=
    GlobalTheory.ProperImmersionPoint.main E r X L eW N a w et ha hw hw0 het het0 hpos hpr
  refine ⟨j0, jj, ⟨x, hx, hx0⟩, fun p hp => ?_⟩
  have hopen : IsOpen X.dom := by
    have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
      continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
    have hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
      intro τ
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, Matrix.of_apply, mat]
      fun_prop
    have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := fun τ i => by
      unfold dmin lminor
      exact ((hgram τ).matrix_submatrix _ _).matrix_det
    show IsOpen (GG X.Ψ X.Gm X.p0)
    simp only [GG, Set.setOf_forall, Set.setOf_and]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
    · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
  have hev : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X x z ∈ X.dom ∧ w j0 (cpt X x z) ≠ 0 := by
    have hmem : X.dom ∩ {y | w j0 y ≠ 0} ∈ 𝓝 x := by
      have hc : ContinuousAt (w j0) x := ((hw j0).1.differentiableAt (hopen.mem_nhds hx)).continuousAt
      exact Filter.inter_mem (hopen.mem_nhds hx) (hc.eventually_ne hx0)
    have hc0 : ContinuousAt (cpt X x) 0 := (PoinPf.diff_cpt X x).continuous.continuousAt
    rw [← PoinPf.cpt_zero X x] at hmem
    exact hc0.preimage_mem_nhds hmem
  refine GlobalTheory.JacobianIndependence.eq_zero_of_det_fderiv_ne_zero (nd X)
    (fun k z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) (fun k => ?_) hdet p ?_
  · filter_upwards [hev] with z hz
    have hd : ∀ m, DifferentiableAt ℂ (fun z => w m (cpt X x z)) z := fun m =>
      ((hw m).1.differentiableAt (hopen.mem_nhds hz.1)).comp z ((PoinPf.diff_cpt X x) z)
    have hi : DifferentiableAt ℂ (fun z => (w j0 (cpt X x z))⁻¹) z :=
      (differentiableAt_inv (𝕜 := ℂ) hz.2).comp z (hd j0)
    have hq := (hd (jj k)).mul hi
    have he : (fun z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) =
        fun z => w (jj k) (cpt X x z) * (w j0 (cpt X x z))⁻¹ := by
      funext y
      exact div_eq_mul_inv _ _
    show DifferentiableAt ℂ (fun z => w (jj k) (cpt X x z) / w j0 (cpt X x z)) z
    rw [he]
    exact hq
  · filter_upwards [hev] with z hz
    exact hp _ hz.1 hz.2

/- English proof (translation)
Take `⟨C, hC, hCd, hCx⟩` from `GlobalTheory.DefiniteFrames.exists_compact_of_definite E r X hp`. Take `⟨x0, hx0⟩` from `exists_mem_dom X`. Conclude with `ratiosFree_of_proper X L 0 1 w (fun _ => 1) one_pos hw hw0 (isSec_one X) ⟨x0, hx0, one_ne_zero⟩ (by simpa using hdom) (fun δ _ => ⟨C, hC, hCd, fun x hx _ => hCx x hx⟩)`.
-/
theorem ratiosFree_of_definite (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (hw : ∀ k, X.IsSec L (w k)) (hw0 : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (hdom : IsStrictDom X L)
    (hp : X.p0 = 0 ∨ r ≤ X.p0) : RatiosFree X w := by
  obtain ⟨C, hC, hCd, hCx⟩ := GlobalTheory.DefiniteFrames.exists_compact_of_definite E r X hp
  obtain ⟨x0, hx0⟩ := exists_mem_dom X
  exact ratiosFree_of_proper X L 0 1 w (fun _ => 1) one_pos hw hw0 (isSec_one X) ⟨x0, hx0, one_ne_zero⟩
    (by simpa using hdom) (fun δ _ => ⟨C, hC, hCd, fun x hx _ => hCx x hx⟩)

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.BigRec

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

/- English proof (translation)
Unfold `rdU`. Conclude with `dif_pos hx`.
-/
theorem rdU_of_mem (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x} (hx : x ∈ (U.X k).dom) :
    rdU U f k x = toC (evR Xo c f (U.un k ⟨x, hx⟩)) := by
  unfold rdU
  exact dif_pos hx

def rdHom (U : Unf Xo c σ r) (k : U.Comp) {x} (hx : x ∈ (U.X k).dom)
    (hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k ⟨x, hx⟩)) :
    Rul Xo c →+* ℂ where
  toFun f := toC (evR Xo c f (U.un k ⟨x, hx⟩))
  map_one' := evalAt_one (S := CAt σ) _ _ (U.un k ⟨x, hx⟩) hT
  map_mul' f g := evalAt_mul _ _ f g (U.un k ⟨x, hx⟩)
  map_zero' := evalAt_zero _ _ (U.un k ⟨x, hx⟩)
  map_add' f g := evalAt_add _ _ f g (U.un k ⟨x, hx⟩)

/- English proof (translation)
Establish `hf : ∀ f, rdU U f k x = rdHom U k hx hT f` using `fun f => rdU_of_mem U f k hx`. Simplify using `only [hf]`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]`. Use `congr 1`. Use extensionality with `a`.

Use `show toC (evR Xo c (algebraMap _ _ a) _) = σ a`. Unfold `evR toC evalAt`. Rewrite using `[dif_pos (by exact hT)]`. Use `erw [AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem rdU_aeval (U : Unf Xo c σ r) (k : U.Comp) {x} (hx : x ∈ (U.X k).dom)
    (hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k ⟨x, hx⟩))
    {N : ℕ} (w : Fin N → Rul Xo c) (P : MvPolynomial (Fin N) c.F) :
    rdU U (MvPolynomial.aeval w P) k x = MvPolynomial.eval₂ σ (fun i => rdU U (w i) k x) P := by
  have hf : ∀ f, rdU U f k x = rdHom U k hx hT f := fun f => rdU_of_mem U f k hx
  simp only [hf]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  ext a
  show toC (evR Xo c (algebraMap _ _ a) _) = σ a
  unfold evR toC evalAt
  rw [dif_pos (by exact hT)]
  erw [AlgHom.commutes]
  rfl

/- English proof (translation)
Introduce `x hx`. Use `letI : Field (CAt σ) := inferInstanceAs (Field ℂ)`. Use `haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)`. Take `⟨i, hi⟩` from `hN (CAt σ) (U.un k ⟨x, hx⟩)`. Conclude with `⟨i, by rw [rdU_of_mem U _ k hx]; exact hi⟩`.
-/
theorem exists_rdU_ne_zero (U : Unf Xo c σ r) (k : U.Comp) {N : ℕ} {w : Fin N → Rul Xo c}
    (hN : NoCommonZero Xo c w) : ∀ x ∈ (U.X k).dom, ∃ i, rdU U (w i) k x ≠ 0 := by
  intro x hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨i, hi⟩ := hN (CAt σ) (U.un k ⟨x, hx⟩)
  exact ⟨i, by rw [rdU_of_mem U _ k hx]; exact hi⟩

end Read

section Record

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
include hj in
/- English proof (translation)
Establish `hU` using `h.toLawsCore.unf j hj σ hσ`. Unfold `IsUnf at hU`. Establish `hm : F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n` using `(Submodule.mem_inf.mp ((esec_mem_C h hj).mp F.2)).1`. Conclude with `hU.2.2.2.2.1 (wtA u) u.n (dom_wtA u) F.1 hm k`.
-/
theorem isSec_rd {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j σ).Comp) :
    ((T.U j σ).X k).IsSec (laU (T.U j σ) (wtA u) u.n k) (rdU (T.U j σ) F.1 k) := by
  have hU := h.toLawsCore.unf j hj σ hσ
  unfold IsUnf at hU
  have hm : F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := (Submodule.mem_inf.mp ((esec_mem_C h hj).mp F.2)).1
  exact hU.2.2.2.2.1 (wtA u) u.n (dom_wtA u) F.1 hm k

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `h0`. Establish `hsp` using `GlobalTheory.Reg.compSplit_record D T h j hj hG`. Unfold `CompSplitSt at hsp`. Establish `hinj` using `GlobalTheory.Reg.genValInj_record D T h j hj hG`. Unfold `GenValInjSt at hinj`.

Establish `hT : GenFromTest (T.Q.Xo j) T.Q.c hG` using `(GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c).2 hG`. Take `⟨g', hg'Z, hg'o⟩` from `hsp Z u' g`. Establish `hev : ∀ Z', evC hG Z' ((esecMul h hj F g' : (recB h.toLawsCore).Cusp j (wadd u u')) : T.R j) = evC hG Z' (F : T.R j) * evC hG Z' (g' : T.R j)`. Introduce `Z'`. Establish `h1` using `esec_evC_aeval h hj hG hT Z' ![(F : T.R j), (g' : T.R j)] (MvPolynomial.X 0 * MvPolynomial.X 1)`.

Simplify using `only [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h1`. Rewrite using `[esecMul_coe]`. Conclude with `h1`. Establish `hP0 : esecMul h hj F g' = 0` using `hinj _ _ fun Z' => by`. Rewrite using `[hev]`.

Distinguish the cases in `hZ : Z' = Z`. Substitute `hZ` using the available equality. Rewrite using `[h0, zero_mul]`. Rewrite using `[hg'o Z' hZ, mul_zero]`. Establish `hinc : (recPlus h j hj).inc u F * (recPlus h j hj).inc u' g' = 0` using `by show (recPJ h j hj).inc u F * (recPJ h j hj).inc u' g' = 0`.

Rewrite using `[← esec_inc_mul h hj F g', hP0, map_zero]`. Establish `hg0` using `hF u' g' hinc`. Establish `hz : evC hG Z (0 : T.R j) = 0`. Simplify using `using esec_evC_aeval h hj hG hT Z ![] (0 : MvPolynomial (Fin 0) T.Q.c.F)`. Rewrite `hg'Z` using `[hg0]`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[← hg'Z]`. Simplify using `using hz`.
-/
theorem evC_ne_zero_of_nonZeroComp (hG : GenFrEx (T.Q.Xo j) T.Q.c) {u u' : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F)
    (Z : Comp (T.Q.Xo j) T.Q.c) (g : (recB h.toLawsCore).Cusp j u') (hg : evC hG Z g.1 ≠ 0) :
    evC hG Z F.1 ≠ 0 := by
  intro h0
  have hsp := GlobalTheory.Reg.compSplit_record D T h j hj hG
  unfold CompSplitSt at hsp
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  unfold GenValInjSt at hinj
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c).2 hG
  obtain ⟨g', hg'Z, hg'o⟩ := hsp Z u' g
  have hev : ∀ Z', evC hG Z' ((esecMul h hj F g' : (recB h.toLawsCore).Cusp j (wadd u u')) : T.R j) =
      evC hG Z' (F : T.R j) * evC hG Z' (g' : T.R j) := by
    intro Z'
    have h1 := esec_evC_aeval h hj hG hT Z' ![(F : T.R j), (g' : T.R j)]
      (MvPolynomial.X 0 * MvPolynomial.X 1)
    simp only [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    rw [esecMul_coe]
    exact h1
  have hP0 : esecMul h hj F g' = 0 := hinj _ _ fun Z' => by
    rw [hev]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg'o Z' hZ, mul_zero]
  have hinc : (recPlus h j hj).inc u F * (recPlus h j hj).inc u' g' = 0 := by
    show (recPJ h j hj).inc u F * (recPJ h j hj).inc u' g' = 0
    rw [← esec_inc_mul h hj F g', hP0, map_zero]
  have hg0 := hF u' g' hinc
  have hz : evC hG Z (0 : T.R j) = 0 := by
    simpa using esec_evC_aeval h hj hG hT Z ![] (0 : MvPolynomial (Fin 0) T.Q.c.F)
  rw [hg0] at hg'Z
  apply hg
  rw [← hg'Z]
  simpa using hz

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
include hj in

/- English proof (translation)
Establish `hP : T.Q.PinDat` using `h.toLawsCore.pins.2.2.2`. Establish `htr` using `(GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q hP j hj).2`. Establish `hΩ0 : Algebra.trdeg T.Q.c.F (Om Z) = (WeightFamilies.dimY D j : Cardinal)`. Unfold `FnTrdeg at htr`. Conclude with `htr Z`.

Take `⟨j0, jj, ⟨x0, hx0, hne⟩, hind⟩` from `hfree`. Establish `hT : GenFromTest (T.Q.Xo j) T.Q.c hG` using `(GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c).2 hG`. Establish `hv0 : evC hG Z (w j0).1 ≠ 0` using `fun h0 => hne ((hk wL (w j0)).mp h0 x0 hx0)`. Use `⟨j0, hv0, ?_⟩` and prove the remaining obligations. Establish `hΩ : Algebra.trdeg T.Q.c.F (Om Z) = (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((T.U j σ).X k) : Cardinal)`.

Rewrite using `[hnd]`. Conclude with `hΩ0`. Rewrite using `[← hnd]`. Use `trdeg_ratios σ hΩ (fun m => evC hG Z (w m).1) j0 jj hv0 (fun m x => rdU (T.U j σ) (w m).1 k x) ((T.U j σ).X k).dom ?_ hind` and prove the remaining obligations. Introduce `d P hP' hPv x hx`.

Establish `hmem` using `esec_hom_mem h hj (fun m => ((w m).1 : T.R j)) (fun m => (w m).2) P hP'`. Establish `hF : evC hG Z (MvPolynomial.aeval (fun m => ((w m).1 : T.R j)) P) = 0`. Rewrite using `[esec_evC_aeval h hj hG hT Z]`. Conclude with `hPv`. Establish `h2` using `(hk _ ⟨_, hmem⟩).mp hF x hx`.

Rewrite `h2` using `[rdU_aeval (T.U j σ) k hx (h.toLawsCore.unTest j hj σ hσ k ⟨x, hx⟩)]`. Conclude with `h2`.
-/
theorem trdeg_of_ratiosFree (hG : GenFrEx (T.Q.Xo j) T.Q.c) {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ)
    {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL)
    (Z : Comp (T.Q.Xo j) T.Q.c) (k : (T.U j σ).Comp)
    (hk : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u),
      evC hG Z F.1 = 0 ↔ ∀ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x = 0)
    (hnd : ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((T.U j σ).X k) = WeightFamilies.dimY D j)
    (hfree : RatiosFree ((T.U j σ).X k) fun m => rdU (T.U j σ) (w m).1 k) :
    ∃ k₀, evC hG Z (w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F
      (Set.range fun k => evC hG Z (w k).1 / evC hG Z (w k₀).1)) = WeightFamilies.dimY D j := by
  have hP : T.Q.PinDat := h.toLawsCore.pins.2.2.2
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q hP j hj).2
  have hΩ0 : Algebra.trdeg T.Q.c.F (Om Z) = (WeightFamilies.dimY D j : Cardinal) := by
    unfold FnTrdeg at htr
    exact htr Z
  obtain ⟨j0, jj, ⟨x0, hx0, hne⟩, hind⟩ := hfree
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c).2 hG
  have hv0 : evC hG Z (w j0).1 ≠ 0 := fun h0 => hne ((hk wL (w j0)).mp h0 x0 hx0)
  refine ⟨j0, hv0, ?_⟩
  have hΩ : Algebra.trdeg T.Q.c.F (Om Z) = (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((T.U j σ).X k) : Cardinal) := by
    rw [hnd]
    exact hΩ0
  rw [← hnd]
  refine trdeg_ratios σ hΩ (fun m => evC hG Z (w m).1) j0 jj hv0 (fun m x => rdU (T.U j σ) (w m).1 k x)
    ((T.U j σ).X k).dom ?_ hind
  intro d P hP' hPv x hx
  have hmem := esec_hom_mem h hj (fun m => ((w m).1 : T.R j)) (fun m => (w m).2) P hP'
  have hF : evC hG Z (MvPolynomial.aeval (fun m => ((w m).1 : T.R j)) P) = 0 := by
    rw [esec_evC_aeval h hj hG hT Z]
    exact hPv
  have h2 := (hk _ ⟨_, hmem⟩).mp hF x hx
  rw [rdU_aeval (T.U j σ) k hx (h.toLawsCore.unTest j hj σ hσ k ⟨x, hx⟩)] at h2
  exact h2

end Record

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hrun hc hc2 Z`. Distinguish the cases in `hjm : j < D.R.m`. Take `⟨hiet, hnz, σ, hσ, hph⟩` from `hrun hjm`. Take `⟨k, hk⟩` from `(GlobalTheory.CompModel.comp_read_on_model D T h j hj hG σ hσ).1 Z`. Take `⟨hnd, -, hdomE, -⟩` from `GlobalTheory.RunWts.weights_of_run D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS σ hσ k`.

Use `trdeg_of_ratiosFree h hj hG hσ G.w Z k hk hnd ?_` and prove the remaining obligations. Take `⟨ph, -, hphla, hI2⟩` from `hph k`. Take `⟨x1, hx1⟩` from `exists_mem_dom ((T.U j σ).X k)`. Take `⟨i1, hi1⟩` from `exists_rdU_ne_zero (T.U j σ) k hN x1 hx1`. Establish `hg : evC hG Z (G.w i1).1 ≠ 0` using `fun h0' => hi1 ((hk _ _).mp h0' x1 hx1)`.

Establish `het : evC hG Z G.et.1 ≠ 0` using `evC_ne_zero_of_nonZeroComp h hj hG G.et hnz Z (G.w i1) hg`. Establish `het0 : ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) G.et.1 k x ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `het ((hk _ _).mpr hcon)`.

Establish `hr : 0 < g0 D`. Establish `hr0 : 0 < D.R.r`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Use `show 0 < D.R.k + D.R.m - 1`.

Use linear arithmetic over natural numbers and integers. Unfold `g0`. Check the signs of the components of the expression. Establish `hac : ((G.iet * g0 D : ℕ) : ℝ) * c < (G.iet : ℝ)`. Establish `hi : (0 : ℝ) < G.iet` using `by exact_mod_cast hiet`.

Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hc2 hi.le]`. Conclude with `ratiosFree_of_proper _ _ _ (G.iet * g0 D) (fun m => rdU (T.U j σ) (G.w m).1 k) (rdU (T.U j σ) G.et.1 k) (Nat.mul_pos hiet hr) (fun m => isSec_rd h hj hσ (G.w m) k) (exists_rdU_ne_zero _ k hN) (isSec_rd h hj hσ G.et k) het0 (hdomE G.iet hiet) (GlobalTheory.ProperFromMinimum.exists …`. Establish `hjm' : j = D.R.m`. Unfold `InR at hj`.

Use linear arithmetic over natural numbers and integers. Establish `hσ` using `T.good_σ₀`. Take `⟨k, hk⟩` from `(GlobalTheory.CompModel.comp_read_on_model D T h j hj hG T.σ₀ hσ).1 Z`. Take `⟨hnd, hdomL, -, hdef⟩` from `GlobalTheory.RunWts.weights_of_run D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS T.σ₀ hσ k`. Use `trdeg_of_ratiosFree h hj hG hσ G.w Z k hk hnd ?_` and prove the remaining obligations.

Conclude with `ratiosFree_of_definite _ _ (fun m => rdU (T.U j T.σ₀) (G.w m).1 k) (fun m => isSec_rd h hj hσ (G.w m) k) (exists_rdU_ne_zero _ k hN) hdomL (hdef hjm')`.
-/
theorem trdeg_ratios_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z (G.w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z (G.w k).1 / evC hG Z (G.w k₀).1)) = WeightFamilies.dimY D j := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hrun hc hc2 Z
  by_cases hjm : j < D.R.m
  · obtain ⟨hiet, hnz, σ, hσ, hph⟩ := hrun hjm
    obtain ⟨k, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG σ hσ).1 Z
    obtain ⟨hnd, -, hdomE, -⟩ :=
      GlobalTheory.RunWts.weights_of_run D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS σ hσ k
    refine trdeg_of_ratiosFree h hj hG hσ G.w Z k hk hnd ?_
    obtain ⟨ph, -, hphla, hI2⟩ := hph k
    obtain ⟨x1, hx1⟩ := exists_mem_dom ((T.U j σ).X k)
    obtain ⟨i1, hi1⟩ := exists_rdU_ne_zero (T.U j σ) k hN x1 hx1
    have hg : evC hG Z (G.w i1).1 ≠ 0 := fun h0' => hi1 ((hk _ _).mp h0' x1 hx1)
    have het : evC hG Z G.et.1 ≠ 0 := evC_ne_zero_of_nonZeroComp h hj hG G.et hnz Z (G.w i1) hg
    have het0 : ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) G.et.1 k x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact het ((hk _ _).mpr hcon)
    have hr : 0 < g0 D := by
      have hr0 : 0 < D.R.r := by
        have h1 := D.R.two_le_m
        have h2 := D.R.m_add_three_le_k
        show 0 < D.R.k + D.R.m - 1
        omega
      unfold g0
      positivity
    have hac : ((G.iet * g0 D : ℕ) : ℝ) * c < (G.iet : ℝ) := by
      have hi : (0 : ℝ) < G.iet := by exact_mod_cast hiet
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hc2 hi.le]
    exact ratiosFree_of_proper _ _ _ (G.iet * g0 D) (fun m => rdU (T.U j σ) (G.w m).1 k) (rdU (T.U j σ) G.et.1 k)
      (Nat.mul_pos hiet hr) (fun m => isSec_rd h hj hσ (G.w m) k) (exists_rdU_ne_zero _ k hN)
      (isSec_rd h hj hσ G.et k) het0 (hdomE G.iet hiet)
      (GlobalTheory.ProperFromMinimum.exists_compact _ _ _ _ _ _ _ _ _ _ _ ph hphla hI2 hac)
  · have hjm' : j = D.R.m := by
      unfold InR at hj
      omega
    have hσ := T.good_σ₀
    obtain ⟨k, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG T.σ₀ hσ).1 Z
    obtain ⟨hnd, hdomL, -, hdef⟩ :=
      GlobalTheory.RunWts.weights_of_run D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS T.σ₀ hσ k
    refine trdeg_of_ratiosFree h hj hG hσ G.w Z k hk hnd ?_
    exact ratiosFree_of_definite _ _ (fun m => rdU (T.U j T.σ₀) (G.w m).1 k)
      (fun m => isSec_rd h hj hσ (G.w m) k) (exists_rdU_ne_zero _ k hN) hdomL (hdef hjm')

end GlobalTheory.BigTrdeg
