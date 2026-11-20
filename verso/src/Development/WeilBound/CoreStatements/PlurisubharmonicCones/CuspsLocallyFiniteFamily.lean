import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntriesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteSat
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace LevelTowerAlt.LocFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

noncomputable def rg (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => (R.ip (R.P (e k)) (R.P (e l))).re

/- English proof (translation)
Use `show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x`. Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]`.
-/
theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

/- English proof (translation)
Use extensionality with `k l`. Simplify using `only [rg, transpose_apply, of_apply]`. Rewrite using `[← conj_ip R (R.P (e l)) (R.P (e k))]`. Simplify using the standard rewrite rules.
-/
theorem rg_symm (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : (rg R e)ᵀ = rg R e := by
  ext k l
  simp only [rg, transpose_apply, of_apply]
  rw [← conj_ip R (R.P (e l)) (R.P (e k))]
  simp

/- English proof (translation)
Establish `: R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) = ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ)`. Unfold `RiemLat.ip`. Rewrite using `[star_sum, mulVec_sum, dotProduct_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[sum_dotProduct]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Rewrite using `[show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem ip_sum (R : RiemLat E g Λ) {N : ℕ} (u : Fin N → Fin g → ℂ) (x y : Fin N → ℝ) :
    (R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l)).re = ∑ k, ∑ l, x k * (R.ip (u k) (u l)).re * y l := by
  have : R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) =
      ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ) := by
    unfold RiemLat.ip
    rw [star_sum, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]
    ring
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

/- English proof (translation)
Establish `h1 : x ⬝ᵥ rg R e *ᵥ x = (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re`. Rewrite using `[ip_sum]`. Simplify using `only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]`. Rewrite using `[h1]`. Use `R.pos _ fun h0 => hx ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Take `⟨w, hw⟩` from `R.unimod.2 (e.coord k)`. Establish `h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0)`. Introduce `l`. Establish `ha` using `R.alt (e l + w)`.

Simplify using `only [map_add, LinearMap.add_apply, R.alt] at ha`. Establish `hb : R.form w (e l) = if l = k then 1 else 0`. Rewrite using `[hw]`. Simplify using `[Finsupp.single_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ)`. Rewrite using `[sum_dotProduct, Complex.im_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]`. Rewrite `h3` using `[h0]`.

Simplify using `only [h2] at h3`. Simplify using `using h3`.
-/
theorem rg_pos (R : RiemLat E g Λ) {N : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ rg R e *ᵥ x := by
  have h1 : x ⬝ᵥ rg R e *ᵥ x =
      (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re := by
    rw [ip_sum]
    simp only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]
  rw [h1]
  refine R.pos _ fun h0 => hx ?_
  funext k
  obtain ⟨w, hw⟩ := R.unimod.2 (e.coord k)
  have h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0) := by
    intro l
    have ha := R.alt (e l + w)
    simp only [map_add, LinearMap.add_apply, R.alt] at ha
    have hb : R.form w (e l) = if l = k then 1 else 0 := by
      rw [hw]; simp [Finsupp.single_apply]
    linarith
  have h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ) := by
    rw [sum_dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]
  rw [h0] at h3
  simp only [h2] at h3
  simpa using h3

/- English proof (translation)
Establish `h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k)`. Introduce `i`. Use `conv_lhs => rw [← e.sum_repr (v i)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]`. Use extensionality with `i j`. Establish `: rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re * ((e.repr (v j) l : ℤ) : ℝ)`. Rewrite using `[← ip_sum, ← h, ← h]`. Both sides reduce to the same expression.

Rewrite using `[this, Finset.sum_comm]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]`.
-/
theorem rg_coords (R : RiemLat E g Λ) {N m : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) :
    rg R v = (coords e v).map (Int.castRingHom ℝ) * rg R e * ((coords e v).map (Int.castRingHom ℝ))ᵀ := by
  have h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k) := by
    intro i
    conv_lhs => rw [← e.sum_repr (v i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]
  ext i j
  have : rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re *
      ((e.repr (v j) l : ℤ) : ℝ) := by
    rw [← ip_sum, ← h, ← h]
    rfl
  rw [this, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]

end LevelTowerAlt.LocFin

open LevelTowerAlt.LocFin in
/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀`. Use `haveI := (R t₀).free`. Use `haveI := (R t₀).fin`. Set `e` to `Module.finBasis ℤ Λ`. Establish `hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U`.

Introduce `i j`. Take `⟨h1, h2⟩` from `(GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j`. Establish `e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I`. Use function extensionality and compare the values at `t`. Conclude with `(Complex.re_add_im _).symm`.

Rewrite using `[e]`. Conclude with `(Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)`. Establish `hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U`. Introduce `x y`. Unfold `RiemLat.ip`.

Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply]`. Use `continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_` and prove the remaining obligations. Use `continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_` and prove the remaining obligations. Conclude with `(continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))`. Establish `hS : ContinuousOn (fun t => rg (R t) e) U` using `continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => Complex.continuous_re.comp_continuousOn (hip (e k) (e l))`.

Take `⟨c, hc, hev⟩` from `unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.1 ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)`. Take `⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))` from `⟨_, rfl⟩`. Establish `hD0 : 0 ≤ Dk` using `hDk ▸ Real.rpow_nonneg (abs_nonneg _) _`. Establish `hfin` using `(finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn`.

Establish `hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I` using `fun t ht t' ht' I h => ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩`. Use `⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht => ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩` and prove the remaining obligations. Use `Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap)` using `Subtype.val_injective`. Use `haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj`.

Use `haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)`. Use `haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.finBasis ℤ I`. Establish `hli : LinearIndependent ℤ fun i => (b i : Λ)` using `b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)`. Take `⟨hm, hdet⟩` from `GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b`.

Take `⟨⟨r, v, hv⟩, hN⟩` from `GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1`. Establish `hnz0` using `(hN r v hv).2.1`. Take `⟨hd0, hd1⟩` from `det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e) (rg_symm _ _) hc (hball t ht.2)`. Rewrite `hd1` using `[← rg_coords]`. Establish `hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ`.

Simplify using `using hli.fintype_card_le_finrank`. Use `⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩, fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩` and prove the remaining obligations. Use `congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `using this`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `I.sum_mem fun i _ => zsmul_mem (b i).2 _`. Establish `h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I`. Use `hdet.le.trans ?_` and prove the remaining obligations. Rewrite using `[← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]`.

Establish `h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I)` using `pow_nonneg hD0 _`. Conclude with `pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2`. Establish `h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤ (Dk / c) ^ Module.finrank ℤ I`. Rewrite using `[div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]`. Conclude with `hd1.trans h1`.

Establish `h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ` using `(pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hle)`. Conclude with `(h2.trans h3).trans (Int.le_ceil _)` after adjusting the coercions.
-/
theorem LevelTowerAlt.cusps_locally_finite_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀
  classical
  haveI := (R t₀).free
  haveI := (R t₀).fin
  let e := Module.finBasis ℤ Λ
  have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
    intro i j
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
    have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im _).symm
    rw [e]
    exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
  have hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U := by
    intro x y
    unfold RiemLat.ip
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_
    exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))
  have hS : ContinuousOn (fun t => rg (R t) e) U :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun l =>
      Complex.continuous_re.comp_continuousOn (hip (e k) (e l))
  obtain ⟨c, hc, hev⟩ := unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dk := hDk ▸ Real.rpow_nonneg (abs_nonneg _) _
  have hfin := (finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage
    (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn
  have hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I := fun t ht t' ht' I h =>
    ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩
  refine ⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht =>
    ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩
  refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ I
  have hli : LinearIndependent ℤ fun i => (b i : Λ) :=
    b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨hm, hdet⟩ := GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b
  obtain ⟨⟨r, v, hv⟩, hN⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1
  have hnz0 := (hN r v hv).2.1
  obtain ⟨hd0, hd1⟩ := det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e)
    (rg_symm _ _) hc (hball t ht.2)
  rw [← rg_coords] at hd1
  have hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ := by
    simpa using hli.fintype_card_le_finrank
  refine ⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩,
    fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩
  · have := congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simpa using this
  · rintro ⟨y, rfl⟩
    exact I.sum_mem fun i _ => zsmul_mem (b i).2 _
  · have h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I := by
      refine hdet.le.trans ?_
      rw [← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]
      have h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I) := pow_nonneg hD0 _
      exact pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2
    have h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤
        (Dk / c) ^ Module.finrank ℤ I := by
      rw [div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]
      exact hd1.trans h1
    have h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ :=
      (pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hle)
    exact_mod_cast (h2.trans h3).trans (Int.le_ceil _)
