import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsPshOfTangent
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Sg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos R.herm fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `R.pos (star x) (star_ne_zero.2 hx)`. Rewrite `h1` using `[star_star]`. Use `Complex.pos_iff.2 ⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : star (star x ⬝ᵥ R.Hm *ᵥ x) = star x ⬝ᵥ R.Hm *ᵥ x`.

Rewrite using `[← star_dotProduct_star, star_star, star_mulVec, R.herm.eq, dotProduct_mulVec, dotProduct_comm]`. Conclude with `(Complex.conj_eq_iff_im.1 h2).symm`.
-/
theorem posDef_Hm (R : RiemLat E g Λ) : R.Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos R.herm fun x hx => ?_
  have h1 := R.pos (star x) (star_ne_zero.2 hx)
  rw [star_star] at h1
  refine Complex.pos_iff.2 ⟨h1, ?_⟩
  have h2 : star (star x ⬝ᵥ R.Hm *ᵥ x) = star x ⬝ᵥ R.Hm *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, R.herm.eq, dotProduct_mulVec, dotProduct_comm]
  exact (Complex.conj_eq_iff_im.1 h2).symm

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem mul_entry {l m : Type} (A : Matrix l (Fin g) ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (B : Matrix m (Fin g) ℂ)
    (i : l) (j : m) : (A * H * Bᴴ) i j = A i ⬝ᵥ H *ᵥ star (B j) := by
  rw [Matrix.mul_assoc]
  rfl

def per (R : RiemLat E g Λ) (e : Fin g ⊕ Fin g → Λ) : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ := Matrix.of fun k => R.P (e k)

def frm (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (e : Fin g ⊕ Fin g → Λ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  (2 * Complex.I) • (Int.castRingHom ℂ).mapMatrix (Matrix.of fun k l => f (e k) (e l))

/- English proof (translation)
Use extensionality with `k l`. Establish `hh` using `(Matrix.isHermitian_mul_mul_conjTranspose (per R e) R.herm).apply l k`. Establish `h1 : ((per R e * R.Hm * (per R e)ᴴ) k l).im = R.form (e k) (e l)`. Rewrite using `[mul_entry]`. Conclude with `R.im _ _`.

Rewrite using `[Matrix.sub_apply, Matrix.transpose_apply, ← hh, Complex.star_def, Complex.sub_conj, h1]`. Simplify using `[frm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_eq (R : RiemLat E g Λ) (e : Fin g ⊕ Fin g → Λ) :
    per R e * R.Hm * (per R e)ᴴ - (per R e * R.Hm * (per R e)ᴴ)ᵀ = frm R.form e := by
  ext k l
  have hh := (Matrix.isHermitian_mul_mul_conjTranspose (per R e) R.herm).apply l k
  have h1 : ((per R e * R.Hm * (per R e)ᴴ) k l).im = R.form (e k) (e l) := by
    rw [mul_entry]
    exact R.im _ _
  rw [Matrix.sub_apply, Matrix.transpose_apply, ← hh, Complex.star_def, Complex.sub_conj, h1]
  simp [frm]
  ring

/- English proof (translation)
Rewrite using `[frm, det_smul, ← RingHom.map_det]`. Use `mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)) ?_` and prove the remaining obligations. Rewrite using `[eq_intCast, Int.cast_ne_zero]`. Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h`.

Establish `h1 : f (∑ k, v k • e k) = 0`. Use `e.ext fun l => ?_` and prove the remaining obligations. Use `congrFun h0 l` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, map_sum, LinearMap.sum_apply]`. Establish `h2 : ∑ k, v k • e k = 0` using `hf (by rw [h1, map_zero])`.

Conclude with `hv (funext (Fintype.linearIndependent_iff.1 e.linearIndependent v h2))`.
-/
theorem frm_det {f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ} (hf : Function.Injective f) (e : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :
    (frm f e).det ≠ 0 := by
  rw [frm, det_smul, ← RingHom.map_det]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)) ?_
  rw [eq_intCast, Int.cast_ne_zero]
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  have h1 : f (∑ k, v k • e k) = 0 := by
    refine e.ext fun l => ?_
    have := congrFun h0 l
    simpa [Matrix.vecMul, dotProduct, map_sum, LinearMap.sum_apply] using this
  have h2 : ∑ k, v k • e k = 0 := hf (by rw [h1, map_zero])
  exact hv (funext (Fintype.linearIndependent_iff.1 e.linearIndependent v h2))

end LevelTowerAlt.Sg

open LevelTowerAlt.Sg in
/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ Ψ _ n U R hU hR`. Break down `U.eq_empty_or_nonempty with rfl | ⟨t1, ht1⟩` into its components or cases. Use `⟨fun i j => ⟨contDiffOn_empty, contDiffOn_empty⟩, fun a x => differentiableOn_empty, fun m u _ _ => ?_⟩` and prove the remaining obligations. Conclude with `isPsh_of_tangent (continuousOn_empty _) fun t0 h => absurd h (Set.notMem_empty t0)`. Use `haveI := (R t1).free`.

Use `haveI := (R t1).fin`. Set `e : Module.Basis (Fin g ⊕ Fin g) ℤ Λ` to `(Module.finBasisOfFinrankEq ℤ Λ (n := g + g) (by rw [(R t1).rank, two_mul])).reindex finSumFinEquiv.symm`. Establish `hK : (frm (R t1).form e).det ≠ 0` using `frm_det (R t1).unimod.1 e`. Establish `hper : ∀ v : Fin g ⊕ Fin g → Λ, MS ℂ U fun t => per (R t) v` using `fun v => MS.of_diff hU fun i j => differentiableOn_pi.1 (hR.2 (v i)) j`. Establish `he : ∀ t ∈ U, per (R t) e * (R t).Hm * (per (R t) e)ᴴ - (per (R t) e * (R t).Hm * (per (R t) e)ᴴ)ᵀ = frm (R t1).form e` using `fun t ht => by rw [per_eq, hR.1 t ht t1 ht1]`.

Use `⟨fun i j => ?_, fun a x t0 ht0 => ?_, fun m u hu hli => ?_⟩` and prove the remaining obligations. Establish `h` using `herm_smooth (H := fun t => (R t).Hm) (hper e) hK he i j`. Conclude with `⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩`. Take `⟨V, G, C, hVo, htV, hVU, hG, -, hGC, -⟩` from `local_frame (H := fun t => (R t).Hm) hU (hper e) hK he ht0`. Establish `hM : MS ℂ V fun t => (Matrix.of fun _ : Unit => x) * (G t * C) * per (R t) (fun k => a • e k)` using `((MS.const _).mul (hG.mul (MS.const _))).mul ((hper _).mono hVU)`.

Establish `hD : DifferentiableOn ℂ (fun t => (R t).B a x) V`. Use `differentiableOn_pi.2 fun j => ((hM () j).differentiableOn (by simp)).congr fun t ht => ?_` and prove the remaining obligations. Establish `hrow : ∀ (y : Matrix Unit (Fin g ⊕ Fin g) ℂ) (v : Fin g ⊕ Fin g → Λ), (y * per (R t) v) () = ∑ k, y () k • (R t).P (v k)`. Introduce `y v`. Use function extensionality and compare the values at `b`.

Simplify using `[Matrix.mul_apply, per, Finset.sum_apply]`. Establish `h1 : x = ∑ k, ((Matrix.of fun _ : Unit => x) * (G t * C)) () k • (R t).P (e k)`. Rewrite using `[← hrow, Matrix.mul_assoc, hGC t ht, Matrix.mul_one]`. Both sides reduce to the same expression. Use `congrFun (f := (R t).B a x) ?_ j` and prove the remaining obligations.

Use `Eq.trans ?_ (hrow ((Matrix.of fun _ : Unit => x) * (G t * C)) fun k => a • e k).symm` and prove the remaining obligations. Use `conv_lhs => rw [h1]`. Simplify using `only [map_sum, map_smul, (R t).act]`. Conclude with `(hD.differentiableAt (hVo.mem_nhds htV)).differentiableWithinAt`. Establish `h` using `logdet_psh (H := fun t => (R t).Hm) (u := fun t => Matrix.of fun i => u i t) hU (hper e) hK (fun t _ => posDef_Hm (R t)) he (MS.of_diff hU fun i j => differentiableOn_pi.1 (hu i) j) hli`.

Establish `e1 : (fun t => Real.log ((R t).gram fun i => u i t).det.re) = fun t => Real.log ((Matrix.of fun i => u i t) * (R t).Hm * (Matrix.of fun i => u i t)ᴴ).det.re`. Use function extensionality and compare the values at `t`. Rewrite using `[← Matrix.det_transpose]`. Use `congr 3`. Use extensionality with `a b`.

Rewrite using `[mul_entry]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `h`.
-/
theorem LevelTowerAlt.holomorphic_family_smooth_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ), IsOpen U → IsHolFam U R → (∀ i j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).re) U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).im) U) ∧ (∀ a x, DifferentiableOn ℂ (fun t => (R t).B a x) U) ∧ ∀ (m : ℕ) (u : Fin m → (Fin n → ℂ) → Fin g → ℂ), (∀ i, DifferentiableOn ℂ (u i) U) → (∀ t ∈ U, LinearIndependent ℂ fun i => u i t) → ReciprocityTheory.AnForm.A.IsPsh U fun t => Real.log ((R t).gram fun i => u i t).det.re := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R hU hR
  rcases U.eq_empty_or_nonempty with rfl | ⟨t1, ht1⟩
  · refine ⟨fun i j => ⟨contDiffOn_empty, contDiffOn_empty⟩, fun a x => differentiableOn_empty, fun m u _ _ => ?_⟩
    exact isPsh_of_tangent (continuousOn_empty _) fun t0 h => absurd h (Set.notMem_empty t0)
  haveI := (R t1).free
  haveI := (R t1).fin
  let e : Module.Basis (Fin g ⊕ Fin g) ℤ Λ :=
    (Module.finBasisOfFinrankEq ℤ Λ (n := g + g) (by rw [(R t1).rank, two_mul])).reindex finSumFinEquiv.symm
  have hK : (frm (R t1).form e).det ≠ 0 := frm_det (R t1).unimod.1 e
  have hper : ∀ v : Fin g ⊕ Fin g → Λ, MS ℂ U fun t => per (R t) v := fun v =>
    MS.of_diff hU fun i j => differentiableOn_pi.1 (hR.2 (v i)) j
  have he : ∀ t ∈ U, per (R t) e * (R t).Hm * (per (R t) e)ᴴ - (per (R t) e * (R t).Hm * (per (R t) e)ᴴ)ᵀ =
      frm (R t1).form e := fun t ht => by rw [per_eq, hR.1 t ht t1 ht1]
  refine ⟨fun i j => ?_, fun a x t0 ht0 => ?_, fun m u hu hli => ?_⟩
  · have h := herm_smooth (H := fun t => (R t).Hm) (hper e) hK he i j
    exact ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩
  · obtain ⟨V, G, C, hVo, htV, hVU, hG, -, hGC, -⟩ :=
      local_frame (H := fun t => (R t).Hm) hU (hper e) hK he ht0
    have hM : MS ℂ V fun t => (Matrix.of fun _ : Unit => x) * (G t * C) * per (R t) (fun k => a • e k) :=
      ((MS.const _).mul (hG.mul (MS.const _))).mul ((hper _).mono hVU)
    have hD : DifferentiableOn ℂ (fun t => (R t).B a x) V := by
      refine differentiableOn_pi.2 fun j => ((hM () j).differentiableOn (by simp)).congr fun t ht => ?_
      have hrow : ∀ (y : Matrix Unit (Fin g ⊕ Fin g) ℂ) (v : Fin g ⊕ Fin g → Λ),
          (y * per (R t) v) () = ∑ k, y () k • (R t).P (v k) := by
        intro y v
        funext b
        simp [Matrix.mul_apply, per, Finset.sum_apply]
      have h1 : x = ∑ k, ((Matrix.of fun _ : Unit => x) * (G t * C)) () k • (R t).P (e k) := by
        rw [← hrow, Matrix.mul_assoc, hGC t ht, Matrix.mul_one]
        rfl
      refine congrFun (f := (R t).B a x) ?_ j
      refine Eq.trans ?_ (hrow ((Matrix.of fun _ : Unit => x) * (G t * C)) fun k => a • e k).symm
      conv_lhs => rw [h1]
      simp only [map_sum, map_smul, (R t).act]
    exact (hD.differentiableAt (hVo.mem_nhds htV)).differentiableWithinAt
  · have h := logdet_psh (H := fun t => (R t).Hm) (u := fun t => Matrix.of fun i => u i t) hU (hper e) hK
      (fun t _ => posDef_Hm (R t)) he (MS.of_diff hU fun i j => differentiableOn_pi.1 (hu i) j) hli
    have e1 : (fun t => Real.log ((R t).gram fun i => u i t).det.re) = fun t =>
        Real.log ((Matrix.of fun i => u i t) * (R t).Hm * (Matrix.of fun i => u i t)ᴴ).det.re := by
      funext t
      rw [← Matrix.det_transpose]
      congr 3
      ext a b
      rw [mul_entry]
      rfl
    rw [e1]
    exact h
