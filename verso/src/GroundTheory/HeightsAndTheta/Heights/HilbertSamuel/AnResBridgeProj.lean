import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

/- English proof (translation)
Introduce `x hx j hj`. Assume the negation of the conclusion as `h`. Conclude with `hx (Or.inr ⟨j, hj, h⟩)`.
-/
theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

/- English proof (translation)
Introduce `h` and use `hx (Or.inl (Or.inl h))`.
-/
theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J :=
  fun h => hx (Or.inl (Or.inl h))

/- English proof (translation)
Introduce `h` and use `hx (Or.inl (Or.inr h))`.
-/
theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 :=
  fun h => hx (Or.inl (Or.inr h))

/- English proof (translation)
Take `⟨k0⟩` from `hK`. Set `c : K → ℂ` to `Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.lift x x)) 0)⁻¹`. Establish `hc : ∀ k, c k ≠ 0`. Introduce `k`. Distinguish the cases in `hk : k = k0`.

Substitute `hk` using the available equality. Simplify using `[c, h0]`. Simplify using `[c, Function.update_of_ne hk]`. Establish `hpc : ∏ k, c k = (Ψ (segre (R.lift x x)) 0)⁻¹`. Simplify using `[c, Finset.prod_update_of_mem (Finset.mem_univ k0)]`.

Use `⟨fun p => c p.1 * R.lift x x p, mcPts_smul hPh c hc (R.mem x x (R.mem_U x)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[segre_smul, hpc]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `[brW, h0]`. Simplify using `only [brW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, brQ]`. Rewrite using `[div_eq_inv_mul]`.
-/
theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.lift x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.lift x x p, mcPts_smul hPh c hc (R.mem x x (R.mem_U x)), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [brW, h0]
    · simp only [brW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, brQ]
      rw [div_eq_inv_mul]

/- English proof (translation)
Introduce `x hx x' hx' hw`. Use `R.inj x x' hx.1 ?_` and prove the remaining obligations. Use `sameOrbit_of_segre (R.mem x' x' (R.mem_U x')).1 (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_` and prove the remaining obligations. Use `congrArg (fun v => Ψ (segre (R.lift x x)) 0 • v) hw` as an intermediate fact. Simplify using `only [brW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this`.

Conclude with `this`.
-/
theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.inj x x' hx.1 ?_
  refine sameOrbit_of_segre (R.mem x' x' (R.mem_U x')).1
    (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.lift x x)) 0 • v) hw
  simp only [brW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)` as an intermediate fact. Rewrite `this` using `[show brQ R Ψ x = y from hx.1]`. Then use the resulting hypothesis.
-/
theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
      ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
  rwa [show brQ R Ψ x = y from hx.1] at this

/- English proof (translation)
Take `⟨z, hz, rfl, hΨz⟩` from `hw`. Establish `hzJ : z ∉ mcPts J` using `fun h => hy ⟨z, hz, h, hΨz⟩`. Take `⟨x, c, hc, hxc⟩` from `R.surj z hz hzJ`. Establish `hseg : segre (R.lift x x) = (∏ k, c k) • segre z` using `by rw [hxc, segre_smul]`. Establish `hpc : ∏ k, c k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`.

Establish `hΨx : Ψ (segre (R.lift x x)) = (∏ k, c k) • Fin.cons 1 y` using `by rw [hseg, map_smul, hΨz]`. Establish `h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, c k` using `by simp [hΨx]`. Use `⟨x, fun h => hzJ ?_, by rw [h0]; exact hpc, ?_, ?_⟩` and prove the remaining obligations. Use `mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Rewrite using `[hxc]`. Clear denominators, using `[hc p.1]` for the nonvanishing conditions. Use function extensionality and compare the values at `i`. Simplify using `only [brQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[brW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]`.
-/
theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hz, h, hΨz⟩
  obtain ⟨x, c, hc, hxc⟩ := R.surj z hz hzJ
  have hseg : segre (R.lift x x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.lift x x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzJ ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hxc]
    field_simp [hc p.1]
  · funext i
    simp only [brQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [brW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
