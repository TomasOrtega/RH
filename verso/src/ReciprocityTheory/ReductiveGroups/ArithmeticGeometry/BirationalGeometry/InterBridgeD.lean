import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

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
theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J := fun h => hx (Or.inl (Or.inl h))

/- English proof (translation)
Introduce `h` and use `hx (Or.inl (Or.inr h))`.
-/
theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))

/- English proof (translation)
Establish `hz0 : R.lift x x ∈ mcPts P` using `R.mem x x (R.mem_U x)`. Set `k0 : K` to `hK.some`. Set `cc : K → ℂ` to `fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1`. Establish `hcc : ∀ k, cc k ≠ 0`. Introduce `k`.

Simplify using `only [cc]`. Use `split_ifs`. Conclude with `inv_ne_zero h0`. Conclude with `one_ne_zero`. Establish `horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x)` using `⟨cc, hcc, rfl⟩`.

Establish `hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹` using `by simp [cc]`. Establish `hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x`. Rewrite using `[segre_smul, hprod]`. Both sides reduce to the same expression. Use `⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩` and prove the remaining obligations.

Use `show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)`. Rewrite using `[map_smul]`. Use function extensionality and compare the values at `i`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩` into its components or cases. Simplify using `[inv_mul_cancel₀ h0]`.

Simplify using `[brQ, div_eq_inv_mul]`.
-/
theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  have hz0 : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  let k0 : K := hK.some
  let cc : K → ℂ := fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1
  have hcc : ∀ k, cc k ≠ 0 := by
    intro k
    simp only [cc]
    split_ifs
    · exact inv_ne_zero h0
    · exact one_ne_zero
  have horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x) := ⟨cc, hcc, rfl⟩
  have hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by simp [cc]
  have hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x := by
    rw [segre_smul, hprod]
    rfl
  refine ⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩
  show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)
  rw [map_smul]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [inv_mul_cancel₀ h0]
  · simp [brQ, div_eq_inv_mul]

/- English proof (translation)
Introduce `x hx x' hx' h`. Establish `hz'` using `(R.mem x' x' (R.mem_U x')).1`. Apply `R.inj x x' hx.1` to reduce the goal to its premises. Apply `sameOrbit_of_segre hz' (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (mul_ne_zero hx.2 (inv_ne_zero hx'.2))` to reduce the goal to its premises. Establish `h' : (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = (Ψ (segre (R.lift x' x')) 0)⁻¹ • segre (R.lift x' x')` using `h`.

Rewrite using `[mul_smul, ← h', smul_smul, mul_inv_cancel₀ hx.2, one_smul]`.
-/
theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' h
  have hz' := (R.mem x' x' (R.mem_U x')).1
  apply R.inj x x' hx.1
  apply sameOrbit_of_segre hz' (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹)
    (mul_ne_zero hx.2 (inv_ne_zero hx'.2))
  have h' : (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) =
      (Ψ (segre (R.lift x' x')) 0)⁻¹ • segre (R.lift x' x') := h
  rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ hx.2, one_smul]

/- English proof (translation)
Establish `hPh : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Use `Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)` and prove the remaining obligations. Introduce `x hx`. Establish `h0` using `projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2`. Establish `hq : brQ R Ψ x = y` using `hx.1`.

Rewrite using `[← hq]`. Conclude with `brW_mem_fibre R Ψ hP.1 hPh h0`. Introduce `x hx x' hx' h`. Conclude with `brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩ ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h`.
-/
theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  refine Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)
  · intro x hx
    have h0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2
    have hq : brQ R Ψ x = y := hx.1
    rw [← hq]
    exact brW_mem_fibre R Ψ hP.1 hPh h0
  · intro x hx x' hx' h
    exact brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩
      ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h

/- English proof (translation)
Take `⟨z, hz, hzw, hΨw⟩` from `hw`. Establish `hzJ : z ∉ mcPts J`. Introduce `hzJ`. Use `hy ⟨z, hz, hzJ, ?_⟩` and prove the remaining obligations. Rewrite using `[hzw]`.

Conclude with `hΨw`. Take `⟨x, hx⟩` from `R.surj z hz hzJ`. Take `⟨cc, hcc, hlift⟩` from `hx`. Establish `hμ : ∏ k, cc k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hcc k`. Establish `hseg : segre (R.lift x x) = (∏ k, cc k) • w`.

Rewrite using `[hlift, segre_smul, hzw]`. Establish `hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y`. Rewrite using `[hseg, map_smul, hΨw]`. Establish `h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k`. Rewrite using `[hΨl]`.

Simplify using the standard rewrite rules. Use `⟨x, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hzJ` to reduce the goal to its premises. Use `mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Rewrite using `[hlift]`. Conclude with `(inv_mul_cancel_left₀ (hcc p.1) (z p)).symm`. Rewrite using `[h0]`. Conclude with `hμ`.

Use function extensionality and compare the values at `i`. Simplify using `only [brQ, hΨl]`. Simplify using `[hμ]`. Use `show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w`. Rewrite using `[h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]`.
-/
theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  have hzJ : z ∉ mcPts J := by
    intro hzJ
    refine hy ⟨z, hz, hzJ, ?_⟩
    rw [hzw]
    exact hΨw
  obtain ⟨x, hx⟩ := R.surj z hz hzJ
  obtain ⟨cc, hcc, hlift⟩ := hx
  have hμ : ∏ k, cc k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hcc k
  have hseg : segre (R.lift x x) = (∏ k, cc k) • w := by
    rw [hlift, segre_smul, hzw]
  have hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨw]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k := by
    rw [hΨl]
    simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzJ
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h
    funext p
    rw [hlift]
    exact (inv_mul_cancel_left₀ (hcc p.1) (z p)).symm
  · rw [h0]
    exact hμ
  · funext i
    simp only [brQ, hΨl]
    simp [hμ]
  · show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w
    rw [h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end ReciprocityTheory.ChartRestriction.G.Geo
