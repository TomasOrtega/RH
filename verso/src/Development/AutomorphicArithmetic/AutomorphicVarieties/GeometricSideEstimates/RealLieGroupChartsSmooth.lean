import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianChartScalarInvariance
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `⟨g * infGL E a (show IsUnit (Matrix.of x) from hx).unit, fun f => ?_⟩` and prove the remaining obligations. Conclude with `chart_val f g (show IsUnit (Matrix.of x) from hx).unit`.
-/
private theorem chart_ex (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ y : GA E a, ∀ f : GA E a → ℂ, chart f g x = f y := by
  refine ⟨g * infGL E a (show IsUnit (Matrix.of x) from hx).unit, fun f => ?_⟩
  exact chart_val f g (show IsUnit (Matrix.of x) from hx).unit

/- English proof (translation)
Simplify using `using chart_val u g 1`.
-/
private theorem chart_at_one (u : GA E a → ℂ) (g : GA E a) : chart u g (oneL E a) = u g := by
  simpa using chart_val u g 1

/- English proof (translation)
The claim follows from `isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)`.
-/
private theorem ev_inv : ∀ᶠ x in nhds (oneL E a), x ∈ invSet E a :=
  isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)

/- English proof (translation)
Introduce `g`. Use `(hh.comp (hf g) fun x hx => ?_).congr fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `chart_ex g hx`. Rewrite using `[hy]`. Conclude with `hS y`.

Take `⟨y, hy⟩` from `chart_ex g hx`. Simplify using `only [Function.comp, hy]`.
-/
private theorem comp_mem {h : ℂ → ℂ} {S : Set ℂ} (hh : ContDiffOn ℝ ∞ h S) {f : GA E a → ℂ} (hf : f ∈ Sm E a)
    (hS : ∀ g, f g ∈ S) : (fun g => h (f g)) ∈ Sm E a := by
  intro g
  refine (hh.comp (hf g) fun x hx => ?_).congr fun x hx => ?_
  · obtain ⟨y, hy⟩ := chart_ex g hx
    rw [hy]; exact hS y
  · obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]

/- English proof (translation)
Establish `e : chart (fun g => h (f g)) g =ᶠ[nhds (oneL E a)] h ∘ chart f g` using `by filter_upwards [ev_inv] with x hx`. Take `⟨y, hy⟩` from `chart_ex g hx`. Simplify using `only [Function.comp, hy]`. Rewrite `hd` using `[← chart_at_one f g]`. Establish `h2` using `(hd.hasFDerivAt.restrictScalars ℝ).comp (oneL E a) (differentiableAt_chart hf g).hasFDerivAt`.

Rewrite using `[lieD, lieD, e.fderiv_eq, h2.fderiv]`. Simplify using `[mul_comm]`.
-/
private theorem comp_lie {h : ℂ → ℂ} {f : GA E a → ℂ} (hf : f ∈ Sm E a) (g : GA E a) {d : ℂ}
    (hd : HasDerivAt h d (f g)) (X : Lie E a) : lieD X (fun g => h (f g)) g = d * lieD X f g := by
  have e : chart (fun g => h (f g)) g =ᶠ[nhds (oneL E a)] h ∘ chart f g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]
  rw [← chart_at_one f g] at hd
  have h2 := (hd.hasFDerivAt.restrictScalars ℝ).comp (oneL E a) (differentiableAt_chart hf g).hasFDerivAt
  rw [lieD, lieD, e.fderiv_eq, h2.fderiv]
  simp [mul_comm]

/- English proof (translation)
Introduce `g`. Use `((h g).mul (h' g)).congr fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `chart_ex g hx`. Simplify using `only [hy]`.
-/
private theorem prodSm_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    (fun g => f g * f' g) ∈ Sm E a := by
  intro g
  refine ((h g).mul (h' g)).congr fun x hx => ?_
  obtain ⟨y, hy⟩ := chart_ex g hx
  simp only [hy]

/- English proof (translation)
Establish `e : chart (fun g => f g * f' g) g =ᶠ[nhds (oneL E a)] chart f g * chart f' g` using `by filter_upwards [ev_inv] with x hx`. Take `⟨y, hy⟩` from `chart_ex g hx`. Simplify using `only [Pi.mul_apply, hy]`. Rewrite using `[lieD, lieD, lieD, e.fderiv_eq, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), chart_at_one, chart_at_one]`. Simplify using `[mul_comm]`.
-/
private theorem prod_lie {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) (g : GA E a) (X : Lie E a) :
    lieD X (fun g => f g * f' g) g = f g * lieD X f' g + lieD X f g * f' g := by
  have e : chart (fun g => f g * f' g) g =ᶠ[nhds (oneL E a)] chart f g * chart f' g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Pi.mul_apply, hy]
  rw [lieD, lieD, lieD, e.fderiv_eq, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g),
    chart_at_one, chart_at_one]
  simp [mul_comm]

end

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Establish `hT` using `(UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1`. Establish `hS` using `UpperTheory.hermitian_chart_scalar_invariance E a ha L hL`. Establish `mem : ∀ P ∈ poly E a, mean L P ∈ meanAlg L` using `fun P hP => Algebra.subset_adjoin ⟨P, hP, rfl⟩`. Take `⟨θ, hθ, hθX⟩` from `hS 1 (one_mem _)`.

Establish `hv : ∀ g, θ.1 g = (Th L g : ℝ)` using `fun g => by rw [hθ]; exact (hT g).2`. Establish `hpos : ∀ g, 0 < Th L g` using `fun g => lt_of_lt_of_le one_pos (hT g).1`. Establish `hne : ∀ g, θ.1 g ≠ 0` using `fun g => by`. Rewrite using `[hv]`. Conclude with `(hpos g).ne'` after adjusting the coercions.

Establish `hsl : ∀ g, θ.1 g ∈ Complex.slitPlane` using `fun g => by`. Rewrite using `[hv]`. Conclude with `Complex.ofReal_mem_slitPlane.2 (hpos g)`. Use `⟨fun P hP => ?_, ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, hφX⟩` from `hS P hP`.

Establish `hi : (fun g => (θ.1 g)⁻¹) ∈ Sm E a` using `comp_mem (S := {0}ᶜ) ((contDiffOn_inv ℂ).restrict_scalars ℝ) θ.2 hne`. Use `⟨⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩, ?_, fun X => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `only [mean, hφ, hv, div_eq_mul_inv]`. Take `⟨Q, hQ, eQ⟩` from `hφX X`.

Take `⟨R, hR, eR⟩` from `hθX X`. Establish `e : (lie E a X ⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩).1 = mean L Q - mean L P * mean L R`. Use function extensionality and compare the values at `g`. Establish `e1 : lieD X φ.1 g = gsum L (pg Q) g` using `congrFun eQ g`. Establish `e2 : lieD X θ.1 g = gsum L (pg R) g` using `congrFun eR g`.

Rewrite using `[GlobalTheory.CuspRep.lie_apply]`. Express the relevant statement in the definitionally equal form `lieD X (fun g => φ.1 g * (fun g => (θ.1 g)⁻¹) g) g = _`. Rewrite using `[prod_lie φ.2 hi, comp_lie θ.2 g (hasDerivAt_inv (hne g)), e1, e2]`. Simplify using `only [Pi.sub_apply, Pi.mul_apply, mean, ← hv, hφ]`. Use `hne g` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (mem Q hQ) (mul_mem (mem P hP) (mem R hR))`. Establish `hl : (fun g => Complex.log (θ.1 g)) ∈ Sm E a` using `comp_mem (S := Complex.slitPlane) (fun z hz => ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt) θ.2 hsl`.

Use `⟨⟨_, hl⟩, fun g => ?_, fun X => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.log (θ.1 g) = _`. Rewrite using `[hv, fn, Complex.ofReal_log (hpos g).le]`. Take `⟨R, hR, eR⟩` from `hθX X`. Establish `e : (lie E a X ⟨_, hl⟩).1 = mean L R`.

Use function extensionality and compare the values at `g`. Establish `e2 : lieD X θ.1 g = gsum L (pg R) g` using `congrFun eR g`. Rewrite using `[GlobalTheory.CuspRep.lie_apply]`. Express the relevant statement in the definitionally equal form `lieD X (fun g => Complex.log (θ.1 g)) g = _`. Rewrite using `[comp_lie θ.2 g (Complex.hasDerivAt_log (hsl g)), e2, mean, hv, div_eq_inv_mul]`.

Rewrite using `[e]`. Conclude with `mem R hR`.
-/
theorem UpperTheory.realLieGroup_charts_smooth :
    MeanSm := by
  intro E _ _ _ a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hS := UpperTheory.hermitian_chart_scalar_invariance E a ha L hL
  have mem : ∀ P ∈ poly E a, mean L P ∈ meanAlg L := fun P hP => Algebra.subset_adjoin ⟨P, hP, rfl⟩
  obtain ⟨θ, hθ, hθX⟩ := hS 1 (one_mem _)
  have hv : ∀ g, θ.1 g = (Th L g : ℝ) := fun g => by rw [hθ]; exact (hT g).2
  have hpos : ∀ g, 0 < Th L g := fun g => lt_of_lt_of_le one_pos (hT g).1
  have hne : ∀ g, θ.1 g ≠ 0 := fun g => by
    rw [hv]; exact_mod_cast (hpos g).ne'
  have hsl : ∀ g, θ.1 g ∈ Complex.slitPlane := fun g => by
    rw [hv]; exact Complex.ofReal_mem_slitPlane.2 (hpos g)
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨φ, hφ, hφX⟩ := hS P hP
    have hi : (fun g => (θ.1 g)⁻¹) ∈ Sm E a :=
      comp_mem (S := {0}ᶜ) ((contDiffOn_inv ℂ).restrict_scalars ℝ) θ.2 hne
    refine ⟨⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩, ?_, fun X => ?_⟩
    · funext g
      simp only [mean, hφ, hv, div_eq_mul_inv]
    · obtain ⟨Q, hQ, eQ⟩ := hφX X
      obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩).1 = mean L Q - mean L P * mean L R := by
        funext g
        have e1 : lieD X φ.1 g = gsum L (pg Q) g := congrFun eQ g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => φ.1 g * (fun g => (θ.1 g)⁻¹) g) g = _
        rw [prod_lie φ.2 hi, comp_lie θ.2 g (hasDerivAt_inv (hne g)), e1, e2]
        simp only [Pi.sub_apply, Pi.mul_apply, mean, ← hv, hφ]
        have := hne g
        field_simp
        ring
      rw [e]
      exact sub_mem (mem Q hQ) (mul_mem (mem P hP) (mem R hR))
  · have hl : (fun g => Complex.log (θ.1 g)) ∈ Sm E a :=
      comp_mem (S := Complex.slitPlane)
        (fun z hz => ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt) θ.2 hsl
    refine ⟨⟨_, hl⟩, fun g => ?_, fun X => ?_⟩
    · change Complex.log (θ.1 g) = _
      rw [hv, fn, Complex.ofReal_log (hpos g).le]
    · obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨_, hl⟩).1 = mean L R := by
        funext g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => Complex.log (θ.1 g)) g = _
        rw [comp_lie θ.2 g (Complex.hasDerivAt_log (hsl g)), e2, mean, hv, div_eq_inv_mul]
      rw [e]
      exact mem R hR
