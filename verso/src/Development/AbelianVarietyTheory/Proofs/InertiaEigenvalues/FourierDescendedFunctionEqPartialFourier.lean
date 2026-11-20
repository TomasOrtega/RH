import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaarStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `h : ∀ᶠ z in 𝓝 x, ψ x = ψ z` using `by filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz`. Establish `hz' : ‖z - x‖ ≤ 1` using `by simpa [Metric.mem_closedBall, dist_eq_norm] using hz`. Establish `e : z = x + (z - x)` using `by abel`. Rewrite using `[e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]`.

Conclude with `continuousAt_const.congr h`.
-/
theorem continuous_of_isStdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (fun x => ψ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ z in 𝓝 x, ψ x = ψ z := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
    have hz' : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have e : z = x + (z - x) := by abel
    rw [e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]
  exact continuousAt_const.congr h

/- English proof (translation)
The claim follows from `(Isometry.of_dist_eq fun a b => by rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous`.
-/
theorem continuous_star_E [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous

end GlobalTheory.JR.FourDesc

open GlobalTheory.JR.FourDesc in
/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf`. Use `haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use `haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`.

Use `letI := M.mE`. Use `haveI := M.bE`. Use `letI := M.mU`. Use `haveI := M.bU`. Use `haveI := M.haarE`.

Use `haveI := M.haarU`. Use `haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))`. Use `haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩`. Take `⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE` from `⟨_, rfl⟩`.

Use `haveI : SigmaFinite P := by rw [hP]; infer_instance`. Use `haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance`. Take `⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α)` from `⟨_, rfl⟩`. Use `haveI : IsFiniteMeasure ν := by`. Rewrite using `[hν]`.

Conclude with `isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne`. Use `haveI : IsFiniteMeasureOnCompacts (P.prod ν) := inferInstance`. Establish `hψc` using `continuous_of_isStdChar hψ`. Establish `htr : Continuous (fun e : E => Algebra.trace F E e)` using `LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)`. Establish `hfc : Continuous f` using `hf.1.continuous`.

Establish `hαcont : Continuous α` using `hα.continuous`. Establish `hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E), star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w`. Introduce `g v w`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]`. Set `jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E))` to `fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)`.

Establish `hjg : ∀ g y, jg g y = g.1 *ᵥ j y` using `fun g y => rfl`. Establish `hjgI : ∀ g, A.IsIsom x (jg g)` using `fun g y y' => by rw [hjg, hjg, hstar, hx]`. Establish `I` using `GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x`. Establish `hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))` using `(I j hx).1`. Establish `hmapj : Measure.map j μ = P` using `by rw [hP]; exact (I j hx).2 μ hμ`.

Establish `hmapg : ∀ g, Measure.map (jg g) μ = P` using `fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ`. Establish `hjc : Continuous j` using `IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)`. Establish `hjm : Measurable j` using `hjc.measurable`. Establish `hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v)` using `fun g => continuous_const.matrix_mulVec continuous_id`. Establish `hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P`.

Introduce `g`. Establish `e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g)` using `funext fun y => (hjg g y).symm`. Use `conv_lhs => rw [← hmapj]`. Rewrite using `[Measure.map_map (hgc g).measurable hjm, e, hmapg g]`. Establish `hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) → ∫ g, h g ∂ν = ∫ g, h g ∂M.μU`.

Introduce `h hh`. Rewrite using `[hν]`. Conclude with `setIntegral_eq_integral_of_forall_compl_eq_zero hh`. Use function extensionality and compare the values at `y`. Set `G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ` to `fun v g => f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))`.

Establish `hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam))`. Unfold `actU`. Use `Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)` and prove the remaining obligations. Use `fun_prop`. Use `fun_prop`.

Establish `hGc : Continuous (Function.uncurry G)`. Establish `h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y)` using `by fun_prop`. Conclude with `((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul (hψc.comp (htr.comp h1))`. Establish `hGs : HasCompactSupport (Function.uncurry G)`. Use `HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_` and prove the remaining obligations.

Introduce and unpack `⟨v, g⟩ hvg`. Assume the negation of the conclusion as `hne`. Apply `hvg` to reduce the goal to its premises. Establish `h1 : f (actU g (Ax, v, lam)) ≠ 0` using `fun h => hne (by simp [G, h])`. Establish `h2 : α g ≠ 0` using `fun h => hne (by simp [G, h])`.

Use `⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [actU, Prod.mk.injEq, and_true]`. Rewrite using `[Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]`. Establish `hGi : Integrable (Function.uncurry G) (P.prod ν)` using `hGc.integrable_of_hasCompactSupport hGs`. Establish `hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P`.

Establish `e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y')`. Introduce `y'`. Simplify using `only [Et.descFn, hker, G]`. Rewrite using `[← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]`. Simplify using `only [fourB, e]`.

Rewrite using `[← hmapj, integral_map hjm.aemeasurable (by`. Rewrite using `[hmapj]`. Conclude with `(hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]`. Rewrite using `[hL, integral_integral_swap hGi]`. Simplify using `only [Et.descFn]`.

Rewrite using `[← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Establish `e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) * ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ)`. Introduce `v`.

Simplify using `only [G, actU, hstar]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1]`. Rewrite using `[integral_mul_const]`. Use `congr 1`.

Establish `hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) * ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1)))`. Establish `h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1)` using `by fun_prop`. Establish `h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam))` using `by fun_prop`. Conclude with `(hfc.comp h2).mul (hψc.comp (htr.comp h1))`. Establish `key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) * ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) = ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) * ψ (Algebra.trace F E (star c ⬝ᵥ (act …` using `integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)`.

Rewrite `key` using `[hPg g]`. Rewrite using `[key.symm]`. Simplify using `only [fourU]`. Rewrite using `[hP]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.JR.fourB_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  intro F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf
  haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI := M.mE
  haveI := M.bE
  letI := M.mU
  haveI := M.bU
  haveI := M.haarE
  haveI := M.haarU
  haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE := ⟨_, rfl⟩
  haveI : SigmaFinite P := by rw [hP]; infer_instance
  haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne
  haveI : IsFiniteMeasureOnCompacts (P.prod ν) := inferInstance
  have hψc := continuous_of_isStdChar hψ
  have htr : Continuous (fun e : E => Algebra.trace F E e) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)
  have hfc : Continuous f := hf.1.continuous
  have hαcont : Continuous α := hα.continuous
  have hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E),
      star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro g v w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  let jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E)) :=
    fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)
  have hjg : ∀ g y, jg g y = g.1 *ᵥ j y := fun g y => rfl
  have hjgI : ∀ g, A.IsIsom x (jg g) := fun g y y' => by rw [hjg, hjg, hstar, hx]
  have I := GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x
  have hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := (I j hx).1
  have hmapj : Measure.map j μ = P := by rw [hP]; exact (I j hx).2 μ hμ
  have hmapg : ∀ g, Measure.map (jg g) μ = P := fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ
  have hjc : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjm : Measurable j := hjc.measurable
  have hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v) :=
    fun g => continuous_const.matrix_mulVec continuous_id
  have hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P := by
    intro g
    have e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g) := funext fun y => (hjg g y).symm
    conv_lhs => rw [← hmapj]
    rw [Measure.map_map (hgc g).measurable hjm, e, hmapg g]
  have hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) →
      ∫ g, h g ∂ν = ∫ g, h g ∂M.μU := by
    intro h hh
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hh
  funext y
  let G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ := fun v g =>
    f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))
  have hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam)) := by
    unfold actU
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
    · fun_prop
    · fun_prop
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y) := by fun_prop
    exact ((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul
      (hψc.comp (htr.comp h1))
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image
      (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_
    rintro ⟨v, g⟩ hvg
    by_contra hne
    apply hvg
    have h1 : f (actU g (Ax, v, lam)) ≠ 0 := fun h => hne (by simp [G, h])
    have h2 : α g ≠ 0 := fun h => hne (by simp [G, h])
    refine ⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [actU, Prod.mk.injEq, and_true]
    rw [Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  have hGi : Integrable (Function.uncurry G) (P.prod ν) := hGc.integrable_of_hasCompactSupport hGs
  have hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P := by
    have e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y') := by
      intro y'
      simp only [Et.descFn, hker, G]
      rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]
    simp only [fourB, e]
    rw [← hmapj, integral_map hjm.aemeasurable (by
      rw [hmapj]; exact (hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]
  rw [hL, integral_integral_swap hGi]
  simp only [Et.descFn]
  rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]
  congr 1
  funext g
  have e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) *
      ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ) := by
    intro v
    simp only [G, actU, hstar]
    ring
  simp_rw [e1]
  rw [integral_mul_const]
  congr 1
  have hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) := by
    have h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1) := by fun_prop
    have h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam)) := by fun_prop
    exact (hfc.comp h2).mul (hψc.comp (htr.comp h1))
  have key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) =
      ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) (g.1 *ᵥ v) ∂P :=
    integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)
  rw [hPg g] at key
  rw [key.symm]
  simp only [fourU]
  rw [hP]
  rfl
