import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.NormGeneratorLeOfPolynomialAnnihilated

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `H _ _ u p M v y h0 hadd hiso hfin hy hp hM`. Take `⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v)` from `⟨_, rfl⟩`. Rewrite `hfin` using `[← hE]`. Use `haveI : FiniteDimensional ℂ E := hfin`. Establish `hcomm : ∀ s t x, u s (u t x) = u t (u s x)`.

Introduce `s t x`. Establish `h : u s * u t = u t * u s` using `by rw [← hadd, ← hadd, add_comm]`. Conclude with `DFunLike.congr_fun h x`. Establish `h0' : ∀ a, u 0 a = a`. Introduce `a`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Establish `hstab : ∀ s, ∀ x ∈ E, u s x ∈ E`. Introduce `s x hx`. Rewrite `hx`, the goal using `[hE]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨t, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨s + t, by simp [hadd]⟩`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => simpa using Submodule.smul_mem _ c ha`. Establish `hvE : v ∈ E`. Rewrite using `[hE]`. Conclude with `Submodule.subset_span ⟨0, h0' v⟩`.

Establish `hclosed : IsClosed (E : Set H)` using `Submodule.closed_of_finiteDimensional E`. Establish `hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E`. Introduce `w hw d hd`. Establish `ht` using `hasDerivAt_iff_tendsto_slope.1 hd`. Use `hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Rewrite using `[slope_def_module]`. Conclude with `(E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))`. Establish `hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 → HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0`. Introduce `s w d hd`. Set `LR : H →L[ℝ] H` to `(u s).restrictScalars ℝ`.

Establish `h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0` using `LR.hasFDerivAt.comp_hasDerivAt 0 hd`. Establish `h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w)`. Use function extensionality and compare the values at `t`. Conclude with `hcomm s t w`. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Establish `hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0`. Introduce `w hw`. Rewrite `hw` using `[hE]`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Conclude with `⟨u s y, hsh s v y hy⟩`. Consider the case `zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨da, hda⟩` from `ha`. Take `⟨db, hdb⟩` from `hb`. Use `⟨da + db, ?_⟩` and prove the remaining obligations. Use `hda.add hdb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Consider the case `smul c a _ ha`. Take `⟨da, hda⟩` from `ha`. Use `⟨c • da, ?_⟩` and prove the remaining obligations. Use `hda.const_smul c using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Establish `hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0`. Introduce `w`. Take `⟨d, hd⟩` from `hder w w.2`.

Rewrite using `[hd.deriv]`. Conclude with `hd`. Set `D : Module.End ℂ E` to `{ toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩ map_add' := by`. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `(hd (a + b)).unique ?_` and prove the remaining obligations. Use `(hd a).add (hd b) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Use the proof step `map_smul' := by`. Introduce `c a`. Apply `Subtype.ext` to reduce the goal to its premises. Use `(hd (c • a)).unique ?_` and prove the remaining obligations. Use `(hd a).const_smul c using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Use `rfl }`. Set `u' : ℝ → Module.End ℂ E` to `fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)`. Establish `hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H)` using `fun t x => rfl`.

Establish `hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0` using `fun x => rfl`. Establish `haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H)`. Introduce `t q`. Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a`.

Introduce `x`. Simplify using `[aeval_C]`. Consider the case `add f g hf hg`. Introduce `x`. Simplify using `[hf, hg]`.

Consider the case `monomial n a ih`. Introduce `x`. Establish `h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X` using `by ring`. Rewrite using `[h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']`. Establish `hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x)`.

Introduce `s t q`. Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a`. Introduce `x`. Simplify using `[aeval_C]`.

Consider the case `add f g hf hg`. Introduce `x`. Simplify using `[hf, hg]`. Consider the case `monomial n a ih`. Introduce `x`.

Establish `h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X` using `by ring`. Rewrite using `[h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]`. Establish `hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0`. Introduce `t x hx`. Rewrite `hx` using `[hE]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Use `show aeval (u t) (p t) (u s v) = 0`. Rewrite using `[hcq, hp, map_zero]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`. Establish `hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0`. Introduce `x`.

Rewrite using `[hasDerivAt_iff_tendsto_slope]`. Establish `h` using `hasDerivAt_iff_tendsto_slope.1 (hd x)`. Rewrite using `[tendsto_subtype_rng]`. Use `h.congr fun t => ?_` and prove the remaining obligations. Simplify using `[slope_def_module, hu']`.

Establish `hbound` using `UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M (by`. Use extensionality with `x`. Simplify using `[hu', h0'])`. Use the proof step `(by`. Introduce `s t`.

Use extensionality with `x`. Simplify using `[hu', hadd])`. Use the proof step `(by`. Introduce `t x`. Conclude with `hiso t x)`.

Use the proof step `hder'`. Use the proof step `(by`. Introduce `t`. Use extensionality with `x`. Rewrite using `[haev]`.

Simplify using `using hkill t x x.2)`. Use `hM ⟨v, hvE⟩`. Establish `hDv : ((D ⟨v, hvE⟩ : E) : H) = y`. Rewrite using `[hD]`. Conclude with `hy.deriv`.

Establish `hn : ‖D ⟨v, hvE⟩‖ = ‖y‖`. Rewrite using `[← hDv]`. Both sides reduce to the same expression. Rewrite `hbound` using `[hn]`. Conclude with `hbound`.
-/
theorem UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : ℝ → H →L[ℂ] H) (p : ℝ → ℂ[X]) (M : ℝ) (v y : H), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => u t v)) → HasDerivAt (fun t : ℝ => u t v) y 0 → (∀ t, aeval (u t) (p t) v = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ‖y‖ ≤ M * ‖v‖ := by
  intro H _ _ u p M v y h0 hadd hiso hfin hy hp hM
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v) := ⟨_, rfl⟩
  rw [← hE] at hfin
  haveI : FiniteDimensional ℂ E := hfin
  have hcomm : ∀ s t x, u s (u t x) = u t (u s x) := by
    intro s t x
    have h : u s * u t = u t * u s := by rw [← hadd, ← hadd, add_comm]
    exact DFunLike.congr_fun h x
  have h0' : ∀ a, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hstab : ∀ s, ∀ x ∈ E, u s x ∈ E := by
    intro s x hx
    rw [hE] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨s + t, by simp [hadd]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hvE : v ∈ E := by
    rw [hE]
    exact Submodule.subset_span ⟨0, h0' v⟩
  have hclosed : IsClosed (E : Set H) := Submodule.closed_of_finiteDimensional E
  have hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E := by
    intro w hw d hd
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    refine hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))
  have hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 →
      HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0 := by
    intro s w d hd
    let LR : H →L[ℝ] H := (u s).restrictScalars ℝ
    have h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 hd
    have h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w) := by
      funext t
      exact hcomm s t w
    rw [h2] at h1
    exact h1
  have hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0 := by
    intro w hw
    rw [hE] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨u s y, hsh s v y hy⟩
    | zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨da, hda⟩ := ha
      obtain ⟨db, hdb⟩ := hb
      refine ⟨da + db, ?_⟩
      convert hda.add hdb using 1
      funext t
      simp
    | smul c a _ ha =>
      obtain ⟨da, hda⟩ := ha
      refine ⟨c • da, ?_⟩
      convert hda.const_smul c using 1
      funext t
      simp
  have hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0 := by
    intro w
    obtain ⟨d, hd⟩ := hder w w.2
    rw [hd.deriv]
    exact hd
  let D : Module.End ℂ E :=
    { toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        refine (hd (a + b)).unique ?_
        convert (hd a).add (hd b) using 1
        · funext t
          simp
        · rfl
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine (hd (c • a)).unique ?_
        convert (hd a).const_smul c using 1
        · funext t
          simp
        · rfl }
  let u' : ℝ → Module.End ℂ E := fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)
  have hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H) := fun t x => rfl
  have hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0 := fun x => rfl
  have haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H) := by
    intro t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']
  have hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x) := by
    intro s t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]
  have hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0 := by
    intro t x hx
    rw [hE] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      show aeval (u t) (p t) (u s v) = 0
      rw [hcq, hp, map_zero]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0 := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hasDerivAt_iff_tendsto_slope.1 (hd x)
    rw [tendsto_subtype_rng]
    refine h.congr fun t => ?_
    simp [slope_def_module, hu']
  have hbound := UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M
    (by
      ext x
      simp [hu', h0'])
    (by
      intro s t
      ext x
      simp [hu', hadd])
    (by
      intro t x
      exact hiso t x)
    hder'
    (by
      intro t
      ext x
      rw [haev]
      simpa using hkill t x x.2)
    hM ⟨v, hvE⟩
  have hDv : ((D ⟨v, hvE⟩ : E) : H) = y := by
    rw [hD]
    exact hy.deriv
  have hn : ‖D ⟨v, hvE⟩‖ = ‖y‖ := by
    rw [← hDv]
    rfl
  rw [hn] at hbound
  exact hbound
