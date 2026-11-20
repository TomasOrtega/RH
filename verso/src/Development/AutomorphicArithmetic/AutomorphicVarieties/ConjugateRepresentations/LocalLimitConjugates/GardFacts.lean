import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConvolutionL2Class
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvGrow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HasDerivAtConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce `g`. Take `⟨C, N, h⟩` from `hφ g`. Take `⟨C', N', h'⟩` from `hψ g`. Use `⟨|C| + |C'|, N + N', fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CuspRep.one_le_height y`.

Establish `h0 : 0 ≤ GlobalTheory.CuspRep.height y` using `zero_le_one.trans h1`. Establish `e1 : C * GlobalTheory.CuspRep.height y ^ N ≤ |C| * GlobalTheory.CuspRep.height y ^ (N + N')` using `mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (pow_nonneg h0 _) (abs_nonneg C)`. Establish `e2 : C' * GlobalTheory.CuspRep.height y ^ N' ≤ |C'| * GlobalTheory.CuspRep.height y ^ (N + N')` using `mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left _ _)) (pow_nonneg h0 _) (abs_nonneg C')`. Rewrite using `[add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add ((h y).trans e1) ((h' y).trans e2))`.
-/
private theorem grow_lin {φ ψ : GA E a → ℂ} (hφ : Grow φ) (hψ : Grow ψ) : Grow (φ + ψ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  obtain ⟨C', N', h'⟩ := hψ g
  refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
  have h1 := GlobalTheory.CuspRep.one_le_height y
  have h0 : 0 ≤ GlobalTheory.CuspRep.height y := zero_le_one.trans h1
  have e1 : C * GlobalTheory.CuspRep.height y ^ N ≤ |C| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (pow_nonneg h0 _) (abs_nonneg C)
  have e2 : C' * GlobalTheory.CuspRep.height y ^ N' ≤ |C'| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left _ _)) (pow_nonneg h0 _) (abs_nonneg C')
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add ((h y).trans e1) ((h' y).trans e2))

/- English proof (translation)
Introduce `g`. Take `⟨C, N, h⟩` from `hφ g`. Use `⟨‖s‖ * C, N, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, norm_smul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (h y) (norm_nonneg s)`.
-/
private theorem grow_smul (s : ℂ) {φ : GA E a → ℂ} (hφ : Grow φ) : Grow (s • φ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  refine ⟨‖s‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg s)

/- English proof (translation)
The claim follows from `isOpen_stab_of_mem_nhds (finRep E a) φ (Filter.mem_of_superset hS h)`.
-/
private theorem lev_of {φ : Sm E a} {S : Set (GL (Fin a) (Af E))} (hS : S ∈ 𝓝 1)
    (h : ∀ k ∈ S, act (.fin k) φ = φ) : HasLev φ :=
  isOpen_stab_of_mem_nhds (finRep E a) φ (Filter.mem_of_superset hS h)

/- English proof (translation)
Use `h.mem_nhds ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finRep E a 1 φ = φ`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
private theorem lev_nhds {φ : Sm E a} (h : HasLev φ) : {k : GL (Fin a) (Af E) | act (.fin k) φ = φ} ∈ 𝓝 1 := by
  refine h.mem_nhds ?_
  change finRep E a 1 φ = φ
  rw [map_one]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `φ.1 (x * g) = ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y * ψ.1 (y⁻¹ * x * g) ∂μ`. Rewrite using `[e]`. Simplify using `only [cv, mul_assoc]`.
-/
private theorem rt_cv (μ : Measure (GA E a)) {φ ψ : Sm E a} {F : HL μ} (e : φ.1 = cv ψ.1 F) (g : GA E a) :
    (rt E a g φ).1 = cv (rt E a g ψ).1 F := by
  funext x
  change φ.1 (x * g) = ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y * ψ.1 (y⁻¹ * x * g) ∂μ
  rw [e]
  simp only [cv, mul_assoc]

end

/- English proof (translation)
Introduce `E _ _ _ a ha μ _ _ φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ h`. Take `⟨ψ, F, hψ, e⟩` from `h`. Take `⟨t1, t2⟩` from `testOps E a ψ`.

Establish `hc : Continuous ψ.1` using `(t1 hψ.2).1`. Use `⟨lev_of (lev_nhds hψ.2) fun k hk => ?_, ?_, ?_, fun X => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hk' : rt E a (finGL E a k) ψ = ψ` using `hk`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(rt E a (finGL E a k) φ).1 = φ.1`.

Rewrite using `[rt_cv μ e, hk', e]`. Take `⟨h, -⟩` from `convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1 F`. Unfold `InL`. Rewrite using `[e]`. Conclude with `h`.

Rewrite using `[e]`. Conclude with `cvGrow E a ha μ ψ.1 hc hψ.1 F`. Conclude with `Submodule.subset_span ⟨_, F, (t2 hψ).1 X, cvLie E a μ ψ φ hψ F e X⟩`. Conclude with `Submodule.subset_span ⟨_, F, (t2 hψ).2 g, rt_cv μ e g⟩`. Consider the case `zero`.

Use `⟨lev_of Filter.univ_mem fun k _ => map_zero _, ⟨fun _ _ _ => rfl, ?_⟩, fun g => ⟨0, 0, fun y => by simp⟩, fun X => by rw [map_zero]; exact zero_mem _, fun g => by rw [map_zero]; exact zero_mem _⟩` and prove the remaining obligations. Conclude with `MemLp.zero`. Consider the case `add φ ψ _ _ h h'`. Use `⟨lev_of (Filter.inter_mem (lev_nhds h.1) (lev_nhds h'.1)) fun k hk => ?_, ?_, grow_lin h.2.2.1 h'.2.2.1, fun X => by rw [map_add]; exact add_mem (h.2.2.2.1 X) (h'.2.2.2.1 X), fun g => by rw [map_add]; exact add_mem (h.2.2.2.2 g) (h'.2.2.2.2 g)⟩` and prove the remaining obligations. Rewrite using `[map_add, hk.1, hk.2]`.

Simplify `((clFacts E a μ).1 φ ψ 1 1 h.2.1 h'.2.1).1` using `only [one_smul]`. Consider the case `smul s φ _ h`. Use `⟨lev_of (lev_nhds h.1) fun k hk => ?_, ?_, grow_smul s h.2.2.1, fun X => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.1 X), fun g => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.2 g)⟩` and prove the remaining obligations. Rewrite using `[map_smul, hk]`. Simplify `((clFacts E a μ).1 φ φ s 0 h.2.1 h.2.1).1` using `only [zero_smul, add_zero]`.
-/
theorem UpperTheory.V.Cj.H.gardFacts :
    UpperTheory.V.Cj.H.GardFacts := by
  intro E _ _ _ a ha μ _ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, e⟩ := h
    obtain ⟨t1, t2⟩ := testOps E a ψ
    have hc : Continuous ψ.1 := (t1 hψ.2).1
    refine ⟨lev_of (lev_nhds hψ.2) fun k hk => ?_, ?_, ?_, fun X => ?_, fun g => ?_⟩
    · have hk' : rt E a (finGL E a k) ψ = ψ := hk
      apply Subtype.ext
      change (rt E a (finGL E a k) φ).1 = φ.1
      rw [rt_cv μ e, hk', e]
    · obtain ⟨h, -⟩ := convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1 F
      unfold InL
      rw [e]
      exact h
    · rw [e]
      exact cvGrow E a ha μ ψ.1 hc hψ.1 F
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).1 X, cvLie E a μ ψ φ hψ F e X⟩
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).2 g, rt_cv μ e g⟩
  | zero =>
    refine ⟨lev_of Filter.univ_mem fun k _ => map_zero _, ⟨fun _ _ _ => rfl, ?_⟩, fun g => ⟨0, 0, fun y => by simp⟩,
      fun X => by rw [map_zero]; exact zero_mem _, fun g => by rw [map_zero]; exact zero_mem _⟩
    exact MemLp.zero
  | add φ ψ _ _ h h' =>
    refine ⟨lev_of (Filter.inter_mem (lev_nhds h.1) (lev_nhds h'.1)) fun k hk => ?_, ?_, grow_lin h.2.2.1 h'.2.2.1,
      fun X => by rw [map_add]; exact add_mem (h.2.2.2.1 X) (h'.2.2.2.1 X),
      fun g => by rw [map_add]; exact add_mem (h.2.2.2.2 g) (h'.2.2.2.2 g)⟩
    · rw [map_add, hk.1, hk.2]
    · simpa only [one_smul] using ((clFacts E a μ).1 φ ψ 1 1 h.2.1 h'.2.1).1
  | smul s φ _ h =>
    refine ⟨lev_of (lev_nhds h.1) fun k hk => ?_, ?_, grow_smul s h.2.2.1,
      fun X => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.1 X),
      fun g => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.2 g)⟩
    · rw [map_smul, hk]
    · simpa only [zero_smul, add_zero] using ((clFacts E a μ).1 φ φ s 0 h.2.1 h.2.1).1
