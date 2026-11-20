import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxeeig

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
The claim follows from `isOpen_ne_fun (continuous_id.matrix_det) continuous_const`.
-/
theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

/- English proof (translation)
Conclude with `(le_top : (1 : ℕ∞) ≤ ⊤)` after adjusting the coercions.
-/
theorem one_le_inf : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)

/- English proof (translation)
Use `show (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)`. Conclude with `(le_top : ((⊤ : ℕ∞) + 1) ≤ ⊤)` after adjusting the coercions.
-/
theorem inf_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  show (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1) ≤ ⊤)

/- English proof (translation)
The claim follows from `(hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hg)`.
-/
theorem diffAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℝ f g :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hg)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rd_std (F : Mat n → ℂ) (g X : Mat n) : Rd X F g = fderiv ℝ F g (g * X) := rfl

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl

/- English proof (translation)
Conclude with `(hf.fderiv_of_isOpen isOpen_GLs inf_add_one_le).clm_apply (mulR X).contDiff.contDiffOn`.
-/
theorem rd_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) := by
  exact (hf.fderiv_of_isOpen isOpen_GLs inf_add_one_le).clm_apply (mulR X).contDiff.contDiffOn

/- English proof (translation)
Unfold `Eu`. Conclude with `((rd_contDiffOn hf _).add ((rd_contDiffOn hf _).const_smul _)).const_smul _`.
-/
theorem eu_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (b c : Fin n) : ContDiffOn ℝ ∞ (Eu s b c f) (GLs n) := by
  unfold Eu
  exact ((rd_contDiffOn hf _).add ((rd_contDiffOn hf _).const_smul _)).const_smul _

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `b c`. Simplify using `only [Epow]`.

Use `split_ifs`. Conclude with `hf`. Conclude with `contDiffOn_const`. Consider the case `succ m ih`. Introduce `b c`.

Establish `e : Epow s (m + 1) b c f = fun x => ∑ d, Eu s b d (Epow s m d c f) x`. Use function extensionality and compare the values at `x`. Simplify using `only [Epow, Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `ContDiffOn.sum fun d _ => eu_contDiffOn (ih d c) s b d`.
-/
theorem epow_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) : ∀ m b c, ContDiffOn ℝ ∞ (Epow s m b c f) (GLs n) := by
  intro m
  induction m with
  | zero =>
    intro b c
    simp only [Epow]
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    intro b c
    have e : Epow s (m + 1) b c f = fun x => ∑ d, Eu s b d (Epow s m d c f) x := by
      funext x; simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun d _ => eu_contDiffOn (ih d c) s b d

/- English proof (translation)
Simplify using `only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h.fderiv_eq]`.
-/
theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f₁ f₂ : Mat n → V} {g : Mat n}
    (h : f₁ =ᶠ[𝓝 g] f₂) (s : Bool) (b c : Fin n) : Eu s b c f₁ g = Eu s b c f₂ g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h.fderiv_eq]

/- English proof (translation)
Establish `hm : fderiv ℝ (fun x => F x * a x) g = F g • fderiv ℝ a g + a g • fderiv ℝ F g` using `(hF.hasFDerivAt.fun_mul ha.hasFDerivAt).fderiv`. Establish `key : ∀ X : Mat n, Rd X (fun x => F x * a x) g = F g * Rd X a g + a g * Rd X F g`. Introduce `X`. Rewrite using `[rd_std, rd_std, rd_std, hm]`. Simplify using `[smul_eq_mul]`.

Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, key, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eu_mul {F a : Mat n → ℂ} {g : Mat n} (hF : DifferentiableAt ℝ F g) (ha : DifferentiableAt ℝ a g)
    (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => F x * a x) g = F g * Eu s b c a g + a g * Eu s b c F g := by
  have hm : fderiv ℝ (fun x => F x * a x) g = F g • fderiv ℝ a g + a g • fderiv ℝ F g :=
    (hF.hasFDerivAt.fun_mul ha.hasFDerivAt).fderiv
  have key : ∀ X : Mat n, Rd X (fun x => F x * a x) g = F g * Rd X a g + a g * Rd X F g := by
    intro X
    rw [rd_std, rd_std, rd_std, hm]
    simp [smul_eq_mul]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, smul_eq_mul]
  ring

/- English proof (translation)
Establish `key : ∀ X : Mat n, Rd X (fun x => ∑ i, ψ i x • v i) g = ∑ i, Rd X (ψ i) g • v i`. Introduce `X`. Simplify using `only [rd_std]`. Establish `h : HasFDerivAt (fun x => ∑ i, ψ i x • v i) (∑ i, (fderiv ℝ (ψ i) g).smulRight (v i)) g` using `HasFDerivAt.fun_sum fun i _ => (hψ i).hasFDerivAt.smul_const (v i)`. Unfold `Rd`.

Rewrite using `[h.fderiv]`. Simplify using `[ContinuousLinearMap.smulRight_apply]`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, key, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul _ (Rd (Matrix.single b c Complex.I) (ψ i) g), ← add_smul, smul_smul]`.

Use `congr 1`.
-/
theorem eu_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (ψ : ι → Mat n → ℂ) (v : ι → V)
    {g : Mat n} (hψ : ∀ i, DifferentiableAt ℝ (ψ i) g) (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => ∑ i, ψ i x • v i) g = ∑ i, Eu s b c (ψ i) g • v i := by
  have key : ∀ X : Mat n, Rd X (fun x => ∑ i, ψ i x • v i) g = ∑ i, Rd X (ψ i) g • v i := by
    intro X
    simp only [rd_std]
    have h : HasFDerivAt (fun x => ∑ i, ψ i x • v i) (∑ i, (fderiv ℝ (ψ i) g).smulRight (v i)) g :=
      HasFDerivAt.fun_sum fun i _ => (hψ i).hasFDerivAt.smul_const (v i)
    unfold Rd
    rw [h.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul _ (Rd (Matrix.single b c Complex.I) (ψ i) g), ← add_smul, smul_smul]
  congr 1

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `b c g _`. Simplify using `only [Epow]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ m ih`. Introduce `b c g hg`. Simplify using `only [Epow, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Establish `he : Epow s m d c (fun x => F x * G x) =ᶠ[𝓝 g] fun x => F x * Epow s m d c G x` using `Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx`. Rewrite using `[eu_congr he, eu_mul (diffAt hF hg) (diffAt (epow_contDiffOn hG s m d c) hg), hk g hg, mul_zero, add_zero]`.
-/
theorem epow_mul_of_kill {F G : Mat n → ℂ} (hF : ContDiffOn ℝ ∞ F (GLs n)) (hG : ContDiffOn ℝ ∞ G (GLs n)) (s : Bool)
    (hk : ∀ g ∈ GLs n, ∀ b c, Eu s b c F g = 0) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => F x * G x) g = F g * Epow s m b c G g := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have he : Epow s m d c (fun x => F x * G x) =ᶠ[𝓝 g] fun x => F x * Epow s m d c G x :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
    rw [eu_congr he, eu_mul (diffAt hF hg) (diffAt (epow_contDiffOn hG s m d c) hg), hk g hg, mul_zero, add_zero]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `b c g _`. Simplify using `only [Epow]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ m ih`. Introduce `b c g hg`. Simplify using `only [Epow, Finset.sum_apply]`. Establish `step : ∀ d, Eu s b d (Epow s m d c fun x => ∑ i, φ i x • v i) g = ∑ i, Eu s b d (Epow s m d c (φ i)) g • v i`.

Introduce `d`. Establish `he : (Epow s m d c fun x => ∑ i, φ i x • v i) =ᶠ[𝓝 g] fun x => ∑ i, Epow s m d c (φ i) x • v i` using `Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx`. Rewrite using `[eu_congr he, eu_sum_smul _ _ (fun i => diffAt (epow_contDiffOn (hφ i) s m d c) hg)]`. Simplify using `only [step]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`.
-/
theorem epow_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ι → Mat n → ℂ) (v : ι → V)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (GLs n)) (s : Bool) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => ∑ i, φ i x • v i) g = ∑ i, Epow s m b c (φ i) g • v i := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply]
    have step : ∀ d, Eu s b d (Epow s m d c fun x => ∑ i, φ i x • v i) g =
        ∑ i, Eu s b d (Epow s m d c (φ i)) g • v i := by
      intro d
      have he : (Epow s m d c fun x => ∑ i, φ i x • v i) =ᶠ[𝓝 g] fun x => ∑ i, Epow s m d c (φ i) x • v i :=
        Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
      rw [eu_congr he, eu_sum_smul _ _ (fun i => diffAt (epow_contDiffOn (hφ i) s m d c) hg)]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]

end PositivityTheory.RgBcC.Cxeeig

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC.Cxeeig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n χ ι V _ _ _ h a v hh ha hhe hae`. Establish `hφ : ∀ i, ContDiffOn ℝ ∞ (fun x => h i x * a i x) (GLs n)` using `fun i => (hh i).mul (ha i)`. Introduce `s m g hg`. Establish `hsum : gel s m (fun x => ∑ i, (h i x * a i x) • v i) g = ∑ i, gel s m (fun x => h i x * a i x) g • v i`. Simplify using `only [gel, Finset.sum_apply]`.

Rewrite using `[Finset.sum_congr rfl fun b _ => epow_sum_smul (fun i x => h i x * a i x) v hφ s m b b g hg, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Establish `hone : ∀ i, gel s m (fun x => h i x * a i x) g = GlobalTheory.Dec.gelfVal (χ s) m * (h i g * a i g)`. Introduce `i`.

Consider the cases of `s with`. Consider the case `true`. Establish `e : (fun x => h i x * a i x) = fun x => a i x * h i x` using `by funext x; ring`. Simplify using `only [gel, Finset.sum_apply]`. Rewrite using `[e, Finset.sum_congr rfl fun b _ => epow_mul_of_kill (ha i) (hh i) true (fun g hg b c => (hae i g hg).2 b c) m b b g hg, ← Finset.mul_sum]`.

Use `(hhe i g hg).1 m` as an intermediate fact. Simplify using `only [gel, Finset.sum_apply] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `false`.

Simplify using `only [gel, Finset.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun b _ => epow_mul_of_kill (hh i) (ha i) false (fun g hg b c => (hhe i g hg).2 b c) m b b g hg, ← Finset.mul_sum]`. Use `(hae i g hg).1 m` as an intermediate fact. Simplify using `only [gel, Finset.sum_apply] at this`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hone i, smul_smul]`.
-/
theorem eigProd : EigProd := by
  intro n χ ι V _ _ _ h a v hh ha hhe hae
  have hφ : ∀ i, ContDiffOn ℝ ∞ (fun x => h i x * a i x) (GLs n) := fun i => (hh i).mul (ha i)
  intro s m g hg
  have hsum : gel s m (fun x => ∑ i, (h i x * a i x) • v i) g =
      ∑ i, gel s m (fun x => h i x * a i x) g • v i := by
    simp only [gel, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun b _ => epow_sum_smul (fun i x => h i x * a i x) v hφ s m b b g hg, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
  have hone : ∀ i, gel s m (fun x => h i x * a i x) g = GlobalTheory.Dec.gelfVal (χ s) m * (h i g * a i g) := by
    intro i
    cases s with
    | true =>
      have e : (fun x => h i x * a i x) = fun x => a i x * h i x := by funext x; ring
      simp only [gel, Finset.sum_apply]
      rw [e, Finset.sum_congr rfl fun b _ => epow_mul_of_kill (ha i) (hh i) true (fun g hg b c => (hae i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hhe i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
    | false =>
      simp only [gel, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun b _ => epow_mul_of_kill (hh i) (ha i) false (fun g hg b c => (hhe i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hae i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hone i, smul_smul]

end PositivityTheory.RgBcC
