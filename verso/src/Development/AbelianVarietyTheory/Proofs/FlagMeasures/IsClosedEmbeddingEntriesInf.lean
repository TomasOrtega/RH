import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageEqOfMemLowKSubStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverageStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

/- English proof (translation)
Establish `key` using `(uJEmb n ε).1`. Conclude with `key`.
-/
theorem isClosedEmbedding_entries {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
  have key := (uJEmb n ε).1
  exact key

/- English proof (translation)
Establish `h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ))` using `fun v => isClosedEmbedding_entries (I.ε v)`. Conclude with `Topology.IsClosedEmbedding.piMap h`.
-/
theorem isClosedEmbedding_entries_inf (I : AutInst) :
    Topology.IsClosedEmbedding (fun g : I.Ginf =>
      (fun v i j => uMat (g v) i j : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) := by
  have h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding
      (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ)) :=
    fun v => isClosedEmbedding_entries (I.ε v)
  exact Topology.IsClosedEmbedding.piMap h

/- English proof (translation)
Establish `hemb` using `isClosedEmbedding_entries ε`. Establish `hrep : Continuous (fun g : UJ ε => σ (umat g) w)` using `(hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)`. Establish `hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w)` using `(hc.comp_isClosedEmbedding hemb).smul_right`. Conclude with `((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs`.
-/
theorem integrable_loc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {F : (Fin n → Fin n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
  have hemb := isClosedEmbedding_entries ε
  have hrep : Continuous (fun g : UJ ε => σ (umat g) w) :=
    (hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)
  have hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

/- English proof (translation)
Establish `hemb` using `isClosedEmbedding_entries_inf B.I`. Establish `hrep : Continuous (fun g : B.I.Ginf => B.σs g w)` using `hσ.2.2.2 w`. Establish `hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v)` using `rfl`. Use `haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by`. Rewrite using `[hμ]`.

Use `infer_instance`. Establish `hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w)` using `(hc.comp_isClosedEmbedding hemb).smul_right`. Conclude with `((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs`.
-/
theorem integrable_inf (B : RowsAut) (hσ : IsURep B.σs) (w : B.Hs)
    {F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) (muInf B.I) := by
  have hemb := isClosedEmbedding_entries_inf B.I
  have hrep : Continuous (fun g : B.I.Ginf => B.σs g w) := hσ.2.2.2 w
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by
    rw [hμ]
    infer_instance
  have hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

/- English proof (translation)
Take `⟨hin, hact, hden⟩` from `B.tens_spec`. Use `set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef`. Establish `hGs : ContDiff ℝ ∞ G` using `contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (Fin B.I.n → Fin B.I.n → ℂ) v))`. Establish `hGc : HasCompactSupport G`. Use `HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v) (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx`. Take `⟨v, hv⟩` from `hx`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)`. Use `⟨G, hGs, hGc, ?_⟩` and prove the remaining obligations.

Use `eq_of_inner_eq_on_dense_span hden ?_` and prove the remaining obligations. Introduce and unpack `y ⟨x, rfl⟩`. Establish `hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))⟫_ℂ = ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v))`. Introduce `v`. Rewrite using `[← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]`.

Simplify using `only [inner_smul_right]`. Establish `hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ = ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ) ∂(muInf B.I)`. Rewrite using `[← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[inner_smul_right, hact, hin, Finset.prod_mul_distrib]`. Establish `hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v)` using `rfl`. Establish `hprod` using `integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v)) (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)`. Rewrite using `[hglob, hin, hμ]`. Use `Eq.trans ?_ hprod.symm` and prove the remaining obligations.

Conclude with `Finset.prod_congr rfl (fun v _ => hloc v)`.
-/
theorem tens_average (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hσ : IsURep B.σs)
    (w : ∀ v, B.H v) (F : InfinitePlace B.I.F → (Fin B.I.n → Fin B.I.n → ℂ) → ℂ)
    (hF : ∀ v, ContDiff ℝ ∞ (F v)) (hc : ∀ v, HasCompactSupport (F v)) :
    ∃ G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      B.tens (fun v => ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))) =
        ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I) := by
  classical
  obtain ⟨hin, hact, hden⟩ := B.tens_spec
  set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (Fin B.I.n → Fin B.I.n → ℂ) v))
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v)
      (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨v, hv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)
  refine ⟨G, hGs, hGc, ?_⟩
  refine eq_of_inner_eq_on_dense_span hden ?_
  rintro y ⟨x, rfl⟩
  have hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v)
        ∂(muG (B.I.ε v))⟫_ℂ =
      ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v)) := by
    intro v
    rw [← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]
    simp only [inner_smul_right]
  have hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ =
      ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ)
        ∂(muInf B.I) := by
    rw [← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]
    congr 1
    funext g
    rw [inner_smul_right, hact, hin, Finset.prod_mul_distrib]
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  have hprod := integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)
  rw [hglob, hin, hμ]
  refine Eq.trans ?_ hprod.symm
  exact Finset.prod_congr rfl (fun v _ => hloc v)

/- English proof (translation)
Introduce `hSL B d hd P u hu`. Establish `hσ : IsURep B.σs` using `(tensorRep B d hd).1`. Establish `hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)` using `fun v => (hd v).2.1.2.2.1`. Set `Av : B.Hs → Prop` to `fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)`. Establish `hzero : Av 0`.

Use `⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩` and prove the remaining obligations. Simplify using `only [zero_smul, integral_zero]`. Establish `hadd : ∀ a b, Av a → Av b → Av (a + b)`. Introduce and unpack `a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩`. Use `⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁) (integrable_inf B hσ _ hF₂.continuous hc₂)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[Pi.add_apply, add_smul]`. Establish `hsmul : ∀ (c : ℂ) a, Av a → Av (c • a)`.

Introduce and unpack `c a ⟨F₁, hF₁, hc₁, rfl⟩`. Use `⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩` and prove the remaining obligations. Rewrite using `[← integral_smul]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[mul_smul]`. Establish `hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x)`. Introduce `x hx`. Establish `hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v))`. Introduce `v`.

Establish `hlow` using `(hd v).2.2.1`. Establish `hw0 : B.w v ≠ 0`. Introduce `h0`. Establish `h1` using `hlow.1`. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one h1`. Establish `hK` using `(hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1`. Conclude with `GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)`. Use `choose Fl hFl hcl hxl using hloc`. Take `⟨G, hG, hcG, hEq⟩` from `tens_average B hU hσ B.w Fl hFl hcl`.

Use `⟨G, hG, hcG, ?_⟩` and prove the remaining obligations. Rewrite using `[← hEq]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `hxl v`.

Establish `hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y)`. Introduce and unpack `E y ⟨F₁, hF₁, hc₁, rfl⟩`. Take `⟨F', hF', hc', hder⟩` from `GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage B F₁ E (B.tens B.w) hσ hF₁ hc₁`. Conclude with `⟨F', hF', hc', hder.deriv⟩`. Establish `hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v), (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x))`.

Introduce `l x hx`. Proceed by induction on `l with`. Consider the case `nil => exact hbase x hx`. Consider the case `cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih`. Establish `hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧ y = wordAct B l (B.tens x)}` using `hu`.

Use `clear hu`. Proceed by induction on `hu' using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, x, -, hx, rfl⟩` from `hy`. Conclude with `hword l x hx`.

Consider the case `zero => exact hzero`. Consider the case `add a b _ _ ha hb => exact hadd a b ha hb`. Consider the case `smul c a _ ha => exact hsmul c a ha`.
-/
theorem exists_smooth_average : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro hSL B d hd P u hu
  have hσ : IsURep B.σs := (tensorRep B d hd).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hd v).2.1.2.2.1

  let Av : B.Hs → Prop := fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ,
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)
  have hzero : Av 0 := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simp only [zero_smul, integral_zero]
  have hadd : ∀ a b, Av a → Av b → Av (a + b) := by
    rintro a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩
    refine ⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩
    rw [← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁)
      (integrable_inf B hσ _ hF₂.continuous hc₂)]
    congr 1
    funext g
    rw [Pi.add_apply, add_smul]
  have hsmul : ∀ (c : ℂ) a, Av a → Av (c • a) := by
    rintro c a ⟨F₁, hF₁, hc₁, rfl⟩
    refine ⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x) := by
    intro x hx
    have hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v)) := by
      intro v
      have hlow := (hd v).2.2.1
      have hw0 : B.w v ≠ 0 := by
        intro h0
        have h1 := hlow.1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hK := (hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1
      exact GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)
    choose Fl hFl hcl hxl using hloc
    obtain ⟨G, hG, hcG, hEq⟩ := tens_average B hU hσ B.w Fl hFl hcl
    refine ⟨G, hG, hcG, ?_⟩
    rw [← hEq]
    congr 1
    funext v
    exact hxl v

  have hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y) := by
    rintro E y ⟨F₁, hF₁, hc₁, rfl⟩
    obtain ⟨F', hF', hc', hder⟩ := GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage B F₁ E (B.tens B.w) hσ hF₁ hc₁
    exact ⟨F', hF', hc', hder.deriv⟩
  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v),
      (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x)) := by
    intro l x hx
    induction l with
    | nil => exact hbase x hx
    | cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih
  have hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)))
      (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧
        y = wordAct B l (B.tens x)} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, x, -, hx, rfl⟩ := hy
    exact hword l x hx
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

end GlobalTheory.StepAverage
