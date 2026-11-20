import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticImplicitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Module
open scoped ContDiff

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Take `⟨p, r, hp⟩` from `hψ`. Use `filter_upwards [Metric.eball_mem_nhds y₀ hp.r_pos] with u hu`. Establish `hmem : u - y₀ ∈ Metric.eball (0 : E) r`. Simplify `hu` using `[Metric.mem_eball, edist_eq_enorm_sub]`. Establish `hs` using `hp.hasSum_iteratedFDeriv hmem`.

Simplify using `only [h0, smul_zero, add_sub_cancel] at hs`. Conclude with `hs.unique hasSum_zero`.
-/
theorem eventually_zero_of_iteratedFDeriv_diag {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀)
    (h0 : ∀ (n : ℕ) (v : E), iteratedFDeriv ℂ n ψ y₀ (fun _ => v) = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  obtain ⟨p, r, hp⟩ := hψ
  filter_upwards [Metric.eball_mem_nhds y₀ hp.r_pos] with u hu
  have hmem : u - y₀ ∈ Metric.eball (0 : E) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hu
  have hs := hp.hasSum_iteratedFDeriv hmem
  simp only [h0, smul_zero, add_sub_cancel] at hs
  exact hs.unique hasSum_zero

/- English proof (translation)
Rewrite using `[iteratedFDeriv_succ_apply_right]`. Establish `hc : ContDiffAt ℂ ω (fderiv ℂ ψ) y₀` using `hψ.fderiv.contDiffAt`. Establish `h1` using `(ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left hc (i := n) le_top`. Establish `h2 : (fun y => fderiv ℂ ψ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ ψ` using `rfl`. Rewrite using `[h2, h1]`.

Both sides reduce to the same expression.
-/
theorem iteratedFDeriv_succ_diag_eq {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀) (n : ℕ) (v : E) :
    iteratedFDeriv ℂ (n + 1) ψ y₀ (fun _ => v) =
      iteratedFDeriv ℂ n (fun y => fderiv ℂ ψ y v) y₀ (fun _ => v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hc : ContDiffAt ℂ ω (fderiv ℂ ψ) y₀ := hψ.fderiv.contDiffAt
  have h1 := (ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left hc (i := n) le_top
  have h2 : (fun y => fderiv ℂ ψ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ ψ := rfl
  rw [h2, h1]
  rfl

/- English proof (translation)
Establish `step : ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E, AnalyticAt ℂ (fun y => fderiv ℂ φ y v) y₀ ∧ ∀ᶠ u in 𝓝 y₀, u ∈ C → fderiv ℂ φ u v = 0`. Introduce `φ hφ hφC v`. Use `⟨((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hφ.fderiv, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hφ.eventually_analyticAt, hφC.eventually_nhds, hU] with c hca hcC hcU hc`. Rewrite using `[hC c ⟨hc, hcU⟩ φ hca hcC]`.

Both sides reduce to the same expression. Establish `key : ∀ n : ℕ, ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E, iteratedFDeriv ℂ n φ y₀ (fun _ => v) = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro φ _ hφC v`.

Simplify using `using hφC.self_of_nhds hy₀`. Consider the case `succ n ih`. Introduce `φ hφ hφC v`. Rewrite using `[iteratedFDeriv_succ_diag_eq hφ]`. Take `⟨h1, h2⟩` from `step φ hφ hφC v`.

Conclude with `ih _ h1 h2 v`. Conclude with `eventually_zero_of_iteratedFDeriv_diag hψ fun n v => key n ψ hψ hψC v`.
-/
theorem eventually_zero_of_conormal_zero {C : Set E} {y₀ : E} (hy₀ : y₀ ∈ C) {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hC : ∀ c ∈ C ∩ U, ∀ ψ : E → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ C → ψ u = 0) →
      fderiv ℂ ψ c = 0)
    {ψ : E → ℂ} (hψ : AnalyticAt ℂ ψ y₀) (hψC : ∀ᶠ u in 𝓝 y₀, u ∈ C → ψ u = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  have step : ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E,
      AnalyticAt ℂ (fun y => fderiv ℂ φ y v) y₀ ∧ ∀ᶠ u in 𝓝 y₀, u ∈ C → fderiv ℂ φ u v = 0 := by
    intro φ hφ hφC v
    refine ⟨((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hφ.fderiv, ?_⟩
    filter_upwards [hφ.eventually_analyticAt, hφC.eventually_nhds, hU] with c hca hcC hcU hc
    rw [hC c ⟨hc, hcU⟩ φ hca hcC]
    rfl
  have key : ∀ n : ℕ, ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) →
      ∀ v : E, iteratedFDeriv ℂ n φ y₀ (fun _ => v) = 0 := by
    intro n
    induction n with
    | zero => intro φ _ hφC v; simpa using hφC.self_of_nhds hy₀
    | succ n ih =>
      intro φ hφ hφC v
      rw [iteratedFDeriv_succ_diag_eq hφ]
      obtain ⟨h1, h2⟩ := step φ hφ hφC v
      exact ih _ h1 h2 v
  exact eventually_zero_of_iteratedFDeriv_diag hψ fun n v => key n ψ hψ hψC v

end Germs

noncomputable def conormalSpan {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (z : σ → ℂ) :
    Submodule ℂ ((σ → ℂ) →L[ℂ] ℂ) :=
  Submodule.span ℂ {ℓ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h z ∧ (∀ᶠ u in 𝓝 z, u ∈ Y → h u = 0) ∧
    fderiv ℂ h z = ℓ}

/- English proof (translation)
Use `set rk : (σ → ℂ) → ℕ := fun z => finrank ℂ (conormalSpan Y z) with hrk`. Establish `hbdd : BddAbove (rk '' (Y ∩ U))` using `⟨finrank ℂ ((σ → ℂ) →L[ℂ] ℂ), by rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩`. Take `⟨a, haYU, har⟩` from `Nat.sSup_mem (hne.image rk) hbdd`. Establish `hmax : ∀ z ∈ Y ∩ U, rk z ≤ rk a` using `fun z hz => har ▸ le_csSup hbdd ⟨z, hz, rfl⟩`. Take `⟨b, hbS, hbspan, hbli⟩` from `exists_linearIndependent ℂ {ℓ : (σ → ℂ) →L[ℂ] ℂ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧ fderiv ℂ h a = ℓ}`.

Establish `: Finite b` using `hbli.finite`. Set `_ : Fintype b` to `Fintype.ofFinite b`. Establish `hb' : ∀ ℓ : b, ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧ fderiv ℂ h a = ℓ` using `fun ℓ => hbS ℓ.2`. Use `choose h hha hhY hhd using hb'`. Establish `hfun : (fun j : b => fderiv ℂ (h j) a) = ((↑) : b → (σ → ℂ) →L[ℂ] ℂ)` using `funext hhd`.

Establish `hli_a : LinearIndependent ℂ (fun j => fderiv ℂ (h j) a)` using `hfun ▸ hbli`. Establish `hcard : rk a = Fintype.card b`. Establish `hsp : conormalSpan Y a = Submodule.span ℂ (Set.range fun j : b => fderiv ℂ (h j) a)`. Rewrite using `[hfun, Subtype.range_coe, hbspan]`. Both sides reduce to the same expression.

Use `show finrank ℂ (conormalSpan Y a) = _`. Rewrite using `[hsp]`. Conclude with `finrank_span_eq_card hli_a`. Establish `E3 : ∀ᶠ z in 𝓝 a, LinearIndependent ℂ (fun j => fderiv ℂ (h j) z)`. Establish `ht : Tendsto (fun z => fun j => fderiv ℂ (h j) z) (𝓝 a) (𝓝 fun j => fderiv ℂ (h j) a)` using `tendsto_pi_nhds.2 fun j => (hha j).fderiv.continuousAt.tendsto`.

Conclude with `ht.eventually hli_a.eventually`. Establish `E : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (∀ j, AnalyticAt ℂ (h j) z) ∧ (∀ j, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) z)` using `(show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds haYU.2).and ((eventually_all.2 fun j => (hha j).eventually_analyticAt).and ((eventually_all.2 hhY).and E3))`. Take `⟨W, hWP, hWo, haW⟩` from `eventually_nhds_iff.1 E`. Use `⟨a, haYU.1, b, inferInstance, h, W, hWo, haW, fun z hz => (hWP z hz).1, fun j z hz => (hWP z hz).2.1 j, fun j z hz => (hWP z hz).2.2.1 j, hli_a, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hzW, hzY⟩ ψ hψ hψY`.

Take `⟨hzU, hza, -, hzli⟩` from `hWP z hzW`. Establish `hle : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) ≤ conormalSpan Y z`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `Submodule.subset_span ⟨h j, hza j, ?_, rfl⟩` and prove the remaining obligations.

Use `filter_upwards [hWo.mem_nhds hzW] with u hu huY using (hWP u hu).2.2.1 j huY`. Establish `heq : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) = conormalSpan Y z` using `Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_eq_card hzli, ← hcard]; exact hmax z ⟨hzY, hzU⟩)`. Rewrite using `[heq]`. Conclude with `Submodule.subset_span ⟨ψ, hψ, hψY, rfl⟩`.
-/
theorem exists_maxRank_equations {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) {U : Set (σ → ℂ)}
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    ∃ a ∈ Y, ∃ (ι : Type) (_ : Fintype ι) (h : ι → (σ → ℂ) → ℂ) (W : Set (σ → ℂ)),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ (∀ j, ∀ z ∈ W, AnalyticAt ℂ (h j) z) ∧
      (∀ j, ∀ z ∈ W, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) ∧
      ∀ z ∈ W ∩ Y, ∀ ψ : (σ → ℂ) → ℂ, AnalyticAt ℂ ψ z → (∀ᶠ u in 𝓝 z, u ∈ Y → ψ u = 0) →
        fderiv ℂ ψ z ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) := by
  classical
  set rk : (σ → ℂ) → ℕ := fun z => finrank ℂ (conormalSpan Y z) with hrk
  have hbdd : BddAbove (rk '' (Y ∩ U)) :=
    ⟨finrank ℂ ((σ → ℂ) →L[ℂ] ℂ), by rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨a, haYU, har⟩ := Nat.sSup_mem (hne.image rk) hbdd
  have hmax : ∀ z ∈ Y ∩ U, rk z ≤ rk a := fun z hz => har ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ
    {ℓ : (σ → ℂ) →L[ℂ] ℂ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ}
  have : Finite b := hbli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hb' : ∀ ℓ : b, ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ := fun ℓ => hbS ℓ.2
  choose h hha hhY hhd using hb'
  have hfun : (fun j : b => fderiv ℂ (h j) a) = ((↑) : b → (σ → ℂ) →L[ℂ] ℂ) := funext hhd
  have hli_a : LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) := hfun ▸ hbli
  have hcard : rk a = Fintype.card b := by
    have hsp : conormalSpan Y a = Submodule.span ℂ (Set.range fun j : b => fderiv ℂ (h j) a) := by
      rw [hfun, Subtype.range_coe, hbspan]
      rfl
    show finrank ℂ (conormalSpan Y a) = _
    rw [hsp]
    exact finrank_span_eq_card hli_a
  have E3 : ∀ᶠ z in 𝓝 a, LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) := by
    have ht : Tendsto (fun z => fun j => fderiv ℂ (h j) z) (𝓝 a) (𝓝 fun j => fderiv ℂ (h j) a) :=
      tendsto_pi_nhds.2 fun j => (hha j).fderiv.continuousAt.tendsto
    exact ht.eventually hli_a.eventually
  have E : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (∀ j, AnalyticAt ℂ (h j) z) ∧ (∀ j, z ∈ Y → h j z = 0) ∧
      LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) :=
    (show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds haYU.2).and ((eventually_all.2 fun j => (hha j).eventually_analyticAt).and
      ((eventually_all.2 hhY).and E3))
  obtain ⟨W, hWP, hWo, haW⟩ := eventually_nhds_iff.1 E
  refine ⟨a, haYU.1, b, inferInstance, h, W, hWo, haW, fun z hz => (hWP z hz).1,
    fun j z hz => (hWP z hz).2.1 j, fun j z hz => (hWP z hz).2.2.1 j, hli_a, ?_⟩
  rintro z ⟨hzW, hzY⟩ ψ hψ hψY
  obtain ⟨hzU, hza, -, hzli⟩ := hWP z hzW
  have hle : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) ≤ conormalSpan Y z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨h j, hza j, ?_, rfl⟩
    filter_upwards [hWo.mem_nhds hzW] with u hu huY using (hWP u hu).2.2.1 j huY
  have heq : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) = conormalSpan Y z :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_span_eq_card hzli, ← hcard]; exact hmax z ⟨hzY, hzU⟩)
  rw [heq]
  exact Submodule.subset_span ⟨ψ, hψ, hψY, rfl⟩

/- English proof (translation)
Introduce `σ _ X w hX`. Take `⟨N, k, f, hNo, hwN, hf, hXN⟩` from `hX`. Use `⟨N, hNo, hwN, fun B hBo hBN x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`.

Establish `hU : IsOpen (interior t ∩ B)` using `isOpen_interior.inter hBo`. Take `⟨a, haY, ι, hι, h, W, hWo, haW, hWU, hha, hhY, hli, hspan⟩` from `exists_maxRank_equations (X ∩ B) hU ⟨x, hx, mem_interior_iff_mem_nhds.2 ht, hx.2⟩`. Take `⟨d, A, O, V, g, -, hOo, hVo, haV, hVW, hg, hAg, hVO⟩` from `hIFT σ ι h a W (fun j => hha j a haW) (fun j => hhY j a haW haY) hli (hWo.mem_nhds haW)`. Establish `hgV : ∀ y ∈ O, g y ∈ V ∧ ∀ j, h j (g y) = 0` using `fun y hy => (show g y ∈ {z | z ∈ V ∧ ∀ j, h j z = 0} from hVO ▸ Set.mem_image_of_mem g hy)`. Establish `hYV : ∀ z ∈ X ∩ B, z ∈ V → g (A z) = z ∧ A z ∈ O`.

Introduce `z hzY hzV`. Establish `hz : z ∈ g '' O` using `hVO ▸ (⟨hzV, fun j => hhY j z (hVW hzV) hzY⟩ : z ∈ {z | z ∈ V ∧ ∀ j, h j z = 0})`. Take `⟨y, hy, rfl⟩` from `hz`. Rewrite using `[hAg y hy]`. Conclude with `⟨rfl, hy⟩`.

Take `⟨hga, hy₀O⟩` from `hYV a haY haV`. Establish `hAD : ∀ y ∈ O, A.comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _`. Introduce `y hy`. Establish `h3 : HasFDerivAt (fun y => A (g y)) (A.comp (fderiv ℂ g y)) y` using `A.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt`. Establish `h4 : HasFDerivAt (fun y => A (g y)) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) y` using `(hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using hAg u hu)`.

Conclude with `h3.unique h4`. Establish `hhD : ∀ y ∈ O, ∀ j, (fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y) = 0`. Introduce `y hy j`. Establish `h3 : HasFDerivAt (fun y => h j (g y)) ((fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y)) y` using `(hha j (g y) (hVW (hgV y hy).1)).differentiableAt.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt`. Establish `h4 : HasFDerivAt (fun y => h j (g y)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) y` using `(hasFDerivAt_const 0 y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using (hgV u hu).2 j)`.

Conclude with `h3.unique h4`. Establish `hC : ∀ c ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} ∩ O, ∀ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} → ψ u = 0) → fderiv ℂ ψ c = 0`. Introduce and unpack `c ⟨⟨hcO, hcY⟩, -⟩ ψ hψ hψC`. Establish `hzV` using `(hgV c hcO).1`. Establish `hAz : A (g c) = c` using `hAg c hcO`.

Establish `hψ' : AnalyticAt ℂ ψ (A (g c))` using `by rw [hAz]; exact hψ`. Establish `hH : AnalyticAt ℂ (fun u => ψ (A u)) (g c)` using `hψ'.comp (A.analyticAt (g c))`. Establish `hHY : ∀ᶠ u in 𝓝 (g c), u ∈ X ∩ B → ψ (A u) = 0`. Establish `hAt : Tendsto A (𝓝 (g c)) (𝓝 c)`. Establish `h0` using `A.continuous.tendsto (g c)`.

Rewrite `h0` using `[hAz]`. Then use the resulting hypothesis. Use `filter_upwards [hVo.mem_nhds hzV, hAt hψC] with u huV huψ huY`. Take `⟨hgu, huO⟩` from `hYV u huY huV`. Conclude with `huψ ⟨huO, hgu.symm ▸ huY⟩`. Establish `hmem` using `hspan (g c) ⟨hVW hzV, hcY⟩ _ hH hHY`.

Establish `hchain : fderiv ℂ (fun u => ψ (A u)) (g c) = (fderiv ℂ ψ c).comp A`. Establish `hψd : HasFDerivAt ψ (fderiv ℂ ψ c) (A (g c))`. Rewrite using `[hAz]`. Conclude with `hψ.differentiableAt.hasFDerivAt`. Conclude with `(hψd.comp (g c) A.hasFDerivAt).fderiv`.

Establish `hkill : ∀ ℓ ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) (g c)), ℓ.comp (fderiv ℂ g c) = 0`. Introduce `ℓ hℓ`. Proceed by induction on `hℓ using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hhD c hcO j`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [ContinuousLinearMap.add_comp, hx, hy, add_zero]`. Consider the case `smul r x _ hx`. Rewrite using `[ContinuousLinearMap.smul_comp, hx]`. Use extensionality with `v`.

Simplify using the standard rewrite rules. Establish `hk` using `hkill _ hmem`. Rewrite `hk` using `[hchain, ContinuousLinearMap.comp_assoc, hAD c hcO, ContinuousLinearMap.comp_id]`. Conclude with `hk`. Establish `hvan : ∀ i, ∀ᶠ y in 𝓝 (A a), f i (g y) = 0`.

Introduce `i`. Use `eventually_zero_of_conormal_zero (C := {y | y ∈ O ∧ g y ∈ X ∩ B}) ⟨hy₀O, hga.symm ▸ haY⟩ (hOo.mem_nhds hy₀O) hC ?_ ?_` and prove the remaining obligations. Establish `hfa : AnalyticAt ℂ (f i) (g (A a))` using `hga.symm ▸ hf i a (hBN haY.2)`. Conclude with `hfa.comp (hg (A a) hy₀O)`. Use `Eventually.of_forall fun y hy => ?_` and prove the remaining obligations.

Establish `hgy : g y ∈ X ∩ N` using `⟨hy.2.1, hBN hy.2.2⟩`. Rewrite `hgy` using `[hXN]`. Conclude with `hgy.2 i`. Take `⟨O', hO'P, hO'o, hy₀O'⟩` from `eventually_nhds_iff.1 ((eventually_all.2 hvan).and (hOo.mem_nhds hy₀O))`. Use `⟨a, interior_subset (hWU haW).1, haY, d, A, O', V ∩ A ⁻¹' O', g, hO'o, hVo.inter (hO'o.preimage A.continuous), ⟨haV, hy₀O'⟩, hg.mono fun y hy => (hO'P y hy).2, fun y hy => hAg y (hO'P y hy).2, ?_⟩` and prove the remaining obligations.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzY, hzV, hzO'⟩`. Conclude with `⟨A z, hzO', (hYV z hzY hzV).1⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨hf0, hyO⟩` from `hO'P y hy`. Establish `hgyV` using `(hgV y hyO).1`. Establish `hgB : g y ∈ B` using `(hWU (hVW hgyV)).2`. Establish `hgX : g y ∈ X`. Establish `hz : g y ∈ {z | z ∈ N ∧ ∀ i, f i z = 0}` using `⟨hBN hgB, hf0⟩`.

Rewrite `hz` using `[← hXN]`. Conclude with `hz.1`. Use `⟨⟨hgX, hgB⟩, hgyV, ?_⟩` and prove the remaining obligations. Use `show A (g y) ∈ O'`. Rewrite using `[hAg y hyO]`.

Conclude with `hy`.
-/
theorem RegularLocusDense.proof (hIFT : AnalyticImplicitChart.Statement) : RegularLocusDense.Statement := by
  intro σ _ X w hX
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N, hNo, hwN, fun B hBo hBN x hx => ?_⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : IsOpen (interior t ∩ B) := isOpen_interior.inter hBo
  obtain ⟨a, haY, ι, hι, h, W, hWo, haW, hWU, hha, hhY, hli, hspan⟩ :=
    exists_maxRank_equations (X ∩ B) hU ⟨x, hx, mem_interior_iff_mem_nhds.2 ht, hx.2⟩
  obtain ⟨d, A, O, V, g, -, hOo, hVo, haV, hVW, hg, hAg, hVO⟩ :=
    hIFT σ ι h a W (fun j => hha j a haW) (fun j => hhY j a haW haY) hli (hWo.mem_nhds haW)

  have hgV : ∀ y ∈ O, g y ∈ V ∧ ∀ j, h j (g y) = 0 := fun y hy =>
    (show g y ∈ {z | z ∈ V ∧ ∀ j, h j z = 0} from hVO ▸ Set.mem_image_of_mem g hy)
  have hYV : ∀ z ∈ X ∩ B, z ∈ V → g (A z) = z ∧ A z ∈ O := by
    intro z hzY hzV
    have hz : z ∈ g '' O := hVO ▸ (⟨hzV, fun j => hhY j z (hVW hzV) hzY⟩ : z ∈ {z | z ∈ V ∧ ∀ j, h j z = 0})
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hAg y hy]
    exact ⟨rfl, hy⟩
  obtain ⟨hga, hy₀O⟩ := hYV a haY haV

  have hAD : ∀ y ∈ O, A.comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _ := by
    intro y hy
    have h3 : HasFDerivAt (fun y => A (g y)) (A.comp (fderiv ℂ g y)) y :=
      A.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => A (g y)) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using hAg u hu)
    exact h3.unique h4
  have hhD : ∀ y ∈ O, ∀ j, (fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y) = 0 := by
    intro y hy j
    have h3 : HasFDerivAt (fun y => h j (g y)) ((fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y)) y :=
      (hha j (g y) (hVW (hgV y hy).1)).differentiableAt.hasFDerivAt.comp y
        (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => h j (g y)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) y :=
      (hasFDerivAt_const 0 y).congr_of_eventuallyEq
        (by filter_upwards [hOo.mem_nhds hy] with u hu using (hgV u hu).2 j)
    exact h3.unique h4

  have hC : ∀ c ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} ∩ O, ∀ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ c →
      (∀ᶠ u in 𝓝 c, u ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} → ψ u = 0) → fderiv ℂ ψ c = 0 := by
    rintro c ⟨⟨hcO, hcY⟩, -⟩ ψ hψ hψC
    have hzV := (hgV c hcO).1
    have hAz : A (g c) = c := hAg c hcO
    have hψ' : AnalyticAt ℂ ψ (A (g c)) := by rw [hAz]; exact hψ
    have hH : AnalyticAt ℂ (fun u => ψ (A u)) (g c) := hψ'.comp (A.analyticAt (g c))
    have hHY : ∀ᶠ u in 𝓝 (g c), u ∈ X ∩ B → ψ (A u) = 0 := by
      have hAt : Tendsto A (𝓝 (g c)) (𝓝 c) := by
        have h0 := A.continuous.tendsto (g c)
        rwa [hAz] at h0
      filter_upwards [hVo.mem_nhds hzV, hAt hψC] with u huV huψ huY
      obtain ⟨hgu, huO⟩ := hYV u huY huV
      exact huψ ⟨huO, hgu.symm ▸ huY⟩
    have hmem := hspan (g c) ⟨hVW hzV, hcY⟩ _ hH hHY
    have hchain : fderiv ℂ (fun u => ψ (A u)) (g c) = (fderiv ℂ ψ c).comp A := by
      have hψd : HasFDerivAt ψ (fderiv ℂ ψ c) (A (g c)) := by
        rw [hAz]; exact hψ.differentiableAt.hasFDerivAt
      exact (hψd.comp (g c) A.hasFDerivAt).fderiv
    have hkill : ∀ ℓ ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) (g c)),
        ℓ.comp (fderiv ℂ g c) = 0 := by
      intro ℓ hℓ
      induction hℓ using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hhD c hcO j
      | zero => simp
      | add x y _ _ hx hy => rw [ContinuousLinearMap.add_comp, hx, hy, add_zero]
      | smul r x _ hx =>
        rw [ContinuousLinearMap.smul_comp, hx]
        ext v
        simp
    have hk := hkill _ hmem
    rw [hchain, ContinuousLinearMap.comp_assoc, hAD c hcO, ContinuousLinearMap.comp_id] at hk
    exact hk

  have hvan : ∀ i, ∀ᶠ y in 𝓝 (A a), f i (g y) = 0 := by
    intro i
    refine eventually_zero_of_conormal_zero (C := {y | y ∈ O ∧ g y ∈ X ∩ B})
      ⟨hy₀O, hga.symm ▸ haY⟩ (hOo.mem_nhds hy₀O) hC ?_ ?_
    · have hfa : AnalyticAt ℂ (f i) (g (A a)) := hga.symm ▸ hf i a (hBN haY.2)
      exact hfa.comp (hg (A a) hy₀O)
    · refine Eventually.of_forall fun y hy => ?_
      have hgy : g y ∈ X ∩ N := ⟨hy.2.1, hBN hy.2.2⟩
      rw [hXN] at hgy
      exact hgy.2 i
  obtain ⟨O', hO'P, hO'o, hy₀O'⟩ :=
    eventually_nhds_iff.1 ((eventually_all.2 hvan).and (hOo.mem_nhds hy₀O))
  refine ⟨a, interior_subset (hWU haW).1, haY, d, A, O', V ∩ A ⁻¹' O', g, hO'o,
    hVo.inter (hO'o.preimage A.continuous), ⟨haV, hy₀O'⟩, hg.mono fun y hy => (hO'P y hy).2,
    fun y hy => hAg y (hO'P y hy).2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzY, hzV, hzO'⟩
    exact ⟨A z, hzO', (hYV z hzY hzV).1⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hf0, hyO⟩ := hO'P y hy
    have hgyV := (hgV y hyO).1
    have hgB : g y ∈ B := (hWU (hVW hgyV)).2
    have hgX : g y ∈ X := by
      have hz : g y ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN hgB, hf0⟩
      rw [← hXN] at hz
      exact hz.1
    refine ⟨⟨hgX, hgB⟩, hgyV, ?_⟩
    show A (g y) ∈ O'
    rw [hAg y hyO]
    exact hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
