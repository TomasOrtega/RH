import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv`. Establish `hopen : IsOpen (A.chart i).target` using `(A.chart i).open_target`. Establish `hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v`. Introduce `a`. Establish `h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target` using `C.smooth a i`.

Establish `h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v` using `(h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)`. Conclude with `ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2`. Establish `key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) * A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧ wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) * A.g (A.kap + la) i (C.idx a) ((A.chart i).symm …`. Introduce `a`. Distinguish the cases in `hs : (A.chart i).symm v ∈ tsupport (C.chi a)`.

Establish `hsrc` using `(C.supp a hs).1`. Establish `hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a)` using `(C.supp a hs).2`. Establish `hovl : IsOpen (ovl A.chart i (C.idx a))` using `(A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source`. Establish `hmem : v ∈ ovl A.chart i (C.idx a)` using `⟨hv, hsrc⟩`. Establish `hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v` using `(A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)`.

Establish `htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v` using `(A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)`. Establish `hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v))` using `(hu a).differentiableAt (isOpen_ball.mem_nhds hball)`. Establish `hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A.chart i).symm x))) v` using `hg.mul (hua.comp v htr)`. Establish `heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) * A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A.chart i).symm x))) = (fun x => (C.chi a ((A.chart i).symm x) : ℂ) * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A. …`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ), ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v` using `((A.chart i).continuousAt_symm hv).preimage_mem_nhds ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)`. Establish `hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0` using `Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx`. Establish `hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) * A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ)` using `hz.mono fun x hx => by simp [hx]`. Establish `hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ)` using `hz.mono fun x hx => by simp [hx]`. Establish `hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0` using `ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)`.

Use `⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]`. Establish `hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) * A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) * u a (A.chart (C.idx a) ((A.chart i).symm x))`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.

Establish `hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[← Complex.ofReal_sum, C.sum_one]`. Simplify using the standard rewrite rules. Establish `hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0`.

Rewrite using `[← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]`. Conclude with `ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)`. Rewrite using `[hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]`. Repeatedly rewrite using `[mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]`. Conclude with `Finset.sum_congr rfl fun a _ => (key a).2`.
-/
theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
