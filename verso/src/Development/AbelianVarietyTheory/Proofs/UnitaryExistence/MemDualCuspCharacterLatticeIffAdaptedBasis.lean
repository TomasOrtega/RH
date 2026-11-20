import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Unfold `FJ.crdI at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`.

Take `⟨a, ha, x, hx, hax⟩` from `hv`. Rewrite using `[← h, ← hax]`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)`. Rewrite using `[algebraMap_smul]`. Conclude with `X.Λ.smul_mem o hx.1`.

Consider the case `zero => exact fun b => (cc' b).zero_mem`. Consider the case `add x y _ _ hx hy`. Conclude with `fun b => FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))`. Consider the case `smul c x _ hx`. Conclude with `fun b => FractionalIdeal.mem_coe.1 (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))`.

Introduce `hv`. Use `Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _), ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩` and prove the remaining obligations. Conclude with `(show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`.
-/
theorem mem_crdI_one_iff_of_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    {X : Data E r} (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (h : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) (v : Fin ρ → E) :
    v ∈ FJ.crdI 1 cu ↔ ∀ b, v b ∈ cc' b := by
  constructor
  · intro hv
    unfold FJ.crdI at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, hax⟩ := hv
      rw [← h, ← hax]
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)
      rw [algebraMap_smul]
      exact X.Λ.smul_mem o hx.1
    | zero => exact fun b => (cc' b).zero_mem
    | add x y _ _ hx hy =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))
    | smul c x _ hx =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))
  · intro hv
    refine Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _),
      ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩
    exact (show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/- English proof (translation)
Introduce `E _ _ _ r ρ X cu cc' h u`. Establish `hc` using `mem_crdI_one_iff_of_adapted cu cc' h`. Prove the components needed by the constructor for the conclusion. Introduce `hu a y hy`. Establish `hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu`.

Use `Submodule.subset_span fun x hx => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `hy (x a) ((hc x).1 hx a)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Use `congr 1`.

Simplify using `[Pi.single_apply]`. Establish `h2` using `hu _ hm`. Simplify `h2` using `[Pi.single_apply]`. Introduce `hu x hx`. Express the relevant statement in the definitionally equal form `∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range`.

Unfold `FJ.XcFD at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Use `sum_mem fun i _ => hu i (x i) fun a' ha' => ?_` and prove the remaining obligations. Establish `hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu`.

Rewrite using `[hc]`. Introduce `b`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Simplify using `using ha'`.

Rewrite using `[Pi.single_eq_of_ne hb]`. Conclude with `(cc' b).zero_mem`. Take `⟨n, hn⟩` from `hx _ hm`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`.

Use `congr 1`. Simplify using `[Pi.single_apply]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem ⟨c, rfl⟩ hx`.
-/
theorem mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  intro E _ _ _ r ρ X cu cc' h u
  have hc := mem_crdI_one_iff_of_adapted cu cc' h
  constructor
  · intro hu a y hy
    have hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu := by
      refine Submodule.subset_span fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (x a) ((hc x).1 hx a)
      refine ⟨n, ?_⟩
      rw [← hn]
      congr 1
      simp [Pi.single_apply]
    have h2 := hu _ hm
    simpa [Pi.single_apply] using h2
  · intro hu x hx
    change ∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range
    unfold FJ.XcFD at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine sum_mem fun i _ => hu i (x i) fun a' ha' => ?_
      have hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu := by
        rw [hc]
        intro b
        by_cases hb : b = i
        · subst hb; simpa using ha'
        · rw [Pi.single_eq_of_ne hb]; exact (cc' b).zero_mem
      obtain ⟨n, hn⟩ := hx _ hm
      refine ⟨n, ?_⟩
      rw [hn]
      congr 1
      simp [Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul c x _ hx =>
      have e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [e]
      exact mul_mem ⟨c, rfl⟩ hx

end GlobalTheory
