import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

namespace GlobalTheory.LogDR

/- English proof (translation)
Introduce `X _ Z G a y f η hf hη`. Unfold `logAt spanForms at hη ⊢`. Proceed by induction on `hη using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, v, hv, rfl⟩` from `hx`.

Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨f * c, ?_, v, hv, ?_⟩` and prove the remaining obligations. Conclude with `(show G.RegularAt y c from hc).regAt_mul hf`. Rewrite using `[smul_smul]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `AddSubgroup.add_mem _ hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `AddSubgroup.neg_mem _ hx`.
-/
theorem logAt_smul_mem : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X)
    (f : X.functionField) (η : abelian₂ X.functionField), RegAt y f → η ∈ logAt Z G a y → f • η ∈ logAt Z G a y := by
  intro X _ Z G a y f η hf hη
  unfold logAt spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨f * c, ?_, v, hv, ?_⟩
    · exact (show G.RegularAt y c from hc).regAt_mul hf
    · rw [smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LogDR
