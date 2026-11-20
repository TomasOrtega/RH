import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

/- English proof (translation)
Proceed by induction on `hη using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, v, hv, rfl⟩` from `hx`. Rewrite using `[smul_smul]`. Conclude with `AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Take `⟨e, hG⟩` from `G.exists_isEqn y`. Establish `hGD` using `hG.add hD`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `G.RegularAt y _`. Express the relevant statement in the definitionally equal form `(G + D).RegularAt y c at hc`. Rewrite using `[hG.regularAt_iff]`. Rewrite `hc` using `[hGD.regularAt_iff, Units.val_mul]`. Use `hc using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Establish `h'` using `smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹ (fun c hc => ?_) h`. Rewrite `h'` using `[inv_smul_smul₀ g.ne_zero]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `(G + D).RegularAt y _`.

Express the relevant statement in the definitionally equal form `G.RegularAt y c at hc`. Rewrite using `[hGD.regularAt_iff, Units.val_mul]`. Rewrite `hc` using `[hG.regularAt_iff]`. Use `hc using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.
-/
theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

/- English proof (translation)
Introduce `X _ Z G D a y g η hD` and use `mem_logAt_add_iff Z G D a y g η hD`.
-/
theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
