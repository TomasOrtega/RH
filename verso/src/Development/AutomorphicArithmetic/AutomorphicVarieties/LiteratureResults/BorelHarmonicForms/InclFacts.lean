import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ a π Ξ r`. Establish `hA : ∀ X m, incl π Ξ (lieA π Ξ X m) = smA Ξ X (incl π Ξ m)` using `fun X m => by`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul φ v => rfl`. Establish `hB : ∀ X m, incl π Ξ (lieB π Ξ X m) = smB Ξ X (incl π Ξ m)` using `fun X m => by`. Rewrite using `[smB_apply]`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul φ v => rfl`. Use `⟨?_, fun i m => ?_, fun k m => ?_, fun X m => ?_, fun X m => ?_⟩` and prove the remaining obligations. Conclude with `Module.Flat.rTensor_preserves_injective_linearMap _ π.V.injective_subtype`. Proceed by induction on `m using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Both sides reduce to the same expression. Consider the case `tmul φ v`.

Rewrite using `[cmp_tmul]`. Conclude with `cmp_tmul i φ.1 v`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul φ v => rfl`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul φ v => rfl`.

Rewrite using `[piAdj, smAdj, adj_apply, adj_apply, map_sub, map_sub, hA, hB, LinearMap.map_smul_of_tower]`.
-/
theorem UpperTheory.V.Lit.Bor.inclFacts :
    UpperTheory.V.Lit.Bor.InclFacts := by
  intro E _ _ _ a π Ξ r
  have hA : ∀ X m, incl π Ξ (lieA π Ξ X m) = smA Ξ X (incl π Ξ m) := fun X m => by
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  have hB : ∀ X m, incl π Ξ (lieB π Ξ X m) = smB Ξ X (incl π Ξ m) := fun X m => by
    rw [smB_apply]
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  refine ⟨?_, fun i m => ?_, fun k m => ?_, fun X m => ?_, fun X m => ?_⟩
  · exact Module.Flat.rTensor_preserves_injective_linearMap _ π.V.injective_subtype
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul φ v =>
      rw [cmp_tmul]
      exact cmp_tmul i φ.1 v
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  · rw [piAdj, smAdj, adj_apply, adj_apply, map_sub, map_sub, hA, hB, LinearMap.map_smul_of_tower]
