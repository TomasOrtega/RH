import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialPullbackGivesUnitCocycleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsLocalIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPointStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftMinimalGeneratorsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

/- English proof (translation)
Establish `gen` using `GlobalTheory.T.cocycle_units_trivialize_modulo_ideal`. Establish `data` using `GlobalTheory.T.trivial_pullback_gives_unit_cocycle`. Establish `mingens` using `GlobalTheory.T.minimal_generators_local_ideal`. Establish `flat` using `GlobalTheory.T.minimal_generators_base_change`. Establish `dep` using `GlobalTheory.T.dependency_statement`.

Establish `fibre` using `GlobalTheory.T.first_cohomology_rank_bound_at_closed_point`. Establish `cocycle` using `GlobalTheory.T.unit_cocycle_lift_modulo_maximal`. Establish `finish` using `GlobalTheory.T.unit_cocycle_lift_minimal_generators`. Introduce `R _ _ _ X s n hsm hpr hF M hM I hI hJ`. Establish `hIm : I ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal hI`.

Take `⟨r, t, ht, hmin⟩` from `mingens R I`. Establish `hsep : X.IsSeparated`. Establish `: IsSeparated (s ≫ terminal.from (Sp R))` using `inferInstance`. Rewrite `this` using `[Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)]`. Conclude with `⟨this⟩`.

Use `haveI : Flat s := inferInstance`. Set `A` to `{q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}`. Set `V : A → X.Opens` to `fun a => a.1.2`. Set `j : A → M.ι` to `fun a => a.1.1`. Establish `hj : ∀ a, V a ≤ M.U (j a)` using `fun a => a.2.2`.

Establish `hA : ∀ a, IsAffineOpen (V a)` using `fun a => a.2.1`. Establish `hAA : ∀ a b, IsAffineOpen (V a ⊓ V b)` using `fun a b => (hA a).inf (hA b)`. Establish `hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d)` using `fun a b d => (hAA a b).inf (hA d)`. Establish `hV : ⨆ a, V a = ⊤`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x`. Take `⟨W, hW, hxW, hle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩`. Establish `hsq : I * I ≤ IsLocalRing.maximalIdeal R * I` using `Ideal.mul_mono_left hIm`. It suffices to establish `hrn : r ≤ n by`.

Use `⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `h : i.1 < r`. Simplify using `only [h, dif_pos]`.

Rewrite using `[← ht]`. Conclude with `Ideal.subset_span ⟨_, rfl⟩`. Simplify using `only [h, dif_neg, not_false_eq_true]`. Conclude with `zero_mem _`. Rewrite using `[← ht, Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hrn`. Take `⟨u, z, hz, hc⟩` from `data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)`.

Set `w : ∀ a, Γ(X, V a)` to `fun a => z a * (2 - u a * z a)`. Establish `hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)` using `fun a => by`. Establish `h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)`. Use `Ideal.map_mono hsq ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_mul]`.

Conclude with `Ideal.mul_mem_mul (hz a) (hz a)`. Establish `: u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1))` using `by simp only [w]; ring`. Rewrite using `[this]`. Conclude with `neg_mem h2`. Take `⟨b, hb1, hb2⟩` from `cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc`.

Establish `hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)` using `fun i a c d => flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i`. Take `⟨e, β, ⟨l, hl⟩, he⟩` from `fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3`. Take `⟨J, y, z', hIJ, hy1, hy2⟩` from `finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he`. Conclude with `hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))`.
-/
theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := GlobalTheory.T.trivial_pullback_gives_unit_cocycle
  have mingens := GlobalTheory.T.minimal_generators_local_ideal
  have flat := GlobalTheory.T.minimal_generators_base_change
  have dep := GlobalTheory.T.dependency_statement
  have fibre := GlobalTheory.T.first_cohomology_rank_bound_at_closed_point
  have cocycle := GlobalTheory.T.unit_cocycle_lift_modulo_maximal
  have finish := GlobalTheory.T.unit_cocycle_lift_minimal_generators
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
