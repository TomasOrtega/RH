import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.UnifDim

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

/- English proof (translation)
Establish `hinj` using `AnyUnif.injective_of_ker_le_discrete Λ F fun z hz => by`. Rewrite using `[← hk, ← hF, hz]`. Conclude with `(hk' 0).2 Λ'.zero_mem`. Establish `hsurj : LinearMap.range F = ⊤` using `AHWeil.eq_top_of_add_discrete Λ' _ fun w => by`. Take `⟨z, hz⟩` from `hon (e' w)`.

Use `⟨⟨w - F z, (hk' _).1 ?_⟩, z, by simp⟩` and prove the remaining obligations. Establish `h` using `he' (w - F z) (F z)`. Rewrite `h` using `[sub_add_cancel, hF, hz]`. Conclude with `(mul_eq_right.1 h.symm)`. Simplify using `using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq`.
-/
theorem eq_of_linear_lift {M : Type*} [Group M] {g d : ℕ} (e : (Fin g → ℂ) → M)
    (e' : (Fin d → ℂ) → M) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hon : Function.Surjective e) (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin d → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hk' : ∀ z, e' z = 1 ↔ z ∈ Λ')
    [DiscreteTopology Λ] [DiscreteTopology Λ']
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (hF : ∀ z, e' (F z) = e z) : g = d := by
  have hinj := AnyUnif.injective_of_ker_le_discrete Λ F fun z hz => by
    rw [← hk, ← hF, hz]
    exact (hk' 0).2 Λ'.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete Λ' _ fun w => by
    obtain ⟨z, hz⟩ := hon (e' w)
    refine ⟨⟨w - F z, (hk' _).1 ?_⟩, z, by simp⟩
    have h := he' (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

/- English proof (translation)
Introduce `U f` and use `by simpa only [Set.mem_univ, true_and] using u.hol U f`.
-/
theorem holOn_ex (u : HolUnif A L g) : HolOn Set.univ u.ex := fun U f => by
  simpa only [Set.mem_univ, true_and] using u.hol U f

/- English proof (translation)
Establish `hc : Continuous u.ex` using `continuous_iff_continuousAt.2 fun z => (holOn_ex u).continuousAt (Set.mem_univ z)`. Use `haveI := u.discrete`. Use `haveI := holUnif_isZLattice u`. Use `haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ`. Use `haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ`.

Set `b` to `(Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ`. Establish `hK : IsCompact (closure (ZSpan.fundamentalDomain b))` using `Metric.isCompact_of_isClosed_isBounded isClosed_closure (ZSpan.fundamentalDomain_isBounded b).closure`. Use `isCompact_univ_iff.1 ((hK.image hc).of_isClosed_subset isClosed_univ fun x _ => ?_)` and prove the remaining obligations. Take `⟨z, rfl⟩` from `u.ex_onto x`. Use `⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩` and prove the remaining obligations.

Establish `hm : ((ZSpan.floor b z : _) : Fin g → ℂ) ∈ u.Λ`. Establish `e` using `Module.Basis.ofZLatticeBasis_span ℝ u.Λ (Module.Free.chooseBasis ℤ u.Λ)`. Conclude with `e.le (ZSpan.floor b z).2`. Establish `h` using `u.ex_add (ZSpan.fract b z) (ZSpan.floor b z)`. Rewrite `h` using `[(u.ker _).2 hm, _root_.mul_one, ZSpan.fract_apply, sub_add_cancel]`.

Rewrite using `[ZSpan.fract_apply]`. Conclude with `h.symm`.
-/
theorem compactSpace_points (u : HolUnif A L g) : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have hc : Continuous u.ex :=
    continuous_iff_continuousAt.2 fun z => (holOn_ex u).continuousAt (Set.mem_univ z)
  haveI := u.discrete
  haveI := holUnif_isZLattice u
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (ZSpan.fundamentalDomain_isBounded b).closure
  refine isCompact_univ_iff.1 ((hK.image hc).of_isClosed_subset isClosed_univ fun x _ => ?_)
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
  have hm : ((ZSpan.floor b z : _) : Fin g → ℂ) ∈ u.Λ := by
    have e := Module.Basis.ofZLatticeBasis_span ℝ u.Λ (Module.Free.chooseBasis ℤ u.Λ)
    exact e.le (ZSpan.floor b z).2
  have h := u.ex_add (ZSpan.fract b z) (ZSpan.floor b z)
  rw [(u.ker _).2 hm, _root_.mul_one, ZSpan.fract_apply, sub_add_cancel] at h
  rw [ZSpan.fract_apply]
  exact h.symm

/- English proof (translation)
Introduce `A _ L g d u hd`. Use `letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) := { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with mul_comm := fun a b ↦ by`. Take `⟨z, rfl⟩` from `u.ex_onto a`. Take `⟨w, rfl⟩` from `u.ex_onto b`. Conclude with `(u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }`.

Establish `hval` using `@valAt'_rules`. Establish `hprod` using `@holFamily_lift hval`. Establish `htop` using `@isTopologicalGroup_complexPoints hval`. Establish `hchart` using `@HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom) (@exists_holomorphic_section_of_etale)`. Use `htop A` as an intermediate fact.

Use `compactSpace_points u` as an intermediate fact. Establish `hpost` using `fun X x => (hval X x).2.2.2.1`. Establish `hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w` using `fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]`. Take `⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩` from `hchart A d hd 1`. Set `φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin d → ℂ)` to `chart t hW hσ ht ho`.

Establish `hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U` using `hσ0 ▸ (ht 0 h0).1`. Establish `hφ : IsAnalyticGroupChart φ`. Use `⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(ht 0 h0).2 i` as an intermediate fact. Rewrite `this` using `[hσ0]`. Then use the resulting hypothesis.

Establish `hH` using `hmulHol _ (W ×ˢ W) _ _ (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1) (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)`. Use `hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_` and prove the remaining obligations. Simplify `hU1` using `only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one]`. Establish `hsurj : Function.Surjective hφ.exp` using `hφ.exp_surjective fun n hn x => by`. Take `⟨z, hz⟩` from `u.ex_onto x.toMul`.

Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Use `⟨Additive.ofMul (u.ex ((n : ℂ)⁻¹ • z)), ?_⟩` and prove the remaining obligations. Establish `h1 : n • ((n : ℂ)⁻¹ • z) = z`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]`. Establish `h2` using `holUnif_ex_nsmul_eq_pow u ((n : ℂ)⁻¹ • z) n`.

Rewrite `h2` using `[h1, hz]`. Rewrite using `[← ofMul_pow, ← h2]`. Both sides reduce to the same expression. Establish `hu` using `holOn_ex u`. Establish `hu0 : u.ex 0 = 1` using `holUnif_ex_zero_eq_one u`.

Establish `h1 : φ (u.ex 0) = 0` using `by rw [hu0]; exact hφ.map_zero`. Establish `h2 : AnalyticAt ℂ (fun w => φ (u.ex w)) 0` using `hu.analyticAt t (Set.mem_univ _) (hu0 ▸ hU1)`. Establish `hG0 : hφ.log (φ (u.ex 0)) = 0`. Simplify using `only [h1]`. Conclude with `hφ.isLocalCommGroupLaw.log_zero`.

Establish `hGa : AnalyticAt ℂ (fun w => hφ.log (φ (u.ex w))) 0` using `AnalyticAt.comp (g := hφ.log) (h1 ▸ hφ.isLocalCommGroupLaw.analyticAt_log) h2`. Establish `hGe : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (hφ.exp (hφ.log (φ (u.ex w)))).toMul = u.ex w`. Establish `h3 : Tendsto u.ex (𝓝 0) (𝓝 1)` using `hu0 ▸ (hu.continuousAt (Set.mem_univ 0)).tendsto`. Conclude with `h3.eventually hφ.exp_log`. Establish `hF` using `EndoLinear.fderiv_lifts (fun v => (hφ.exp v).toMul) (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) hφ.periodLattice (fun z => Iff.rfl) inferInstance u.ex u.ex_add _ hG0 hGa.differentiableAt hGe`.

Use `haveI := u.discrete`. Conclude with `eq_of_linear_lift u.ex (fun v => (hφ.exp v).toMul) (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) u.ex_onto u.Λ hφ.periodLattice u.ker (fun z => Iff.rfl) (fderiv ℂ (fun w => hφ.log (φ (u.ex w))) 0).toLinearMap hF`.
-/
theorem eq_relativeDimension : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ)
    (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  intro A _ L g d u hd
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := htop A
  have := compactSpace_points u
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A d hd 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin d → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => by
    obtain ⟨z, hz⟩ := u.ex_onto x.toMul
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine ⟨Additive.ofMul (u.ex ((n : ℂ)⁻¹ • z)), ?_⟩
    have h1 : n • ((n : ℂ)⁻¹ • z) = z := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    have h2 := holUnif_ex_nsmul_eq_pow u ((n : ℂ)⁻¹ • z) n
    rw [h1, hz] at h2
    rw [← ofMul_pow, ← h2]
    rfl
  have hu := holOn_ex u
  have hu0 : u.ex 0 = 1 := holUnif_ex_zero_eq_one u
  have h1 : φ (u.ex 0) = 0 := by rw [hu0]; exact hφ.map_zero
  have h2 : AnalyticAt ℂ (fun w => φ (u.ex w)) 0 :=
    hu.analyticAt t (Set.mem_univ _) (hu0 ▸ hU1)
  have hG0 : hφ.log (φ (u.ex 0)) = 0 := by
    simp only [h1]
    exact hφ.isLocalCommGroupLaw.log_zero
  have hGa : AnalyticAt ℂ (fun w => hφ.log (φ (u.ex w))) 0 :=
    AnalyticAt.comp (g := hφ.log) (h1 ▸ hφ.isLocalCommGroupLaw.analyticAt_log) h2
  have hGe : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (hφ.exp (hφ.log (φ (u.ex w)))).toMul = u.ex w := by
    have h3 : Tendsto u.ex (𝓝 0) (𝓝 1) := hu0 ▸ (hu.continuousAt (Set.mem_univ 0)).tendsto
    exact h3.eventually hφ.exp_log
  have hF := EndoLinear.fderiv_lifts (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) hφ.periodLattice (fun z => Iff.rfl)
    inferInstance u.ex u.ex_add _ hG0 hGa.differentiableAt hGe
  haveI := u.discrete
  exact eq_of_linear_lift u.ex (fun v => (hφ.exp v).toMul)
    (fun z w => congrArg Additive.toMul (hφ.exp.map_add z w)) u.ex_onto u.Λ hφ.periodLattice u.ker
    (fun z => Iff.rfl) (fderiv ℂ (fun w => hφ.log (φ (u.ex w))) 0).toLinearMap hF

end GlobalTheory.CompanionTheory.Ar.UnifDim
