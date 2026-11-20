import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotZero

/- English proof (translation)
Use `haveI : LocallyCompactSpace R := hR.locallyCompactSpace`. Use `haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)`. Use `haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance`. Use `⟨fun r hr x => h.left hr x, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `h.unique hR IsQuotIntL1.zero`.
-/
theorem left_and_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {R : Subgroup G}
    (hR : IsClosed (R : Set G)) (μR : Measure R) [μR.IsHaarMeasure] [μR.IsInvInvariant]
    (μG : Measure G) [μG.IsHaarMeasure] {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 μR μG f z) :
    (∀ r ∈ R, ∀ x, f (r * x) = f x) ∧ (f = 0 → z = 0) := by
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  refine ⟨fun r hr x => h.left hr x, ?_⟩
  rintro rfl
  exact h.unique hR IsQuotIntL1.zero

open scoped Pointwise Topology in

/- English proof (translation)
Take `⟨K, hKn, hK⟩` from `local_compact_nhds (x := (1 : R)) (n := Set.univ) Filter.univ_mem`. Establish `hKc : IsCompact K` using `hK.2`. Rewrite `hKn` using `[nhds_subtype, Filter.mem_comap]`. Take `⟨U, hU, hUK⟩` from `hKn`. Take `⟨V, hVo, hV1, hVV⟩` from `exists_open_nhds_one_mul_subset hU`.

Use `set W : Set G := V ∩ V⁻¹`. Establish `hWo : IsOpen W` using `hVo.inter hVo.inv`. Establish `hW1 : (1 : G) ∈ W` using `⟨hV1, by simpa using hV1⟩`. Use `set K' : Set G := Subtype.val '' K`. Establish `hK'c : IsCompact K'` using `hKc.image continuous_subtype_val`.

Establish `hK'R : K' ⊆ R` using `by rintro _ ⟨k, -, rfl⟩; exact k.2`. Use `isClosed_of_closure_subset fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hyW, hyR⟩` from `mem_closure_iff.1 hx (x • W) (hWo.smul x) (by simpa using Set.smul_mem_smul_set (a := x) hW1)`. Take `⟨v₁, hv₁, rfl⟩` from `hyW`. Establish `hsub : (x • W) ∩ (R : Set G) ⊆ (x • v₁) • K'`.

Introduce and unpack `r ⟨⟨v₂, hv₂, rfl⟩, hr⟩`. Establish `hm : v₁⁻¹ * v₂ ∈ U` using `hVV (Set.mul_mem_mul (by simpa using hv₁.2) hv₂.1)`. Establish `hmR : v₁⁻¹ * v₂ ∈ R`. Use `R.mul_mem (R.inv_mem hyR) hr` as an intermediate fact. Simplify `this` using `[smul_eq_mul, mul_assoc]`.

Use `⟨v₁⁻¹ * v₂, ⟨⟨v₁⁻¹ * v₂, hmR⟩, hUK hm, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[smul_eq_mul, mul_assoc]`. Establish `hx' : x ∈ closure ((x • W) ∩ (R : Set G))` using `(hWo.smul x).inter_closure ⟨by simpa using Set.smul_mem_smul_set (a := x) hW1, hx⟩`. Establish `hcl : IsClosed ((x • v₁) • K')` using `(hK'c.smul _).isClosed`. Use `closure_minimal hsub hcl hx'` as an intermediate fact.

Take `⟨k, hk, hkx⟩` from `this`. Simplify using `only [smul_eq_mul] at hkx hyR`. Rewrite using `[← hkx]`. Conclude with `R.mul_mem hyR (hK'R hk)`.
-/
theorem isClosed_of_locallyCompactSpace {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (R : Subgroup G) [LocallyCompactSpace R] : IsClosed (R : Set G) := by
  obtain ⟨K, hKn, hK⟩ := local_compact_nhds (x := (1 : R)) (n := Set.univ) Filter.univ_mem
  have hKc : IsCompact K := hK.2
  rw [nhds_subtype, Filter.mem_comap] at hKn
  obtain ⟨U, hU, hUK⟩ := hKn
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU
  set W : Set G := V ∩ V⁻¹
  have hWo : IsOpen W := hVo.inter hVo.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  set K' : Set G := Subtype.val '' K
  have hK'c : IsCompact K' := hKc.image continuous_subtype_val
  have hK'R : K' ⊆ R := by rintro _ ⟨k, -, rfl⟩; exact k.2
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨y, hyW, hyR⟩ := mem_closure_iff.1 hx (x • W) (hWo.smul x) (by simpa using Set.smul_mem_smul_set (a := x) hW1)
  obtain ⟨v₁, hv₁, rfl⟩ := hyW
  have hsub : (x • W) ∩ (R : Set G) ⊆ (x • v₁) • K' := by
    rintro r ⟨⟨v₂, hv₂, rfl⟩, hr⟩
    have hm : v₁⁻¹ * v₂ ∈ U := hVV (Set.mul_mem_mul (by simpa using hv₁.2) hv₂.1)
    have hmR : v₁⁻¹ * v₂ ∈ R := by
      have := R.mul_mem (R.inv_mem hyR) hr
      simpa [smul_eq_mul, mul_assoc] using this
    refine ⟨v₁⁻¹ * v₂, ⟨⟨v₁⁻¹ * v₂, hmR⟩, hUK hm, rfl⟩, ?_⟩
    simp [smul_eq_mul, mul_assoc]
  have hx' : x ∈ closure ((x • W) ∩ (R : Set G)) :=
    (hWo.smul x).inter_closure ⟨by simpa using Set.smul_mem_smul_set (a := x) hW1, hx⟩
  have hcl : IsClosed ((x • v₁) • K') := (hK'c.smul _).isClosed
  have := closure_minimal hsub hcl hx'
  obtain ⟨k, hk, hkx⟩ := this
  simp only [smul_eq_mul] at hkx hyR
  rw [← hkx]
  exact R.mul_mem hyR (hK'R hk)

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, -, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W`. Take `⟨j1, j2, j3, j4, j5, -, j7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀`. Take `⟨hN, h𝓝, h𝓝1⟩` from `J.vN.unit`. Take `⟨K, hK, hcov⟩` from `J.cpt`. Establish `hμ` using `J.v0.haar`.

Take `⟨p, hpc, hp⟩` from `GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d`. Establish `hNc` using `GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)`. Use `haveI : LocallyCompactSpace (flagN J.d) := hNc.locallyCompactSpace`. Take `⟨e, -⟩` from `GlobalTheory.SemiHaar.exists_homeo (flagN J.d) J.d.emb0 (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 J.d.continuous_embed ⟨p, hpc, hp⟩`. Use `haveI : LocallyCompactSpace (jacGrp J.d) := e.symm.isClosedEmbedding.locallyCompactSpace`.

Use `⟨isClosed_of_locallyCompactSpace (jacGrp J.d), ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN J.d) J.d.emb0 hNc J.d.continuous_embed (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩ (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝 (by rw …`.
-/
theorem jac_haar_inv {D : D7} {ρ : ℕ} (J : JacLev D ρ) :
    IsClosed (jacGrp J.d : Set (GA D J.W)) ∧ J.μR.IsHaarMeasure ∧ J.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hNc := GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)
  haveI : LocallyCompactSpace (flagN J.d) := hNc.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN J.d) J.d.emb0 (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1
    J.d.continuous_embed ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (jacGrp J.d) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (jacGrp J.d), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN J.d) J.d.emb0 hNc J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, -, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V`. Take `⟨j1, j2, j3, j4, j5, -, j7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A`. Take `⟨hN, h𝓝, h𝓝1⟩` from `B.vN.unit`. Take `⟨K, hK, hcov⟩` from `B.cpt`. Establish `hμ` using `B.vA.haar`.

Take `⟨p, hpc, hp⟩` from `GlobalTheory.BesProj.exists_continuous_proj D B.V B.V₀ B.A B.L ρ B.d B.o`. Take `⟨hc, hcl, hnorm, -, hrat⟩` from `GlobalTheory.Unf.besSemi D ρ B`. Establish `hΛ : ∀ δ ∈ GQ B.A, embA B.d B.o δ ∈ GQ B.V` using `fun δ hδ => by`. Simplify using `using (hrat 1 (one_mem _) δ).2 ⟨one_mem _, hδ⟩`. Use `haveI : LocallyCompactSpace (flagN B.d) := hcl.locallyCompactSpace`.

Take `⟨e, -⟩` from `GlobalTheory.SemiHaar.exists_homeo (flagN B.d) (embA B.d B.o) hnorm hc ⟨p, hpc, hp⟩`. Use `haveI : LocallyCompactSpace (besGrp B.d B.o) := e.symm.isClosedEmbedding.locallyCompactSpace`. Use `⟨isClosed_of_locallyCompactSpace (besGrp B.d B.o), ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN B.d) (embA B.d B.o) hcl hc hnorm ⟨p, hpc, hp⟩ (GQ B.V) (GQ B.A) hΛ hK hcov B.vA.μ B.vA.fund B.vN.ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)`.
-/
theorem bes_haar_inv {D : D7} {ρ : ℕ} (B : BesLev D ρ) :
    IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ B.μR.IsHaarMeasure ∧ B.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨hN, h𝓝, h𝓝1⟩ := B.vN.unit
  obtain ⟨K, hK, hcov⟩ := B.cpt
  have hμ := B.vA.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.BesProj.exists_continuous_proj D B.V B.V₀ B.A B.L ρ B.d B.o
  obtain ⟨hc, hcl, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hΛ : ∀ δ ∈ GQ B.A, embA B.d B.o δ ∈ GQ B.V := fun δ hδ => by
    simpa using (hrat 1 (one_mem _) δ).2 ⟨one_mem _, hδ⟩
  haveI : LocallyCompactSpace (flagN B.d) := hcl.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN B.d) (embA B.d B.o) hnorm hc ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (besGrp B.d B.o) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (besGrp B.d B.o), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN B.d) (embA B.d B.o) hcl hc hnorm ⟨p, hpc, hp⟩
    (GQ B.V) (GQ B.A) hΛ hK hcov B.vA.μ B.vA.fund B.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

end GlobalTheory.QuotZero
