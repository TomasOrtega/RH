import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

/- English proof (translation)
Use `hU.completeSpace` as an intermediate fact. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Apply `h0` to reduce the goal to its premises. Establish `hle : isoPart δ π ⊤ ≤ Uᗮ` using `isoPart_le U.isClosed_orthogonal fun T hT x => by`.

Establish `hS : U.starProjection ∘L T ∈ homIn δ π U` using `⟨fun x => U.starProjection_apply_mem _, fun g x => by`. Simplify using `only [comp_apply, hT.2 g x, hU.starProjection_apply hπ]⟩`. Use `DFunLike.congr_fun (hn _ hS) x` as an intermediate fact. Rewrite `this` using `[comp_apply, zero_apply]`. Conclude with `(Submodule.starProjection_apply_eq_zero_iff _).1 this`.

Rewrite `hle` using `[hiso, top_le_iff, Submodule.orthogonal_eq_top_iff]`. Conclude with `hle`.
-/
theorem exists_homIn_ne_zero (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) {U : Submodule ℂ H}
    (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ S ∈ homIn δ π U, S ≠ 0 := by
  have := hU.completeSpace
  by_contra hn
  push_neg at hn
  apply h0
  have hle : isoPart δ π ⊤ ≤ Uᗮ := isoPart_le U.isClosed_orthogonal fun T hT x => by
    have hS : U.starProjection ∘L T ∈ homIn δ π U :=
      ⟨fun x => U.starProjection_apply_mem _, fun g x => by
        simp only [comp_apply, hT.2 g x, hU.starProjection_apply hπ]⟩
    have := DFunLike.congr_fun (hn _ hS) x
    rw [comp_apply, zero_apply] at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 this
  rw [hiso, top_le_iff, Submodule.orthogonal_eq_top_iff] at hle
  exact hle

/- English proof (translation)
Take `⟨S, hS, hS0⟩` from `exists_homIn_ne_zero hπ hiso hU h0`. Conclude with `⟨_, by rintro _ ⟨x, rfl⟩; exact hS.1 x, isCopy_range hδ hπ hS hS0⟩`.
-/
theorem exists_isCopy_le (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {U : Submodule ℂ H} (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ W ≤ U, IsCopy δ π W := by
  obtain ⟨S, hS, hS0⟩ := exists_homIn_ne_zero hπ hiso hU h0
  exact ⟨_, by rintro _ ⟨x, rfl⟩; exact hS.1 x, isCopy_range hδ hπ hS hS0⟩

/- English proof (translation)
Take `⟨V, hVW, hV⟩` from `exists_isCopy_le hδ hπ hiso hW.1 hW.2.1`. Establish `hV'` using `hV.isIrredSubrep hδ.irred`. Break down `hW.2.2 V hVW hV'.1 with h | h` into its components or cases. Conclude with `absurd h hV'.2.1`. Conclude with `h ▸ hV`.
-/
theorem isCopy_of_isIrredSubrep (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {W : Submodule ℂ H} (hW : IsIrredSubrep π W) : IsCopy δ π W := by
  obtain ⟨V, hVW, hV⟩ := exists_isCopy_le hδ hπ hiso hW.1 hW.2.1
  have hV' := hV.isIrredSubrep hδ.irred
  rcases hW.2.2 V hVW hV'.1 with h | h
  · exact absurd h hV'.2.1
  · exact h ▸ hV

/- English proof (translation)
Take `⟨ι, W, hW, hs⟩` from `GlobalTheory.DiscreteSum.exists_isHilbertSum hπ fun U hU h0 => by`. Take `⟨V, hV, hc⟩` from `exists_isCopy_le hδ hπ hiso hU h0`. Conclude with `⟨V, hV, hc.isIrredSubrep hδ.irred⟩`. Use `choose e he hr using fun i => isCopy_iff.1 (isCopy_of_isIrredSubrep hδ hπ hiso (hW i))`. Establish `hmem : ∀ i x, e i x ∈ W i` using `fun i x => hr i ▸ ⟨x, rfl⟩`.

Set `v : (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) → H` to `fun p => e p.1 (GlobalTheory.OpTrace.stdBasis X p.2)`. Establish `hon : Orthonormal ℂ v`. Use `⟨fun p => by simp [v, (GlobalTheory.OpTrace.stdBasis X).orthonormal.1], fun p q hpq => ?_⟩` and prove the remaining obligations. Take `⟨i, a⟩` from `p`. Take `⟨j, c⟩` from `q`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hac : a ≠ c` using `fun h => hpq (by rw [h])`. Simplify using `only [v, LinearIsometry.inner_map_map]`. Conclude with `(GlobalTheory.OpTrace.stdBasis X).orthonormal.2 hac`.

Conclude with `hs.OrthogonalFamily hij ⟨_, hmem i _⟩ ⟨_, hmem j _⟩`. Establish `hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun x hx => ?_` and prove the remaining obligations. Use `GlobalTheory.DiscreteSum.eq_zero_of_isHilbertSum hs fun i y hy => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩ : y ∈ LinearMap.range (e i).toLinearMap` from `(hr i).symm ▸ hy`.

Establish `h1 : ∀ a, ⟪GlobalTheory.OpTrace.stdBasis X a, adjoint (e i).toContinuousLinearMap x⟫_ℂ = 0` using `fun a => by`. Rewrite using `[adjoint_inner_right]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self (f := v) ⟨i, a⟩)) hx`. Establish `h2 : adjoint (e i).toContinuousLinearMap x = 0`. Use `(GlobalTheory.OpTrace.stdBasis X).hasSum_repr (adjoint (e i).toContinuousLinearMap x)` as an intermediate fact.

Simplify using `only [HilbertBasis.repr_apply_apply, h1, zero_smul] at this`. Conclude with `(hasSum_zero.unique this).symm`. Express the relevant statement in the definitionally equal form `⟪(e i).toContinuousLinearMap z, x⟫_ℂ = 0`. Rewrite using `[← adjoint_inner_right, h2, inner_zero_right]`. Conclude with `⟨ι, e, HilbertBasis.mkOfOrthogonalEqBot hon hsp, he, fun p => by simp [v]⟩`.
-/
theorem exists_hilbertBasis (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) :
    ∃ (ι : Type) (e : ι → (X →ₗᵢ[ℂ] H)) (b : HilbertBasis (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) ℂ H),
      (∀ i g x, e i (δ g x) = π g (e i x)) ∧ ∀ p, b p = e p.1 (GlobalTheory.OpTrace.stdBasis X p.2) := by
  obtain ⟨ι, W, hW, hs⟩ := GlobalTheory.DiscreteSum.exists_isHilbertSum hπ fun U hU h0 => by
    obtain ⟨V, hV, hc⟩ := exists_isCopy_le hδ hπ hiso hU h0
    exact ⟨V, hV, hc.isIrredSubrep hδ.irred⟩
  choose e he hr using fun i => isCopy_iff.1 (isCopy_of_isIrredSubrep hδ hπ hiso (hW i))
  have hmem : ∀ i x, e i x ∈ W i := fun i x => hr i ▸ ⟨x, rfl⟩
  let v : (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) → H := fun p => e p.1 (GlobalTheory.OpTrace.stdBasis X p.2)
  have hon : Orthonormal ℂ v := by
    refine ⟨fun p => by simp [v, (GlobalTheory.OpTrace.stdBasis X).orthonormal.1], fun p q hpq => ?_⟩
    obtain ⟨i, a⟩ := p
    obtain ⟨j, c⟩ := q
    by_cases hij : i = j
    · subst hij
      have hac : a ≠ c := fun h => hpq (by rw [h])
      simp only [v, LinearIsometry.inner_map_map]
      exact (GlobalTheory.OpTrace.stdBasis X).orthonormal.2 hac
    · exact hs.OrthogonalFamily hij ⟨_, hmem i _⟩ ⟨_, hmem j _⟩
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    refine GlobalTheory.DiscreteSum.eq_zero_of_isHilbertSum hs fun i y hy => ?_
    obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (e i).toLinearMap := (hr i).symm ▸ hy
    have h1 : ∀ a, ⟪GlobalTheory.OpTrace.stdBasis X a, adjoint (e i).toContinuousLinearMap x⟫_ℂ = 0 := fun a => by
      rw [adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self (f := v) ⟨i, a⟩)) hx
    have h2 : adjoint (e i).toContinuousLinearMap x = 0 := by
      have := (GlobalTheory.OpTrace.stdBasis X).hasSum_repr (adjoint (e i).toContinuousLinearMap x)
      simp only [HilbertBasis.repr_apply_apply, h1, zero_smul] at this
      exact (hasSum_zero.unique this).symm
    change ⟪(e i).toContinuousLinearMap z, x⟫_ℂ = 0
    rw [← adjoint_inner_right, h2, inner_zero_right]
  exact ⟨ι, e, HilbertBasis.mkOfOrthogonalEqBot hon hsp, he, fun p => by simp [v]⟩

end GlobalTheory.IsotypicTrace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap MeasureTheory

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

/- English proof (translation)
Set `E : X →L[ℂ] H` to `e.toContinuousLinearMap`. Establish `he' : ∀ g x, E (δ g x) = π g (E x)` using `he`. Establish `hEE : ∀ x, adjoint E (E x) = x` using `fun x => ext_inner_left ℂ fun y => by`. Rewrite using `[adjoint_inner_right]`. Conclude with `e.inner_map_map y x`.

Establish `hEa : ∀ g y, adjoint E (π g y) = δ g (adjoint E y)` using `fun g y => (GlobalTheory.DiscreteSum.adjoint_mem_homIn hδ.unitary hπ (T := E) (mem_homIn_top.2 he')).2 g y`. Establish `hRδ' : IsRepOp δ μ f (adjoint E ∘L repOp π μ f ∘L E)` using `fun x => by`. Establish `hk : ∀ g, f g • δ g x = adjoint E (f g • π g (E x))` using `fun g => by`. Rewrite using `[map_smul, hEa, hEE]`. Simplify using `only [hk]`.

Use `⟨(adjoint E).integrable_comp (hR (E x)).1, ?_⟩` and prove the remaining obligations. Rewrite using `[comp_apply, comp_apply, (hR (E x)).2, (adjoint E).integral_comp_comm (hR (E x)).1]`. Establish `hRδ : IsRepOp δ μ f (repOp δ μ f)` using `by rw [hRδ'.repOp_eq]; exact hRδ'`. Establish `hcomm : ∀ y, adjoint E (repOp π μ f y) = repOp δ μ f (adjoint E y)` using `fun y => by`. Rewrite using `[(hR y).2, ← (adjoint E).integral_comp_comm (hR y).1, (hRδ (adjoint E y)).2]`.

Simplify using `only [map_smul, hEa]`. Establish `hQ' : ∀ g y, Q (π g y) = π g (Q y)` using `fun g y => DFunLike.congr_fun (hQ g) y`. Take `⟨c, hc⟩` from `GlobalTheory.hilbert_schur X G δ hδ.unitary.norm_apply (fun S hS h => hδ.irred.2 S ⟨hS, h⟩) (adjoint E ∘L Q ∘L E) fun g => by`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `δ g (adjoint E (Q (E x))) = adjoint E (Q (E (δ g x)))`.

Rewrite using `[he', hQ', hEa]`. Establish `hP : adjoint E ∘L (repOp π μ f * Q) ∘L E = c • repOp δ μ f`. Use extensionality with `x`. Establish `hx : adjoint E (Q (E x)) = c • x` using `DFunLike.congr_fun hc x`. Express the relevant statement in the definitionally equal form `adjoint E (repOp π μ f (Q (E x))) = c • repOp δ μ f x`.

Rewrite using `[hcomm, hx, map_smul]`. Establish `htr' : trace (adjoint E ∘L (repOp π μ f * Q) ∘L E) = 0`. Rewrite using `[hP, trace_smul, htr, mul_zero]`. Establish `h` using `(hA.comp_comp (adjoint E) E).hasSum_trace (stdBasis X)`. Rewrite `h` using `[htr']`.

Use `h.congr_fun fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ⟪stdBasis X a, adjoint E ((repOp π μ f * Q) (E (stdBasis X a)))⟫_ℂ`. Rewrite using `[adjoint_inner_right]`. Both sides reduce to the same expression.
-/
theorem hasSum_copy [MeasurableSpace G] {μ : Measure G} {f : G → ℂ} (hδ : IsIrrUnitary δ)
    (hπ : IsUnitaryRep π) (hR : IsRepOp π μ f (repOp π μ f)) (e : X →ₗᵢ[ℂ] H)
    (he : ∀ g x, e (δ g x) = π g (e x)) (Q : H →L[ℂ] H) (hQ : ∀ g, Q * π g = π g * Q)
    (htr : trace (repOp δ μ f) = 0) (hA : IsTraceClass (repOp π μ f * Q)) :
    HasSum (fun a => ⟪e (stdBasis X a), (repOp π μ f * Q) (e (stdBasis X a))⟫_ℂ) 0 := by
  let E : X →L[ℂ] H := e.toContinuousLinearMap
  have he' : ∀ g x, E (δ g x) = π g (E x) := he
  have hEE : ∀ x, adjoint E (E x) = x := fun x => ext_inner_left ℂ fun y => by
    rw [adjoint_inner_right]
    exact e.inner_map_map y x
  have hEa : ∀ g y, adjoint E (π g y) = δ g (adjoint E y) := fun g y =>
    (GlobalTheory.DiscreteSum.adjoint_mem_homIn hδ.unitary hπ (T := E) (mem_homIn_top.2 he')).2 g y
  have hRδ' : IsRepOp δ μ f (adjoint E ∘L repOp π μ f ∘L E) := fun x => by
    have hk : ∀ g, f g • δ g x = adjoint E (f g • π g (E x)) := fun g => by
      rw [map_smul, hEa, hEE]
    simp only [hk]
    refine ⟨(adjoint E).integrable_comp (hR (E x)).1, ?_⟩
    rw [comp_apply, comp_apply, (hR (E x)).2, (adjoint E).integral_comp_comm (hR (E x)).1]
  have hRδ : IsRepOp δ μ f (repOp δ μ f) := by rw [hRδ'.repOp_eq]; exact hRδ'
  have hcomm : ∀ y, adjoint E (repOp π μ f y) = repOp δ μ f (adjoint E y) := fun y => by
    rw [(hR y).2, ← (adjoint E).integral_comp_comm (hR y).1, (hRδ (adjoint E y)).2]
    simp only [map_smul, hEa]
  have hQ' : ∀ g y, Q (π g y) = π g (Q y) := fun g y => DFunLike.congr_fun (hQ g) y
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur X G δ hδ.unitary.norm_apply (fun S hS h => hδ.irred.2 S ⟨hS, h⟩)
    (adjoint E ∘L Q ∘L E) fun g => by
      ext x
      change δ g (adjoint E (Q (E x))) = adjoint E (Q (E (δ g x)))
      rw [he', hQ', hEa]
  have hP : adjoint E ∘L (repOp π μ f * Q) ∘L E = c • repOp δ μ f := by
    ext x
    have hx : adjoint E (Q (E x)) = c • x := DFunLike.congr_fun hc x
    change adjoint E (repOp π μ f (Q (E x))) = c • repOp δ μ f x
    rw [hcomm, hx, map_smul]
  have htr' : trace (adjoint E ∘L (repOp π μ f * Q) ∘L E) = 0 := by
    rw [hP, trace_smul, htr, mul_zero]
  have h := (hA.comp_comp (adjoint E) E).hasSum_trace (stdBasis X)
  rw [htr'] at h
  refine h.congr_fun fun a => ?_
  change _ = ⟪stdBasis X a, adjoint E ((repOp π μ f * Q) (E (stdBasis X a)))⟫_ℂ
  rw [adjoint_inner_right]
  rfl

end GlobalTheory.IsotypicTrace

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ μ f hf X _ _ _ H _ _ _ δ π hδ hπ hiso _ Q hQ htr hA`. Distinguish the cases in `hex : ∃ T, IsRepOp π μ f T`. Use `swap`. Establish `h0 : repOp π μ f = 0` using `by rw [repOp, dif_neg hex]`. Rewrite using `[h0, zero_mul, trace_zero]`.

Establish `hR : IsRepOp π μ f (repOp π μ f)`. Take `⟨T, hT⟩` from `hex`. Rewrite using `[hT.repOp_eq]`. Conclude with `hT`. Take `⟨ι, e, b, he, hb⟩` from `IsotypicTrace.exists_hilbertBasis hδ hπ hiso`.

Establish `h1` using `hA.hasSum_trace b`. Establish `h2 : ∀ i, HasSum (fun a => ⟪b ⟨i, a⟩, (repOp π μ f * Q) (b ⟨i, a⟩)⟫_ℂ) 0` using `fun i => by`. Simplify `IsotypicTrace.hasSum_copy hδ hπ hR (e i) (he i) Q hQ htr.2 hA` using `only [hb]`. Conclude with `(hasSum_zero.unique (h1.sigma h2)).symm`.
-/
theorem trace_repOp_mul_eq_zero_of_isIsotypic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ), Integrable f μ → ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (π : G →* (H →L[ℂ] H)), IsIrrUnitary δ → IsUnitaryRep π → GlobalTheory.AutMult.IsIsotypic δ π → ∀ [SecondCountableTopology G] (Q : H →L[ℂ] H), (∀ g, Q * π g = π g * Q) → HasTrace (repOp δ μ f) 0 → IsTraceClass (repOp π μ f * Q) → trace (repOp π μ f * Q) = 0 := by
  intro G _ _ _ _ _ μ f hf X _ _ _ H _ _ _ δ π hδ hπ hiso _ Q hQ htr hA
  by_cases hex : ∃ T, IsRepOp π μ f T
  swap
  · have h0 : repOp π μ f = 0 := by rw [repOp, dif_neg hex]
    rw [h0, zero_mul, trace_zero]
  have hR : IsRepOp π μ f (repOp π μ f) := by
    obtain ⟨T, hT⟩ := hex
    rw [hT.repOp_eq]; exact hT
  obtain ⟨ι, e, b, he, hb⟩ := IsotypicTrace.exists_hilbertBasis hδ hπ hiso
  have h1 := hA.hasSum_trace b
  have h2 : ∀ i, HasSum (fun a => ⟪b ⟨i, a⟩, (repOp π μ f * Q) (b ⟨i, a⟩)⟫_ℂ) 0 := fun i => by
    simpa only [hb] using IsotypicTrace.hasSum_copy hδ hπ hR (e i) (he i) Q hQ htr.2 hA
  exact (hasSum_zero.unique (h1.sigma h2)).symm

end GlobalTheory
