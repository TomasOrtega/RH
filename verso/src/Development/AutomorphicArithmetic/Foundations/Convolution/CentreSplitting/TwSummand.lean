import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem aux {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G → G) (he : Function.Surjective e) (U : H →L[ℂ] H) (h1 : ∀ v, ‖U v‖ = ‖v‖)
    (h2 : Function.Surjective U) (h3 : ∀ g v, U (π g v) = π (e g) (U v)) (hc : ∀ v, U v ∈ W ↔ v ∈ W) (V : Submodule ℂ H) :
    IsSummandOf π W V ↔ IsSummandOf π W (V.map U.toLinearMap) := by
  let I : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, h1⟩
  have hinj : Function.Injective U := I.injective
  have hcm : ∀ X : Submodule ℂ H, (X.map U.toLinearMap).comap U.toLinearMap = X :=
    fun X => Submodule.comap_map_eq_of_injective hinj X
  have hmc : ∀ X : Submodule ℂ H, (X.comap U.toLinearMap).map U.toLinearMap = X :=
    fun X => Submodule.map_comap_eq_of_surjective h2 X
  have cl1 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.map U.toLinearMap : Set H) :=
    fun X hX => I.isometry.isClosedEmbedding.isClosedMap _ hX
  have cl2 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.comap U.toLinearMap : Set H) :=
    fun X hX => hX.preimage U.continuous
  have i1 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.map U.toLinearMap) := by
    rintro X hX g _ ⟨v, hv, rfl⟩
    obtain ⟨g, rfl⟩ := he g
    exact ⟨_, hX g v hv, h3 g v⟩
  have i2 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.comap U.toLinearMap) := fun X hX g v hv => by
    show U _ ∈ X
    rw [h3]
    exact hX _ _ hv
  constructor
  · intro h
    refine ⟨?_, cl1 _ h.closed, i1 _ h.inv, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact (hc v).2 (h.le hv)
    · rw [← hcm V, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
    · rcases h.irred _ ((Submodule.comap_mono hX).trans (hcm V).le) (cl2 _ c) (i2 _ i) with e | e
      · left; rw [← hmc X, e, Submodule.map_bot]
      · right; rw [← hmc X, e]
  · intro h
    have a1 := cl2 _ h.closed
    have a2 := i2 _ h.inv
    rw [hcm] at a1 a2
    refine ⟨fun v hv => (hc v).1 (h.le ⟨v, hv, rfl⟩), a1, a2, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rw [e, Submodule.map_bot]
    · rcases h.irred _ (Submodule.map_mono hX) (cl1 _ c) (i1 _ i) with e | e
      · left; rw [← hcm X, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
      · right; rw [← hcm X, e, hcm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.ConvolutionTheory.Dp.twSummand :
    UpperTheory.ConvolutionTheory.Dp.TwSummand := by
  intro K _ _ n μ _ θ V
  obtain ⟨h1, h2, h3⟩ := twUnitary K n μ θ
  have hinj : Function.Injective θ.U := (⟨θ.U.toLinearMap, h1⟩ : LL μ →ₗᵢ[ℂ] LL μ).injective
  refine aux _ _ θ.e θ.e.surjective θ.U h1 h2 h3 (fun v => ?_) V
  have e : θ.U (PositivityTheory.Rg.Tf.Core.Pc μ v) = PositivityTheory.Rg.Tf.Core.Pc μ (θ.U v) := DFunLike.congr_fun θ.U_comm v
  have a : ∀ x, PositivityTheory.Rg.Tf.Core.Pc μ x = x ↔ x ∈ cuspidalL2 μ := fun x => Submodule.starProjection_eq_self_iff
  rw [← a, ← a, ← e, hinj.eq_iff]
