import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Use `CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_` and prove the remaining obligations. Establish `h` using `CuspMax.mem_unipRad_iff_entries.1 hu i j hij`. Distinguish the cases in `hh : i = j`. Substitute `hh` using the available equality. Establish `h1` using `(redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])`.

Simplify using `using h1`. Rewrite using `[Matrix.one_apply_ne hh]`. Conclude with `(redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])`.
-/
private theorem redK_mem_unipRad {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) k}
    (hu : g ∈ unipRad k e) (hK : g ∈ KO k (Fin n)) : redK k (Fin n) ⟨g, hK⟩ ∈ unipRad 𝓀[k] e := by
  refine CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_
  have h := CuspMax.mem_unipRad_iff_entries.1 hu i j hij
  by_cases hh : i = j
  · subst hh
    have h1 := (redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])
    simpa using h1
  · rw [Matrix.one_apply_ne hh]
    exact (redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])

/- English proof (translation)
Introduce `s d e hne v hv`. Establish `hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n)))`. Use `GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))`. Rewrite `h1` using `[levelZero_apply]`. Then use the resulting hypothesis.

Establish `hne' : unipRad k e ≠ ⊥` using `CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)`. Use `haveI := hc.2 s d e hne'`. Conclude with `Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))`.
-/
private theorem finCusp_levelZero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCuspidal π) : PositivityTheory.Rg.DzCount.FinCusp (levelZero π) := by
  intro s d e hne v hv
  have hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    refine GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)
    have h1 := congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))
    rwa [levelZero_apply] at h1
  have hne' : unipRad k e ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)
  haveI := hc.2 s d e hne'
  exact Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))

/- English proof (translation)
Establish `key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤`. Introduce `W hW`. Use `haveI : Nontrivial W.toSubmodule := by`. Rewrite using `[Submodule.nontrivial_iff_ne_bot]`. Introduce `h`.

Conclude with `hW (Subrepresentation.toSubmodule_injective h)`. Set `j : W.toSubmodule →ₗ[ℂ] π.V` to `(fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype`. Establish `hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation`. Introduce `s d e hne w hw`. Conclude with `Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))`.

Establish `hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a c hac`. Conclude with `Subtype.ext (Subtype.ext hac)`. Introduce `g w`.

Conclude with `levelZero_apply π.ρ g w`. Establish `hfix` using `PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show W.toSubmodule = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Establish `hv : (v : π.V) ∈ LinearMap.range j` using `hfix ▸ v.2`. Take `⟨w, hw⟩` from `hv`. Establish `hwv : (w : fixed π.ρ (KOne k (Fin n))) = v` using `Subtype.ext hw`. Rewrite using `[← hwv]`.

Conclude with `w.2`. Use `haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by`. Use `⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩` and prove the remaining obligations. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `v hv`. Establish `hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule` using `Submodule.mem_top`. Rewrite `hm` using `[← h']`. Conclude with `congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)`. Prove the components needed by the constructor for the conclusion.

Introduce `W`. Distinguish the cases in `h : W = ⊥`. Conclude with `Or.inl h`. Conclude with `Or.inr (key W h)`.
-/
private theorem irreducible_levelZero (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (hω : HasCentralChar π.ρ ω)
    (hF : PositivityTheory.Rg.DzCount.FinCusp (levelZero π.ρ)) (hD : fixed π.ρ (KOne k (Fin n)) ≠ ⊥) :
    (levelZero π.ρ).IsIrreducible := by
  have key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤ := by
    intro W hW
    haveI : Nontrivial W.toSubmodule := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let j : W.toSubmodule →ₗ[ℂ] π.V := (fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype
    have hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation := by
      intro s d e hne w hw
      exact Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))
    have hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j := by
      refine ⟨?_, ?_⟩
      · intro a c hac
        exact Subtype.ext (Subtype.ext hac)
      · intro g w
        exact levelZero_apply π.ρ g w
    have hfix := PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro v _
    have hv : (v : π.V) ∈ LinearMap.range j := hfix ▸ v.2
    obtain ⟨w, hw⟩ := hv
    have hwv : (w : fixed π.ρ (KOne k (Fin n))) = v := Subtype.ext hw
    rw [← hwv]
    exact w.2
  haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by
    refine ⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hm
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)
  constructor
  intro W
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (key W h)

end

/- English proof (translation)
Introduce `k _ _ _ _ _ y hc hD`. Establish `hadm` using `(UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥) (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)`. Rewrite `hadm` using `[levelPre_bot]`. Take `⟨ω, hω⟩` from `(GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y`. Establish `hF` using `finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2`.

Conclude with `⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.cuspIrr :
    CuspIrr := by
  intro k _ _ _ _ _ y hc hD
  have hadm := (UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥)
    (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
  rw [levelPre_bot] at hadm
  obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y
  have hF := finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2
  exact ⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩
