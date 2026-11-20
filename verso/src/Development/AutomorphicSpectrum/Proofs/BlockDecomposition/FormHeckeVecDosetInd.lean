import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.SphComp

/- English proof (translation)
Use `set D := DoubleCoset.doubleCoset g (K : Set G) K with hD`. Establish `hm` using `Formalism.UG.Final.DosetIndMem G K ℂ g`. Establish `hfin : {c : G ⧸ K | c.out ∈ D}.Finite`. Use `(Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_` and prove the remaining obligations. Introduce `c hc`.

Establish `h' : c.out ∈ D` using `hc`. Simplify using `only [Set.mem_setOf_eq, dosetInd]`. Rewrite using `[Set.indicator_of_mem h']`. Simplify using the standard rewrite rules. Establish `hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x)`.

Introduce `γ hγ`. Take `⟨a, ha, b, hb, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hγ`. Establish `e` using `LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))`. Simplify using `only [LinearMap.comp_apply] at e`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]`.

Establish `e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) = ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x)` using `l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)`. Establish `e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) = Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x))`. Use function extensionality and compare the values at `c`. Distinguish the cases in `h : c.out ∈ D`. Establish `h1 : dosetInd ℂ K g c.out = 1`.

Simplify using `only [dosetInd]`. Rewrite using `[Set.indicator_of_mem h]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]`. Establish `h1 : dosetInd ℂ K g c.out = 0`.

Simplify using `only [dosetInd]`. Conclude with `Set.indicator_of_notMem h _`. Rewrite using `[Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]`. Establish `hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card`. Rewrite using `[← Set.ncard_eq_toFinset_card _ hfin]`.

Conclude with `Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}`. Rewrite using `[e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]`. Simplify using the standard rewrite rules.
-/
theorem form_heckeVec_dosetInd {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K)
    (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, l ∘ₗ ρ k = l) (g : G) :
    l (heckeVec ρ K (dosetInd ℂ K g) x) =
      (Nat.card {c : G ⧸ K // (c.out : G) ∈ DoubleCoset.doubleCoset g (K : Set G) K} : ℂ) * l (ρ g x) := by
  classical
  set D := DoubleCoset.doubleCoset g (K : Set G) K with hD
  have hm := Formalism.UG.Final.DosetIndMem G K ℂ g
  have hfin : {c : G ⧸ K | c.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_
    intro c hc
    have h' : c.out ∈ D := hc
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x) := by
    intro γ hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hγ
    have e := LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))
    simp only [LinearMap.comp_apply] at e
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]
  have e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) =
      ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x) :=
    l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)
  have e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) =
      Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x)) := by
    funext c
    by_cases h : c.out ∈ D
    · have h1 : dosetInd ℂ K g c.out = 1 := by
        simp only [dosetInd]
        rw [Set.indicator_of_mem h]
        simp
      rw [Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]
    · have h1 : dosetInd ℂ K g c.out = 0 := by
        simp only [dosetInd]
        exact Set.indicator_of_notMem h _
      rw [Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]
  have hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}
  rw [e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]
  simp

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g`. Establish `hK` using `Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n`. Establish `e` using `congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))`. Rewrite `e` using `[map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g]`. Conclude with `e`.
-/
theorem sphCompare : PositivityTheory.SphericalProduct.SphCompare := by
  intro L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have e := congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))
  rw [map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g] at e
  exact e

end GlobalTheory.CompanionTheory.SphComp

end
