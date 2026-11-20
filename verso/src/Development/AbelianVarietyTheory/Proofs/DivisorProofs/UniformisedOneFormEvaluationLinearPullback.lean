import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

/- English proof (translation)
Introduce `A _ g L u A' _ g' L' u' φ M h hM p z hz`. Establish `hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left` using `fun w => by rw [hM w]; rfl`. Establish `hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) w = val u.ex p.1.2.1 b (M w)`. Introduce `w hw b`. Establish `k` using `valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw`.

Rewrite `k` using `[← hpt]`. Conclude with `k`. Establish `hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1`. Introduce `w hw`. Express the relevant statement in the definitionally equal form `⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1`.

Rewrite using `[hpt, top_le_preimage_comp]`. Conclude with `fun x hx => p.2 (hw hx)`. Use `⟨hpre z hz, hval z hz, ?_⟩` and prove the remaining obligations. Establish `hopen : ∀ U, IsOpen (pre u.ex U)` using `fun U => (u.hol U 0).1`. Establish `hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)` using `fun U b => (u.hol U b).2`.

Establish `hopen' : ∀ U, IsOpen (pre u'.ex U)` using `fun U => (u'.hol U 0).1`. Take `⟨-, hsm, hD⟩` from `GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)`. Take `⟨-, hsm', hD'⟩` from `GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz`. Introduce `ξ`. Establish `hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1)))`.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hξ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`.

Rewrite using `[SemiHom.m1_D, hD', hD]`. Establish `e : val u'.ex p.1.1.1 (secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M` using `Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b`. Rewrite using `[e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz))) M.differentiableAt, M.fderiv]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, ContinuousLinearMap.add_comp]`.

Consider the case `smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]`.
-/
theorem evForm_secPull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  intro A _ g L u A' _ g' L' u' φ M h hM p z hz
  have hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left := fun w => by rw [hM w]; rfl
  have hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) w =
      val u.ex p.1.2.1 b (M w) := by
    intro w hw b
    have k := valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw
    rw [← hpt] at k
    exact k
  have hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1 := by
    intro w hw
    change ⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1
    rw [hpt, top_le_preimage_comp]
    exact fun x hx => p.2 (hw hx)
  refine ⟨hpre z hz, hval z hz, ?_⟩
  have hopen : ∀ U, IsOpen (pre u.ex U) := fun U => (u.hol U 0).1
  have hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U) := fun U b => (u.hol U b).2
  have hopen' : ∀ U, IsOpen (pre u'.ex U) := fun U => (u'.hol U 0).1
  obtain ⟨-, hsm, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)
  obtain ⟨-, hsm', hD'⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz
  intro ξ
  have hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [SemiHom.m1_D, hD', hD]
    have e : val u'.ex p.1.1.1 (secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M :=
      Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b
    rw [e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz)))
      M.differentiableAt, M.fderiv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, ContinuousLinearMap.add_comp]
  | smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]

end GlobalTheory.CechPer
