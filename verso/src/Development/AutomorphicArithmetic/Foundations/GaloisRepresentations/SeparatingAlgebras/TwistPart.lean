import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `E _ _ _ a w₀ K W J A _ θ χ hC hK F hF`. Set `χ' : (lev K w₀ J) →* ℂˣ` to `χ.comp (θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2))`. Take `⟨I, G, h1, h2, rfl⟩` from `GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W (lev K w₀ J) χ' F fun c v g => hF c.1 c.2 v g`. Use `Submodule.sum_mem _ fun π hπ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : G π = 0`.

Rewrite using `[h0]`. Conclude with `zero_mem _`. Establish `hlaw : ∀ c (hc : c ∈ lev K w₀ J) v g, (G π).1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * (G π).1 v g` using `fun c hc v g => h2 π hπ ⟨c, hc⟩ v g`. Establish `hfix : G π ∈ fixedBy W K` using `fun k hk v g => by`. Establish `hkC : k ∈ lev K w₀ J` using `(le_sup_left : K ≤ lev K w₀ J) hk`.

Establish `e : (⟨cLoc w₀ k, hC k hkC⟩ : J) = 1` using `Subtype.ext (hK k hk)`. Rewrite using `[hlaw k hkC v g, e]`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, (G π).1 v ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `h0 (Subtype.ext (LinearMap.ext hcon))`. Establish `hP : GlobalTheory.CongW.HasTypeVec w₀ K J θ χ π.V` using `⟨(G π).1 v, AutSub.mem_finPart.1 (h1 π hπ) v, hv, fun x hx => funext fun g => hfix x hx v g, fun x hx h => funext fun g => hlaw x ((le_sup_right : _ ≤ lev K w₀ J) ⟨hx, h⟩) v g⟩`. Conclude with `Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩)`.
-/
theorem UpperTheory.Gal.Gen.twistPart_pf :
    UpperTheory.Gal.Gen.TwistPart := by
  intro E _ _ _ a w₀ K W J A _ θ χ hC hK F hF
  let χ' : (lev K w₀ J) →* ℂˣ := χ.comp (θ.comp
    (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2))
  obtain ⟨I, G, h1, h2, rfl⟩ := GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W (lev K w₀ J) χ' F fun c v g => hF c.1 c.2 v g
  refine Submodule.sum_mem _ fun π hπ => ?_
  by_cases h0 : G π = 0
  · rw [h0]
    exact zero_mem _
  have hlaw : ∀ c (hc : c ∈ lev K w₀ J) v g,
      (G π).1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * (G π).1 v g :=
    fun c hc v g => h2 π hπ ⟨c, hc⟩ v g
  have hfix : G π ∈ fixedBy W K := fun k hk v g => by
    have hkC : k ∈ lev K w₀ J := (le_sup_left : K ≤ lev K w₀ J) hk
    have e : (⟨cLoc w₀ k, hC k hkC⟩ : J) = 1 := Subtype.ext (hK k hk)
    rw [hlaw k hkC v g, e]
    simp
  obtain ⟨v, hv⟩ : ∃ v, (G π).1 v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (Subtype.ext (LinearMap.ext hcon))
  have hP : GlobalTheory.CongW.HasTypeVec w₀ K J θ χ π.V :=
    ⟨(G π).1 v, AutSub.mem_finPart.1 (h1 π hπ) v, hv, fun x hx => funext fun g => hfix x hx v g,
      fun x hx h => funext fun g =>
        hlaw x ((le_sup_right : _ ≤ lev K w₀ J) ⟨hx, h⟩) v g⟩
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩)
