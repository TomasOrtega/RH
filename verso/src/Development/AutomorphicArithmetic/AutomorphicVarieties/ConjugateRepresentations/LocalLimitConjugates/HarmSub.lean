import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section SlopeTestRemainingChoices

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish `e : Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ)` using `Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)`. Use `(Cm.isAutForm_iff _).2 ?_` and prove the remaining obligations. Rewrite using `[← Cm.coe_smEq, e]`. Conclude with `((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g`.
-/
private theorem aut_fin (g : GL (Fin a) (Af E)) {φ : Sm E a} (h : GlobalTheory.CuspRep.IsAutForm φ) :
    GlobalTheory.CuspRep.IsAutForm (finRep E a g φ) := by
  have e : Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
    Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)
  refine (Cm.isAutForm_iff _).2 ?_
  rw [← Cm.coe_smEq, e]
  exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

/- English proof (translation)
Introduce `t u` and use `by have c : Commute (cap t u) (act (.fin g)) := (S.capAct E a t u).2.1 (.fin g) have e : cap t u (finRep E a g φ) = finRep E a g (cap t u φ) := LinearMap.congr_fun c.eq φ rw [e, h t u, map_smul]`.
-/
private theorem char_fin (g : GL (Fin a) (Af E)) {m : (E →+* ℂ) → Multiset ℂ} {φ : Sm E a} (h : Cj.HasChar m φ) :
    Cj.HasChar m (finRep E a g φ) := fun t u => by
  have c : Commute (cap t u) (act (.fin g)) := (S.capAct E a t u).2.1 (.fin g)
  have e : cap t u (finRep E a g φ) = finRep E a g (cap t u φ) := LinearMap.congr_fun c.eq φ
  rw [e, h t u, map_smul]

/- English proof (translation)
Establish `: sqSub E a r ≤ (sqSub E a r).comap (finRep E a g)` using `Submodule.span_le.2 fun ψ hψ => Submodule.subset_span ((petInv E a ha r).1 g ψ hψ)`. Conclude with `this h`.
-/
private theorem sq_fin (ha : 1 ≤ a) (r : ℝ) (g : GL (Fin a) (Af E)) {φ : Sm E a} (h : φ ∈ sqSub E a r) :
    finRep E a g φ ∈ sqSub E a r := by
  have : sqSub E a r ≤ (sqSub E a r).comap (finRep E a g) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span ((petInv E a ha r).1 g ψ hψ)
  exact this h

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ a ha Ξ r m q`. Take `⟨L, L1, L2⟩` from `(levSub E a Ξ q).2.2`. Establish `comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsH r m α → IsH r m β → IsH r m (s • α + β)`. Introduce `s α β hα hβ`. Establish `ap : ∀ X i, cmp i ((s • α + β) X) = s • cmp i (α X) + cmp i (β X)` using `fun X i => by`.

Rewrite using `[show (s • α + β) X = s • α X + β X from rfl, map_add, map_smul]`. Use `⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.lev)) ((L1 _).2 hβ.lev)), by rw [dCo_comb, hα.closed, hβ.closed, smul_zero, add_zero], fun X i => ⟨?_, fun t u => ?_⟩, fun X i => ?_⟩` and prove the remaining obligations. Rewrite using `[ap]`. Conclude with `Cm.mem_range_ofAut.1 (Submodule.add_mem _ (Submodule.smul_mem _ s (Cm.mem_range_ofAut.2 (hα.aut X i).1)) (Cm.mem_range_ofAut.2 (hβ.aut X i).1))`. Rewrite using `[ap, map_add, map_smul, (hα.aut X i).2 t u, (hβ.aut X i).2 t u, smul_add, smul_comm]`.

Rewrite using `[ap]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ s (hα.sq X i)) (hβ.sq X i)`. Establish `zero : IsH r m (0 : Geo.Co Ξ q)`. Establish `ap : ∀ X i, cmp i ((0 : Geo.Co Ξ q) X) = 0` using `fun X i => map_zero _`. Use `⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], fun X i => ⟨?_, fun t u => ?_⟩, fun X i => ?_⟩` and prove the remaining obligations.

Rewrite using `[ap]`. Conclude with `Cm.mem_range_ofAut.1 (Submodule.zero_mem _)`. Rewrite using `[ap, map_zero, smul_zero]`. Rewrite using `[ap]`. Conclude with `Submodule.zero_mem _`.

Use `⟨{ carrier := {ω | IsH r m ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce `α β hα hβ`. Use `comb 1 α β hα hβ` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Introduce `s α hα`.

Use `comb s α 0 hα zero` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis. Introduce and unpack `x ω ⟨h1, h2, h3, h4⟩`. Use `⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, fun X i => ?_, fun X i => ?_⟩` and prove the remaining obligations. Take `⟨U, -, -, u3⟩` from `h1`.

Rewrite using `[(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2, ← transRep_apply, map_zero]`. Rewrite using `[cmp_trans]`. Conclude with `⟨aut_fin x (h3 X i).1, char_fin x (h3 X i).2⟩`. Rewrite using `[cmp_trans]`. Conclude with `sq_fin ha r x (h4 X i)`.
-/
theorem UpperTheory.V.Cj.H.harmSub :
    UpperTheory.V.Cj.H.HarmSub := by
  intro E _ _ _ a ha Ξ r m q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsH r m α → IsH r m β → IsH r m (s • α + β) := by
    intro s α β hα hβ
    have ap : ∀ X i, cmp i ((s • α + β) X) = s • cmp i (α X) + cmp i (β X) := fun X i => by
      rw [show (s • α + β) X = s • α X + β X from rfl, map_add, map_smul]
    refine ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.lev)) ((L1 _).2 hβ.lev)),
      by rw [dCo_comb, hα.closed, hβ.closed, smul_zero, add_zero], fun X i => ⟨?_, fun t u => ?_⟩, fun X i => ?_⟩
    · rw [ap]
      exact Cm.mem_range_ofAut.1 (Submodule.add_mem _ (Submodule.smul_mem _ s (Cm.mem_range_ofAut.2 (hα.aut X i).1))
        (Cm.mem_range_ofAut.2 (hβ.aut X i).1))
    · rw [ap, map_add, map_smul, (hα.aut X i).2 t u, (hβ.aut X i).2 t u, smul_add, smul_comm]
    · rw [ap]
      exact Submodule.add_mem _ (Submodule.smul_mem _ s (hα.sq X i)) (hβ.sq X i)
  have zero : IsH r m (0 : Geo.Co Ξ q) := by
    have ap : ∀ X i, cmp i ((0 : Geo.Co Ξ q) X) = 0 := fun X i => map_zero _
    refine ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], fun X i => ⟨?_, fun t u => ?_⟩,
      fun X i => ?_⟩
    · rw [ap]
      exact Cm.mem_range_ofAut.1 (Submodule.zero_mem _)
    · rw [ap, map_zero, smul_zero]
    · rw [ap]
      exact Submodule.zero_mem _
  refine ⟨{ carrier := {ω | IsH r m ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, fun X i => ?_, fun X i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact ⟨aut_fin x (h3 X i).1, char_fin x (h3 X i).2⟩
    · rw [cmp_trans]
      exact sq_fin ha r x (h4 X i)
