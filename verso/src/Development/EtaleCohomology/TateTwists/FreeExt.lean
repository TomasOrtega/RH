import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.AlexanderWhitneyExistence
import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwExPf

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using `only [GlobalTheory.EtC.ev, Cochain.add_v, Preadditive.comp_add]`. Both sides reduce to the same expression.
-/
theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp only [GlobalTheory.EtC.ev, Cochain.add_v, Preadditive.comp_add]
  rfl

/- English proof (translation)
Set `φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F` to `φ`. Set `ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F` to `ψ`. Express the relevant statement in the definitionally equal form `φ' = ψ'`. Apply `((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective` to reduce the goal to its premises. Rewrite using `[Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]`.

Use `NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)` and prove the remaining obligations. Conclude with `h U.unop x.down`.
-/
theorem free_ext (P : PSh) (F : Shv R) (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  let φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := φ
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := ψ
  change φ' = ψ'
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)
  exact h U.unop x.down

/- English proof (translation)
Use `Cochain.ext _ _ (fun i j hij => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : 0 ≤ -i`. Take `⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ)` from `⟨(-i).toNat, by omega⟩`. Rewrite using `[← cancel_epi (chainsXIso R E p).inv]`. Conclude with `free_ext _ _ _ _ fun U x => h p j hij U x`.

Apply `IsZero.eq_of_src` to reduce the goal to its premises. Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce `i' hi'`. Express the relevant statement in the definitionally equal form `-(i' : ℤ) = i at hi'`. Use linear arithmetic over natural numbers and integers.
-/
theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  refine Cochain.ext _ _ (fun i j hij => ?_)
  by_cases hi : 0 ≤ -i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ _ _ fun U x => h p j hij U x
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i' hi'
    change -(i' : ℤ) = i at hi'
    omega

end LateralTheory.EtaleFoundations.AwExPf
