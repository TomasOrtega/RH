import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

/- English proof (translation)
Introduce `R _ _ A N σ c t t' h j`. Establish `ht : @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R` using `R) (Kb R)) A.A).left (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' = c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).le …`. Establish `e : secTw A N σ t' = σ c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R` using `R) (Kb R)) A.A).left (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) (secTw A N σ t) := by`. Unfold `secTw`. Rewrite using `[show t' = @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' from rfl, ht, map_smulₛₗ]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem secTw_chart_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) →
    ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  intro R _ _ A N σ c t t' h j
  have ht : @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' =
      c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t :=
    GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun i => h i
  have e : secTw A N σ t' = σ c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ))))
      (secTw A N σ t) := by
    unfold secTw
    rw [show t' = @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' from rfl,
      ht, map_smulₛₗ]
    rfl
  rw [e]
  rfl

end GlobalTheory.Mum.Conj
