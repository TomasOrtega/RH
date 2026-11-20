import Mathlib

namespace GlobalTheory

open IsDiscreteValuationRing in

/- English proof (translation)
Introduce `O _ _ _ M _ _ _`. Take `⟨n, ι, _, p, hp, e, ⟨f⟩⟩` from `Module.equiv_free_prod_directSum (R := O) (M := M)`. Establish `hid : ∀ i, (Submodule.span O {p i ^ e i} : Submodule O O) = (IsLocalRing.maximalIdeal O ^ e i : Ideal O)`. Introduce `i`. Rewrite using `[(irreducible_iff_uniformizer _).1 (hp i), Ideal.span_singleton_pow]`.

Set `σ` to `Fintype.equivFin ι`. Use `⟨n, Fintype.card ι, fun j => e (σ.symm j), ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite O O (Fin n)) (DirectSum.linearEquivFunOnFintype O ι (fun i => O ⧸ O ∙ p i ^ e i) ≪≫ₗ LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _ (hid i)) ≪≫ₗ (LinearEquiv.piCongrLeft O (fun i : ι => O ⧸ IsLocalRing.ma …`.
-/
theorem dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ),
    Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  intro O _ _ _ M _ _ _
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := M)
  have hid : ∀ i, (Submodule.span O {p i ^ e i} : Submodule O O) =
      (IsLocalRing.maximalIdeal O ^ e i : Ideal O) := by
    intro i
    rw [(irreducible_iff_uniformizer _).1 (hp i), Ideal.span_singleton_pow]
  classical
  let σ := Fintype.equivFin ι
  refine ⟨n, Fintype.card ι, fun j => e (σ.symm j), ⟨?_⟩⟩
  exact f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite O O (Fin n))
    (DirectSum.linearEquivFunOnFintype O ι (fun i => O ⧸ O ∙ p i ^ e i) ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _ (hid i)) ≪≫ₗ
      (LinearEquiv.piCongrLeft O (fun i : ι => O ⧸ IsLocalRing.maximalIdeal O ^ e i) σ.symm).symm)

end GlobalTheory
