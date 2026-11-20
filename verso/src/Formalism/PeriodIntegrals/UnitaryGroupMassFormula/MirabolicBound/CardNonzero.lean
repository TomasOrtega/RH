import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.LastRowMul

namespace PI.GGMirBoundW

open Finset Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

/- English proof (translation)
Rewrite using `[Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]`.
-/
theorem card_nonzero (F : Type) [Field F] [Fintype F] (m : ℕ) :
    Fintype.card {r : Fin m → F // r ≠ 0} = Fintype.card F ^ m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]

/- English proof (translation)
Introduce `hB hC hJ hR hO hS F _ _ n IH ψ₀ hψ V _ _ π ℓ hℓ hW`. Set `π' : Representation ℂ (GL (Fin (n + 1)) F) V` to `π.comp (E F (n + 1))`. Establish `hW' : IsWhit ψ₀ π' ℓ`. Introduce `u hu v`. Establish `h` using `hW (E F (n + 1) u) (hB F (n + 1) u hu).1 v`.

Simplify using `only [psiU] at h ⊢`. Rewrite `h` using `[(hB F (n + 1) u hu).2]`. Conclude with `h`. Take `⟨p, hpL, hpI⟩` from `IH ψ₀ hψ V π' ℓ hℓ hW'`. Set `R` to `{r : Fin (n + 1) → F // r ≠ 0}`.

Use `choose g hg using fun r : R => hR F n r.1 r.2`. Set `A : R × Fin (D F (n + 1)) → GL (Fin (n + 1)) F` to `fun q => p q.2 * g q.1`. Establish `hArow : ∀ q j, (A q : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j`. Introduce `q j`. Use `show ((p q.2 * g q.1 : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j`.

Rewrite using `[lastRow_mul (hpL q.2), hg]`. Set `f : R × Fin (D F (n + 1)) → Module.Dual ℂ V` to `fun q => ℓ ∘ₗ π (E F (n + 1) (A q))`. Establish `hf : ∀ (x : Fin (n + 1) → F) (r : R) (i : Fin (D F (n + 1))), (π (col x)).dualMap (f (r, i)) = (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x • f (r, i)`. Introduce `x r i`. Use extensionality with `v`.

Use `show ℓ (π (E F (n + 1) (A (r, i))) (π (col x) v)) = ψ₀ (r.1 ⬝ᵥ x) * ℓ (π (E F (n + 1) (A (r, i))) v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hJ F (n + 1) (A (r, i)) x, map_mul, Module.End.mul_apply, hW _ (hC F n _).1, psiU, (hC F n _).2]`. Use `congr 2`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hArow]`.

Establish `hblock : ∀ r : R, LinearIndependent ℂ (fun i => f (r, i))`. Introduce `r`. Establish `he : (fun i => f (r, i)) = (π (E F (n + 1) (g r))).dualMap ∘ (fun i => ℓ ∘ₗ π' (p i))`. Use function extensionality and compare the values at `i`. Use extensionality with `v`.

Use `show ℓ (π (E F (n + 1) (p i * g r)) v) = ℓ (π (E F (n + 1) (p i)) (π (E F (n + 1) (g r)) v))`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply]`. Rewrite using `[he]`. Use `hpI.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective ?_))` and prove the remaining obligations. Introduce `v`.

Use `⟨π (E F (n + 1) (g r))⁻¹ v, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hN : ((Fintype.card F : ℂ) ^ (n + 1)) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)`. Establish `horth : ∀ r s : R, ∑ x : Fin (n + 1) → F, (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x * (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) s x = if r = s then (Fintype.card F : ℂ) ^ (n + 1) else 0`.

Introduce `r s`. Rewrite using `[hO F (n + 1) ψ₀ hψ r.1 s.1]`. Conclude with `if_congr Subtype.val_inj rfl rfl`. Establish `hind` using `hS (Module.Dual ℂ V) (Fin (n + 1) → F) R (Fin (D F (n + 1))) (fun x => (π (col x)).dualMap) (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) _ hN (fun r s => by convert horth r s) f hf hblock`. Establish `hcard : Fintype.card (Fin (D F (n + 1 + 1))) = Fintype.card (R × Fin (D F (n + 1)))`.

Rewrite using `[Fintype.card_fin, Fintype.card_prod, card_nonzero, Fintype.card_fin, D, D, Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), mul_comm]`. Set `e : Fin (D F (n + 1 + 1)) ≃ R × Fin (D F (n + 1))` to `Fintype.equivOfCardEq hcard`. Use `⟨fun k => E F (n + 1) (A (e k)), fun k => lastRowE_E _, ?_⟩` and prove the remaining obligations. Conclude with `hind.comp e e.injective`.
-/
theorem stepOf : StepOf := by
  intro hB hC hJ hR hO hS F _ _ n IH ψ₀ hψ V _ _ π ℓ hℓ hW

  let π' : Representation ℂ (GL (Fin (n + 1)) F) V := π.comp (E F (n + 1))
  have hW' : IsWhit ψ₀ π' ℓ := by
    intro u hu v
    have h := hW (E F (n + 1) u) (hB F (n + 1) u hu).1 v
    simp only [psiU] at h ⊢
    rw [(hB F (n + 1) u hu).2] at h
    exact h
  obtain ⟨p, hpL, hpI⟩ := IH ψ₀ hψ V π' ℓ hℓ hW'
  let R := {r : Fin (n + 1) → F // r ≠ 0}
  choose g hg using fun r : R => hR F n r.1 r.2
  let A : R × Fin (D F (n + 1)) → GL (Fin (n + 1)) F := fun q => p q.2 * g q.1
  have hArow : ∀ q j, (A q : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j := by
    intro q j
    show ((p q.2 * g q.1 : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j
    rw [lastRow_mul (hpL q.2), hg]
  let f : R × Fin (D F (n + 1)) → Module.Dual ℂ V := fun q => ℓ ∘ₗ π (E F (n + 1) (A q))

  have hf : ∀ (x : Fin (n + 1) → F) (r : R) (i : Fin (D F (n + 1))),
      (π (col x)).dualMap (f (r, i)) = (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x • f (r, i) := by
    intro x r i
    ext v
    show ℓ (π (E F (n + 1) (A (r, i))) (π (col x) v)) = ψ₀ (r.1 ⬝ᵥ x) * ℓ (π (E F (n + 1) (A (r, i))) v)
    rw [← Module.End.mul_apply, ← map_mul, hJ F (n + 1) (A (r, i)) x, map_mul, Module.End.mul_apply,
      hW _ (hC F n _).1, psiU, (hC F n _).2]
    congr 2
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hArow]

  have hblock : ∀ r : R, LinearIndependent ℂ (fun i => f (r, i)) := by
    intro r
    have he : (fun i => f (r, i)) = (π (E F (n + 1) (g r))).dualMap ∘ (fun i => ℓ ∘ₗ π' (p i)) := by
      funext i
      ext v
      show ℓ (π (E F (n + 1) (p i * g r)) v) = ℓ (π (E F (n + 1) (p i)) (π (E F (n + 1) (g r)) v))
      rw [map_mul, map_mul, Module.End.mul_apply]
    rw [he]
    refine hpI.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective ?_))
    intro v
    refine ⟨π (E F (n + 1) (g r))⁻¹ v, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hN : ((Fintype.card F : ℂ) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  have horth : ∀ r s : R, ∑ x : Fin (n + 1) → F, (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x *
      (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) s x = if r = s then (Fintype.card F : ℂ) ^ (n + 1) else 0 := by
    intro r s
    rw [hO F (n + 1) ψ₀ hψ r.1 s.1]
    exact if_congr Subtype.val_inj rfl rfl
  have hind := hS (Module.Dual ℂ V) (Fin (n + 1) → F) R (Fin (D F (n + 1)))
    (fun x => (π (col x)).dualMap) (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x)))
    _ hN (fun r s => by convert horth r s) f hf hblock
  have hcard : Fintype.card (Fin (D F (n + 1 + 1))) = Fintype.card (R × Fin (D F (n + 1))) := by
    rw [Fintype.card_fin, Fintype.card_prod, card_nonzero, Fintype.card_fin, D, D,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), mul_comm]
  let e : Fin (D F (n + 1 + 1)) ≃ R × Fin (D F (n + 1)) := Fintype.equivOfCardEq hcard
  refine ⟨fun k => E F (n + 1) (A (e k)), fun k => lastRowE_E _, ?_⟩
  exact hind.comp e e.injective

end

end PI.GGMirBoundW
