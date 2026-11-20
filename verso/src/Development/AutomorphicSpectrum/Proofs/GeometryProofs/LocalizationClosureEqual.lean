import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

/- English proof (translation)
Establish `hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q'` using `Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)`. Establish `hne : (∏ q', s q') ≠ 0` using `Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'`. Establish `e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q'`. Rewrite `hne`, the goal using `[← hprod]`. Establish `h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0` using `right_ne_zero_of_mul hne`.

Clear denominators, using `[h0 q, h1]` for the nonvanishing conditions. Rewrite using `[e]`. Conclude with `(locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _) (le_locSub D _ (D.prod_mem fun q' _ => hD q'))`.
-/
theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

/- English proof (translation)
Introduce `K _ Q _ A B t h0 hA hB hAB hBA`. Establish `hT : (∏ q, t q) ∈ A` using `A.prod_mem fun q _ => hA q`. Establish `hTi : (∏ q, t q)⁻¹ ∈ B`. Rewrite using `[← Finset.prod_inv_distrib]`. Conclude with `B.prod_mem fun q _ => hB q`.

Establish `hBle : B ≤ locSub A (∏ q, t q)`. Use `hBA.trans ((Subring.closure_le).2 ?_)` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨q, rfl⟩)`. Conclude with `le_locSub A _ hx`. Conclude with `inv_mem_locSub_prod A t h0 hA q`.

Establish `hAle : A ≤ locSub B (∏ q, t q)⁻¹`. Use `hAB.trans ((Subring.closure_le).2 ?_)` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨q, rfl⟩)`. Conclude with `le_locSub B _ hx`. Establish `h` using `inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q`.

Rewrite `h` using `[Finset.prod_inv_distrib]`. Simplify using `using h`. Use `le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)` and prove the remaining obligations. Introduce and unpack `x (hx | hx)`. Conclude with `hAle hx`.

Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `le_locSub B _ hTi`. Introduce and unpack `x (hx | hx)`. Conclude with `hBle hx`. Rewrite using `[Set.mem_singleton_iff.1 hx, inv_inv]`.

Conclude with `le_locSub A _ hT`.
-/
theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
