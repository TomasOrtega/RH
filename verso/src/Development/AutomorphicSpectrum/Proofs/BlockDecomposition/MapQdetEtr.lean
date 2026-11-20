import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliMap

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/- English proof (translation)
Unfold `Formalism.REAL.Tm`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_Tm (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    φ (Formalism.REAL.Tm X u a b) = Formalism.REAL.Tm (fun a b => φ (X a b)) u a b := by
  unfold Formalism.REAL.Tm
  split_ifs <;> simp

/- English proof (translation)
Unfold `Formalism.REAL.qminor`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `congr 2`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `map_Tm φ X _ _ _`.
-/
theorem map_qminor (φ : A →ₐ[ℂ] B) {n t : ℕ} (X : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    φ (Formalism.REAL.qminor X a b u) = Formalism.REAL.qminor (fun a b => φ (X a b)) a b u := by
  unfold Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  exact map_Tm φ X _ _ _

/- English proof (translation)
Unfold `Formalism.REAL.qdet`. Conclude with `map_qminor φ X id id u`.
-/
theorem map_qdet (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u := by
  unfold Formalism.REAL.qdet
  exact map_qminor φ X id id u

/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero => by_cases h : a = b <;> simp [Formalism.REAL.epow, h]`. Consider the case `succ m ih => simp [Formalism.REAL.epow, map_sum, map_mul, ih, apply_ite]`.
-/
theorem map_epow (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    φ (Formalism.REAL.epow X k a b) = Formalism.REAL.epow (fun a b => φ (X a b)) k a b := by
  induction k generalizing a b with
  | zero => by_cases h : a = b <;> simp [Formalism.REAL.epow, h]
  | succ m ih => simp [Formalism.REAL.epow, map_sum, map_mul, ih, apply_ite]

/- English proof (translation)
Unfold `Formalism.REAL.etr`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl (fun a _ => map_epow φ X k a a)`.
-/
theorem map_etr (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) :
    φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  unfold Formalism.REAL.etr
  rw [map_sum]
  exact Finset.sum_congr rfl (fun a _ => map_epow φ X k a a)

/- English proof (translation)
Introduce `A B _ _ _ _ φ n X u k`. Conclude with `⟨map_qdet φ X u, map_etr φ X k⟩`.
-/
theorem map_qdet_etr : ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (n : ℕ) (X : Fin n → Fin n → A) (u : ℂ) (k : ℕ),
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u ∧
      φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  intro A B _ _ _ _ φ n X u k
  exact ⟨map_qdet φ X u, map_etr φ X k⟩

end GlobalTheory.CompanionTheory.CapelliMap
