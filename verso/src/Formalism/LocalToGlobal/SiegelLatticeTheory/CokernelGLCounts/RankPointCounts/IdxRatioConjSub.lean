import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.IdxCocycle

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

section Conj

variable {G : Type} [Group G]

def cj (s : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj s⁻¹).toMonoidHom

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem mem_cj {s : G} {X : Subgroup G} {g : G} : g ∈ cj s X ↔ s * g * s⁻¹ ∈ X := by
  unfold cj
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨s * g * s⁻¹, h, by simp [mul_assoc]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cj_le {s : G} {X Y : Subgroup G} (h : X ≤ Y) : cj s X ≤ cj s Y := Subgroup.map_mono h

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cj_self {s : G} {X : Subgroup G} (hs : s ∈ X) : cj s X = X := by
  ext g
  rw [mem_cj]
  constructor
  · intro h
    have h2 : s⁻¹ * (s * g * s⁻¹) * s ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hs) h) hs
    simpa [mul_assoc] using h2
  · intro h
    exact X.mul_mem (X.mul_mem hs h) (X.inv_mem hs)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem relIndex_cj (s : G) (X Y : Subgroup G) : (cj s X).relIndex (cj s Y) = X.relIndex Y := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s⁻¹).injective

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem idxRatio_self (A : Subgroup G) : IdxRatio A A = 1 := by
  simp [IdxRatio, Subgroup.relIndex_self]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem idxRatio_conj_sub (A B B' : Subgroup G) (s : G) (hBA : B ≤ A) (hAB' : A ≤ B') (hs : s ∈ B')
    (hfin : B.relIndex B' ≠ 0) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  have hmul : B.relIndex A * A.relIndex B' = B.relIndex B' := Subgroup.relIndex_mul_relIndex B A B' hBA hAB'
  have hBA0 : B.relIndex A ≠ 0 := fun h => hfin (by rw [← hmul, h, zero_mul])
  have hAB0 : A.relIndex B' ≠ 0 := fun h => hfin (by rw [← hmul, h, mul_zero])
  have hB'eq : cj s B' = B' := cj_self hs
  have hA'le : cj s A ≤ B' := hB'eq ▸ cj_le hAB'
  have hA'idx : (cj s A).relIndex B' = A.relIndex B' := by
    rw [← relIndex_cj s A B', hB'eq]
  have e1 := idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hBA0)
  have e2 := idxCocycle G A (cj s A) B' hA'le (by rw [hA'idx]; exact hAB0)
  have e3 := idxCocycle G A A B' hAB' hAB0
  rw [idxRatio_self] at e3
  rw [hA'idx, ← e3] at e2
  rw [e1, e2, relIndex_cj, mul_one]

end Conj

section Dc

variable {K : Type} [Group K] (A : Subgroup K) (π : K →* A) (H : Subgroup K)

def dcMap (k : K) : A ⧸ H.map π := QuotientGroup.mk (π k)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem dcMap_surjective (hπ : ∀ a : A, π a = a) : Function.Surjective (dcMap A π H) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, by simp [dcMap, hπ]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem dcMap_eq_iff (k k' : K) :
    dcMap A π H k = dcMap A π H k' ↔ ∃ n ∈ π.ker, ∃ h ∈ H, k' = n * k * h := by
  unfold dcMap
  rw [QuotientGroup.eq, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hH, hh⟩
    refine ⟨k' * h⁻¹ * k⁻¹, ?_, h, hH, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hh]
    group
  · rintro ⟨n, hn, h, hH, rfl⟩
    refine ⟨h, hH, ?_⟩
    rw [MonoidHom.mem_ker] at hn
    rw [map_mul, map_mul, hn, one_mul]
    group

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem card_dc (hπ : ∀ a : A, π a = a) :
    Nat.card (Quotient (Setoid.ker (dcMap A π H))) = (H.map π).index := by
  rw [Subgroup.index, Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ (dcMap_surjective A π H hπ))]

end Dc

end Formalism.L2.SG.Pf.ProdEP2Core
