import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori.UpInv

variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]

def low (wt : ι → ℕ) (P : ι → Module.End L V) (m : ℕ) : Submodule L V where
  carrier := {x | ∀ i, m ≤ wt i → P i x = 0}
  add_mem' {x y} hx hy i hi := by rw [map_add, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi, smul_zero]

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sum_pieces {P : ι → Module.End L V} (hP : IsPieces P) (x : V) :
    ∑ j, P j x = x := by
  have h := congrArg (fun T : Module.End L V => T x) hP.sum
  simpa [LinearMap.sum_apply] using h

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem map_low_le {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P)
    {a : Module.End L V} (ha : IsUpper wt P a) (m : ℕ) :
    (low wt P m).map a ≤ low wt P m := by
  rintro _ ⟨x, hx, rfl⟩ i hi
  have hx' : x ∈ low wt P m := hx
  rw [← sum_pieces hP x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m ≤ wt j
  · rw [hx' j hj, map_zero, map_zero]
  · have h := congrArg (fun T : Module.End L V => T x) (ha i j (by omega))
    simpa using h

/- English proof (translation)
Introduce a local definition for the expression. A detailed English derivation is pending.
-/
theorem map_low_eq [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) (m : ℕ) : (low wt P m).map a = low wt P m := by
  let e : V ≃ₗ[L] V := LinearEquiv.ofLinear a a' h1 h2
  exact Submodule.eq_of_le_of_finrank_eq (map_low_le hP ha m)
    (LinearEquiv.finrank_map_eq e (low wt P m))

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem inv_mem_low [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) {m : ℕ} {x : V} (hx : x ∈ low wt P m) : a' x ∈ low wt P m := by
  rw [← map_low_eq hP h1 h2 ha m] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := congrArg (fun T : Module.End L V => T y) h2
  have h' : a' (a y) = y := by simpa using h
  rwa [h']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem piece_mem_low {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P) (j : ι) (x : V) :
    P j x ∈ low wt P (wt j + 1) := by
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  have h := congrArg (fun T : Module.End L V => T x) (hP.orth i j hij)
  simpa using h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isUpper_inv : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V),
    GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 →
      GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  intro L V ι _ _ _ _ _ wt P hP a a' h1 h2 ha i j hij
  refine LinearMap.ext fun x => ?_
  have h := inv_mem_low hP h1 h2 ha (piece_mem_low (wt := wt) hP j x) i (by omega)
  simpa using h

end GlobalTheory.CompanionTheory.Iwahori.UpInv

end
