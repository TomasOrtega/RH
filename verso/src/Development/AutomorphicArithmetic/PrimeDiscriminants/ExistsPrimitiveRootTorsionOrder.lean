import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField

noncomputable section

namespace UpperTheory

section field

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_primitiveRoot_torsionOrder : ∃ ζ : E, IsPrimitiveRoot ζ (Units.torsionOrder E) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Units.torsion E, orderOf μ = Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion E)
  refine ⟨(((μ : (𝓞 E)ˣ) : 𝓞 E) : E), ?_⟩
  have h1 : IsPrimitiveRoot μ (Units.torsionOrder E) := hμ ▸ IsPrimitiveRoot.orderOf μ
  have h2 : IsPrimitiveRoot (μ : (𝓞 E)ˣ) (Units.torsionOrder E) := IsPrimitiveRoot.coe_submonoidClass_iff.2 h1
  exact (IsPrimitiveRoot.coe_units_iff.2 h2).map_of_injective (f := algebraMap (𝓞 E) E) RingOfIntegers.coe_injective

variable {E}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem root_iff_pow_torsionOrder (x : E) : (∃ m : ℕ, 0 < m ∧ x ^ m = 1) ↔ x ^ Units.torsionOrder E = 1 := by
  refine ⟨fun h => ?_, fun h => ⟨_, Units.torsionOrder_pos E, h⟩⟩
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 h
  have : NeZero (orderOf x) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
  exact orderOf_dvd_iff_pow_eq_one.1 (Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf x))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem two_dvd_torsionOrder : 2 ∣ Units.torsionOrder E := (Units.even_torsionOrder E).two_dvd

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem torsionOrder_dvd_of_algHom (N : ℕ) (hN : Even N) (hN0 : 0 < N) (ψ : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Units.torsionOrder E ∣ N := by
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero (Units.torsionOrder E) := ⟨(Units.torsionOrder_pos E).ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
  have h := Units.dvd_torsionOrder_of_isPrimitiveRoot (hζ.map_of_injective (f := ψ) ψ.toRingHom.injective)
  rwa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := N) (K := CyclotomicField N ℚ), if_pos hN] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem roots_pm_iff : (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1) ↔ Units.torsionOrder E = 2 := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
    refine Nat.dvd_antisymm (hζ.dvd_of_pow_eq_one 2 ?_) two_dvd_torsionOrder
    rcases h ζ ⟨_, Units.torsionOrder_pos E, hζ.pow_eq_one⟩ with rfl | rfl <;> norm_num
  · intro h x hx
    rw [root_iff_pow_torsionOrder, h] at hx
    exact mul_self_eq_one_iff.1 (by rwa [← sq])

end field

end UpperTheory

namespace Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def w : ℕ := Units.torsionOrder H.E

def nuW (l : ℕ) : ℕ := H.w.factorization l

def IsMu (x : H.E) : Prop := ∃ m : ℕ, 0 < m ∧ x ^ m = 1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem w_pos : 0 < H.w := Units.torsionOrder_pos H.E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem two_dvd_w : 2 ∣ H.w := UpperTheory.two_dvd_torsionOrder

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem two_le_w : 2 ≤ H.w := Nat.le_of_dvd H.w_pos H.two_dvd_w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isMu_iff (x : H.E) : H.IsMu x ↔ x ^ H.w = 1 := UpperTheory.root_iff_pow_torsionOrder x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_primitiveRoot_w : ∃ ζ : H.E, IsPrimitiveRoot ζ H.w := UpperTheory.exists_primitiveRoot_torsionOrder H.E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem muPM_iff : H.MuPM ↔ H.w = 2 := UpperTheory.roots_pm_iff

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem MuPM.nuW (h : H.MuPM) (l : ℕ) : H.nuW l = if l = 2 then 1 else 0 := by
  unfold HostRaw.nuW
  rw [H.muPM_iff.1 h, Nat.prime_two.factorization, Finsupp.single_apply]
  simp only [eq_comm]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem w_dvd_condN : H.w ∣ H.condN :=
  UpperTheory.torsionOrder_dvd_of_algHom H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) H.cycEmb

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_nuW_mul_log_le (S : Finset ℕ) : ∑ l ∈ S, (H.nuW l : ℝ) * Real.log l ≤ Real.log H.w := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h0 : ∀ l : ℕ, 0 ≤ (H.w.factorization l : ℝ) * Real.log l := fun l => by positivity
  calc ∑ l ∈ S, (H.nuW l : ℝ) * Real.log l
      = ∑ l ∈ S ∩ H.w.factorization.support, (H.w.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.inter_subset_left fun l hl hl' => ?_).symm
        have : H.w.factorization l = 0 := by
          by_contra h
          exact hl' (Finset.mem_inter.2 ⟨hl, Finsupp.mem_support_iff.2 h⟩)
        simp [HostRaw.nuW, this]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun l _ _ => h0 l

end Formalism.HC.HostRaw

end
