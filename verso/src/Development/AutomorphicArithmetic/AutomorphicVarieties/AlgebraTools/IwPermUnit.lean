import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLenStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem hk_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) : hk ρ I 1 = 1 :=
  (hkNorm A G M ρ I 1 hI (one_mem _)).2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.permUnit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)), IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w hq
  have hI : HeckePair (iwC k n C) := (heckePairIwC k n C).1
  induction h : invLen w generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 h, map_one, hk_one ρ _ hI]
    exact isUnit_one
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have h0 : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        unfold invLen
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro p _ ⟨h1, h2⟩
        exact lt_asymm h1 h2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hlen := ((lenStep n w).1 i j hij).2 hlt
    have hlt' : (Equiv.swap i j * w)⁻¹ i < (Equiv.swap i j * w)⁻¹ j := by
      simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hlt
    have hm := permMul k n C A M ρ (Equiv.swap i j * w) i j hij hlt'
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at hm
    rw [← hm]
    exact ((simpleQuad k n C A M ρ i j hij).1 hq).mul (ih _ (by omega))
