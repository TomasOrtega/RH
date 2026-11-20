import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ ι J z hfin`. Use `set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO`. Use `haveI : Finite O := hfin.to_subtype`. Use `set w : J → Qbar l := fun j => ι.symm (z j) with hw`. Set `K : Finset J → IntermediateField ℚ_[l] (Qbar l)` to `fun s => IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))`.

Establish `hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s)` using `fun s => by haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Establish `hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O`. Introduce `s`. Use `haveI := hKfin s`.

Rewrite using `[← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]`. Set `g : (K s →ₐ[ℚ_[l]] Qbar l) → O` to `fun φ => ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)), ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l)) (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩`. Apply `Nat.card_le_card_of_injective g` to reduce the goal to its premises. Introduce `φ ψ h`. Apply `IntermediateField.adjoin_algHom_ext` to reduce the goal to its premises.

Introduce and unpack `x ⟨j, hj, rfl⟩`. Establish `h1` using `ι.injective (congrFun (congrArg Subtype.val h) j)`. Establish `e1` using `AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩`. Establish `e2` using `AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2`.

Conclude with `e1.symm.trans (h1.trans e2)`. Use `set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR`. Establish `hne : R.Nonempty` using `⟨_, ∅, rfl⟩`. Establish `hbdd : BddAbove R` using `⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩`. Take `⟨s0, hs0⟩` from `Nat.sSup_mem hne hbdd`.

Use `haveI := hKfin s0`. Use `⟨K s0, inferInstance, fun j => ?_⟩` and prove the remaining obligations. Establish `hle : K s0 ≤ K (insert j s0)` using `IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))`. Use `haveI := hKfin (insert j s0)`. Establish `heq : K s0 = K (insert j s0)`.

Apply `IntermediateField.eq_of_le_of_finrank_le hle` to reduce the goal to its premises. Rewrite using `[show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]`. Conclude with `le_csSup hbdd ⟨insert j s0, rfl⟩`. Rewrite using `[heq]`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩`.
-/
theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
