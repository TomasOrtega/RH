import Mathlib
import Formalism.SharpRestriction.GrowthBounds.DataG

open Formalism.MainNotions.G MvPolynomial

noncomputable section

namespace GlobalTheory.PrescribedRank

variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def noPlaces : Places p O Kf where
  w := 0
  nV := 0
  n' := fun _ => 0
  W := fun _ => O
  Qq := fun _ => Kf
  ι := fun _ => RingHom.id Kf
  σ := fun _ => RingEquiv.refl Kf
  j := fun _ => RingHom.id O
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun _ _ _ => 0
  dom := fun v => v.elim0

instance : IsEmpty (Fin (noPlaces p O Kf).nV) := inferInstanceAs (IsEmpty (Fin 0))

def trivLevel : Level (noPlaces p O Kf) where
  Γ := PUnit
  act := fun _ => 1
  χ := 1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tup_eq (L L' : (noPlaces p O Kf).Tup) : L = L' := funext fun v => isEmptyElim v

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isLatTup (L : (noPlaces p O Kf).Tup) : (noPlaces p O Kf).IsLatTup L := fun v => isEmptyElim v

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem actX_apply (γ : (trivLevel p O Kf).Γ) (x : (noPlaces p O Kf).Xsp) :
    (trivLevel p O Kf).actX γ x = x := by
  have h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _ := fun G =>
    MvPolynomial.algHom_ext fun i => isEmptyElim i.1
  unfold Level.actX Places.natAct
  rw [h, Fintype.prod_empty]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem htupW_eq (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    rw [Fintype.prod_empty]
    rfl
  · rintro rfl
    exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_funMod (Hv : (noPlaces p O Kf).Tup → Submodule O (noPlaces p O Kf).Xsp)
    (F : (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) :
    F ∈ (trivLevel p O Kf).funMod Hv ↔ ∀ L, F L ∈ Hv L := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩ L
    exact h L (isLatTup p O Kf L)
  · intro h
    refine ⟨⟨fun L _ => h L, fun L hL => absurd (isLatTup p O Kf L) hL⟩, fun γ L => ?_⟩
    have hχ : (trivLevel p O Kf).χ γ = 1 := rfl
    rw [tup_eq p O Kf ((trivLevel p O Kf).smul γ L) L, hχ]
    simp [actX_apply]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem finClasses : (trivLevel p O Kf).FinClasses :=
  ⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ =>
    ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩

def gat (d : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := noPlaces p O Kf
  comp := Fin d
  lev := fun _ => trivLevel p O Kf
  e := 0

def constMap (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) where
  toFun c := fun i _ => c i • (1 : (noPlaces p O Kf).Xsp)
  map_add' a b := by
    funext i L
    simp [add_smul]
  map_smul' a b := by
    funext i L
    simp [mul_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem constMap_injective (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h : c i • (1 : (noPlaces p O Kf).Xsp) = 0 := congrFun (congrFun hc i) (fun v => isEmptyElim v)
  have h2 := congrArg (MvPolynomial.coeff 0) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero,
    Algebra.smul_def, mul_one] at h2
  apply hinj
  rw [h2]
  simp

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem range_constMap (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by
  ext F
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ i L
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    refine ⟨fun i => c i (fun v => isEmptyElim v), ?_⟩
    funext i L
    rw [tup_eq p O Kf L (fun v => isEmptyElim v)]
    exact hc i _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem gat_d (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) : (gat p O Kf d).d = d := by
  have h : (gat p O Kf d).d = Module.finrank O
      (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW) := rfl
  rw [h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GAtP₂ : ∀ (p d : ℕ), p.Prime → ∃ G : GAtP p, G.d = d ∧ G.FinClasses := by
  intro p d hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨gat p ℤ_[p] ℚ_[p] d, gat_d p _ _ d (IsFractionRing.injective ℤ_[p] ℚ_[p]),
    fun _ => finClasses p _ _⟩

end GlobalTheory.PrescribedRank
