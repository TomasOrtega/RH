import Mathlib

noncomputable section

namespace GlobalTheory.OrbitUnfold

def ConjSelf (Γ : Type) : Type := Γ

namespace ConjSelf

variable {Γ : Type} [Group Γ]

def of (γ : Γ) : ConjSelf Γ := γ

def val (γ : ConjSelf Γ) : Γ := γ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_of (γ : Γ) : val (of γ) = γ := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem of_val (γ : ConjSelf Γ) : of (val γ) = γ := rfl

instance : MulAction Γ (ConjSelf Γ) where
  smul η γ := of (η * val γ * η⁻¹)
  one_smul γ := by
    show of ((1 : Γ) * val γ * 1⁻¹) = γ
    simp
  mul_smul a b γ := by
    show of (a * b * val γ * (a * b)⁻¹) = of (a * val (of (b * val γ * b⁻¹)) * a⁻¹)
    simp only [val_of]
    congr 1
    group

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_smul (η : Γ) (γ : ConjSelf Γ) : val (η • γ) = η * val γ * η⁻¹ := rfl

/- English proof (translation)
Use extensionality with `η`. Rewrite using `[MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg val h`.

Rewrite `h'` using `[val_smul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `h show of (η * val γ * η⁻¹) = γ`. Rewrite using `[h]`. Use `show val γ * η * η⁻¹ = val γ`.

Use `group`.
-/
theorem stabilizer_eq_centralizer (γ : ConjSelf Γ) :
    MulAction.stabilizer Γ γ = Subgroup.centralizer {val γ} := by
  ext η
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg val h
    rw [val_smul] at h'
    calc η * val γ = η * val γ * η⁻¹ * η := by group
      _ = val γ * η := by rw [h']
  · intro h
    show of (η * val γ * η⁻¹) = γ
    rw [h]
    show val γ * η * η⁻¹ = val γ
    group

end ConjSelf

open ConjSelf

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

/- English proof (translation)
Rewrite using `[← stabilizer_eq_centralizer]`. Use extensionality with `η`. Simplify using `only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_def, Prod.ext_iff]`.
-/
theorem stabilizer_pair (p : Y × ConjSelf Γ) :
    MulAction.stabilizer Γ p = MulAction.stabilizer Γ p.1 ⊓ Subgroup.centralizer {val p.2} := by
  rw [← stabilizer_eq_centralizer]
  ext η
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_def, Prod.ext_iff]

def pairTerm (F : Y → Γ → ℂ) (p : Y × ConjSelf Γ) : ℂ :=
  ((Nat.card (MulAction.stabilizer Γ p) : ℕ) : ℂ)⁻¹ * F p.1 (val p.2)

/- English proof (translation)
Unfold `pairTerm`. Rewrite using `[MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.card_map_of_injective (MulAut.conj η).injective]`. Use `congr 1`. Conclude with `hF η p.1 (val p.2)`.
-/
theorem pairTerm_smul (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (η : Γ) (p : Y × ConjSelf Γ) : pairTerm F (η • p) = pairTerm F p := by
  unfold pairTerm
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj η).injective]
  congr 1
  exact hF η p.1 (val p.2)

/- English proof (translation)
Take `⟨η, hη⟩` from `Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p))`. Rewrite using `[← hη]`. Conclude with `pairTerm_smul F hF η p`.
-/
theorem pairTerm_out (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (p : Y × ConjSelf Γ) :
    pairTerm F (Quotient.out (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p)) = pairTerm F p := by
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p))
  rw [← hη]
  exact pairTerm_smul F hF η p

def pairSum (F : Y → Γ → ℂ) : ℂ :=
  ∑ᶠ o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ), pairTerm F (Quotient.out o)

end GlobalTheory.OrbitUnfold
