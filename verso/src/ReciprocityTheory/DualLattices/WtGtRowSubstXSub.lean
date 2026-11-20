import ReciprocityTheory.DualLattices.ConstantCoeffRowSubst

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))

def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem wt_add (A B : Fin ν × ι →₀ ℕ) : wt (A + B) = wt A + wt B := by
  unfold wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

def tor (s : ℂ) : Matrix (Fin ν) (Fin ν) ℂ := Matrix.diagonal fun k => s ^ (2 ^ (ν - 1 - (k : ℕ)))

def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (coeff A P)

def WtGe (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d ≤ wt A

def WtGt (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d < wt A

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem WtGt.ge {d : ℕ} {P : MvPolynomial (Fin ν × ι) ℂ} (h : WtGt d P) : WtGe d P :=
  fun A hA => le_of_lt (h A hA)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem WtGt.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGt d P) (h2 : WtGt d Q) :
    WtGt d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem WtGe.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe d Q) :
    WtGe d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem WtGe.mul {d e : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe e Q) :
    WtGe (d + e) (P * Q) := by
  intro A hA
  obtain ⟨B, hB, B', hB', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hA)
  rw [wt_add]
  have := h1 B hB
  have := h2 B' hB'
  omega

end ReciprocityTheory.PGsh
