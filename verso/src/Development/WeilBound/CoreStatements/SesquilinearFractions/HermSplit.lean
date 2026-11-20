import Development.WeilBound.CoreStatements.SesquilinearFractions.PerDiscrete

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

def Hm : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k k' => if ty k = ty k' then 2 * Complex.I * ty k (G (blk hty k) (blk hty k')) else 0

def Q (σ : E →+* ℂ) (z w : Fin g → ℂ) : ℂ :=
  ∑ k : {k // ty k = σ}, ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k')

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem herm_split (z w : Fin g → ℂ) : hermForm (Hm hty G) z w = ∑ σ, Q hty G σ z w := by
  have hF : ∀ σ : E →+* ℂ, ∀ k : {k // ty k = σ},
      ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k') =
      z k * (Hm hty G *ᵥ star w) k := by
    intro σ ⟨k, hk⟩
    simp only [mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype (fun k' => ty k' = σ)]
    have h2 : ∑ k' : {k' // ¬ ty k' = σ}, z k * (Hm hty G k k' * conj (w k')) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨k', hk'⟩ _
      have hne : ¬ ty k = ty k' := by
        rw [hk]
        exact fun h => hk' h.symm
      simp [Hm, hne]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    rintro ⟨k', hk'⟩ _
    have heq : ty k = ty k' := hk.trans hk'.symm
    simp only [Hm, Matrix.of_apply, heq, if_true]
    rw [hk']
    ring
  unfold hermForm
  rw [dotProduct, ← Fintype.sum_fiberwise ty]
  apply Finset.sum_congr rfl
  intro σ _
  unfold Q
  apply Finset.sum_congr rfl
  intro k _
  exact (hF σ k).symm

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem Q_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin p, ∑ b : Fin p, z ((eP hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inl a) (.inl b))) * conj (w ((eP hty σ h).symm b)) := by
  have hb : ∀ a : Fin p, blk hty ((eP hty σ h).symm a : Fin g) = Sum.inl a := by
    intro a
    rw [blk_inl hty σ h _ ((eP hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem Q_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin q, ∑ b : Fin q, z ((eQ hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inr a) (.inr b))) * conj (w ((eQ hty σ h).symm b)) := by
  have hb : ∀ a : Fin q, blk hty ((eQ hty σ h).symm a : Fin g) = Sum.inr a := by
    intro a
    rw [blk_inr hty σ h _ ((eQ hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

end PositivityTheory.Xgf.DPer

end
