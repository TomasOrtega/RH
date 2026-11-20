import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeIndepSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeIndep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem eq_zero_of_monomial_mul (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (coeff (e + d)) h
  rw [coeff_monomial_mul, one_mul, coeff_zero] at this
  rw [this, coeff_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem eq_zero_of_mk_eq_zero {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I), LocalizedModule.mk_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [one_smul, one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at ht
  obtain ⟨e, he⟩ := cellMon_monomial t.2
  rw [he] at ht
  exact eq_zero_of_monomial_mul e ht

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers.
-/
theorem shift_injective (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
-/
theorem smul_smul_monoFrac (I : ∀ k, Finset (ι k)) (u : (Σ k, ι k) →₀ ℕ) (r : S) (b : (Σ k, ι k) → ℤ)
    (hI : ∀ k, negSet b k ⊆ I k) (hb : negExp b ≤ u) :
    (monomial u (1 : S) : MRingOver S ι) • (r • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (monomial (posExp b + u - negExp b) r)) (1 : KH.cellMon S I) := by
  rw [monoFrac, dif_pos hI, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  simp only [smul_eq_mul, smul_monomial, monomial_mul, mul_one, one_mul]
  congr 1
  rw [add_tsub_cancel_of_le (le_add_left hb), add_comm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

A detailed English derivation is pending.
-/
theorem eq_zero_of_sum_smul_monoFrac (I : ∀ k, Finset (ι k)) (A : Finset ((Σ k, ι k) → ℤ))
    (g : ((Σ k, ι k) → ℤ) → S) (hg : ∀ b ∈ A, ¬ (∀ k, negSet b k ⊆ I k) → g b = 0)
    (h : ∑ b ∈ A, g b • monoFrac S I b = 0) : ∀ a ∈ A, g a = 0 := by
  classical
  set u : (Σ k, ι k) →₀ ℕ := ∑ b ∈ A.filter (fun b => ∀ k, negSet b k ⊆ I k), negExp b with hu
  set c : ((Σ k, ι k) → ℤ) → ((Σ k, ι k) →₀ ℕ) := fun b => posExp b + u - negExp b with hc
  have hle : ∀ b ∈ A, (∀ k, negSet b k ⊆ I k) → negExp b ≤ u := fun b hb hI =>
    Finset.single_le_sum (f := negExp) (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨hb, hI⟩)
  have hterm : ∀ b ∈ A, (monomial u (1 : S) : MRingOver S ι) • (g b • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (c b) (g b)))
        (1 : KH.cellMon S I) := by
    intro b hb
    by_cases hI : ∀ k, negSet b k ⊆ I k
    · exact smul_smul_monoFrac I u (g b) b hI (hle b hb hI)
    · rw [hg b hb hI, zero_smul, smul_zero, monomial_zero, map_zero, LocalizedModule.zero_mk]
  have key : ∑ b ∈ A, monomial (c b) (g b) = 0 := by
    apply eq_zero_of_mk_eq_zero (I := I)
    have e1 : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (∑ b ∈ A, monomial (c b) (g b))) (1 : KH.cellMon S I) =
        ∑ b ∈ A, LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
          (monomial (c b) (g b))) (1 : KH.cellMon S I) := by
      rw [map_sum]
      exact map_sum (LocalizedModule.mkLinearMap (KH.cellMon S I) _) _ _
    rw [e1, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  intro a ha
  by_cases hI : ∀ k, negSet a k ⊆ I k
  · have hk := congrArg (coeff (c a)) key
    rw [coeff_sum, Finset.sum_eq_single a, coeff_monomial, if_pos rfl, coeff_zero] at hk
    · exact hk
    · intro b hb hba
      by_cases hbI : ∀ k, negSet b k ⊆ I k
      · rw [coeff_monomial, if_neg]
        exact fun hcb => hba (shift_injective u (hle b hb hbI) (hle a ha hI) hcb)
      · rw [hg b hb hbI, monomial_zero, coeff_zero]
    · exact fun hna => absurd ha hna
  · exact hg a ha hI

end KHFreeIndep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem KHFreeIndep.full : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
