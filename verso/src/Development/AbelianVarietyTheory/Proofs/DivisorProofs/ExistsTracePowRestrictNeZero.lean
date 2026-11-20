import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionHeisenbergInvariant

noncomputable section

open ValuativeRel GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.GLDoubling

namespace GlobalTheory.IwahoriUnit

section Gen

variable {G : Type} [Group G]

def cosets (I : Subgroup G) (x : G) : Set (G ⧸ I) :=
  (QuotientGroup.mk : G → G ⧸ I) '' DoubleCoset.doubleCoset x I I

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem cosets_eq_orbit (I : Subgroup G) (x : G) : cosets I x = MulAction.orbit I (x : G ⧸ I) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * x : G) : G ⧸ I) = ((a * x * b : G) : G ⧸ I)
    rw [QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨a, rfl⟩
    exact ⟨a * x * 1, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, 1, one_mem _, rfl⟩, by rw [mul_one]; rfl⟩

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem fixed_eq_fixd (π : Representation E G V) (I : Subgroup G) : fixed π I = UpperTheory.V.Hi.fixd π I := by
  ext v
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem hk_apply (π : Representation E G V) (I : Subgroup G) (x : G) (h : (cosets I x).Finite)
    (v : UpperTheory.V.Hi.fixd π I) :
    (UpperTheory.V.AlgebraTools.hk π I x v : V) = ∑ᶠ q ∈ cosets I x, π q.out v := by
  rw [cosets_eq_orbit] at h ⊢
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := h
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply E G V π I I x h).1 v, UpperTheory.V.Hi.dc,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_cosets (x : GL (Fin N) k) : (cosets (iwahori k (Fin N)) x).Finite := by
  rw [cosets_eq_orbit, ← (UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1]
  exact (UpperTheory.V.AlgebraTools.heckePairIwC k N ⊤).1 x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dom_of_antitone {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {ν : Fin N → ℤ} (hν : Antitone ν) :
    UpperTheory.V.AlgebraTools.Dom (fun i => ϖ ^ ν i) := by
  intro i j hij
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hν hij)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem torusElt_pow (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    torusElt k (Fin N) ϖ ν ^ m = diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m) := by
  rw [map_pow]; rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dom_pow {t : Fin N → kˣ} (ht : UpperTheory.V.AlgebraTools.Dom t) (m : ℕ) : UpperTheory.V.AlgebraTools.Dom (t ^ m) := by
  intro i j hij
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_left₀ zero_le' (ht i j hij) m

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_equiv_doubleCoset (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (ν : Fin N → ℤ) (hν : Antitone ν) (E V : Type) [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (π : Representation E (GL (Fin N) k) V) :
    (∀ m : ℕ, (cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m)).Finite) ∧
    ∃ T : fixed π (iwahori k (Fin N)) ≃ₗ[E] fixed π (iwahori k (Fin N)),
      (∀ v, (T v : V) = ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν), π q.out v) ∧
      ∀ (m : ℕ) v, ((T ^ m) v : V) =
        ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m), π q.out v := by
  refine ⟨fun m => finite_cosets _, ?_⟩
  have hd := dom_of_antitone hϖ hν
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : E) := by
    refine IsUnit.mk0 _ (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul k N ⊤ E V π
  rw [(UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1] at hmul hunit
  rw [fixed_eq_fixd]
  have hone : UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) 1) = 1 := by
    have h := hmul 1 1 UpperTheory.V.AlgebraTools.dom_one UpperTheory.V.AlgebraTools.dom_one
    rw [mul_one] at h
    exact (hunit hq 1 UpperTheory.V.AlgebraTools.dom_one).mul_left_cancel (h.trans (mul_one _).symm)
  have hpow : ∀ m : ℕ, UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) fun i => ϖ ^ ν i) ^ m =
      UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m)) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih => rw [pow_succ, pow_succ, ih, hmul _ _ (dom_pow hd m) hd]
  have hb := (Module.End.isUnit_iff _).1 (hunit hq _ hd)
  refine ⟨LinearEquiv.ofBijective _ hb, fun v => hk_apply π _ _ (finite_cosets _) v, fun m v => ?_⟩
  rw [← hk_apply π _ _ (finite_cosets _) v, torusElt_pow, ← hpow]
  congr 1
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end GlobalTheory.IwahoriUnit
