import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_OE : Module.finrank (𝓞 X.B.I.F) (𝓞 X.B.I.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 X.B.I.F) X.B.I.F (𝓞 X.B.I.E) X.B.I.E]
  exact X.B.I.cm.deg2

def tau : 𝓞 X.B.I.E →+* 𝓞 X.B.I.E := RingOfIntegers.mapRingHom (starRingEnd X.B.I.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_coe (x : 𝓞 X.B.I.E) :
    algebraMap (𝓞 X.B.I.E) X.B.I.E (tau X x) = star (algebraMap (𝓞 X.B.I.E) X.B.I.E x) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tau_alg (a : 𝓞 X.B.I.F) :
    tau X (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) = algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a := by
  apply RingOfIntegers.coe_injective
  rw [tau_coe, ← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
    IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E]
  exact (X.B.I.cm.fixed _).2 ⟨_, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem approx (v : HeightOneSpectrum (𝓞 X.B.I.F)) (P : Ideal (𝓞 X.B.I.E)) [P.IsMaximal]
    [P.LiesOver v.asIdeal] (hf : P.inertiaDeg (𝓞 X.B.I.F) = 1)
    (x : 𝓞 X.B.I.E) : ∃ a : 𝓞 X.B.I.F, x - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a ∈ P := by
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P] at hf
  let : Field (𝓞 X.B.I.F ⧸ v.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 X.B.I.E ⧸ P) := Ideal.Quotient.field _
  have htop : (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hf
  have hx : Ideal.Quotient.mk P x ∈ (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) :=
    htop ▸ Algebra.mem_top
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← hy]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem omVUnram_holds : OmVUnram X := by
  intro v P hP hPb hPv
  have : P.IsMaximal := hP.isMaximal hPb
  have := v.isPrime
  have : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  have : Fintype (v.asIdeal.primesOver (𝓞 X.B.I.E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 X.B.I.E)
  rw [finrank_OE X] at hsum
  have he := Ideal.ramificationIdx_pos P (𝓞 X.B.I.F)
  have hf := Ideal.inertiaDeg_pos P (𝓞 X.B.I.F)
  have hmem : P ∈ v.asIdeal.primesOver (𝓞 X.B.I.E) := ⟨hP, inferInstance⟩
  have hle := Finset.single_le_sum
    (f := fun q : v.asIdeal.primesOver (𝓞 X.B.I.E) => q.1.ramificationIdx (𝓞 X.B.I.F) * q.1.inertiaDeg (𝓞 X.B.I.F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨P, hmem⟩)
  simp only at hle
  by_contra hne
  have h2 : 2 * P.inertiaDeg (𝓞 X.B.I.F) ≤ P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) :=
    Nat.mul_le_mul_right _ (by omega)
  have hf1 : P.inertiaDeg (𝓞 X.B.I.F) = 1 := by
    generalize P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) = m at *
    omega

  have hττ : ∀ x, tau X (tau X x) = x := fun x => by
    apply RingOfIntegers.coe_injective; rw [tau_coe, tau_coe, star_star]
  have hQ : (P.comap (tau X)).IsPrime := Ideal.comap_isPrime (tau X) P
  have hQv : (P.comap (tau X)).comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) = v.asIdeal := by
    ext a
    simp only [Ideal.mem_comap, tau_alg]
    rw [← Ideal.mem_comap, hPv]
  have : (P.comap (tau X)).LiesOver v.asIdeal := ⟨hQv.symm⟩
  have hQP : P.comap (tau X) = P := by
    by_contra hQP
    have hQmem : P.comap (tau X) ∈ v.asIdeal.primesOver (𝓞 X.B.I.E) := ⟨hQ, inferInstance⟩
    have hneq : (⟨P, hmem⟩ : v.asIdeal.primesOver (𝓞 X.B.I.E)) ≠ ⟨P.comap (tau X), hQmem⟩ :=
      fun h => hQP (congrArg Subtype.val h).symm
    have h3 := Finset.sum_le_sum_of_subset
      (f := fun q : v.asIdeal.primesOver (𝓞 X.B.I.E) => q.1.ramificationIdx (𝓞 X.B.I.F) * q.1.inertiaDeg (𝓞 X.B.I.F))
      (Finset.subset_univ {⟨P, hmem⟩, ⟨P.comap (tau X), hQmem⟩})
    rw [Finset.sum_pair hneq] at h3
    have heQ := Ideal.ramificationIdx_pos (P.comap (tau X)) (𝓞 X.B.I.F)
    have hfQ := Ideal.inertiaDeg_pos (P.comap (tau X)) (𝓞 X.B.I.F)
    simp only at h3
    have h4 : 1 ≤ (P.comap (tau X)).ramificationIdx (𝓞 X.B.I.F) * (P.comap (tau X)).inertiaDeg (𝓞 X.B.I.F) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h5 : 2 ≤ P.ramificationIdx (𝓞 X.B.I.F) * P.inertiaDeg (𝓞 X.B.I.F) := by omega
    omega

  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P inferInstance
  obtain ⟨a, ha⟩ := approx X v P hf1 θ
  have hτθ : tau X θ = t := by
    apply RingOfIntegers.coe_injective; rw [tau_coe]; exact htθ.symm
  have hb : tau X (θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) ∈ P := by
    have : θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a ∈ P.comap (tau X) := by rw [hQP]; exact ha
    exact this
  rw [map_sub, hτθ, tau_alg] at hb
  apply hnot
  have h6 : θ - t = (θ - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) - (t - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) := by ring
  rw [h6]
  exact sub_mem ha hb

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
