import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.HeckeInertComm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.InertRank

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_dvd_all {A ι : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    (a : ι → A) (s : Finset ι) (h : ∃ i ∈ s, a i ≠ 0) :
    ∃ j ∈ s, a j ≠ 0 ∧ ∀ i ∈ s, a j ∣ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert k s _ ih =>
    by_cases hs : ∃ i ∈ s, a i ≠ 0
    · obtain ⟨j, hj, hj0, hdvd⟩ := ih hs
      rcases ValuationRing.dvd_total (a j) (a k) with hjk | hkj
      · refine ⟨j, Finset.mem_insert_of_mem hj, hj0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hjk
        · exact hdvd i hi
      · refine ⟨k, Finset.mem_insert_self _ _, fun h0 => hj0 ?_, fun i hi => ?_⟩
        · rw [h0] at hkj
          exact zero_dvd_iff.1 hkj
        · rcases Finset.mem_insert.1 hi with rfl | hi
          · exact dvd_rfl
          · exact hkj.trans (hdvd i hi)
    · push_neg at hs
      obtain ⟨i, hi, hi0⟩ := h
      have hk : a k ≠ 0 := by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hi0
        · exact absurd (hs i hi) hi0
      refine ⟨k, Finset.mem_insert_self _ _, hk, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact dvd_rfl
      · rw [hs i hi]
        exact dvd_zero _

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_dvd_all_away {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (P : HeightOneSpectrum R) (a : ι → R) (h : ∃ i, a i ≠ 0) :
    ∃ j, a j ≠ 0 ∧ ∀ i, ∃ r s : R, s ∉ P.asIdeal ∧ s * a i = a j * r := by
  let A := Localization.AtPrime P.asIdeal
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal)
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot A
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨j, -, hj0, hdvd⟩ := exists_dvd_all (fun i => algebraMap R A (a i)) Finset.univ
    ⟨i0, Finset.mem_univ _, fun h0 => hi0 (hinj (by simpa using h0))⟩
  refine ⟨j, fun h0 => hj0 (by simp [h0]), fun i => ?_⟩
  obtain ⟨c, hc⟩ := hdvd i (Finset.mem_univ _)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl c
  refine ⟨r, (s : R), s.2, hinj ?_⟩
  have hs := IsLocalization.mk'_spec A r s
  simp only at hc
  rw [map_mul, map_mul, hc, ← hs]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exists_dep_away {E : Type} [Field E] [NumberField E] {n : ℕ} {ι : Type} [Fintype ι]
    (P : HeightOneSpectrum (𝓞 E)) (v : ι → Fin n → E) (hcard : n < Fintype.card ι) :
    ∃ b : ι → 𝓞 E, ∑ i, b i • v i = 0 ∧ ∃ j, b j ∉ P.asIdeal := by
  classical
  have hdep : ¬ LinearIndependent (𝓞 E) v := by
    intro hli
    have := (LinearIndependent.iff_fractionRing (𝓞 E) E).1 hli |>.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨a, ha, hne⟩ := Fintype.not_linearIndependent_iff.1 hdep
  obtain ⟨j, hj0, hall⟩ := exists_dvd_all_away P a hne
  choose r s hs hrs using hall
  refine ⟨fun i => (∏ k ∈ Finset.univ.erase i, s k) * r i, ?_, j, ?_⟩
  · have hcoef : ∀ i, a j * ((∏ k ∈ Finset.univ.erase i, s k) * r i) = (∏ k, s k) * a i := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      linear_combination (-(∏ k ∈ Finset.univ.erase i, s k)) * hrs i
    have h1 : a j • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hcoef, mul_smul]
      rw [← Finset.smul_sum, ha, smul_zero]
    have hj0' : algebraMap (𝓞 E) E (a j) ≠ 0 := by simpa using hj0
    have h2 : algebraMap (𝓞 E) E (a j) • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [algebraMap_smul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left hj0'
  · have hsj : r j = s j := by
      have : a j * r j = a j * s j := by rw [← hrs j, mul_comm]
      exact mul_left_cancel₀ hj0 this
    beta_reduce
    rw [hsj, mul_comm, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j)]
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hmem
    exact hs k hk

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem coeff_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {P : Ideal (𝓞 E)} {y : List ℕ}
    (hy : ∀ a ∈ y, 0 < a) (A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n))
    (e : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P y)
    (x : Fin y.length → A)
    (hx : ∀ i, e (Submodule.Quotient.mk (x i)) = Pi.single i 1)
    (b : Fin y.length → 𝓞 E) (hz : (∑ i, b i • (x i : Formalism.L2.Col.Sp E n)) ∈ B)
    (i : Fin y.length) : b i ∈ P := by
  classical
  have hq : (Submodule.Quotient.mk (∑ k, b k • x k) : A ⧸ (B ⊓ A).comap A.subtype) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    refine ⟨?_, (∑ k, b k • x k).2⟩
    simpa using hz
  have he : (∑ k, b k • (Pi.single k 1 : Formalism.L2.Col.inType P y)) = 0 := by
    have := congrArg e hq
    rw [map_zero] at this
    rw [← this, ← Submodule.mkQ_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Submodule.mkQ_apply, hx]
  have hi := congrFun he i
  rw [Finset.sum_apply, Finset.sum_eq_single i
    (fun k _ hk => by rw [Pi.smul_apply, Pi.single_eq_of_ne hk.symm, smul_zero]) (by simp),
    Pi.smul_apply, Pi.single_eq_same] at hi
  have hi' : (Ideal.Quotient.mk (P ^ y.get i)) (b i) = 0 := by
    simpa [Algebra.smul_def] using hi
  have hmem := Ideal.Quotient.eq_zero_iff_mem.1 hi'
  have hpos : 0 < y.get i := hy _ (List.get_mem y i)
  exact Ideal.pow_le_self hpos.ne' hmem

/- English proof (translation)
Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem two_mul_length_le {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (P : HeightOneSpectrum (𝓞 E)) (y : List ℕ)
    (d e : Col.DecoSet E n ST SG) (hy : ∀ a ∈ y, 0 < a) (he : e ∈ d.inertSet P.asIdeal y) :
    2 * y.length ≤ n := by
  classical
  obtain ⟨⟨⟨e1⟩, ⟨e2⟩⟩, -, -⟩ := he
  by_contra hlt
  have lift : ∀ {A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n)}
      (f : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P.asIdeal y),
      ∃ x : Fin y.length → A, ∀ i, f (Submodule.Quotient.mk (x i)) = Pi.single i 1 := by
    intro A B f
    have : ∀ i, ∃ a : A, f (Submodule.Quotient.mk a) = Pi.single i 1 := fun i => by
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (f.symm (Pi.single i 1))
      exact ⟨a, by rw [ha, LinearEquiv.apply_symm_apply]⟩
    choose x hx using this
    exact ⟨x, hx⟩
  obtain ⟨x, hx⟩ := lift e1
  obtain ⟨x', hx'⟩ := lift e2
  obtain ⟨b, hb, j, hj⟩ := exists_dep_away (ι := Fin y.length ⊕ Fin y.length) P
    (Sum.elim (fun i => (x i : Formalism.L2.Col.Sp E n)) (fun i => (x' i : Formalism.L2.Col.Sp E n)))
    (by simp; omega)
  rw [Fintype.sum_sum_type] at hb
  simp only [Sum.elim_inl, Sum.elim_inr] at hb
  have h1 : (∑ i, b (Sum.inl i) • (x i : Formalism.L2.Col.Sp E n)) ∈ e.1.N := by
    rw [eq_neg_of_add_eq_zero_left hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x' i).2)
  have h2 : (∑ i, b (Sum.inr i) • (x' i : Formalism.L2.Col.Sp E n)) ∈ d.1.N := by
    rw [eq_neg_of_add_eq_zero_right hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x i).2)
  rcases j with j | j
  · exact hj (coeff_mem hy _ _ e1 x hx (fun i => b (Sum.inl i)) h1 j)
  · exact hj (coeff_mem hy _ _ e2 x' hx' (fun i => b (Sum.inr i)) h2 j)

end GlobalTheory.InertRank
