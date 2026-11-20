import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.HeckeInertComm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.InertRank

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp at h`. Consider the case `insert k s _ ih`. Distinguish the cases in `hs : ∃ i ∈ s, a i ≠ 0`. Take `⟨j, hj, hj0, hdvd⟩` from `ih hs`.

Break down `ValuationRing.dvd_total (a j) (a k) with hjk | hkj` into its components or cases. Use `⟨j, Finset.mem_insert_of_mem hj, hj0, fun i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `hjk`. Conclude with `hdvd i hi`.

Use `⟨k, Finset.mem_insert_self _ _, fun h0 => hj0 ?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite `hkj` using `[h0]`. Conclude with `zero_dvd_iff.1 hkj`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `dvd_rfl`.

Conclude with `hkj.trans (hdvd i hi)`. Use `push_neg at hs`. Take `⟨i, hi, hi0⟩` from `h`. Establish `hk : a k ≠ 0`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases.

Conclude with `hi0`. Conclude with `absurd (hs i hi) hi0`. Use `⟨k, Finset.mem_insert_self _ _, hk, fun i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `dvd_rfl`.

Rewrite using `[hs i hi]`. Conclude with `dvd_zero _`.
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
Set `A` to `Localization.AtPrime P.asIdeal`. Establish `hinj : Function.Injective (algebraMap R A)` using `IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal)`. Use `haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot A`. Take `⟨i0, hi0⟩` from `h`. Take `⟨j, -, hj0, hdvd⟩` from `exists_dvd_all (fun i => algebraMap R A (a i)) Finset.univ ⟨i0, Finset.mem_univ _, fun h0 => hi0 (hinj (by simpa using h0))⟩`.

Use `⟨j, fun h0 => hj0 (by simp [h0]), fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hdvd i (Finset.mem_univ _)`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.asIdeal.primeCompl c`. Use `⟨r, (s : R), s.2, hinj ?_⟩` and prove the remaining obligations. Establish `hs` using `IsLocalization.mk'_spec A r s`.

Simplify using `only at hc`. Rewrite using `[map_mul, map_mul, hc, ← hs]`. Expand and normalize the polynomial expressions, which then agree.
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
Establish `hdep : ¬ LinearIndependent (𝓞 E) v`. Introduce `hli`. Use `(LinearIndependent.iff_fractionRing (𝓞 E) E).1 hli |>.fintype_card_le_finrank` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Take `⟨a, ha, hne⟩` from `Fintype.not_linearIndependent_iff.1 hdep`. Take `⟨j, hj0, hall⟩` from `exists_dvd_all_away P a hne`. Use `choose r s hs hrs using hall`. Use `⟨fun i => (∏ k ∈ Finset.univ.erase i, s k) * r i, ?_, j, ?_⟩` and prove the remaining obligations. Establish `hcoef : ∀ i, a j * ((∏ k ∈ Finset.univ.erase i, s k) * r i) = (∏ k, s k) * a i`.

Introduce `i`. Rewrite using `[← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]`. Take the linear combination `(-(∏ k ∈ Finset.univ.erase i, s k)) * hrs i`. Establish `h1 : a j • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0`. Rewrite using `[Finset.smul_sum]`.

Repeatedly rewrite using `[smul_smul, hcoef, mul_smul]`. Rewrite using `[← Finset.smul_sum, ha, smul_zero]`. Establish `hj0' : algebraMap (𝓞 E) E (a j) ≠ 0` using `by simpa using hj0`. Establish `h2 : algebraMap (𝓞 E) E (a j) • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0`. Rewrite using `[algebraMap_smul]`.

Conclude with `h1`. Conclude with `(smul_eq_zero.1 h2).resolve_left hj0'`. Establish `hsj : r j = s j`. Establish `: a j * r j = a j * s j` using `by rw [← hrs j, mul_comm]`. Conclude with `mul_left_cancel₀ hj0 this`.

Use `beta_reduce`. Rewrite using `[hsj, mul_comm, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j)]`. Introduce `hmem`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hmem`. Conclude with `hs k hk`.
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
Establish `hq : (Submodule.Quotient.mk (∑ k, b k • x k) : A ⧸ (B ⊓ A).comap A.subtype) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Use `⟨?_, (∑ k, b k • x k).2⟩` and prove the remaining obligations. Simplify using `using hz`. Establish `he : (∑ k, b k • (Pi.single k 1 : Formalism.L2.Col.inType P y)) = 0`.

Use `congrArg e hq` as an intermediate fact. Rewrite `this` using `[map_zero]`. Rewrite using `[← this, ← Submodule.mkQ_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, Submodule.mkQ_apply, hx]`.

Establish `hi` using `congrFun he i`. Rewrite `hi` using `[Finset.sum_apply, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.smul_apply, Pi.single_eq_of_ne hk.symm, smul_zero]) (by simp), Pi.smul_apply, Pi.single_eq_same]`. Establish `hi' : (Ideal.Quotient.mk (P ^ y.get i)) (b i) = 0`. Simplify `hi` using `[Algebra.smul_def]`. Establish `hmem` using `Ideal.Quotient.eq_zero_iff_mem.1 hi'`.

Establish `hpos : 0 < y.get i` using `hy _ (List.get_mem y i)`. Conclude with `Ideal.pow_le_self hpos.ne' hmem`.
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
Take `⟨⟨⟨e1⟩, ⟨e2⟩⟩, -, -⟩` from `he`. Assume the negation of the conclusion as `hlt`. Establish `lift : ∀ {A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n)} (f : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P.asIdeal y), ∃ x : Fin y.length → A, ∀ i, f (Submodule.Quotient.mk (x i)) = Pi.single i 1`. Introduce `A B f`. Establish `: ∀ i, ∃ a : A, f (Submodule.Quotient.mk a) = Pi.single i 1` using `fun i => by`.

Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (f.symm (Pi.single i 1))`. Conclude with `⟨a, by rw [ha, LinearEquiv.apply_symm_apply]⟩`. Use `choose x hx using this`. Conclude with `⟨x, hx⟩`. Take `⟨x, hx⟩` from `lift e1`.

Take `⟨x', hx'⟩` from `lift e2`. Take `⟨b, hb, j, hj⟩` from `exists_dep_away (ι := Fin y.length ⊕ Fin y.length) P (Sum.elim (fun i => (x i : Formalism.L2.Col.Sp E n)) (fun i => (x' i : Formalism.L2.Col.Sp E n))) (by simp; omega)`. Rewrite `hb` using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hb`. Establish `h1 : (∑ i, b (Sum.inl i) • (x i : Formalism.L2.Col.Sp E n)) ∈ e.1.N`.

Rewrite using `[eq_neg_of_add_eq_zero_left hb]`. Conclude with `neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x' i).2)`. Establish `h2 : (∑ i, b (Sum.inr i) • (x' i : Formalism.L2.Col.Sp E n)) ∈ d.1.N`. Rewrite using `[eq_neg_of_add_eq_zero_right hb]`. Conclude with `neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x i).2)`.

Break down `j with j | j` into its components or cases. Conclude with `hj (coeff_mem hy _ _ e1 x hx (fun i => b (Sum.inl i)) h1 j)`. Conclude with `hj (coeff_mem hy _ _ e2 x' hx' (fun i => b (Sum.inr i)) h2 j)`.
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
