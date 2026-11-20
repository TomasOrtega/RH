import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

/- English proof (translation)
Use `haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by`. Take `⟨c, rfl⟩` from `hA a`. Conclude with `isIntegral_algebraMap⟩`. Establish `hy : IsIntegral ℂ y` using `isIntegral_trans y h`. Conclude with `minpoly.mem_range_of_degree_eq_one ℂ y (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))`.
-/
private lemma int_range {L A : Type} [Field L] [Algebra ℂ L] [CommRing A] [Algebra ℂ A] [Algebra A L]
    [IsScalarTower ℂ A L] (hA : ∀ a : A, a ∈ (algebraMap ℂ A).range) {y : L} (h : IsIntegral A y) :
    y ∈ (algebraMap ℂ L).range := by
  haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by
    obtain ⟨c, rfl⟩ := hA a
    exact isIntegral_algebraMap⟩
  have hy : IsIntegral ℂ y := isIntegral_trans y h
  exact minpoly.mem_range_of_degree_eq_one ℂ y
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))

/- English proof (translation)
Take `⟨p, hp, he⟩` from `hy`. Use `⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `he`.
-/
private lemma int_mono {E L : Type} [CommRing E] [Algebra ℂ E] [CommRing L] [Algebra E L]
    {A B : Subalgebra ℂ E} (h : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact he

/- English proof (translation)
Take `⟨p, hp, he⟩` from `hy`. Use `set q : Polynomial L := p.map (algebraMap A' L) with hq`. Establish `hqm : q.Monic` using `hp.map _`. Establish `hqe : q.eval₂ (RingHom.id L) y = 0`. Rewrite using `[hq, Polynomial.eval₂_map]`.

Simplify using `using he`. Establish `hcoef : ∀ i, q.coeff i ∈ A'` using `fun i => by`. Rewrite using `[hq, Polynomial.coeff_map]`. Conclude with `(p.coeff i).2`. Establish `hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A`.

Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert a t _ ih`. Take `⟨M, hM⟩` from `ih`.

Take `⟨N, hN⟩` from `hc _ (hcoef a)`. Use `⟨M + N, fun i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Rewrite using `[pow_add, mul_assoc]`. Conclude with `A.mul_mem (A.pow_mem hs _) hN`.

Rewrite using `[add_comm, pow_add, mul_assoc]`. Conclude with `A.mul_mem (A.pow_mem hs _) (hM i hi)`. Take `⟨M, hM⟩` from `hM (Finset.range (q.natDegree + 1))`. Use `⟨M, ?_⟩` and prove the remaining obligations. Establish `hrm : (Polynomial.scaleRoots q (s ^ M)).Monic` using `(Polynomial.monic_scaleRoots_iff _).2 hqm`.

Establish `hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0`. Use `Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)` as an intermediate fact. Rewrite `this` using `[hqe, mul_zero]`. Rewrite using `[mul_comm]`. Conclude with `this`.

Establish `hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A`. Introduce `i`. Rewrite using `[Polynomial.coeff_scaleRoots]`. Break down `lt_trichotomy i q.natDegree with hi | hi | hi` into its components or cases. Take `⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1` from `⟨q.natDegree - i - 1, by omega⟩`.

Rewrite using `[hk, pow_succ, mul_comm, mul_assoc]`. Use `A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))`. Substitute `hi` using the available equality.

Simplify using `[hqm.coeff_natDegree, A.one_mem]`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]`. Conclude with `A.zero_mem`. Establish `hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `i`. Conclude with `⟨⟨_, hA i⟩, rfl⟩`. Take `⟨r, hr, -, hrm'⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm`. Use `⟨r, hrm', ?_⟩` and prove the remaining obligations. Rewrite `hre` using `[← hr, Polynomial.eval₂_map]`.

Simplify using `using hre`.
-/
private lemma int_scale {L : Type} [Field L] [Algebra ℂ L] (A A' : Subalgebra ℂ L) (s : L) (hs : s ∈ A)
    (hc : ∀ c ∈ A', ∃ N : ℕ, s ^ N * c ∈ A) {y : L} (hy : IsIntegral A' y) :
    ∃ N : ℕ, IsIntegral A (y * s ^ N) := by
  obtain ⟨p, hp, he⟩ := hy
  set q : Polynomial L := p.map (algebraMap A' L) with hq
  have hqm : q.Monic := hp.map _
  have hqe : q.eval₂ (RingHom.id L) y = 0 := by
    rw [hq, Polynomial.eval₂_map]
    simpa using he
  have hcoef : ∀ i, q.coeff i ∈ A' := fun i => by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff i).2
  have hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t _ ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨N, hN⟩ := hc _ (hcoef a)
      refine ⟨M + N, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) hN
      · rw [add_comm, pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) (hM i hi)
  obtain ⟨M, hM⟩ := hM (Finset.range (q.natDegree + 1))
  refine ⟨M, ?_⟩
  have hrm : (Polynomial.scaleRoots q (s ^ M)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hqm
  have hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)
    rw [hqe, mul_zero] at this
    rw [mul_comm]
    exact this
  have hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨q.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      refine A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_
      rw [mul_comm]
      exact mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))
    · subst hi
      simp [hqm.coeff_natDegree, A.one_mem]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact A.zero_mem
  have hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hA i⟩, rfl⟩
  obtain ⟨r, hr, -, hrm'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm
  refine ⟨r, hrm', ?_⟩
  rw [← hr, Polynomial.eval₂_map] at hre
  simpa using hre

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩`.
-/
private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩

/- English proof (translation)
Introduce `r hr m hm`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, v, hv, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩`.

Consider the case `zero => simp`. Consider the case `add a c _ _ ha hc`. Rewrite using `[map_add]`. Conclude with `add_mem ha hc`. Consider the case `smul t a _ ha`.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
private lemma omB_stab {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro r hr m hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add]
    exact add_mem ha hc
  | smul t a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K')

/- English proof (translation)
The claim follows from `Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩`.
-/
private lemma rA_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rA ℂ x I ≤ rA ℂ x I' :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

/- English proof (translation)
Introduce `_ hy` and use `int_mono (rA_mono' x h) hy`.
-/
private lemma rB_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rB ℂ K x I ≤ rB ℂ K x I' :=
  fun _ hy => int_mono (rA_mono' x h) hy

/- English proof (translation)
Introduce `_ hy` and use `int_mono (Subalgebra.map_mono (rB_mono' x h)) hy`.
-/
private lemma integralClosure_mono_subset {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') : R2 x j2 J ≤ R2 x j2 J' :=
  fun _ hy => int_mono (Subalgebra.map_mono (rB_mono' x h)) hy

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨i, hi, a, rfl⟩`.
-/
private lemma ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    x a / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

/- English proof (translation)
The claim follows from `show IsIntegral (rA ℂ x I) (algebraMap F K f) from isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)`.
-/
private lemma rA_mem_rB {I : Finset (Fin (d + 1))} {f : F} (hf : f ∈ rA ℂ x I) :
    algebraMap F K f ∈ rB ℂ K x I :=
  show IsIntegral (rA ℂ x I) (algebraMap F K f) from
    isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)

/- English proof (translation)
Use `int_range (A := rA ℂ x ∅) (fun a => ?_) hb` and prove the remaining obligations. Establish `h0 : rA ℂ x ∅ = ⊥` using `by simp [rA]`. Establish `ha : (a : F) ∈ (⊥ : Subalgebra ℂ F)` using `h0 ▸ a.2`. Take `⟨c, hc⟩` from `Algebra.mem_bot.1 ha`. Conclude with `⟨c, Subtype.ext hc⟩`.
-/
private lemma rB_empty {b : K} (hb : b ∈ rB ℂ K x ∅) : b ∈ (algebraMap ℂ K).range := by
  refine int_range (A := rA ℂ x ∅) (fun a => ?_) hb
  have h0 : rA ℂ x ∅ = ⊥ := by simp [rA]
  have ha : (a : F) ∈ (⊥ : Subalgebra ℂ F) := h0 ▸ a.2
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 ha
  exact ⟨c, Subtype.ext hc⟩

/- English proof (translation)
Use `int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy` and prove the remaining obligations. Take `⟨b, hb, hba⟩` from `a.2`. Take `⟨c, rfl⟩` from `rB_empty x hb`. Conclude with `⟨c, Subtype.ext (by rw [← hba]; simp)⟩`.
-/
private lemma integralClosure_empty_const {y : K'} (hy : y ∈ R2 x j2 ∅) : y ∈ (algebraMap ℂ K').range := by
  refine int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy
  obtain ⟨b, hb, hba⟩ := a.2
  obtain ⟨c, rfl⟩ := rB_empty x hb
  exact ⟨c, Subtype.ext (by rw [← hba]; simp)⟩

/- English proof (translation)
The claim follows from `show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)`.
-/
private lemma j2_mem_R2_of_mem_rB {J : Finset (Fin (d + 1))} {b : K} (hb : b ∈ rB ℂ K x J) : j2 b ∈ R2 x j2 J :=
  show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from
    isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)

/- English proof (translation)
Distinguish the cases in `hj' : j' ∈ J`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[Finset.insert_eq_of_mem hj']`. Simplify using `using hb`. Take `⟨N, hN⟩` from `((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb`.

Use `⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩` and prove the remaining obligations. Rewrite `hN` using `[Finset.prod_insert hj', map_mul, mul_pow]`. Use `hN using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma rB_shift (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {b : K}
    (hb : b ∈ rB ℂ K x (insert j' J)) : ∃ N : ℕ, algebraMap F K (x j' / x j) ^ N * b ∈ rB ℂ K x J := by
  by_cases hj' : j' ∈ J
  · refine ⟨0, ?_⟩
    rw [Finset.insert_eq_of_mem hj'] at hb
    simpa using hb
  · obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb
    refine ⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj', map_mul, mul_pow] at hN
    convert hN using 1
    ring

/- English proof (translation)
Establish `hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2` using `⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩`. Take `⟨N, hN⟩` from `int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Take `⟨N, hN⟩` from `rB_shift x h hj hb`. Conclude with `⟨N, ⟨_, hN, by simp⟩⟩) hy`.

Conclude with `⟨N, hN⟩`.
-/
private lemma integralClosure_shift_power (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {y : K'}
    (hy : y ∈ R2 x j2 (insert j' J)) : ∃ N : ℕ, y * j2 (algebraMap F K (x j' / x j)) ^ N ∈ R2 x j2 J := by
  have hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2 :=
    ⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩
  obtain ⟨N, hN⟩ := int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨N, hN⟩ := rB_shift x h hj hb
    exact ⟨N, ⟨_, hN, by simp⟩⟩) hy
  exact ⟨N, hN⟩

end

/- English proof (translation)
Introduce `F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY`. Establish `hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I`. Introduce `I b hb`. Establish `hb' : IsIntegral (rA ℂ (xv x) I) b` using `hb`. Conclude with `(IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))`.

Establish `hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J'` using `fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)`. Use `⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩` and prove the remaining obligations. Use `sup_eq_left.2 fun y hy => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `integralClosure_empty_const (xv x) j2 hy`. Conclude with `(rB ℂ K' (xv x) I).algebraMap_mem c`.

Use `⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ, fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a, fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩` and prove the remaining obligations. Establish `e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i)`. Simplify using `[sysY, map_div₀, div_eq_mul_inv]`. Rewrite using `[e]`. Conclude with `(le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))`.

Establish `e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j))`. Simplify using `[sysY, map_div₀, div_eq_mul_inv]`. Rewrite using `[e]`. Conclude with `(le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))`. Introduce `J j hj j' y hy`.

Conclude with `integralClosure_shift_power (xv x) j2 hY.covZ hj hy`.
-/
theorem UpperTheory.Gal.productCup_of_system.rYBasic_of :
    RYBasic := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  have hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I := by
    intro I b hb
    have hb' : IsIntegral (rA ℂ (xv x) I) b := hb
    exact (IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))
  have hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J' :=
    fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)
  refine ⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩
  · refine sup_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := integralClosure_empty_const (xv x) j2 hy
    exact (rB ℂ K' (xv x) I).algebraMap_mem c
  · refine ⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ,
      fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a,
      fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩
    · have e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))
    · have e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j)) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J)
        (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))
  · intro J j hj j' y hy
    exact integralClosure_shift_power (xv x) j2 hY.covZ hj hy
