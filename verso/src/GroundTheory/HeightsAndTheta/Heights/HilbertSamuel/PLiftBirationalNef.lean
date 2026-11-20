import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftBirationalNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftBirationalNef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Use `⟨a.den, monomial u a.num, a.den_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[map_monomial, C_mul_monomial]`. Use `congr 1`.

Rewrite using `[eq_intCast, mul_comm, Rat.mul_den_eq_num]`. Consider the case `add p q hp hq`. Take `⟨m1, F1, hm1, h1⟩` from `hp`. Take `⟨m2, F2, hm2, h2⟩` from `hq`. Use `⟨m1 * m2, C (m2 : ℤ) * F1 + C (m1 : ℤ) * F2, Nat.mul_pos hm1 hm2, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, map_mul, map_C, map_C, h1, h2]`. Simplify using `only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_of_rat (f : MRingOver ℚ ι) :
    ∃ (m : ℕ) (F : MRing ι), 0 < m ∧ MvPolynomial.map (Int.castRingHom ℚ) F = C (m : ℚ) * f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, monomial u a.num, a.den_pos, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    rw [eq_intCast, mul_comm, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨m1, F1, hm1, h1⟩ := hp
    obtain ⟨m2, F2, hm2, h2⟩ := hq
    refine ⟨m1 * m2, C (m2 : ℤ) * F1 + C (m1 : ℤ) * F2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, h1, h2]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

/- English proof (translation)
Rewrite using `[← algebraMap_int_eq]`. Conclude with `MvPolynomial.aeval_map_algebraMap ℚ _ F`.
-/
theorem mConeMapOver_map (y : (Σ k, ι k) → Ω) (F : MRing ι) :
    KH.mConeMapOver ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
  rw [← algebraMap_int_eq]
  exact MvPolynomial.aeval_map_algebraMap ℚ _ F

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[KH.genIdeal, Ideal.map_le_iff_le_comap]`. Introduce `F hF`. Rewrite using `[Ideal.mem_comap, KH.mIdealOver, RingHom.mem_ker, mConeMapOver_map]`. Conclude with `hF`.

Introduce `f hf`. Take `⟨m, F, hm, hF⟩` from `exists_int_of_rat f`. Rewrite `hf` using `[KH.mIdealOver, RingHom.mem_ker]`. Establish `hF0 : F ∈ mCoordIdeal y`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, ← mConeMapOver_map, hF, map_mul, hf, mul_zero]`.

Establish `hmap : MvPolynomial.map (Int.castRingHom ℚ) F ∈ KH.genIdeal y` using `Ideal.mem_map_of_mem _ hF0`. Establish `hm0 : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hf' : f = C ((m : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F`. Rewrite using `[hF, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]`. Rewrite using `[hf']`.

Conclude with `Ideal.mul_mem_left _ _ hmap`.
-/
theorem genIdeal_eq (y : (Σ k, ι k) → Ω) : KH.genIdeal y = KH.mIdealOver ℚ y := by
  apply le_antisymm
  · rw [KH.genIdeal, Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, KH.mIdealOver, RingHom.mem_ker, mConeMapOver_map]
    exact hF
  · intro f hf
    obtain ⟨m, F, hm, hF⟩ := exists_int_of_rat f
    rw [KH.mIdealOver, RingHom.mem_ker] at hf
    have hF0 : F ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, ← mConeMapOver_map, hF, map_mul, hf, mul_zero]
    have hmap : MvPolynomial.map (Int.castRingHom ℚ) F ∈ KH.genIdeal y := Ideal.mem_map_of_mem _ hF0
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hf' : f = C ((m : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ hmap

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Use `⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩`.

Rewrite using `[KH.genIdeal, hP, Ideal.map_span]`.
-/
theorem isMultiHomogIdeal_genIdeal {y : (Σ k, ι k) → Ω} (h : IsMultiHomogIdeal (mCoordIdeal y)) :
    IsMultiHomogIdeal (KH.genIdeal y) := by
  obtain ⟨S, hS, hP⟩ := h
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  · rw [KH.genIdeal, hP, Ideal.map_span]

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]`.
-/
theorem coord_ne_zero_of_not_mem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

def chartCell (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

/- English proof (translation)
Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Establish `hi' : i = c k` using `Finset.mem_singleton.mp hi`. Substitute `hi'` using the available equality.

Rewrite using `[KH.mConeMapOver, aeval_X]`. Conclude with `mul_ne_zero (fun h => hc k (C_eq_zero.mp h)) (X_ne_zero _)`. Consider the case `one => rw [map_one]`. Conclude with `one_ne_zero`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`.

Conclude with `mul_ne_zero ha hb`.
-/
theorem cone_ne_zero_of_mem_cellMon {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {u : MRingOver ℚ ι} (hu : u ∈ KH.cellMon ℚ (fun k => ({c k} : Finset (ι k)))) : KH.mConeMapOver ℚ y u ≠ 0 := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    have hi' : i = c k := Finset.mem_singleton.mp hi
    subst hi'
    rw [KH.mConeMapOver, aeval_X]
    exact mul_ne_zero (fun h => hc k (C_eq_zero.mp h)) (X_ne_zero _)
  | one => rw [map_one]; exact one_ne_zero
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

/- English proof (translation)
Introduce `h`. Establish `h1 : (LocalizedModule.mk (1 : MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y) 1 : LocalizedModule (KH.cellMon ℚ (fun k => ({c k} : Finset (ι k)))) (MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y)) = LocalizedModule.mk 0 1`. Establish `: Subsingleton (LocalizedModule (KH.cellMon ℚ (fun k => ({c k} : Finset (ι k)))) (MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y))` using `subsingleton_of_zero_eq_one h.symm`. Conclude with `Subsingleton.elim _ _`. Take `⟨u, hu⟩` from `LocalizedModule.mk_eq.mp h1`.

Simplify using `only [one_smul, smul_zero] at hu`. Establish `hu' : Ideal.Quotient.mk (KH.mIdealOver ℚ y) (u : MRingOver ℚ ι) = 0`. Rewrite using `[← hu, Submonoid.smul_def]`. Rewrite using `[← Ideal.Quotient.algebraMap_eq]`. Conclude with `Algebra.algebraMap_eq_smul_one _`.

Establish `hmem : (u : MRingOver ℚ ι) ∈ KH.mIdealOver ℚ y` using `Ideal.Quotient.eq_zero_iff_mem.mp hu'`. Rewrite `hmem` using `[KH.mIdealOver, RingHom.mem_ker]`. Conclude with `cone_ne_zero_of_mem_cellMon hc u.2 hmem`.
-/
theorem loc_one_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    (1 : LocalizedModule (KH.cellMon ℚ (fun k => ({c k} : Finset (ι k)))) (MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y)) ≠ 0 := by
  intro h
  have h1 : (LocalizedModule.mk (1 : MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y) 1 :
      LocalizedModule (KH.cellMon ℚ (fun k => ({c k} : Finset (ι k)))) (MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y)) =
      LocalizedModule.mk 0 1 := by
    have : Subsingleton (LocalizedModule (KH.cellMon ℚ (fun k => ({c k} : Finset (ι k))))
        (MRingOver ℚ ι ⧸ KH.mIdealOver ℚ y)) := subsingleton_of_zero_eq_one h.symm
    exact Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h1
  simp only [one_smul, smul_zero] at hu
  have hu' : Ideal.Quotient.mk (KH.mIdealOver ℚ y) (u : MRingOver ℚ ι) = 0 := by
    rw [← hu, Submonoid.smul_def]
    rw [← Ideal.Quotient.algebraMap_eq]
    exact Algebra.algebraMap_eq_smul_one _
  have hmem : (u : MRingOver ℚ ι) ∈ KH.mIdealOver ℚ y := Ideal.Quotient.eq_zero_iff_mem.mp hu'
  rw [KH.mIdealOver, RingHom.mem_ker] at hmem
  exact cone_ne_zero_of_mem_cellMon hc u.2 hmem

/- English proof (translation)
Take `⟨φ, hinj, hrange, -⟩` from `hB ℚ K ι Ω y n (fun k => ⟨c k, hc k⟩)`. Take `⟨r, z, u, hz, -, hsum⟩` from `hg (chartCell c)`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hz0 : ∀ j, z j = 0`.

Introduce `j`. Establish `h1 : φ ⟨z j, hz j⟩ ∈ KH.secOver ℚ y n` using `hrange ▸ LinearMap.mem_range_self φ _`. Establish `h3 : (⟨z j, hz j⟩ : ↥(KH.cechZc ι (KH.quotPart ℚ (KH.mIdealOver ℚ y)) n 0)) = 0` using `hinj ((hne _ h1).trans (map_zero φ).symm)`. Conclude with `congrArg Subtype.val h3`. Apply `loc_one_ne_zero (K := K) hc` to reduce the goal to its premises.

Conclude with `hsum.symm.trans (Finset.sum_eq_zero fun j _ => by rw [hz0 j]; exact mul_zero (u j))`.
-/
theorem exists_ne_zero_mem_secOver [LinearOrder K] [∀ k, LinearOrder (ι k)] (hB : KH.GlobalSectionsComparisonStatement)
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (n : K → ℤ)
    (hg : KH.GeneratedV ℚ (KH.mIdealOver ℚ y) n) : ∃ s ∈ KH.secOver ℚ y n, s ≠ 0 := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB ℚ K ι Ω y n (fun k => ⟨c k, hc k⟩)
  obtain ⟨r, z, u, hz, -, hsum⟩ := hg (chartCell c)
  by_contra hne
  push Not at hne
  have hz0 : ∀ j, z j = 0 := by
    intro j
    have h1 : φ ⟨z j, hz j⟩ ∈ KH.secOver ℚ y n := hrange ▸ LinearMap.mem_range_self φ _
    have h3 : (⟨z j, hz j⟩ : ↥(KH.cechZc ι (KH.quotPart ℚ (KH.mIdealOver ℚ y)) n 0)) = 0 :=
      hinj ((hne _ h1).trans (map_zero φ).symm)
    exact congrArg Subtype.val h3
  apply loc_one_ne_zero (K := K) hc
  exact hsum.symm.trans (Finset.sum_eq_zero fun j _ => by rw [hz0 j]; exact mul_zero (u j))

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by rw [Nat.cast_one, one_mul]; exact Algebra.subset_adjoin hx⟩`. Consider the case `algebraMap q`. Use `⟨q.den, q.den_pos, ?_⟩` and prove the remaining obligations. Establish `hq : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω)`.

Rewrite using `[← map_natCast (algebraMap ℚ Ω), ← map_mul, mul_comm, Rat.mul_den_eq_num, map_intCast]`. Rewrite using `[hq]`. Conclude with `Subalgebra.intCast_mem _ _`. Consider the case `add a b _ _ ha hb`. Take `⟨m1, hm1, h1⟩` from `ha`.

Take `⟨m2, hm2, h2⟩` from `hb`. Use `⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩` and prove the remaining obligations. Establish `he : ((m1 * m2 : ℕ) : Ω) * (a + b) = (m2 : Ω) * ((m1 : Ω) * a) + (m1 : Ω) * ((m2 : Ω) * b)` using `by push_cast; ring`. Rewrite using `[he]`. Conclude with `add_mem (mul_mem (Subalgebra.natCast_mem _ _) h1) (mul_mem (Subalgebra.natCast_mem _ _) h2)`.

Consider the case `mul a b _ _ ha hb`. Take `⟨m1, hm1, h1⟩` from `ha`. Take `⟨m2, hm2, h2⟩` from `hb`. Use `⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩` and prove the remaining obligations. Establish `he : ((m1 * m2 : ℕ) : Ω) * (a * b) = ((m1 : Ω) * a) * ((m2 : Ω) * b)` using `by push_cast; ring`.

Rewrite using `[he]`. Conclude with `mul_mem h1 h2`.
-/
theorem exists_mul_mem_adjoin_int {T : Set Ω} {x : Ω} (hx : x ∈ Algebra.adjoin ℚ T) :
    ∃ m : ℕ, 0 < m ∧ (m : Ω) * x ∈ Algebra.adjoin ℤ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by rw [Nat.cast_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have hq : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [← map_natCast (algebraMap ℚ Ω), ← map_mul, mul_comm, Rat.mul_den_eq_num, map_intCast]
    rw [hq]
    exact Subalgebra.intCast_mem _ _
  | add a b _ _ ha hb =>
    obtain ⟨m1, hm1, h1⟩ := ha
    obtain ⟨m2, hm2, h2⟩ := hb
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    have he : ((m1 * m2 : ℕ) : Ω) * (a + b) = (m2 : Ω) * ((m1 : Ω) * a) + (m1 : Ω) * ((m2 : Ω) * b) := by
      push_cast; ring
    rw [he]
    exact add_mem (mul_mem (Subalgebra.natCast_mem _ _) h1) (mul_mem (Subalgebra.natCast_mem _ _) h2)
  | mul a b _ _ ha hb =>
    obtain ⟨m1, hm1, h1⟩ := ha
    obtain ⟨m2, hm2, h2⟩ := hb
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    have he : ((m1 * m2 : ℕ) : Ω) * (a * b) = ((m1 : Ω) * a) * ((m2 : Ω) * b) := by push_cast; ring
    rw [he]
    exact mul_mem h1 h2

/- English proof (translation)
Establish `hc : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ m : ℕ, 0 < m ∧ (m : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c`. Introduce `c hc`. Establish `h` using `(Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc`. Rewrite `h` using `[Submodule.mem_comap, LinearMap.mulRight_apply]`. Conclude with `exists_mul_mem_adjoin_int h`.

Set `m : (∀ k, ι k) → ℕ` to `fun c => if h : ∀ k, y ⟨k, c k⟩ ≠ 0 then (hc c h).choose else 1`. Establish `hm : ∀ c, 0 < m c` using `fun c => by`. Simplify using `only [m]`. Use `split_ifs with h`. Conclude with `(hc c h).choose_spec.1`.

Conclude with `one_pos`. Use `⟨∏ c, m c, Finset.prod_pos fun c _ => hm c, ?_⟩` and prove the remaining obligations. Introduce `c hc'`. Take `⟨M, hM⟩ : m c ∣ ∏ c, m c` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ c)`. Establish `hmc : (m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c`.

Simplify using `only [m, dif_pos hc']`. Conclude with `(hc c hc').choose_spec.2`. Establish `he : ((∏ c, m c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) = (M : Ω) * ((m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k)))`. Simplify using `only [hM, Nat.cast_mul, Nat.cast_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `show ((∏ c, m c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) ∈ chartRingZ y c`. Rewrite using `[he]`. Conclude with `mul_mem (Subalgebra.natCast_mem _ _) hmc`.
-/
theorem exists_nat_mul_mem_chartLat {y : (Σ k, ι k) → Ω} {n : K → ℤ} {s : Ω} (hs : s ∈ KH.secOver ℚ y n) :
    ∃ m : ℕ, 0 < m ∧ (m : Ω) * s ∈ chartLat y n 1 := by
  classical
  have hc : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ m : ℕ, 0 < m ∧
      (m : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c := by
    intro c hc
    have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
    rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h
    exact exists_mul_mem_adjoin_int h
  let m : (∀ k, ι k) → ℕ := fun c => if h : ∀ k, y ⟨k, c k⟩ ≠ 0 then (hc c h).choose else 1
  have hm : ∀ c, 0 < m c := fun c => by
    simp only [m]
    split_ifs with h
    · exact (hc c h).choose_spec.1
    · exact one_pos
  refine ⟨∏ c, m c, Finset.prod_pos fun c _ => hm c, ?_⟩
  intro c hc'
  obtain ⟨M, hM⟩ : m c ∣ ∏ c, m c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  have hmc : (m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c := by
    simp only [m, dif_pos hc']
    exact (hc c hc').choose_spec.2
  have he : ((∏ c, m c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) =
      (M : Ω) * ((m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-n k))) := by
    simp only [hM, Nat.cast_mul, Nat.cast_one, one_mul]
    ring
  show ((∏ c, m c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) ∈ chartRingZ y c
  rw [he]
  exact mul_mem (Subalgebra.natCast_mem _ _) hmc

/- English proof (translation)
Introduce `c hc`. Establish `h` using `hs c hc`. Establish `hsplit : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) = (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((fun _ => (-1 : ℤ)) + n : K → ℤ) k))) * ∏ k, (y ⟨k, c k⟩)⁻¹`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_neg_one, ← zpow_add₀ (hc k)]`. Use `congr 1`. Simplify using `only [Pi.add_apply, Nat.cast_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : (s * ∏ k, y ⟨k, c' k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) = (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((fun _ => (-1 : ℤ)) + n : K → ℤ) k))) * ∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩)`.

Rewrite using `[hsplit]`. Simplify using `only [div_eq_mul_inv, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `show (s * ∏ k, y ⟨k, c' k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) ∈ chartRingZ y c`. Rewrite using `[heq]`.

Conclude with `mul_mem h (Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩)`.
-/
theorem mul_prod_mem_chartLat {y : (Σ k, ι k) → Ω} {n : K → ℤ} {s : Ω}
    (hs : s ∈ chartLat y ((fun _ => (-1 : ℤ)) + n) 1) (c' : ∀ k, ι k) :
    s * ∏ k, y ⟨k, c' k⟩ ∈ chartLat y n 1 := by
  intro c hc
  have h := hs c hc
  have hsplit : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((fun _ => (-1 : ℤ)) + n : K → ℤ) k))) * ∏ k, (y ⟨k, c k⟩)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_neg_one, ← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply, Nat.cast_one, one_mul]
    ring
  have heq : (s * ∏ k, y ⟨k, c' k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((fun _ => (-1 : ℤ)) + n : K → ℤ) k))) *
        ∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩) := by
    rw [hsplit]
    simp only [div_eq_mul_inv, Finset.prod_mul_distrib]
    ring
  show (s * ∏ k, y ⟨k, c' k⟩) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) ∈ chartRingZ y c
  rw [heq]
  exact mul_mem h (Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩)

/- English proof (translation)
Use `conv_lhs => rw [G.as_sum]`. Use `conv_rhs => rw [G.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib]`. Establish `hl : ∏ p : Σ k, ι k, lam p.1 ^ m p = ∏ k, lam k ^ d k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hG m hm k]`. Rewrite using `[hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale {y : (Σ k, ι k) → Ω} (lam : K → Ω) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) :
    aeval (fun p => lam p.1 * y p) G = (∏ k, lam k ^ d k) * aeval y G := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  have hl : ∏ p : Σ k, ι k, lam p.1 ^ m p = ∏ k, lam k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  rw [hl]
  ring

/- English proof (translation)
Establish `hdeg : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), m.degree = ∑ i, m i`. Introduce `τ _ m`. Rewrite using `[Finsupp.degree_apply]`. Conclude with `Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by simpa using hx)`. Establish `hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree`.

Introduce `τ m`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression. Establish `hH : G.IsHomogeneous (∑ k, d k)`. Introduce `m hm`.

Rewrite using `[hw, hdeg, Fintype.sum_sigma]`. Conclude with `Finset.sum_congr rfl fun k _ => hG m (mem_support_iff.mpr hm) k`. Establish `hL : ∀ p : Σ k, ι k, (X (⟨(), e p⟩ : Σ _ : Unit, κ) : MRing (fun _ : Unit => κ)).IsHomogeneous 1` using `fun p => isHomogeneous_X _ _`. Establish `h` using `hH.aeval _ hL`. Rewrite `h` using `[one_mul]`.

Introduce `m hm k`. Establish `h'` using `h (mem_support_iff.mp hm)`. Rewrite `h'` using `[hw, hdeg, Fintype.sum_sigma, Fintype.sum_unique]`. Consider the cases of `k`. Conclude with `h'`.
-/
theorem isMultiHomog_subst {κ : Type} [Fintype κ] (e : (Σ k, ι k) → κ) {G : MRing ι} {d : K → ℕ}
    (hG : IsMultiHomog G d) :
    IsMultiHomog (aeval (fun p => (X (⟨(), e p⟩ : Σ _ : Unit, κ) : MRing (fun _ : Unit => κ))) G)
      (fun _ => ∑ k, d k) := by
  classical
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), m.degree = ∑ i, m i := by
    intro τ _ m
    rw [Finsupp.degree_apply]
    exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by simpa using hx)
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : G.IsHomogeneous (∑ k, d k) := by
    intro m hm
    rw [hw, hdeg, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun k _ => hG m (mem_support_iff.mpr hm) k
  have hL : ∀ p : Σ k, ι k,
      (X (⟨(), e p⟩ : Σ _ : Unit, κ) : MRing (fun _ : Unit => κ)).IsHomogeneous 1 :=
    fun p => isHomogeneous_X _ _
  have h := hH.aeval _ hL
  rw [one_mul] at h
  intro m hm k
  have h' := h (mem_support_iff.mp hm)
  rw [hw, hdeg, Fintype.sum_sigma, Fintype.sum_unique] at h'
  cases k
  exact h'

/- English proof (translation)
Introduce `w`. Take `⟨d, G, H, hG, hH, hH0, hGH⟩` from `hy w`. Set `σ : MRing ι →ₐ[ℤ] MRing (fun _ : Unit => κ)` to `aeval fun p => X ⟨(), e p⟩`. Establish `hev : ∀ F : MRing ι, aeval (fun p : Σ _ : Unit, κ => x p.2) (σ F) = aeval (fun p => lam p.1 * y p) F`. Introduce `F`.

Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Simplify using `[hx p]`. Establish `hΛ : (∏ k, lam k ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hlam k)`.

Use `⟨fun _ => ∑ k, d k, σ G, σ H, isMultiHomog_subst e hG, isMultiHomog_subst e hH, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev, aeval_scale lam hH]`. Conclude with `mul_ne_zero hΛ hH0`. Rewrite using `[hev, hev, aeval_scale lam hG, aeval_scale lam hH, hGH]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem birational_of_scaled {κ : Type} [Fintype κ] {y : (Σ k, ι k) → Ω} (hy : Birational y)
    (x : κ → Ω) (e : (Σ k, ι k) → κ) (lam : K → Ω) (hlam : ∀ k, lam k ≠ 0)
    (hx : ∀ p, x (e p) = lam p.1 * y p) :
    Birational (fun p : Σ _ : Unit, κ => x p.2) := by
  intro w
  obtain ⟨d, G, H, hG, hH, hH0, hGH⟩ := hy w
  let σ : MRing ι →ₐ[ℤ] MRing (fun _ : Unit => κ) := aeval fun p => X ⟨(), e p⟩
  have hev : ∀ F : MRing ι, aeval (fun p : Σ _ : Unit, κ => x p.2) (σ F) =
      aeval (fun p => lam p.1 * y p) F := by
    intro F
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext p
    simp [hx p]
  have hΛ : (∏ k, lam k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hlam k)
  refine ⟨fun _ => ∑ k, d k, σ G, σ H, isMultiHomog_subst e hG, isMultiHomog_subst e hH, ?_, ?_⟩
  · rw [hev, aeval_scale lam hH]
    exact mul_ne_zero hΛ hH0
  · rw [hev, hev, aeval_scale lam hG, aeval_scale lam hH, hGH]
    ring

end LiftBirationalNef

open LiftBirationalNef in

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D α b a₀ I hI hV hbir hnef hb ha`. Set `_ : LinearOrder K` to `LinearOrder.lift' _ (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective`. Establish `hgen` using `genIdeal_eq y`. Establish `hhom : IsMultiHomogIdeal (KH.mIdealOver ℚ y)` using `hgen ▸ isMultiHomogIdeal_genIdeal hV.2.1.2.1`.

Establish `hnef' : KH.NefOnF I (KH.mIdealOver ℚ y) α` using `hgen ▸ hnef`. Take `⟨c₁, hc₁⟩` from `(hK ℚ K ι I (KH.mIdealOver ℚ y) α b a₀ hI hhom hnef' hb ha).2 (fun _ => -1)`. Establish `hrel` using `hV.2.1.2.2`. Set `c₀ : ∀ k, ι k` to `fun k => (hrel k).choose`. Establish `hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0` using `fun k => coord_ne_zero_of_not_mem (hrel k).choose_spec`.

Use `⟨1, c₁, le_rfl, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hs0⟩` from `exists_ne_zero_mem_secOver hB y c₀ hc₀ _ (hc₁ t ht)`. Take `⟨m, hm, hms⟩` from `exists_nat_mul_mem_chartLat hs`. Establish `hs' : (m : Ω) * s ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') hs0`. Set `eqv` to `Fintype.equivFin (∀ k, ι k)`.

Use `⟨Fintype.card (∀ k, ι k), fun j => (m : Ω) * s * ∏ k, y ⟨k, eqv.symm j k⟩, fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `mul_prod_mem_chartLat hms _`. Establish `hlam : ∀ k, (m : Ω) * s * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩ ≠ 0` using `fun k => mul_ne_zero hs' (Finset.prod_ne_zero_iff.mpr fun k' _ => hc₀ k')`. Establish `hx : ∀ p : Σ k, ι k, (m : Ω) * s * ∏ k, y ⟨k, eqv.symm (eqv (Function.update c₀ p.1 p.2)) k⟩ = (m : Ω) * s * (∏ k' ∈ Finset.univ.erase p.1, y ⟨k', c₀ k'⟩) * y p`.

Introduce and unpack `⟨k, i⟩`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `h1 : ∏ k', y ⟨k', Function.update c₀ k i k'⟩ = (∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) * y ⟨k, i⟩`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]`. Use `show (m : Ω) * s * ∏ k', y ⟨k', Function.update c₀ k i k'⟩ = (m : Ω) * s * (∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) * y ⟨k, i⟩`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `birational_of_scaled (κ := Fin (Fintype.card (∀ k, ι k))) hbir (fun j => (m : Ω) * s * ∏ k, y ⟨k, eqv.symm j k⟩) (fun p => eqv (Function.update c₀ p.1 p.2)) (fun k => (m : Ω) * s * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) hlam hx`.
-/
theorem LiftBirationalNef.proof (hK : KleimanSchemeAmple.Statement) (hB : KH.GlobalSectionsComparisonStatement) :
    LiftBirationalNef.Statement := by
  intro K _ ι _ Ω _ _ y D α b a₀ I hI hV hbir hnef hb ha
  classical
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  have hgen := genIdeal_eq y
  have hhom : IsMultiHomogIdeal (KH.mIdealOver ℚ y) := hgen ▸ isMultiHomogIdeal_genIdeal hV.2.1.2.1
  have hnef' : KH.NefOnF I (KH.mIdealOver ℚ y) α := hgen ▸ hnef
  obtain ⟨c₁, hc₁⟩ := (hK ℚ K ι I (KH.mIdealOver ℚ y) α b a₀ hI hhom hnef' hb ha).2 (fun _ => -1)
  have hrel := hV.2.1.2.2
  let c₀ : ∀ k, ι k := fun k => (hrel k).choose
  have hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => coord_ne_zero_of_not_mem (hrel k).choose_spec
  refine ⟨1, c₁, le_rfl, fun t ht => ?_⟩
  obtain ⟨s, hs, hs0⟩ := exists_ne_zero_mem_secOver hB y c₀ hc₀ _ (hc₁ t ht)
  obtain ⟨m, hm, hms⟩ := exists_nat_mul_mem_chartLat hs
  have hs' : (m : Ω) * s ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') hs0
  let eqv := Fintype.equivFin (∀ k, ι k)
  refine ⟨Fintype.card (∀ k, ι k), fun j => (m : Ω) * s * ∏ k, y ⟨k, eqv.symm j k⟩, fun j => ?_, ?_⟩
  · rw [mul_one]
    exact mul_prod_mem_chartLat hms _
  · have hlam : ∀ k, (m : Ω) * s * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩ ≠ 0 := fun k =>
      mul_ne_zero hs' (Finset.prod_ne_zero_iff.mpr fun k' _ => hc₀ k')
    have hx : ∀ p : Σ k, ι k, (m : Ω) * s * ∏ k, y ⟨k, eqv.symm (eqv (Function.update c₀ p.1 p.2)) k⟩ =
        (m : Ω) * s * (∏ k' ∈ Finset.univ.erase p.1, y ⟨k', c₀ k'⟩) * y p := by
      rintro ⟨k, i⟩
      rw [Equiv.symm_apply_apply]
      have h1 : ∏ k', y ⟨k', Function.update c₀ k i k'⟩ =
          (∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) * y ⟨k, i⟩ := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
      show (m : Ω) * s * ∏ k', y ⟨k', Function.update c₀ k i k'⟩ =
        (m : Ω) * s * (∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) * y ⟨k, i⟩
      rw [h1]
      ring
    exact birational_of_scaled (κ := Fin (Fintype.card (∀ k, ι k))) hbir
      (fun j => (m : Ω) * s * ∏ k, y ⟨k, eqv.symm j k⟩) (fun p => eqv (Function.update c₀ p.1 p.2))
      (fun k => (m : Ω) * s * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c₀ k'⟩) hlam hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
