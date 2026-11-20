import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGradedRingKernelLift

open Polynomial

namespace GlobalTheory.AdicNoeth

/- English proof (translation)
Establish `hker : ∀ a ∈ I, algebraMap R (reesAlgebra I ⧸ reesShiftIdeal I) a = 0`. Introduce `a ha`. Rewrite using `[← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]`. Introduce `n`. Rewrite using `[Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]`.

Break down `n with _ | n` into its components or cases. Simplify using `using ha`. Simplify using the standard rewrite rules. Use `letI : Algebra (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) := (Ideal.Quotient.lift I (algebraMap R _) hker).toAlgebra`. Establish `: IsScalarTower R (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `: Algebra.FiniteType R (reesAlgebra I)` using `⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩`. Establish `: Algebra.FiniteType R (reesAlgebra I ⧸ reesShiftIdeal I)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (reesShiftIdeal I)) (Ideal.Quotient.mkₐ_surjective R _)`. Establish `: Algebra.FiniteType (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I)` using `Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) _`. Conclude with `Algebra.FiniteType.isNoetherianRing (R ⧸ I) _`.
-/
theorem isNoetherianRing_graded {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (reesAlgebra I ⧸ reesShiftIdeal I) := by
  have hker : ∀ a ∈ I, algebraMap R (reesAlgebra I ⧸ reesShiftIdeal I) a = 0 := by
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    rcases n with _ | n
    · simpa using ha
    · simp
  letI : Algebra (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    (Ideal.Quotient.lift I (algebraMap R _) hker).toAlgebra
  have : IsScalarTower R (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R (reesAlgebra I) := ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  have : Algebra.FiniteType R (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (reesShiftIdeal I))
      (Ideal.Quotient.mkₐ_surjective R _)
  have : Algebra.FiniteType (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) _
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) _

/- English proof (translation)
Rewrite using `[← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]`.
-/
private lemma coeff_mul_monomial_eq_ite {R : Type} [CommRing R] (p : R[X]) (d n : ℕ) (r : R) :
    (p * monomial d r).coeff n = if d ≤ n then p.coeff (n - d) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

/- English proof (translation)
Use `isNoetherianRing_graded I hI` as an intermediate fact. Set `lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ reesShiftIdeal I` to `fun x => Ideal.Quotient.mk (reesShiftIdeal I) ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩`. Take `⟨s, hsS, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range lf)))`. Establish `hpre : ∀ q : s, ∃ x, lf x = q` using `fun q => hsS q.2`. Use `choose pre hpre using hpre`.

Use `⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩` and prove the remaining obligations. Introduce `n g hgJ hgn`. Establish `hs : (↑s : Set (reesAlgebra I ⧸ reesShiftIdeal I)) = Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I)`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I))`. Rewrite using `[← hs, ← hspan]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp hmem`. Use `choose p hp using fun q => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (c q)`.

Establish `hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) - ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩ ∈ reesShiftIdeal I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]`. Establish `hq : ∀ q : s, Ideal.Quotient.mk (reesShiftIdeal I) (p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) = c q • (q : reesAlgebra I ⧸ reesShiftIdeal I)`. Introduce `q`. Rewrite using `[map_mul, hp q, smul_eq_mul]`.

Conclude with `congrArg _ (hpre q)`. Simplify using `only [hq, hc]`. Conclude with `sub_self _`. Rewrite `hz` using `[mem_reesShiftIdeal]`. Use `⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1) else 0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `q dsimp only split_ifs`. Conclude with `(mem_reesAlgebra_iff I _).mp (p q).2 _`. Conclude with `zero_mem _`. Use `hz n using 1` and compare the differences between its conclusion and the goal. Simplify using `only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]`.

Rewrite using `[coeff_monomial, if_pos rfl]`.
-/
theorem exists_leading_generators {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → R) (d : ι → ℕ), (∀ i, f i ∈ J) ∧
      ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1) := by
  classical
  have := isNoetherianRing_graded I hI
  let lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ reesShiftIdeal I := fun x =>
    Ideal.Quotient.mk (reesShiftIdeal I) ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp
    (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range lf)))
  have hpre : ∀ q : s, ∃ x, lf x = q := fun q => hsS q.2
  choose pre hpre using hpre
  refine ⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩
  intro n g hgJ hgn
  have hs : (↑s : Set (reesAlgebra I ⧸ reesShiftIdeal I)) = Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
    ext x; simp
  have hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I)
      (Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I)) := by
    rw [← hs, ← hspan]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  choose p hp using fun q => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (c q)
  have hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) -
      ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩
      ∈ reesShiftIdeal I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hq : ∀ q : s, Ideal.Quotient.mk (reesShiftIdeal I) (p q *
        ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) =
        c q • (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
      intro q
      rw [map_mul, hp q, smul_eq_mul]
      exact congrArg _ (hpre q)
    simp only [hq, hc]
    exact sub_self _
  rw [mem_reesShiftIdeal] at hz
  refine ⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1)
    else 0, ?_, ?_⟩
  · intro q
    dsimp only
    split_ifs
    · exact (mem_reesAlgebra_iff I _).mp (p q).2 _
    · exact zero_mem _
  · convert hz n using 1
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]
    rw [coeff_monomial, if_pos rfl]

/- English proof (translation)
Establish `step : ∀ (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}), ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ r.1 - ∑ i, c i * f i ∈ I ^ (n + 1)` using `fun n r => h n r.1 r.2.1 r.2.2`. Use `choose c hc1 hc2 using step`. Set `res : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n}` to `fun n => Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n}) ⟨g, hg, by simp⟩ (fun n r => ⟨r.1 - ∑ i, c n r i * f i, J.sub_mem r.2.1 (J.sum_mem fun i _ => J.mul_mem_left _ (hf i)), hc2 n r⟩) n`. Set `a : ℕ → ι → R` to `fun n i => c n (res n) i`. Establish `ha : ∀ n i, a n i ∈ I ^ (n - d i)` using `fun n i => hc1 n (res n) i`.

Establish `hres_succ : ∀ n, (res (n + 1)).1 = (res n).1 - ∑ i, a n i * f i` using `fun n => rfl`. Establish `hdecomp : ∀ N, g = ∑ i, (∑ m ∈ Finset.range N, a m i) * f i + (res N).1`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`.

Simplify using `only [Finset.range_zero, Finset.sum_empty, zero_mul, Finset.sum_const_zero, zero_add]`. Both sides reduce to the same expression. Consider the case `succ N ih`. Rewrite using `[hres_succ]`. Simplify using `only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]`.

Use `conv_lhs => rw [ih]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpow : ∀ {m n : ℕ} {x : R}, m ≤ n → x ∈ I ^ n → x ∈ I ^ m` using `fun hmn hx => Ideal.pow_le_pow_right hmn hx`. Establish `htop : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) = I ^ m` using `fun m => by`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`.

Set `T : ι → ℕ → R` to `fun i k => ∑ m ∈ Finset.range (k + d i), a m i`. Establish `hT : ∀ i {m n : ℕ}, m ≤ n → T i m ≡ T i n [SMOD (I ^ m • ⊤ : Submodule R R)]`. Introduce `i m n hmn`. Rewrite using `[SModEq.sub_mem, htop]`. Establish `hd : T i n - T i m = ∑ k ∈ Finset.Ico (m + d i) (n + d i), a k i`.

Simplify using `only [T]`. Rewrite using `[Finset.sum_Ico_eq_sub _ (by omega)]`. Rewrite using `[← neg_sub, hd]`. Use `neg_mem (Ideal.sum_mem _ fun k hk => hpow ?_ (ha k i))` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Use `choose L hL using fun i => IsPrecomplete.prec' (I := I) (T i) (hT i)`. Establish `hzero : g - ∑ i, L i * f i = 0`. Use `IsHausdorff.haus' (I := I) _ fun N => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, htop]`.

Establish `hdD : ∀ i, d i ≤ ∑ j, d j` using `fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)`. Rewrite using `[hdecomp (N + ∑ j, d j)]`. Establish `hS : ∀ i, ∑ m ∈ Finset.range (N + ∑ j, d j), a m i = T i (N + ∑ j, d j - d i)`. Introduce `i`. Simplify using `only [T]`.

Rewrite using `[Nat.sub_add_cancel (by have := hdD i; omega)]`. Establish `hrw : ∑ i, (∑ m ∈ Finset.range (N + ∑ j, d j), a m i) * f i + (res (N + ∑ j, d j)).1 - ∑ i, L i * f i = ∑ i, (T i (N + ∑ j, d j - d i) - L i) * f i + (res (N + ∑ j, d j)).1`. Simplify using `only [hS, sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrw]`.

Use `Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_) (hpow (by omega) (res (N + ∑ j, d j)).2.2)` and prove the remaining obligations. Establish `hLi` using `hL i (N + ∑ j, d j - d i)`. Rewrite `hLi` using `[SModEq.sub_mem, htop]`. Conclude with `hpow (by have := hdD i; omega) hLi`. Rewrite `hzero` using `[sub_eq_zero]`.

Rewrite using `[hzero]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_span_of_leading {R : Type} [CommRing R] (I : Ideal R) [hc : IsAdicComplete I R]
    (J : Ideal R) {ι : Type} [Fintype ι] (f : ι → R) (d : ι → ℕ) (hf : ∀ i, f i ∈ J)
    (h : ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1))
    (g : R) (hg : g ∈ J) : g ∈ Ideal.span (Set.range f) := by
  classical
  have step : ∀ (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}), ∃ c : ι → R,
      (∀ i, c i ∈ I ^ (n - d i)) ∧ r.1 - ∑ i, c i * f i ∈ I ^ (n + 1) :=
    fun n r => h n r.1 r.2.1 r.2.2
  choose c hc1 hc2 using step
  let res : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} := fun n =>
    Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n})
      ⟨g, hg, by simp⟩
      (fun n r => ⟨r.1 - ∑ i, c n r i * f i,
        J.sub_mem r.2.1 (J.sum_mem fun i _ => J.mul_mem_left _ (hf i)), hc2 n r⟩) n
  let a : ℕ → ι → R := fun n i => c n (res n) i
  have ha : ∀ n i, a n i ∈ I ^ (n - d i) := fun n i => hc1 n (res n) i
  have hres_succ : ∀ n, (res (n + 1)).1 = (res n).1 - ∑ i, a n i * f i := fun n => rfl
  have hdecomp : ∀ N, g = ∑ i, (∑ m ∈ Finset.range N, a m i) * f i + (res N).1 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, Finset.sum_const_zero, zero_add]
      rfl
    | succ N ih =>
      rw [hres_succ]
      simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [ih]
      ring
  have hpow : ∀ {m n : ℕ} {x : R}, m ≤ n → x ∈ I ^ n → x ∈ I ^ m :=
    fun hmn hx => Ideal.pow_le_pow_right hmn hx
  have htop : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) = I ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let T : ι → ℕ → R := fun i k => ∑ m ∈ Finset.range (k + d i), a m i
  have hT : ∀ i {m n : ℕ}, m ≤ n → T i m ≡ T i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, htop]
    have hd : T i n - T i m = ∑ k ∈ Finset.Ico (m + d i) (n + d i), a k i := by
      simp only [T]
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [← neg_sub, hd]
    refine neg_mem (Ideal.sum_mem _ fun k hk => hpow ?_ (ha k i))
    rw [Finset.mem_Ico] at hk
    omega
  choose L hL using fun i => IsPrecomplete.prec' (I := I) (T i) (hT i)
  have hzero : g - ∑ i, L i * f i = 0 := by
    refine IsHausdorff.haus' (I := I) _ fun N => ?_
    rw [SModEq.sub_mem, sub_zero, htop]
    have hdD : ∀ i, d i ≤ ∑ j, d j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    rw [hdecomp (N + ∑ j, d j)]
    have hS : ∀ i, ∑ m ∈ Finset.range (N + ∑ j, d j), a m i = T i (N + ∑ j, d j - d i) := by
      intro i
      simp only [T]
      rw [Nat.sub_add_cancel (by have := hdD i; omega)]
    have hrw : ∑ i, (∑ m ∈ Finset.range (N + ∑ j, d j), a m i) * f i + (res (N + ∑ j, d j)).1 -
        ∑ i, L i * f i =
        ∑ i, (T i (N + ∑ j, d j - d i) - L i) * f i + (res (N + ∑ j, d j)).1 := by
      simp only [hS, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      (hpow (by omega) (res (N + ∑ j, d j)).2.2)
    have hLi := hL i (N + ∑ j, d j - d i)
    rw [SModEq.sub_mem, htop] at hLi
    exact hpow (by have := hdD i; omega) hLi
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `R _ I hI hc hq`. Use `isNoetherianRing_iff.mpr ⟨fun J => ?_⟩` and prove the remaining obligations. Take `⟨ι, _, f, d, hf, hlead⟩` from `exists_leading_generators I hI J`. Establish `hJ : J = Ideal.span (Set.range f)` using `le_antisymm (fun g hg => mem_span_of_leading I J f d hf hlead g hg) (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))`. Rewrite using `[hJ]`.

Conclude with `Submodule.fg_span (Set.finite_range f)`.
-/
theorem isNoetherianRing_of_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by
  intro R _ I hI hc hq
  refine isNoetherianRing_iff.mpr ⟨fun J => ?_⟩
  obtain ⟨ι, _, f, d, hf, hlead⟩ := exists_leading_generators I hI J
  have hJ : J = Ideal.span (Set.range f) := le_antisymm
    (fun g hg => mem_span_of_leading I J f d hf hlead g hg)
    (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))
  rw [hJ]
  exact Submodule.fg_span (Set.finite_range f)

end GlobalTheory.AdicNoeth
