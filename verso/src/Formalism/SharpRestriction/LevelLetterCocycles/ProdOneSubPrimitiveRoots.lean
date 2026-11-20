import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial

variable {l : ℕ} [Fact l.Prime]

instance enoughRoots (i : ℕ) : HasEnoughRootsOfUnity (Om l) (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  infer_instance

variable (l)

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ 1)`. Rewrite `hζ` using `[pow_one]`. Conclude with `⟨ζ, hζ.pow_eq_one, hζ.ne_one (Fact.out : l.Prime).one_lt⟩`.
-/
theorem exists_root_ne_one : ∃ z : Om l, z ^ l = 1 ∧ z ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ 1)
  rw [pow_one] at hζ
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (Fact.out : l.Prime).one_lt⟩

/- English proof (translation)
Conclude with `IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos`.
-/
theorem exists_root (x : Om l) : ∃ z : Om l, z ^ l = x := by
  exact IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos

def ζQ : ℕ → Om l
  | 0 => 1
  | 1 => (exists_root_ne_one l).choose
  | (m + 2) => (exists_root l (ζQ (m + 1))).choose

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ζQ_zero : ζQ l 0 = 1 := rfl

/- English proof (translation)
Conclude with `(exists_root_ne_one l).choose_spec.2`.
-/
theorem ζQ_one : ζQ l 1 ≠ 1 := by
  exact (exists_root_ne_one l).choose_spec.2

/- English proof (translation)
Consider the cases of `m with`. Consider the case `zero => exact (exists_root_ne_one l).choose_spec.1`. Consider the case `succ m => exact (exists_root l (ζQ l (m + 1))).choose_spec`.
-/
theorem ζQ_succ (m : ℕ) : ζQ l (m + 1) ^ l = ζQ l m := by
  cases m with
  | zero => exact (exists_root_ne_one l).choose_spec.1
  | succ m => exact (exists_root l (ζQ l (m + 1))).choose_spec

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [← add_assoc, pow_succ', pow_mul, ζQ_succ, ih]`.
-/
theorem ζQ_pow (m k : ℕ) : ζQ l (m + k) ^ (l ^ k) = ζQ l m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, ζQ_succ, ih]

/- English proof (translation)
Establish `h` using `ζQ_pow l 0 m`. Rewrite `h` using `[zero_add, ζQ_zero]`. Then use the resulting hypothesis.
-/
theorem ζQ_pow_eq_one (m : ℕ) : ζQ l m ^ (l ^ m) = 1 := by
  have h := ζQ_pow l 0 m
  rwa [zero_add, ζQ_zero] at h

/- English proof (translation)
Consider the cases of `m with`. Consider the case `zero => simpa [ζQ_zero] using IsPrimitiveRoot.one`. Consider the case `succ m`. Rewrite using `[IsPrimitiveRoot.iff_orderOf]`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises.

Rewrite using `[show m + 1 = 1 + m by omega, ζQ_pow]`. Conclude with `ζQ_one l`. Conclude with `ζQ_pow_eq_one l (m + 1)`.
-/
theorem ζQ_primitive (m : ℕ) : IsPrimitiveRoot (ζQ l m) (l ^ m) := by
  cases m with
  | zero => simpa [ζQ_zero] using IsPrimitiveRoot.one
  | succ m =>
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [show m + 1 = 1 + m by omega, ζQ_pow]
      exact ζQ_one l
    · exact ζQ_pow_eq_one l (m + 1)

variable {l}

/- English proof (translation)
Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions.
-/
theorem one_lt_l : (1 : ℝ) < (l : ℝ) := by
  exact_mod_cast (Fact.out : l.Prime).one_lt

/- English proof (translation)
Establish `h : ‖algebraMap ℚ_[l] (Om l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖` using `PadicAlgCl.norm_extends l _`. Rewrite `h` using `[map_natCast]`. Rewrite using `[h]`. Use `first`. Consider the case `exact Padic.norm_p`.

Consider the case `simp`.
-/
theorem norm_l : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : ‖algebraMap ℚ_[l] (Om l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicAlgCl.norm_extends l _
  rw [map_natCast] at h
  rw [h]
  first
  | exact Padic.norm_p
  | simp

abbrev Q0 (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (Om l) := ⊥

/- English proof (translation)
Use `infer_instance`.
-/
theorem finiteDimensional_Q0_alt : FiniteDimensional ℚ_[l] (Q0 l) := by
  infer_instance

def ofGQ (g : GQ l) : Neutral.B1.GK l (Q0 l) :=
  { g.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 r.2
      change g (r : Om l) = r
      rw [← ha]
      exact g.commutes a }

/- English proof (translation)
Rewrite using `[LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, hx⟩`.

Conclude with `⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩`. Introduce and unpack `⟨m, -, hm, hx⟩`. Conclude with `⟨m, hm, hx⟩`.
-/
theorem Kur_eq : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by
  rw [LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩
  · rintro ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩

/- English proof (translation)
Rewrite `hx` using `[← Kur_eq]`. Take `⟨n, hn, hxn⟩` from `(LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx`. Take `⟨y, hy, h⟩` from `LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn`. Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.1 hy`. Conclude with `⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩`.
-/
theorem norm_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by
  rw [← Kur_eq] at hx
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx
  obtain ⟨y, hy, h⟩ := LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hy
  exact ⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `norm_Kur hx`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[norm_zero, norm_eq_zero]`. Conclude with `h0 ha`.

Use `⟨-a.valuation, ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `first`. Consider the case `exact Padic.norm_eq_zpow_neg_valuation ha0`. Consider the case `exact Padic.norm_eq_pow_val ha0`.
-/
theorem norm_Kur_zpow {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨a, ha⟩ := norm_Kur hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at ha
    exact h0 ha
  refine ⟨-a.valuation, ?_⟩
  rw [ha]
  first
  | exact Padic.norm_eq_zpow_neg_valuation ha0
  | exact Padic.norm_eq_pow_val ha0

/- English proof (translation)
Establish `h` using `congrArg norm hz`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h`.
-/
theorem norm_eq_one_of_pow {n : ℕ} (hn : n ≠ 0) {z : Om l} (hz : z ^ n = 1) : ‖z‖ = 1 := by
  have h := congrArg norm hz
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h

/- English proof (translation)
Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[← eval_one_cyclotomic_prime_pow (R := Om l) (p := l) k', cyclotomic_eq_prod_X_sub_primitiveRoots (ζQ_primitive l (k' + 1)), eval_prod]`. Simplify using the standard rewrite rules.
-/
theorem prod_one_sub_primitiveRoots {k : ℕ} (hk : 0 < k) :
    ∏ x ∈ primitiveRoots (l ^ k) (Om l), (1 - x) = (l : Om l) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [← eval_one_cyclotomic_prime_pow (R := Om l) (p := l) k',
    cyclotomic_eq_prod_X_sub_primitiveRoots (ζQ_primitive l (k' + 1)), eval_prod]
  simp

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ a ih`. Establish `e : 1 - z ^ (a + 1) = (1 - z ^ a) + z ^ a * (1 - z)` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)`.
-/
theorem norm_one_sub_pow_le {z : Om l} (hz : ‖z‖ ≤ 1) (a : ℕ) : ‖1 - z ^ a‖ ≤ ‖1 - z‖ := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 1 - z ^ (a + 1) = (1 - z ^ a) + z ^ a * (1 - z) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

/- English proof (translation)
Establish `hpos : l ^ k ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`. Establish `n1 : ‖z‖ ≤ 1` using `(norm_eq_one_of_pow hpos hz.pow_eq_one).le`. Establish `n2 : ‖z'‖ ≤ 1` using `(norm_eq_one_of_pow hpos hz'.pow_eq_one).le`. Take `⟨i, -, hi⟩` from `hz.eq_pow_of_pow_eq_one hz'.pow_eq_one`. Take `⟨j, -, hj⟩` from `hz'.eq_pow_of_pow_eq_one hz.pow_eq_one`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hj]`. Conclude with `norm_one_sub_pow_le n2 j`. Rewrite using `[← hi]`. Conclude with `norm_one_sub_pow_le n1 i`.
-/
theorem norm_one_sub_eq {k : ℕ} {z z' : Om l} (hz : IsPrimitiveRoot z (l ^ k))
    (hz' : IsPrimitiveRoot z' (l ^ k)) : ‖1 - z‖ = ‖1 - z'‖ := by
  have hpos : l ^ k ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have n1 : ‖z‖ ≤ 1 := (norm_eq_one_of_pow hpos hz.pow_eq_one).le
  have n2 : ‖z'‖ ≤ 1 := (norm_eq_one_of_pow hpos hz'.pow_eq_one).le
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  apply le_antisymm
  · rw [← hj]
    exact norm_one_sub_pow_le n2 j
  · rw [← hi]
    exact norm_one_sub_pow_le n1 i

/- English proof (translation)
Establish `hpos : 0 < l ^ k` using `pow_pos (Fact.out : l.Prime).pos k`. Establish `h` using `congrArg norm (prod_one_sub_primitiveRoots (l := l) hk)`. Rewrite `h` using `[norm_prod, norm_l]`. Rewrite `h` using `[Finset.prod_congr rfl (fun x hx => norm_one_sub_eq ((mem_primitiveRoots hpos).mp hx) hz), Finset.prod_const, hz.card_primitiveRoots]`. Conclude with `h`.
-/
theorem norm_one_sub_pow {k : ℕ} (hk : 0 < k) {z : Om l} (hz : IsPrimitiveRoot z (l ^ k)) :
    ‖1 - z‖ ^ (l ^ k).totient = (l : ℝ)⁻¹ := by
  have hpos : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  have h := congrArg norm (prod_one_sub_primitiveRoots (l := l) hk)
  rw [norm_prod, norm_l] at h
  rw [Finset.prod_congr rfl (fun x hx => norm_one_sub_eq ((mem_primitiveRoots hpos).mp hx) hz),
    Finset.prod_const, hz.card_primitiveRoots] at h
  exact h

section Irr

variable {F : IntermediateField ℚ_[l] (Om l)}

/- English proof (translation)
Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `(hz.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos k)).eq_zero`.
-/
theorem minpoly_dvd_cyclotomic {k : ℕ} {z : Om l} (hz : IsPrimitiveRoot z (l ^ k)) :
    minpoly F z ∣ cyclotomic (l ^ k) F := by
  apply minpoly.dvd
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact (hz.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos k)).eq_zero

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hpos : 0 < l ^ k` using `pow_pos hl.pos k`. Establish `hint : IsIntegral F z` using `⟨_, cyclotomic.monic _ _, by`. Rewrite using `[eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `(hz.isRoot_cyclotomic hpos).eq_zero⟩`.

Establish `hle : (minpoly F z).natDegree ≤ (l ^ k).totient`. Establish `h` using `natDegree_le_of_dvd (minpoly_dvd_cyclotomic (F := F) hz) (cyclotomic_ne_zero (l ^ k) F)`. Rewrite `h` using `[natDegree_cyclotomic]`. Then use the resulting hypothesis. Use `set m := minpoly F z with hm`. Use `set P := m.map (algebraMap F (Om l)) with hP`.

Establish `hd : 0 < m.natDegree` using `minpoly.natDegree_pos hint`. Establish `hmon : P.Monic` using `(minpoly.monic hint).map _`. Establish `hsplit` using `IsAlgClosed.splits P`. Use `haveI : NeZero ((l ^ k : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩`. Establish `hroots : ∀ a ∈ P.roots, IsPrimitiveRoot a (l ^ k)`.

Introduce `a ha`. Rewrite `ha` using `[mem_roots hmon.ne_zero]`. Establish `hdvd : P ∣ cyclotomic (l ^ k) (Om l)`. Rewrite using `[← map_cyclotomic (l ^ k) (algebraMap F (Om l))]`. Conclude with `Polynomial.map_dvd _ (minpoly_dvd_cyclotomic hz)`.

Establish `hr : IsRoot (cyclotomic (l ^ k) (Om l)) a`. Take `⟨q, hq⟩` from `hdvd`. Rewrite using `[IsRoot, hq, eval_mul, ha.eq_zero, zero_mul]`. Conclude with `isRoot_cyclotomic_iff.mp hr`. Establish `hcard : Multiset.card P.roots = m.natDegree` using `by first`.

Consider the case `exact (splits_iff_card_roots.mp hsplit).trans (natDegree_map _)`. Consider the case `exact (natDegree_eq_card_roots' hsplit).symm.trans (natDegree_map _)`. Consider the case `(rw [hP, natDegree_map]; exact (IsAlgClosed.card_roots_eq_natDegree).trans (natDegree_map _))`. Establish `heval : P.eval 1 = (P.roots.map fun a => 1 - a).prod`. Establish `hPdeg : P.natDegree = m.natDegree` using `natDegree_map _`.

Use `conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (hcard.trans hPdeg.symm)]`. Rewrite using `[eval_multiset_prod, Multiset.map_map]`. Simplify using `[Function.comp_def]`. Establish `hnorm : ‖(P.roots.map fun a => 1 - a).prod‖ = ‖1 - z‖ ^ m.natDegree`. Rewrite using `[← hcard]`.

Establish `hr : ∀ a ∈ P.roots, ‖1 - a‖ = ‖1 - z‖` using `fun a ha => norm_one_sub_eq (hroots a ha) hz`. Generalize the expression as in `P.roots = s at hr ⊢`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, ih (fun b hb => hr b (Multiset.mem_cons_of_mem hb)), hr a (Multiset.mem_cons_self a s)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : P.eval 1 ∈ MaximalUnramifiedExtension l`. Rewrite using `[hP, eval_one_map]`. Conclude with `hF (m.eval 1).2`.

Establish `hz1 : z ≠ 1` using `hz.ne_one (Nat.one_lt_pow hk.ne' hl.one_lt)`. Establish `hrpos : 0 < ‖1 - z‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))`. Establish `hval : ‖P.eval 1‖ = ‖1 - z‖ ^ m.natDegree` using `by rw [heval, hnorm]`. Establish `hne : P.eval 1 ≠ 0`. Introduce `h0`.

Rewrite `hval` using `[h0, norm_zero]`. Conclude with `(pow_pos hrpos _).ne' hval.symm`. Take `⟨j, hj⟩` from `norm_Kur_zpow hmem hne`. Establish `hφ` using `norm_one_sub_pow hk hz`. Establish `e1 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (-(m.natDegree : ℤ))`.

Rewrite using `[mul_comm, pow_mul, hφ, inv_pow, zpow_neg, zpow_natCast]`. Establish `e2 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (j * (l ^ k).totient : ℤ)`. Rewrite using `[pow_mul, ← hval, hj, zpow_mul, zpow_natCast]`. Establish `hinj : -(m.natDegree : ℤ) = j * (l ^ k).totient` using `zpow_right_injective₀ (zero_lt_one.trans one_lt_l) one_lt_l.ne' (e1.symm.trans e2)`. Establish `hφpos : 0 < (l ^ k).totient` using `by first`.

Consider the case `exact Nat.totient_pos.mpr hpos`. Consider the case `exact Nat.totient_pos hpos`. Establish `hj' : j ≤ -1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `: (0 : ℤ) ≤ j * (l ^ k).totient` using `mul_nonneg (by omega) (by positivity)`. Use linear arithmetic over natural numbers and integers. Establish `hge : ((l ^ k).totient : ℤ) ≤ m.natDegree` using `by nlinarith`. Establish `: (l ^ k).totient ≤ m.natDegree` using `by exact_mod_cast hge`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_minpoly_eq (hF : F ≤ MaximalUnramifiedExtension l) {k : ℕ} (hk : 0 < k) {z : Om l}
    (hz : IsPrimitiveRoot z (l ^ k)) : (minpoly F z).natDegree = (l ^ k).totient := by
  have hl := (Fact.out : l.Prime)
  have hpos : 0 < l ^ k := pow_pos hl.pos k
  have hint : IsIntegral F z := ⟨_, cyclotomic.monic _ _, by
    rw [eval₂_eq_eval_map, map_cyclotomic]
    exact (hz.isRoot_cyclotomic hpos).eq_zero⟩
  have hle : (minpoly F z).natDegree ≤ (l ^ k).totient := by
    have h := natDegree_le_of_dvd (minpoly_dvd_cyclotomic (F := F) hz) (cyclotomic_ne_zero (l ^ k) F)
    rwa [natDegree_cyclotomic] at h
  set m := minpoly F z with hm
  set P := m.map (algebraMap F (Om l)) with hP
  have hd : 0 < m.natDegree := minpoly.natDegree_pos hint
  have hmon : P.Monic := (minpoly.monic hint).map _
  have hsplit := IsAlgClosed.splits P
  haveI : NeZero ((l ^ k : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩
  have hroots : ∀ a ∈ P.roots, IsPrimitiveRoot a (l ^ k) := by
    intro a ha
    rw [mem_roots hmon.ne_zero] at ha
    have hdvd : P ∣ cyclotomic (l ^ k) (Om l) := by
      rw [← map_cyclotomic (l ^ k) (algebraMap F (Om l))]
      exact Polynomial.map_dvd _ (minpoly_dvd_cyclotomic hz)
    have hr : IsRoot (cyclotomic (l ^ k) (Om l)) a := by
      obtain ⟨q, hq⟩ := hdvd
      rw [IsRoot, hq, eval_mul, ha.eq_zero, zero_mul]
    exact isRoot_cyclotomic_iff.mp hr
  have hcard : Multiset.card P.roots = m.natDegree := by
    first
    | exact (splits_iff_card_roots.mp hsplit).trans (natDegree_map _)
    | exact (natDegree_eq_card_roots' hsplit).symm.trans (natDegree_map _)
    | (rw [hP, natDegree_map]; exact (IsAlgClosed.card_roots_eq_natDegree).trans (natDegree_map _))
  have heval : P.eval 1 = (P.roots.map fun a => 1 - a).prod := by
    have hPdeg : P.natDegree = m.natDegree := natDegree_map _
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (hcard.trans hPdeg.symm)]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hnorm : ‖(P.roots.map fun a => 1 - a).prod‖ = ‖1 - z‖ ^ m.natDegree := by
    rw [← hcard]
    have hr : ∀ a ∈ P.roots, ‖1 - a‖ = ‖1 - z‖ := fun a ha => norm_one_sub_eq (hroots a ha) hz
    generalize P.roots = s at hr ⊢
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ,
        ih (fun b hb => hr b (Multiset.mem_cons_of_mem hb)), hr a (Multiset.mem_cons_self a s)]
      ring
  have hmem : P.eval 1 ∈ MaximalUnramifiedExtension l := by
    rw [hP, eval_one_map]
    exact hF (m.eval 1).2
  have hz1 : z ≠ 1 := hz.ne_one (Nat.one_lt_pow hk.ne' hl.one_lt)
  have hrpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hval : ‖P.eval 1‖ = ‖1 - z‖ ^ m.natDegree := by rw [heval, hnorm]
  have hne : P.eval 1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hval
    exact (pow_pos hrpos _).ne' hval.symm
  obtain ⟨j, hj⟩ := norm_Kur_zpow hmem hne
  have hφ := norm_one_sub_pow hk hz
  have e1 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (-(m.natDegree : ℤ)) := by
    rw [mul_comm, pow_mul, hφ, inv_pow, zpow_neg, zpow_natCast]
  have e2 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (j * (l ^ k).totient : ℤ) := by
    rw [pow_mul, ← hval, hj, zpow_mul, zpow_natCast]
  have hinj : -(m.natDegree : ℤ) = j * (l ^ k).totient :=
    zpow_right_injective₀ (zero_lt_one.trans one_lt_l) one_lt_l.ne' (e1.symm.trans e2)
  have hφpos : 0 < (l ^ k).totient := by
    first
    | exact Nat.totient_pos.mpr hpos
    | exact Nat.totient_pos hpos
  have hj' : j ≤ -1 := by
    by_contra hc
    push_neg at hc
    have : (0 : ℤ) ≤ j * (l ^ k).totient := mul_nonneg (by omega) (by positivity)
    omega
  have hge : ((l ^ k).totient : ℤ) ≤ m.natDegree := by nlinarith
  have : (l ^ k).totient ≤ m.natDegree := by exact_mod_cast hge
  omega

end Irr

end Formalism.MainNotions.N.PreambleDegrees.Loc
