import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.Letter

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

/- English proof (translation)
Simplify using `only [Hd, MvPolynomial.mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq]`.
-/
theorem mem_Hd {R : Type} [CommRing R] {k d : ℕ} {P : MvPolynomial (Fin k) R} :
    P ∈ Hd R k d ↔ ∀ μ ∈ P.support, ∑ c, μ c = d := by
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq]

/- English proof (translation)
Rewrite using `[mem_Hd]`. Introduce `μ hμ`. Rewrite `hμ` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one]`. Use `split_ifs at hμ with h0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hμ`.
-/
theorem Hd_one (R : Type) [CommRing R] (k : ℕ) : (1 : MvPolynomial (Fin k) R) ∈ Hd R k 0 := by
  rw [mem_Hd]
  intro μ hμ
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp
  · exact absurd rfl hμ

/- English proof (translation)
Rewrite using `[mem_Hd]`. Introduce `μ hμ`. Rewrite `hμ` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']`. Use `split_ifs at hμ with h0`. Substitute `h0` using the available equality.

Simplify using `[Finsupp.single_apply]`. Simplify using `at hμ`.
-/
theorem Hd_X (R : Type) [CommRing R] (k : ℕ) (a : R) (c : Fin k) : C a * X c ∈ Hd R k 1 := by
  rw [mem_Hd]
  intro μ hμ
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X'] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp [Finsupp.single_apply]
  · simp at hμ

/- English proof (translation)
Rewrite `hP`, `hQ`, the goal using `[mem_Hd]`. Introduce `μ hμ`. Take `⟨a1, ha1, b1, hb1, rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul P Q hμ)`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hP a1 ha1, hQ b1 hb1]`.
-/
theorem Hd_mul {R : Type} [CommRing R] {k a b : ℕ} {P Q : MvPolynomial (Fin k) R} (hP : P ∈ Hd R k a)
    (hQ : Q ∈ Hd R k b) : P * Q ∈ Hd R k (a + b) := by
  classical
  rw [mem_Hd] at hP hQ ⊢
  intro μ hμ
  obtain ⟨a1, ha1, b1, hb1, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hμ)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hP a1 ha1, hQ b1 hb1]

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.prod_empty, Finset.sum_empty]`. Conclude with `Hd_one R k`.

Introduce `j s hj ih h`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `Hd_mul (h j (Finset.mem_insert_self j s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem Hd_prod {R : Type} [CommRing R] {k : ℕ} {J : Type} (s : Finset J) (δ : J → ℕ)
    (q : J → MvPolynomial (Fin k) R) (h : ∀ i ∈ s, q i ∈ Hd R k (δ i)) :
    ∏ i ∈ s, q i ∈ Hd R k (∑ i ∈ s, δ i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Hd_one R k
  · intro j s hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact Hd_mul (h j (Finset.mem_insert_self j s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def nuL (m d : ℕ) (vec : Bool) : Fin (m + 1) → ℕ :=
  fun t => if vec then (if t = 0 then d else 0) else (if t = Fin.last m then 0 else d)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `nuOf letterWt nuL`. Establish `hl : (Fin.last m : Fin (m + 1)) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg Fin.val h`.

Simplify using `at h2`. Use linear arithmetic over natural numbers and integers. Consider the cases of `vec`. Simplify using `only [Bool.false_eq_true, ↓reduceIte]`. Distinguish the cases in `ht : t = Fin.last m`.

Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Simplify using `[ht]`. Simplify using `only [↓reduceIte]`. Distinguish the cases in `ht : t = 0`.

Substitute `ht` using the available equality. Simplify using `[hl]`. Simplify using `[ht, hl]`.
-/
theorem nuOf_letterWt (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) : nuOf (letterWt m d vec) = nuL m d vec := by
  funext t
  unfold nuOf letterWt nuL
  have hl : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
    omega
  cases vec
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases ht : t = Fin.last m
    · subst ht
      simp
    · simp [ht]
  · simp only [↓reduceIte]
    by_cases ht : t = 0
    · subst ht
      simp [hl]
    · simp [ht, hl]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Apply the tactic sequence `cases vec <;> simp [nuL] <;> split_ifs <;> simp`.
-/
theorem nuL_smul (m d : ℕ) (vec : Bool) : nuL m d vec = d • nuL m 1 vec := by
  funext t
  cases vec <;> simp [nuL] <;> split_ifs <;> simp

def s0 (m : ℕ) (vec : Bool) : ℕ := if vec then 1 else m

/- English proof (translation)
Unfold `Nv`. Simplify using `only [Bool.false_eq_true, ↓reduceIte]`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.val_last, Fin.succAbove_last]`. Unfold `initMinor genM`. Both sides reduce to the same expression.
-/
theorem Nv_false_eq (R : Type) [CommRing R] (m : ℕ) (c : Fin (m + 1)) :
    Nv R m false c = (-1) ^ ((c : ℕ) + m) * initMinor R c.succAbove (Nat.le_succ m) := by
  unfold Nv
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.val_last, Fin.succAbove_last]
  unfold initMinor genM
  rfl

/- English proof (translation)
Rewrite using `[lcminor_initMinor_eq, Fintype.sum_subsingleton _ 1]`. Simplify using `[Nv, MvPolynomial.X]`.
-/
theorem Nv_true_eq (R : Type) [CommRing R] (m : ℕ) (c : Fin (m + 1)) :
    Nv R m true c = initMinor R (fun _ : Fin 1 => c) (Nat.succ_le_succ (Nat.zero_le m)) := by
  rw [lcminor_initMinor_eq, Fintype.sum_subsingleton _ 1]
  simp [Nv, MvPolynomial.X]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `shapeDeg s0 nuL`. Consider the cases of `vec`. Simplify using `only [Bool.false_eq_true, ↓reduceIte]`. Distinguish the cases in `ht : t = Fin.last m`.

Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : (t : ℕ) < m` using `Fin.val_lt_last ht`. Simplify using `[ht, h1]`. Simplify using `only [↓reduceIte]`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : ¬ (t : ℕ) < 1`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Use `ext`. Use `first`. Consider the case `(rw [Fin.val_zero]; omega)`. Consider the case `(simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]; omega)`.

Consider the case `(norm_num; omega)`. Simplify using `[ht, h1]`.
-/
theorem shape_one (m : ℕ) (vec : Bool) : shapeDeg (n := m + 1) (fun _ : Fin 1 => s0 m vec) = nuL m 1 vec := by
  funext t
  unfold shapeDeg s0 nuL
  cases vec
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases ht : t = Fin.last m
    · subst ht
      simp
    · have h1 : (t : ℕ) < m := Fin.val_lt_last ht
      simp [ht, h1]
  · simp only [↓reduceIte]
    by_cases ht : t = 0
    · subst ht
      simp
    · have h1 : ¬ (t : ℕ) < 1 := by
        intro h
        apply ht
        ext
        first
          | (rw [Fin.val_zero]; omega)
          | (simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]; omega)
          | (norm_num; omega)
      simp [ht, h1]

/- English proof (translation)
Consider the cases of `vec`. Rewrite using `[Nv_false_eq]`. Establish `hmem : initMinor R c.succAbove (Nat.le_succ m) ∈ dualWeyl R (m + 1) (m + 1) (nuL m 1 false)`. Rewrite using `[mem_dualWeyl_iff]`. Use `⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩` and prove the remaining obligations.

Establish `e : nuL m 1 false = initW (m + 1) m`. Use function extensionality and compare the values at `t`. Simplify using `only [nuL, initW, Bool.false_eq_true, ↓reduceIte]`. Distinguish the cases in `ht : t = Fin.last m`. Substitute `ht` using the available equality.

Simplify using the standard rewrite rules. Establish `h1 : (t : ℕ) < m` using `Fin.val_lt_last ht`. Simplify using `[ht, h1]`. Rewrite using `[e]`. Conclude with `initMinor_isWeightedHomogeneous _ _`.

Establish `e2 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) ^ ((c : ℕ) + m)) * initMinor R c.succAbove (Nat.le_succ m) = ((-1 : R) ^ ((c : ℕ) + m)) • initMinor R c.succAbove (Nat.le_succ m)`. Rewrite using `[Algebra.smul_def]`. Simplify using the standard rewrite rules. Rewrite using `[e2]`. Conclude with `Submodule.smul_mem _ _ hmem`.

Rewrite using `[Nv_true_eq, mem_dualWeyl_iff]`. Use `⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩` and prove the remaining obligations. Establish `e : nuL m 1 true = initW (m + 1) 1`. Use function extensionality and compare the values at `t`. Simplify using `only [nuL, initW, ↓reduceIte]`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : ¬ (t : ℕ) < 1`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Use `ext`. Use `first`. Consider the case `(rw [Fin.val_zero]; omega)`. Consider the case `(simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]; omega)`.

Consider the case `(norm_num; omega)`. Simplify using `[ht, h1]`. Rewrite using `[e]`. Conclude with `initMinor_isWeightedHomogeneous _ _`.
-/
theorem Nv_mem (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    Nv R m vec c ∈ dualWeyl R (m + 1) (m + 1) (nuL m 1 vec) := by
  cases vec
  · rw [Nv_false_eq]
    have hmem : initMinor R c.succAbove (Nat.le_succ m) ∈ dualWeyl R (m + 1) (m + 1) (nuL m 1 false) := by
      rw [mem_dualWeyl_iff]
      refine ⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩
      have e : nuL m 1 false = initW (m + 1) m := by
        funext t
        simp only [nuL, initW, Bool.false_eq_true, ↓reduceIte]
        by_cases ht : t = Fin.last m
        · subst ht
          simp
        · have h1 : (t : ℕ) < m := Fin.val_lt_last ht
          simp [ht, h1]
      rw [e]
      exact initMinor_isWeightedHomogeneous _ _
    have e2 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) ^ ((c : ℕ) + m)) *
        initMinor R c.succAbove (Nat.le_succ m) =
        ((-1 : R) ^ ((c : ℕ) + m)) • initMinor R c.succAbove (Nat.le_succ m) := by
      rw [Algebra.smul_def]
      simp
    rw [e2]
    exact Submodule.smul_mem _ _ hmem
  · rw [Nv_true_eq, mem_dualWeyl_iff]
    refine ⟨?_, fun l j hlj => initMinor_invariant _ _ l j hlj⟩
    have e : nuL m 1 true = initW (m + 1) 1 := by
      funext t
      simp only [nuL, initW, ↓reduceIte]
      by_cases ht : t = 0
      · subst ht
        simp
      · have h1 : ¬ (t : ℕ) < 1 := by
          intro h
          apply ht
          ext
          first
            | (rw [Fin.val_zero]; omega)
            | (simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]; omega)
            | (norm_num; omega)
        simp [ht, h1]
    rw [e]
    exact initMinor_isWeightedHomogeneous _ _

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Establish `e : (0 : ℕ) • ν = 0`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Rewrite using `[pow_zero, e]`. Conclude with `one_mem_dualWeyl`. Consider the case `succ a ih`. Establish `e : (a + 1) • ν = a • ν + ν`. Use function extensionality and compare the values at `t`.

Simplify using `[add_mul]`. Rewrite using `[pow_succ, e]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeyl_mul ih hf`.
-/
theorem dw_pow {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (a : ℕ) : f ^ a ∈ dualWeyl R r n (a • ν) := by
  induction a with
  | zero =>
    have e : (0 : ℕ) • ν = 0 := by
      funext t
      simp
    rw [pow_zero, e]
    exact one_mem_dualWeyl
  | succ a ih =>
    have e : (a + 1) • ν = a • ν + ν := by
      funext t
      simp [add_mul]
    rw [pow_succ, e]
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul ih hf

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Establish `e : (∑ i ∈ (∅ : Finset J), a i) • ν = 0`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_empty, e]`.

Conclude with `one_mem_dualWeyl`. Introduce `j s hj ih`. Establish `e : (∑ i ∈ insert j s, a i) • ν = a j • ν + (∑ i ∈ s, a i) • ν`. Use function extensionality and compare the values at `t`. Simplify using `[Finset.sum_insert hj, add_mul]`.

Rewrite using `[Finset.prod_insert hj, e]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeyl_mul (dw_pow (hf j) (a j)) ih`.
-/
theorem dw_prod {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ} {J : Type} (s : Finset J)
    (f : J → MvPolynomial (Fin r × Fin n) R) (a : J → ℕ) (hf : ∀ i, f i ∈ dualWeyl R r n ν) :
    ∏ i ∈ s, f i ^ a i ∈ dualWeyl R r n ((∑ i ∈ s, a i) • ν) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have e : (∑ i ∈ (∅ : Finset J), a i) • ν = 0 := by
      funext t
      simp
    rw [Finset.prod_empty, e]
    exact one_mem_dualWeyl
  · intro j s hj ih
    have e : (∑ i ∈ insert j s, a i) • ν = a j • ν + (∑ i ∈ s, a i) • ν := by
      funext t
      simp [Finset.sum_insert hj, add_mul]
    rw [Finset.prod_insert hj, e]
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul (dw_pow (hf j) (a j)) ih

/- English proof (translation)
Introduce `y hy`. Take `⟨P, hP, rfl⟩` from `Submodule.mem_map.1 hy`. Rewrite `hP` using `[mem_Hd]`. Rewrite using `[AlgHom.toLinearMap_apply, P.as_sum, map_sum]`. Use `Submodule.sum_mem _ (fun μ hμ => ?_)` and prove the remaining obligations.

Unfold `theta`. Rewrite using `[MvPolynomial.aeval_monomial, ← Algebra.smul_def]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Establish `hsum : ∑ i ∈ μ.support, μ i = d`. Rewrite using `[← hP μ hμ]`.

Conclude with `Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)`. Establish `hmem` using `dw_prod μ.support (fun i => Nv R m vec i) (fun i => μ i) (fun i => Nv_mem R m vec i)`. Rewrite `hmem` using `[hsum, ← nuL_smul]`. Unfold `Finsupp.prod`. Conclude with `hmem`.
-/
theorem theta_Hd_le (R : Type) [CommRing R] (m d : ℕ) (vec : Bool) :
    (Hd R (m + 1) d).map (theta R m vec).toLinearMap ≤ dualWeyl R (m + 1) (m + 1) (nuL m d vec) := by
  classical
  intro y hy
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hy
  rw [mem_Hd] at hP
  rw [AlgHom.toLinearMap_apply, P.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun μ hμ => ?_)
  unfold theta
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hsum : ∑ i ∈ μ.support, μ i = d := by
    rw [← hP μ hμ]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
  have hmem := dw_prod μ.support (fun i => Nv R m vec i) (fun i => μ i) (fun i => Nv_mem R m vec i)
  rw [hsum, ← nuL_smul] at hmem
  unfold Finsupp.prod
  exact hmem

/- English proof (translation)
Establish `hinj` using `hI.injective`. Establish `hcard : (Finset.univ \ Finset.univ.image I).card = 1` using `by first`. Consider the case `rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]`. Consider the case `rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]`. Simplify using the standard rewrite rules.

Take `⟨c, hc⟩` from `Finset.card_eq_one.1 hcard`. Use `⟨c, (StrictMono.range_inj hI (Fin.strictMono_succAbove c)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.range_succAbove]`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ hy`. Establish `h1 : I y ∈ Finset.univ \ Finset.univ.image I`. Rewrite using `[hc, hy]`. Conclude with `Finset.mem_singleton_self _`.

Simplify using `at h1`. Introduce `hx`. Assume the negation of the conclusion as `hne`. Establish `h1 : x ∈ Finset.univ \ Finset.univ.image I`. Simplify using `only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and]`.

Introduce `hex`. Apply `hne` to reduce the goal to its premises. Simplify using `using hex`. Rewrite `h1` using `[hc]`. Conclude with `hx (Finset.mem_singleton.1 h1)`.
-/
theorem exists_succAbove {m : ℕ} (I : Fin m → Fin (m + 1)) (hI : StrictMono I) :
    ∃ c : Fin (m + 1), I = c.succAbove := by
  classical
  have hinj := hI.injective
  have hcard : (Finset.univ \ Finset.univ.image I).card = 1 := by
    first
      | rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]
      | rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_image_of_injective _ hinj]
    simp
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard
  refine ⟨c, (StrictMono.range_inj hI (Fin.strictMono_succAbove c)).1 ?_⟩
  rw [Fin.range_succAbove]
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩ hy
    have h1 : I y ∈ Finset.univ \ Finset.univ.image I := by
      rw [hc, hy]
      exact Finset.mem_singleton_self _
    simp at h1
  · intro hx
    by_contra hne
    have h1 : x ∈ Finset.univ \ Finset.univ.image I := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and]
      intro hex
      apply hne
      simpa using hex
    rw [hc] at h1
    exact hx (Finset.mem_singleton.1 h1)

/- English proof (translation)
Break down `h with rfl | hs0` into its components or cases. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using Hd_one R (m + 1)`. Rewrite using `[map_one]`. Unfold `initMinor`.

Simplify using `[Matrix.det_isEmpty]`. Consider the cases of `vec`. Simplify using `only [s0, Bool.false_eq_true, ↓reduceIte] at hs0`. Substitute `hs0` using the available equality. Take `⟨c, rfl⟩` from `exists_succAbove I hI`.

Use `⟨MvPolynomial.C ((-1 : R) ^ ((c : ℕ) + s)) * X c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg (by omega)]`. Conclude with `Hd_X R (s + 1) _ c`. Unfold `theta`. Rewrite using `[map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Nv_false_eq, MvPolynomial.algebraMap_eq, ← mul_assoc, map_pow, map_neg, map_one, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]`.

Simplify using `only [s0, ↓reduceIte] at hs0`. Substitute `hs0` using the available equality. Use `⟨X (I 0), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg one_ne_zero]`. Simplify using `using Hd_X R (m + 1) 1 (I 0)`.

Unfold `theta`. Rewrite using `[MvPolynomial.aeval_X, Nv_true_eq]`. Establish `hI2 : (fun _ : Fin 1 => I 0) = I` using `funext fun i => by rw [Subsingleton.elim i 0]`. Rewrite using `[hI2]`.
-/
theorem minor_pre (R : Type) [CommRing R] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (s : ℕ) (hs : s ≤ m + 1)
    (I : Fin s → Fin (m + 1)) (hI : StrictMono I) (h : s = 0 ∨ s = s0 m vec) :
    ∃ q ∈ Hd R (m + 1) (if s = 0 then 0 else 1), theta R m vec q = initMinor R I hs := by
  rcases h with rfl | hs0
  · refine ⟨1, ?_, ?_⟩
    · simpa using Hd_one R (m + 1)
    · rw [map_one]
      unfold initMinor
      simp [Matrix.det_isEmpty]
  · cases vec
    · simp only [s0, Bool.false_eq_true, ↓reduceIte] at hs0
      subst hs0
      obtain ⟨c, rfl⟩ := exists_succAbove I hI
      refine ⟨MvPolynomial.C ((-1 : R) ^ ((c : ℕ) + s)) * X c, ?_, ?_⟩
      · rw [if_neg (by omega)]
        exact Hd_X R (s + 1) _ c
      · unfold theta
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Nv_false_eq, MvPolynomial.algebraMap_eq,
          ← mul_assoc, map_pow, map_neg, map_one, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    · simp only [s0, ↓reduceIte] at hs0
      subst hs0
      refine ⟨X (I 0), ?_, ?_⟩
      · rw [if_neg one_ne_zero]
        simpa using Hd_X R (m + 1) 1 (I 0)
      · unfold theta
        rw [MvPolynomial.aeval_X, Nv_true_eq]
        have hI2 : (fun _ : Fin 1 => I 0) = I := funext fun i => by rw [Subsingleton.elim i 0]
        rw [hI2]

/- English proof (translation)
Establish `hA : ∀ t : Fin (m + 1), (Finset.univ.filter fun k : Fin K => t.val < sz k).card = nuL m d vec t`. Introduce `t`. Rewrite using `[← hshape]`. Both sides reduce to the same expression. Establish `hl : (0 : Fin (m + 1)) ≠ Fin.last m`.

Introduce `h`. Establish `h2` using `congrArg Fin.val h`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers. Establish `hz : ((0 : Fin (m + 1)) : ℕ) = 0` using `by simp`.

Establish `hsum : ∑ k, (if sz k = 0 then 0 else 1) = (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card`. Rewrite using `[Finset.card_filter]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : sz k = 0 <;> simp [h, Nat.pos_iff_ne_zero, Fin.val_zero]`. Establish `h0 : (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card = d`.

Rewrite using `[hA 0]`. Apply the tactic sequence `cases vec <;> simp [nuL, hl]`. Use `⟨?_, hsum.trans h0⟩` and prove the remaining obligations. Introduce `k`. Consider the cases of `vec`.

Simplify using `only [s0, Bool.false_eq_true, ↓reduceIte]`. Establish `hlast : (Finset.univ.filter fun k : Fin K => m < sz k).card = 0`. Establish `h1` using `hA (Fin.last m)`. Simplify `h1` using `[nuL]`. Establish `hle : sz k ≤ m`.

Rewrite `hlast` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `not_lt.1 (hlast (Finset.mem_univ k))`. Establish `hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m`. Introduce `h`. Establish `h2` using `congrArg Fin.val h`.

Simplify using `at h2`. Use linear arithmetic over natural numbers and integers. Establish `hm1 : (Finset.univ.filter fun k : Fin K => m - 1 < sz k).card = d`. Establish `h1` using `hA ⟨m - 1, by omega⟩`. Simplify `h1` using `[nuL, hne]`.

Establish `hsub : (Finset.univ.filter fun k : Fin K => m - 1 < sz k) ⊆ (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k)`. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Use linear arithmetic over natural numbers and integers. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub (by rw [h0, hm1])`.

Distinguish the cases in `hk : sz k = 0`. Use `left`. Conclude with `hk`. Use `right`. Establish `hk0 : k ∈ Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Rewrite `hk0` using `[← heq]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [s0, ↓reduceIte]`. Establish `hne : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg Fin.val h`. Simplify using `at h2`.

Establish `h1 : (Finset.univ.filter fun k : Fin K => 1 < sz k).card = 0`. Establish `h3` using `hA ⟨1, by omega⟩`. Simplify `h3` using `[nuL, hne]`. Rewrite `h1` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Establish `h4` using `h1 (Finset.mem_univ k)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem shape_sizes (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) {K : ℕ} (sz : Fin K → ℕ)
    (hshape : shapeDeg (n := m + 1) sz = nuL m d vec) :
    (∀ k, sz k = 0 ∨ sz k = s0 m vec) ∧ ∑ k, (if sz k = 0 then 0 else 1) = d := by
  classical
  have hA : ∀ t : Fin (m + 1), (Finset.univ.filter fun k : Fin K => t.val < sz k).card = nuL m d vec t := by
    intro t
    rw [← hshape]
    rfl
  have hl : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
    omega
  have hz : ((0 : Fin (m + 1)) : ℕ) = 0 := by simp
  have hsum : ∑ k, (if sz k = 0 then 0 else 1) = (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : sz k = 0 <;> simp [h, Nat.pos_iff_ne_zero, Fin.val_zero]
  have h0 : (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k).card = d := by
    rw [hA 0]
    cases vec <;> simp [nuL, hl]
  refine ⟨?_, hsum.trans h0⟩
  intro k
  cases vec
  · simp only [s0, Bool.false_eq_true, ↓reduceIte]
    have hlast : (Finset.univ.filter fun k : Fin K => m < sz k).card = 0 := by
      have h1 := hA (Fin.last m)
      simpa [nuL] using h1
    have hle : sz k ≤ m := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hlast
      exact not_lt.1 (hlast (Finset.mem_univ k))
    have hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h
      have h2 := congrArg Fin.val h
      simp at h2
      omega
    have hm1 : (Finset.univ.filter fun k : Fin K => m - 1 < sz k).card = d := by
      have h1 := hA ⟨m - 1, by omega⟩
      simpa [nuL, hne] using h1
    have hsub : (Finset.univ.filter fun k : Fin K => m - 1 < sz k) ⊆
        (Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h0, hm1])
    by_cases hk : sz k = 0
    · left
      exact hk
    · right
      have hk0 : k ∈ Finset.univ.filter fun k : Fin K => ((0 : Fin (m + 1)) : ℕ) < sz k := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [← heq] at hk0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
      omega
  · simp only [s0, ↓reduceIte]
    have hne : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0 := by
      intro h
      have h2 := congrArg Fin.val h
      simp at h2
    have h1 : (Finset.univ.filter fun k : Fin K => 1 < sz k).card = 0 := by
      have h3 := hA ⟨1, by omega⟩
      simpa [nuL, hne] using h3
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have h4 := h1 (Finset.mem_univ k)
    omega

/- English proof (translation)
Apply `le_antisymm (theta_Hd_le R m d vec)` to reduce the goal to its premises. Take `⟨b, hb, h2⟩` from `sSBasis R (m + 1) (m + 1) (nuL m d vec)`. Rewrite using `[← hb.2.1, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨-, -, K, sz, hsz, I, hshape, hI, hbi⟩` from `h2 i`.

Take `⟨hs1, hs2⟩` from `shape_sizes m hm d vec sz hshape`. Establish `hq` using `fun k => minor_pre R m hm vec (sz k) (hsz k) (I k) (hI k) (hs1 k)`. Use `choose q hq1 hq2 using hq`. Use `⟨∏ k, q k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs2]`.

Conclude with `Hd_prod Finset.univ _ q fun k _ => hq1 k`. Use `show theta R m vec (∏ k, q k) = b i`. Rewrite using `[map_prod, hbi]`. Unfold `bideterminant`. Conclude with `Finset.prod_congr rfl fun k _ => hq2 k`.
-/
theorem theta_Hd (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool) :
    (Hd R (m + 1) d).map (theta R m vec).toLinearMap = dualWeyl R (m + 1) (m + 1) (nuL m d vec) := by
  apply le_antisymm (theta_Hd_le R m d vec)
  obtain ⟨b, hb, h2⟩ := sSBasis R (m + 1) (m + 1) (nuL m d vec)
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, K, sz, hsz, I, hshape, hI, hbi⟩ := h2 i
  obtain ⟨hs1, hs2⟩ := shape_sizes m hm d vec sz hshape
  have hq := fun k => minor_pre R m hm vec (sz k) (hsz k) (I k) (hI k) (hs1 k)
  choose q hq1 hq2 using hq
  refine ⟨∏ k, q k, ?_, ?_⟩
  · rw [← hs2]
    exact Hd_prod Finset.univ _ q fun k _ => hq1 k
  · show theta R m vec (∏ k, q k) = b i
    rw [map_prod, hbi]
    unfold bideterminant
    exact Finset.prod_congr rfl fun k _ => hq2 k

end Formalism.L2.G.Model
