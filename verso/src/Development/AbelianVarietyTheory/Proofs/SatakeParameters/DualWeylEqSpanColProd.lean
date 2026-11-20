import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.Columns.CoefModB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.WeylMinorDual

open Formalism.GradedWeylDivisibility

def gdet (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.of fun a s : Fin n => (X (a, s) : MvPolynomial (Fin n × Fin n) R)).det

/- English proof (translation)
Use `set M : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) := Matrix.of fun a s : Fin n => Polynomial.C (X (a, s)) with hM`. Establish `h1 : Polynomial.C (gdet R n) = M.det`. Unfold `gdet`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Establish `h2 : rowGen R a b (gdet R n) = (M.updateRow b (M b + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a)).det`. Unfold `gdet`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use `ext1 p q`.

Distinguish the cases in `hp : p = b`. Substitute `hp` using the available equality. Simplify using `[rowGen, hM]`. Simplify using `[rowGen, hM, hp, Matrix.updateRow_ne hp]`. Rewrite using `[h1, h2]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `: M a + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a = (1 + Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a`. Rewrite using `[add_smul, one_smul]`. Rewrite using `[this, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]`.

Simplify using `[mul_comm]`. Rewrite using `[Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]`. Simplify using `[hab]`.
-/
theorem rowGen_gdet (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) :
    rowGen R a b (gdet R n) =
      Polynomial.C (gdet R n) * Polynomial.map C (1 + if a = b then Polynomial.X else (0 : Polynomial R)) := by
  set M : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) :=
    Matrix.of fun a s : Fin n => Polynomial.C (X (a, s)) with hM
  have h1 : Polynomial.C (gdet R n) = M.det := by
    unfold gdet
    rw [RingHom.map_det]
    rfl
  have h2 : rowGen R a b (gdet R n) =
      (M.updateRow b (M b + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a)).det := by
    unfold gdet
    rw [AlgHom.map_det]
    congr 1
    ext1 p q
    by_cases hp : p = b
    · subst hp
      simp [rowGen, hM]
    · simp [rowGen, hM, hp, Matrix.updateRow_ne hp]
  rw [h1, h2]
  by_cases hab : a = b
  · subst hab
    have : M a + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a =
        (1 + Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • M a := by
      rw [add_smul, one_smul]
    rw [this, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
    simp [mul_comm]
  · rw [Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]
    simp [hab]

/- English proof (translation)
Use `set u : Polynomial R := (1 + if a = b then Polynomial.X else (0 : Polynomial R)) ^ e with hu`. Use `⟨u.coeff, ?_, fun k f => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [hu, Polynomial.coeff_zero_eq_eval_zero] split_ifs <;> simp`. Unfold `rowDiv`. Rewrite using `[map_mul, map_pow, rowGen_gdet, mul_pow, ← Polynomial.map_pow, ← hu, ← map_pow, mul_left_comm, Polynomial.coeff_C_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_map, smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowDiv_mul_gdet_pow (R : Type) [CommRing R] (n e : ℕ) (a b : Fin n) :
    ∃ u : ℕ → R, u 0 = 1 ∧ ∀ (k : ℕ) (f : MvPolynomial (Fin n × Fin n) R),
      rowDiv R a b k (f * gdet R n ^ e) =
        ∑ i ∈ Finset.range (k + 1), u (k - i) • (rowDiv R a b i f * gdet R n ^ e) := by
  set u : Polynomial R := (1 + if a = b then Polynomial.X else (0 : Polynomial R)) ^ e with hu
  refine ⟨u.coeff, ?_, fun k f => ?_⟩
  · rw [hu, Polynomial.coeff_zero_eq_eval_zero]
    split_ifs <;> simp
  · unfold rowDiv
    rw [map_mul, map_pow, rowGen_gdet, mul_pow, ← Polynomial.map_pow, ← hu, ← map_pow, mul_left_comm,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_map, smul_eq_C_mul]
    ring

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp [hw, gdet]`. Consider the case `succ n`. Unfold `hw`. Rewrite using `[Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `: (s.castSucc : Fin (n + 1)).val + 1 < n + 1` using `by simp`. Simplify using `only [nuNext, dif_pos this]`.

Use linear arithmetic over natural numbers and integers. Establish `: ¬ ((Fin.last n).val + 1 < n + 1)` using `by simp`. Simplify using `only [nuNext, dif_neg this, Nat.sub_zero, pow_add]`. Both sides reduce to the same expression.
-/
theorem hw_add (R : Type) [CommRing R] (n e : ℕ) (μ : Fin n → ℕ) :
    hw R (le_refl n) (fun r => μ r + e) = hw R (le_refl n) μ * gdet R n ^ e := by
  cases n with
  | zero => simp [hw, gdet]
  | succ n =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have : (s.castSucc : Fin (n + 1)).val + 1 < n + 1 := by simp
      simp only [nuNext, dif_pos this]
      omega
    · have : ¬ ((Fin.last n).val + 1 < n + 1) := by simp
      simp only [nuNext, dif_neg this, Nat.sub_zero, pow_add]
      rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `weyl`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Proceed by induction on `w with`.

Consider the case `nil => exact ⟨hw R le_rfl μ, Submodule.subset_span ⟨[], rfl⟩, (hw_add R n e μ).symm⟩`. Consider the case `cons x w ih`. Take `⟨f, hf, hfe⟩` from `ih`. Take `⟨u, -, hu⟩` from `rowDiv_mul_gdet_pow R n e x.1 x.2.1`. Express the relevant statement in the definitionally equal form `rowDiv R x.1 x.2.1 x.2.2 (applyWord R w _) ∈ _`.

Simplify using `only [LinearMap.mulRight_apply] at hfe`. Rewrite using `[← hfe, hu]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, weylRowDivStable R n n le_rfl μ _ _ i f hf, rfl⟩`. Rewrite using `[weyl, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨w, rfl⟩, rfl⟩`.

Simplify using `only [LinearMap.mulRight_apply, SetLike.mem_coe]`. Proceed by induction on `w with`. Consider the case `nil => exact Submodule.subset_span ⟨[], hw_add R n e μ⟩`. Consider the case `cons x w ih`. Take `⟨u, hu0, hu⟩` from `rowDiv_mul_gdet_pow R n e x.1 x.2.1`.

Express the relevant statement in the definitionally equal form `rowDiv R x.1 x.2.1 x.2.2 (applyWord R w _) * _ ∈ _`. Generalize the expression as in `x.2.2 = k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ihk`. Establish `h` using `weylRowDivStable R n n le_rfl _ x.1 x.2.1 k _ ih`.

Rewrite `h` using `[hu, Finset.sum_range_succ, Nat.sub_self, hu0, one_smul]`. Conclude with `(Submodule.add_mem_iff_right _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (ihk i (Finset.mem_range.mp hi)))).mp h`.
-/
theorem weyl_add (R : Type) [CommRing R] (n e : ℕ) (μ : Fin n → ℕ) :
    weyl R n n le_rfl (fun r => μ r + e) = (weyl R n n le_rfl μ).map (LinearMap.mulRight R (gdet R n ^ e)) := by
  apply le_antisymm
  · unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    induction w with
    | nil => exact ⟨hw R le_rfl μ, Submodule.subset_span ⟨[], rfl⟩, (hw_add R n e μ).symm⟩
    | cons x w ih =>
      obtain ⟨f, hf, hfe⟩ := ih
      obtain ⟨u, -, hu⟩ := rowDiv_mul_gdet_pow R n e x.1 x.2.1
      change rowDiv R x.1 x.2.1 x.2.2 (applyWord R w _) ∈ _
      simp only [LinearMap.mulRight_apply] at hfe
      rw [← hfe, hu]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        ⟨_, weylRowDivStable R n n le_rfl μ _ _ i f hf, rfl⟩
  · rw [weyl, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    simp only [LinearMap.mulRight_apply, SetLike.mem_coe]
    induction w with
    | nil => exact Submodule.subset_span ⟨[], hw_add R n e μ⟩
    | cons x w ih =>
      obtain ⟨u, hu0, hu⟩ := rowDiv_mul_gdet_pow R n e x.1 x.2.1
      change rowDiv R x.1 x.2.1 x.2.2 (applyWord R w _) * _ ∈ _
      generalize x.2.2 = k
      induction k using Nat.strong_induction_on with
      | _ k ihk =>
        have h := weylRowDivStable R n n le_rfl _ x.1 x.2.1 k _ ih
        rw [hu, Finset.sum_range_succ, Nat.sub_self, hu0, one_smul] at h
        exact (Submodule.add_mem_iff_right _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
          (ihk i (Finset.mem_range.mp hi)))).mp h

/- English proof (translation)
Establish `hB : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card = (Finset.univ.filter fun k => sz k = t + 1).card + (Finset.univ.filter fun k => t + 1 < sz k).card`. Introduce `t`. Rewrite using `[← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun k _ hk => by omega), ← Finset.filter_or]`. Use `congr 1`. Use `Finset.filter_congr fun k _ => by omega` and prove the remaining obligations.

Rewrite using `[← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range (n + 1)) (g := sz) (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz k))) g, Finset.prod_range_succ']`. Simplify using `only [Finset.prod_const, hg, one_pow, mul_one]`. Rewrite using `[Finset.prod_range]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `h1` using `hB s`. Establish `h2 : nuNext (shapeDeg (n` using `n) sz) s = (Finset.univ.filter fun k => s.val + 1 < sz k).card := by`. Unfold `nuNext`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[Finset.filter_false_of_mem fun k _ => by have := hsz k; omega]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Unfold `shapeDeg`. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_sizes {M : Type} [CommMonoid M] (g : ℕ → M) (hg : g 0 = 1) (n : ℕ) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) :
    ∏ k, g (sz k) = ∏ s : Fin n, g (s.val + 1) ^ (shapeDeg sz s - nuNext (shapeDeg sz) s) := by
  have hB : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun k => sz k = t + 1).card + (Finset.univ.filter fun k => t + 1 < sz k).card := by
    intro t
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun k _ hk => by omega), ← Finset.filter_or]
    congr 1
    refine Finset.filter_congr fun k _ => by omega
  rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range (n + 1)) (g := sz)
    (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz k))) g, Finset.prod_range_succ']
  simp only [Finset.prod_const, hg, one_pow, mul_one]
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  have h1 := hB s
  have h2 : nuNext (shapeDeg (n := n) sz) s = (Finset.univ.filter fun k => s.val + 1 < sz k).card := by
    unfold nuNext
    split_ifs with h
    · rfl
    · rw [Finset.filter_false_of_mem fun k _ => by have := hsz k; omega]
      rfl
  rw [h2]
  unfold shapeDeg
  omega

open scoped Pointwise in

/- English proof (translation)
Set `M : ℕ → Set (MvPolynomial (Fin n × Fin n) R)` to `fun p => {f | ∃ (hp : p ≤ n) (I : Fin p ↪o Fin n), f = initMinor R I hp}`. Establish `hM0 : M 0 = 1`. Use extensionality with `f`. Simplify using `only [M, Set.mem_setOf_eq, Set.mem_one, initMinor, Matrix.det_isEmpty]`. Conclude with `⟨fun ⟨_, _, h⟩ => h, fun h => ⟨Nat.zero_le _, OrderEmbedding.ofIsEmpty, h⟩⟩`.

Establish `hD : ∏ k, M (sz k) = ∏ k, M (sz' k)`. Rewrite using `[prod_sizes M hM0 n sz hsz, prod_sizes M hM0 n sz' hsz', h]`. Establish `hmem : bideterminant R sz hsz I ∈ ∏ k, M (sz k)` using `(Set.mem_fintype_prod _ _).mpr ⟨fun k => initMinor R (I k) (hsz k), fun k => ⟨hsz k, OrderEmbedding.ofStrictMono _ (hI k), rfl⟩, rfl⟩`. Rewrite `hmem` using `[hD]`. Take `⟨g, hg, hge⟩` from `(Set.mem_fintype_prod _ _).mp hmem`.

Use `choose hp J hJ using hg`. Conclude with `⟨J, by rw [← hge]; exact Finset.prod_congr rfl fun k _ => hJ k⟩`.
-/
theorem bidet_reorder (R : Type) [CommRing R] (n : ℕ) {K K' : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (sz' : Fin K' → ℕ) (hsz' : ∀ k, sz' k ≤ n) (h : shapeDeg (n := n) sz = shapeDeg sz')
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, StrictMono (I k)) :
    ∃ J : ∀ k, Fin (sz' k) ↪o Fin n, bideterminant R sz hsz I = bideterminant R sz' hsz' (fun k => J k) := by
  classical
  let M : ℕ → Set (MvPolynomial (Fin n × Fin n) R) := fun p =>
    {f | ∃ (hp : p ≤ n) (I : Fin p ↪o Fin n), f = initMinor R I hp}
  have hM0 : M 0 = 1 := by
    ext f
    simp only [M, Set.mem_setOf_eq, Set.mem_one, initMinor, Matrix.det_isEmpty]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨Nat.zero_le _, OrderEmbedding.ofIsEmpty, h⟩⟩
  have hD : ∏ k, M (sz k) = ∏ k, M (sz' k) := by
    rw [prod_sizes M hM0 n sz hsz, prod_sizes M hM0 n sz' hsz', h]
  have hmem : bideterminant R sz hsz I ∈ ∏ k, M (sz k) :=
    (Set.mem_fintype_prod _ _).mpr ⟨fun k => initMinor R (I k) (hsz k),
      fun k => ⟨hsz k, OrderEmbedding.ofStrictMono _ (hI k), rfl⟩, rfl⟩
  rw [hD] at hmem
  obtain ⟨g, hg, hge⟩ := (Set.mem_fintype_prod _ _).mp hmem
  choose hp J hJ using hg
  exact ⟨J, by rw [← hge]; exact Finset.prod_congr rfl fun k _ => hJ k⟩

/- English proof (translation)
Set `g : ℕ → MvPolynomial (Fin n × Fin n) R` to `fun p => if h : p ≤ n then lpMinor R p h h else 1`. Establish `hg : g 0 = 1` using `by simp [g, lpMinor]`. Establish `h1 : bideterminant R sz hsz I = ∏ k, g (sz k)`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: I k = Fin.castLE (hsz k)` using `funext fun i => Fin.ext (hI k i)`.

Simplify using `only [g, dif_pos (hsz k), this]`. Both sides reduce to the same expression. Rewrite using `[h1, prod_sizes g hg n sz hsz]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `: s.val + 1 ≤ n` using `s.2`.

Simplify using `only [g, dif_pos this]`.
-/
theorem bidet_lead (R : Type) [CommRing R] (n : ℕ) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k i, (I k i : ℕ) = i) :
    bideterminant R sz hsz I = hw R le_rfl (shapeDeg (n := n) sz) := by
  let g : ℕ → MvPolynomial (Fin n × Fin n) R := fun p => if h : p ≤ n then lpMinor R p h h else 1
  have hg : g 0 = 1 := by simp [g, lpMinor]
  have h1 : bideterminant R sz hsz I = ∏ k, g (sz k) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have : I k = Fin.castLE (hsz k) := funext fun i => Fin.ext (hI k i)
    simp only [g, dif_pos (hsz k), this]
    rfl
  rw [h1, prod_sizes g hg n sz hsz]
  refine Finset.prod_congr rfl fun s _ => ?_
  have : s.val + 1 ≤ n := s.2
  simp only [g, dif_pos this]

/- English proof (translation)
The claim follows from `(Y.colLen_anti 0 c (Nat.zero_le _)).trans hY`.
-/
theorem colLen_le {n : ℕ} {Y : YoungDiagram} (hY : Y.colLen 0 ≤ n) (c : Fin (Y.rowLen 0)) : Y.colLen c ≤ n :=
  (Y.colLen_anti 0 c (Nat.zero_le _)).trans hY

def colProd (R : Type) [CommRing R] (n : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ n)
    (J : ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin n) : MvPolynomial (Fin n × Fin n) R :=
  bideterminant R (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) (fun c => J c)

/- English proof (translation)
Use function extensionality and compare the values at `r`. Unfold `shapeDeg`. Rewrite using `[Finset.filter_congr (q := fun c : Fin (Y.rowLen 0) => c.val < Y.rowLen r) fun c _ => by`. Rewrite using `[← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen], Fin.card_filter_val_lt]`. Conclude with `min_eq_right (Y.rowLen_anti 0 r (Nat.zero_le _))`.
-/
theorem shapeDeg_colLen (n : ℕ) (Y : YoungDiagram) :
    shapeDeg (n := n) (fun c : Fin (Y.rowLen 0) => Y.colLen c) = fun r : Fin n => Y.rowLen r := by
  funext r
  unfold shapeDeg
  rw [Finset.filter_congr (q := fun c : Fin (Y.rowLen 0) => c.val < Y.rowLen r) fun c _ => by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen], Fin.card_filter_val_lt]
  exact min_eq_right (Y.rowLen_anti 0 r (Nat.zero_le _))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Take `⟨b, ⟨-, hb, -⟩, hb'⟩` from `sSBasis R n n (fun r : Fin n => Y.rowLen r)`. Rewrite using `[← hb]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`.

Take `⟨-, -, K, sz, hsz, I, hsh, hI, he⟩` from `hb' m`. Take `⟨J, hJ⟩` from `bidet_reorder R n sz hsz _ (colLen_le hY) (hsh.trans (shapeDeg_colLen n Y).symm) I hI`. Conclude with `⟨J, (he.trans hJ).symm⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨J, rfl⟩`.

Rewrite using `[← shapeDeg_colLen]`. Conclude with `bidetMem R n n _ _ _ _`.
-/
theorem dualWeyl_eq_span_colProd (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (Y : YoungDiagram)
    (hY : Y.colLen 0 ≤ n) :
    dualWeyl R n n (fun r : Fin n => Y.rowLen r) = Submodule.span R (Set.range (colProd R n Y hY)) := by
  apply le_antisymm
  · obtain ⟨b, ⟨-, hb, -⟩, hb'⟩ := sSBasis R n n (fun r : Fin n => Y.rowLen r)
    rw [← hb]
    refine Submodule.span_mono ?_
    rintro _ ⟨m, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hsh, hI, he⟩ := hb' m
    obtain ⟨J, hJ⟩ := bidet_reorder R n sz hsz _ (colLen_le hY) (hsh.trans (shapeDeg_colLen n Y).symm) I hI
    exact ⟨J, (he.trans hJ).symm⟩
  · rw [Submodule.span_le]
    rintro _ ⟨J, rfl⟩
    rw [← shapeDeg_colLen]
    exact bidetMem R n n _ _ _ _

open scoped Pointwise in
/- English proof (translation)
Unfold `tensorLat`. Use `le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `P ⟨F, hF, rfl⟩`. Establish `h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (((blockEmb K s).toLinearMap.restrictScalars R) '' Set.range (f s))` using `fun s => by`. Rewrite using `[← Submodule.map_span]`.

Conclude with `⟨F s, hF s, rfl⟩`. Establish `h2 : ∀ T : Finset S, ∏ s ∈ T, blockEmb K s (F s) ∈ ∏ s ∈ T, Submodule.span R (((blockEmb K s).toLinearMap.restrictScalars R) '' Set.range (f s))`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty]`.

Conclude with `Submodule.one_le.mp le_rfl`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `Submodule.mul_mem_mul (h1 a) ih`. Establish `h3` using `h2 Finset.univ`.

Rewrite `h3` using `[Submodule.prod_span]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations. Introduce `P hP`. Take `⟨g, hg, rfl⟩` from `(Set.mem_fintype_prod _ _).mp hP`. Use `choose G hG hGg using hg`.

Use `choose i hi using hG`. Conclude with `⟨i, Finset.prod_congr rfl fun s _ => by rw [← hGg s, ← hi s]; rfl⟩`. Introduce and unpack `P ⟨i, rfl⟩`. Conclude with `⟨_, fun s => Submodule.subset_span ⟨i s, rfl⟩, rfl⟩`.
-/
theorem tensorLat_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] {n : ℕ}
    {κ : S → Type} (f : ∀ s, κ s → MvPolynomial (Fin n × Fin n) K) :
    tensorLat R K (fun s => Submodule.span R (Set.range (f s))) =
      Submodule.span R (Set.range fun i : ∀ s, κ s => ten fun s => f s (i s)) := by
  classical
  unfold tensorLat
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
  · rintro P ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R
        (((blockEmb K s).toLinearMap.restrictScalars R) '' Set.range (f s)) := fun s => by
      rw [← Submodule.map_span]
      exact ⟨F s, hF s, rfl⟩
    have h2 : ∀ T : Finset S, ∏ s ∈ T, blockEmb K s (F s) ∈ ∏ s ∈ T, Submodule.span R
        (((blockEmb K s).toLinearMap.restrictScalars R) '' Set.range (f s)) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp only [Finset.prod_empty]; exact Submodule.one_le.mp le_rfl
      | insert a T ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose G hG hGg using hg
    choose i hi using hG
    exact ⟨i, Finset.prod_congr rfl fun s _ => by rw [← hGg s, ← hi s]; rfl⟩
  · rintro P ⟨i, rfl⟩
    exact ⟨_, fun s => Submodule.subset_span ⟨i s, rfl⟩, rfl⟩

/- English proof (translation)
Unfold `tensorLat`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨F, hF, rfl⟩ choose G hG hGF using hF`. Use `⟨_, ⟨G, hG, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [← hGF, LinearMap.mulRight_apply, map_mul, Finset.prod_mul_distrib, ten]`. Introduce and unpack `⟨_, ⟨G, hG, rfl⟩, rfl⟩`. Use `⟨fun s => G s * E s, fun s => ⟨G s, hG s, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.mulRight_apply, map_mul, Finset.prod_mul_distrib, ten]`.
-/
theorem tensorLat_map_mul {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] {n : ℕ}
    (M : S → Submodule R (MvPolynomial (Fin n × Fin n) K)) (E : S → MvPolynomial (Fin n × Fin n) K) :
    tensorLat R K (fun s => (M s).map (LinearMap.mulRight R (E s))) =
      (tensorLat R K M).map (LinearMap.mulRight R (ten E)) := by
  unfold tensorLat
  rw [Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨F, hF, rfl⟩
    choose G hG hGF using hF
    refine ⟨_, ⟨G, hG, rfl⟩, ?_⟩
    simp only [← hGF, LinearMap.mulRight_apply, map_mul, Finset.prod_mul_distrib, ten]
  · rintro ⟨_, ⟨G, hG, rfl⟩, rfl⟩
    refine ⟨fun s => G s * E s, fun s => ⟨G s, hG s, rfl⟩, ?_⟩
    simp only [LinearMap.mulRight_apply, map_mul, Finset.prod_mul_distrib, ten]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsx⟩ j`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.StdDual.dual_span_iff (R := R) (c := RingHom.id K) (fun a ha => ha) B.flip E D (fun i j => by rw [LinearMap.flip_apply, h]; simp only [eq_comm]) (s • x) (Submodule.smul_of_tower_mem _ s hx)).mpr hsx (G j) (hG ▸ Submodule.subset_span ⟨j, rfl⟩)`. Rewrite `h1` using `[LinearMap.flip_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply]`.

Conclude with `Submodule.mem_one.mpr h1`. Introduce `H`. Establish `H' : Submodule.span R (Set.range E) ≤ (Formalism.HermitianLatticesTheory.localization₂ p (1 : Submodule R K)).comap ((B x).restrictScalars R)`. Rewrite using `[← hG, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `H j`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hx`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨s, hs, hsa⟩` from `H' (Submodule.subset_span ⟨i, rfl⟩)`. Establish `e : B (∑ j, a j • D j) (E i) = a i`.

Simplify using `[map_sum, h]`. Rewrite `hsa` using `[LinearMap.restrictScalars_apply, e]`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp hsa`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_assoc, ← hr, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_localization_span_iff {R K V κ κ' : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] [Fintype κ] [DecidableEq κ] (p : Ideal R) [p.IsPrime]
    (B : V →ₗ[K] V →ₗ[K] K) (D E : κ → V) (h : ∀ i j, B (D i) (E j) = if i = j then 1 else 0)
    (G : κ' → V) (hG : Submodule.span R (Set.range G) = Submodule.span R (Set.range E))
    (x : V) (hx : x ∈ Submodule.span K (Set.range D)) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p (Submodule.span R (Set.range D)) ↔
      ∀ j, B x (G j) ∈ Formalism.HermitianLatticesTheory.localization₂ p (1 : Submodule R K) := by
  constructor
  · rintro ⟨s, hs, hsx⟩ j
    refine ⟨s, hs, ?_⟩
    have h1 := (GlobalTheory.StdDual.dual_span_iff (R := R) (c := RingHom.id K) (fun a ha => ha) B.flip E D
      (fun i j => by rw [LinearMap.flip_apply, h]; simp only [eq_comm]) (s • x)
      (Submodule.smul_of_tower_mem _ s hx)).mpr hsx (G j) (hG ▸ Submodule.subset_span ⟨j, rfl⟩)
    rw [LinearMap.flip_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply] at h1
    exact Submodule.mem_one.mpr h1
  · intro H
    have H' : Submodule.span R (Set.range E) ≤
        (Formalism.HermitianLatticesTheory.localization₂ p (1 : Submodule R K)).comap ((B x).restrictScalars R) := by
      rw [← hG, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact H j
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsa⟩ := H' (Submodule.subset_span ⟨i, rfl⟩)
    have e : B (∑ j, a j • D j) (E i) = a i := by
      simp [map_sum, h]
    rw [LinearMap.restrictScalars_apply, e] at hsa
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsa
    refine ⟨s, hs, ?_⟩
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Unfold `DomWeight.natW`. Use `Int.toNat_of_nonneg (sub_nonneg.mpr ?_)` and prove the remaining obligations. Establish `hn : 0 < n` using `Fin.pos r`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hn]`.

Conclude with `l.anti (Fin.le_def.mpr (by have := r.2; simp only; omega))`.
-/
theorem natW_cast {n : ℕ} (l : DomWeight n) (r : Fin n) : (l.natW r : ℤ) = l.w r - l.detShift := by
  unfold DomWeight.natW
  refine Int.toNat_of_nonneg (sub_nonneg.mpr ?_)
  have hn : 0 < n := Fin.pos r
  unfold DomWeight.detShift
  rw [dif_pos hn]
  exact l.anti (Fin.le_def.mpr (by have := r.2; simp only; omega))

/- English proof (translation)
Unfold `gdet`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use `ext1 a s`. Simplify using the standard rewrite rules.
-/
theorem map_gdet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : map φ (gdet R n) = gdet S n := by
  unfold gdet
  rw [RingHom.map_det]
  congr 1
  ext1 a s
  simp

/- English proof (translation)
Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Use `congr 1`. Unfold `gdet frDet`. Rewrite using `[AlgHom.map_det]`.

Use `congr 1`. Use `ext1 a s`. Simplify using `[blockEmb]`.
-/
theorem ten_gdet {K ι : Type} [Field K] [Fintype ι] (n : ℕ) (e : ι → ℕ) :
    (ten fun τ => gdet K n ^ e τ) = ∏ τ, frDet K n τ ^ e τ := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow]
  congr 1
  unfold gdet frDet
  rw [AlgHom.map_det]
  congr 1
  ext1 a s
  simp [blockEmb]

/- English proof (translation)
Introduce `h`. Use `congrArg (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.1 v.2) h` as an intermediate fact. Unfold `gdet at this`. Rewrite `this` using `[RingHom.map_det, map_zero]`. Establish `e : (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.1 v.2).mapMatrix (Matrix.of fun a s : Fin n => (X (a, s) : MvPolynomial (Fin n × Fin n) K)) = 1`.

Use extensionality with `a s`. Simplify using the standard rewrite rules. Rewrite `this` using `[e, Matrix.det_one]`. Conclude with `one_ne_zero this`.
-/
theorem gdet_ne_zero (K : Type) [Field K] (n : ℕ) : gdet K n ≠ 0 := by
  intro h
  have := congrArg (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.1 v.2) h
  unfold gdet at this
  rw [RingHom.map_det, map_zero] at this
  have e : (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.1 v.2).mapMatrix
      (Matrix.of fun a s : Fin n => (X (a, s) : MvPolynomial (Fin n × Fin n) K)) = 1 := by
    ext a s
    simp
  rw [e, Matrix.det_one] at this
  exact one_ne_zero this

/- English proof (translation)
Unfold `KM.nablaX ten colProd bideterminant`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations.

Unfold `initMinor`. Rewrite using `[AlgHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]`. Use `congr 1`. Use `ext1 p q`. Establish `hq : (q : ℕ) < n` using `lt_of_lt_of_le q.2 (colLen_le (hν s) c)`.

Simplify using `only [Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X, dif_pos hq, blockEmb, rename_X]`. Both sides reduce to the same expression.
-/
theorem aeval_nablaX {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (n : ℕ) (ν : ι → YoungDiagram)
    (hν : ∀ s, (ν s).colLen 0 ≤ n) (J : KM.ColChoice n ν) :
    MvPolynomial.aeval (R := ℤ) (fun v : ι × ℕ × Fin n =>
        if h : v.2.1 < n then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin n)) : Pol K ι n) else 0) (KM.nablaX n ν J) =
      ten fun s => colProd K n (ν s) (hν s) (J s) := by
  unfold KM.nablaX ten colProd bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor
  rw [AlgHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  have hq : (q : ℕ) < n := lt_of_lt_of_le q.2 (colLen_le (hν s) c)
  simp only [Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X,
    dif_pos hq, blockEmb, rename_X]
  rfl

/- English proof (translation)
The claim follows from `@fockSymTensor_holds K _ starRingOfComm ι _ n _ _`.
-/
theorem fockB_ten {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockB (ten f) (ten g) = ∏ τ, fockB (f τ) (g τ) :=
  @fockSymTensor_holds K _ starRingOfComm ι _ n _ _

/- English proof (translation)
The claim follows from `(@fockSQ K _ starRingOfComm _ σ f g).trans (eq_ratCast _ _)`.
-/
theorem fockB_map {K σ : Type} [Field K] [CharZero K] (f g : MvPolynomial σ ℚ) :
    fockB (map (algebraMap ℚ K) f) (map (algebraMap ℚ K) g) = (fockQ f g : K) :=
  (@fockSQ K _ starRingOfComm _ σ f g).trans (eq_ratCast _ _)

/- English proof (translation)
Introduce `K _ _ ι _ _ n ν lam e hrow hν`. Use `set μ : ι → Fin n → ℕ := fun s r => (ν s).rowLen r with hμ`. Establish `hμe : ∀ s, μ s = fun r => (lam s).natW r + e s`. Introduce `s`. Use function extensionality and compare the values at `r`.

Establish `h1` using `hrow s r`. Establish `h2` using `natW_cast (lam s) r`. Simplify using `only [hμ]`. Use linear arithmetic over natural numbers and integers. Establish `hanti : ∀ s, Antitone (μ s)` using `fun s a b hab => (ν s).rowLen_anti _ _ hab`.

Use `haveI : ∀ τ, Fintype (ssIdx n n (μ τ)) := fun τ => (sSIdxFinite n n _).fintype`. Use `choose b d hb hd hbd using fun τ => GlobalTheory.StdDual.exists_dual_bases n (μ τ) (hanti τ)`. Use `set N : ι → ℚ := fun s => fockQ (hw ℚ (le_refl n) (μ s)) (hw ℚ (le_refl n) (μ s)) with hN`. Establish `hNpos : ∀ s, 0 < N s` using `fun s => (fockQPos _ _ (hw ℚ (le_refl n) (μ s))).2 (hwNe ℚ n n le_rfl _)`. Establish `hc : 0 < ∏ s, N s` using `Finset.prod_pos fun s _ => hNpos s`.

Establish `hcK : ((∏ s, N s : ℚ) : K) ≠ 0` using `by exact_mod_cast hc.ne'`. Use `⟨∏ s, N s, hc, ?_, ?_⟩` and prove the remaining obligations. Introduce `w P hP set φ := algebraMap ℚ K with hφ set E : Pol K ι n := ∏ τ, frDet K n τ ^ e τ with hE`. Establish `hEt : (ten fun τ => gdet K n ^ e τ) = E` using `ten_gdet n e`. Establish `hE0 : E ≠ 0`.

Rewrite using `[← hEt]`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (rename_injective _ (Prod.mk_right_injective τ))).mpr (pow_ne_zero _ (gdet_ne_zero K n))`. Establish `hB : Submodule.span (𝓞 K) (Set.range fun J : KM.ColChoice n ν => ten fun s => colProd K n (ν s) (hν s) (J s)) = Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (b τ (i τ)))`. Use `(tensorLat_span (fun s => colProd K n (ν s) (hν s))).symm.trans (Eq.trans ?_ (tensorLat_span (fun τ i => map φ (b τ i))))` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Establish `h1` using `GlobalTheory.StdDual.dualWeyl_toK K n (μ τ)`. Rewrite `h1` using `[← GlobalTheory.StdDual.span_image_eq _ _ (hb τ), ← Set.range_comp, dualWeyl_eq_span_colProd _ _ _ (hν τ), Submodule.map_span, ← Set.range_comp]`. Use `Eq.trans ?_ h1` and prove the remaining obligations.

Use `congr 2`. Use function extensionality and compare the values at `J`. Conclude with `(fk_map_bidet (algebraMap (𝓞 K) K) _ _ _).symm`. Establish `hD : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (d τ (i τ))) = (delStd K lam).map (LinearMap.mulRight (𝓞 K) E)`. Rewrite using `[← tensorLat_span (fun τ i => map φ (d τ i)), ← hEt, delStd, ← tensorLat_map_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Establish `h1` using `GlobalTheory.StdDual.weyl_toK K n (μ τ)`. Rewrite `h1` using `[← GlobalTheory.StdDual.span_image_eq _ _ (hd τ), ← Set.range_comp]`. Use `Eq.trans h1.symm ?_` and prove the remaining obligations.

Rewrite using `[hμe, weyl_add, delSq, ← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, GlobalTheory.StdLatSpan.toK_apply, map_mul, map_pow, map_gdet]`. Establish `hx : P * E ∈ Submodule.span K (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (d τ (i τ)))`.

Rewrite using `[← Submodule.span_span_of_tower (𝓞 K), hD]`. Rewrite `hP` using `[← (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.2]`. Establish `h1` using `Submodule.mem_map_of_mem (f := LinearMap.mulRight K E) hP`. Rewrite `h1` using `[Submodule.map_span]`. Conclude with `h1`.

Establish `key` using `mem_localization_span_iff w.asIdeal ((((∏ s, N s : ℚ) : K))⁻¹ • fockBL) _ _ (by`. Introduce `i j`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, fockBL_apply, fockB_ten, smul_eq_mul]`. Simplify using `only [hφ, fockB_map]`. Establish `hs : ∀ τ, fockQ (d τ (i τ)) (b τ (j τ)) = if j τ = i τ then N τ else 0` using `fun τ => (fockQPos _ _ _).1.trans (hbd τ _ _)`.

Simplify using `only [hs]`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Simplify using `only [if_true]`. Rewrite using `[← Rat.cast_prod]`.

Conclude with `inv_mul_cancel₀ hcK`. Take `⟨τ, hτ⟩` from `Function.ne_iff.mp hij`. Conclude with `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg (Ne.symm hτ), Rat.cast_zero])))`. Use `_ hB _ hx`. Simplify using `only [aeval_nablaX n ν hν]`.

Use `Iff.trans ?_ key` and prove the remaining obligations. Rewrite using `[hD]`. Use `exists_congr fun s => and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_mul_assoc]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨_, h, rfl⟩`. Introduce and unpack `⟨y, hy, hye⟩`. Rewrite using `[← mul_right_cancel₀ hE0 hye]` and apply the resulting hypothesis. Introduce `J hJ`.

Rewrite using `[aeval_nablaX n ν hν, fockB_ten, Rat.cast_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `: colProd K n (ν s) (hν s) (J s) = map (algebraMap ℚ K) (hw ℚ (le_refl n) (μ s))`. Rewrite using `[lclosedeq_hw_map, colProd, bidet_lead K n _ _ _ (hJ s), shapeDeg_colLen]`. Rewrite using `[this, fockB_map]`.
-/
theorem weyl_dual_minors : ∀ {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (ν : ι → YoungDiagram) (lam : ι → DomWeight n) (e : ι → ℕ), (∀ s (r : Fin n), ((ν s).rowLen r : ℤ) = (lam s).w r - (lam s).detShift + e s) → (∀ s, (ν s).colLen 0 ≤ n) → ∃ c : ℚ, 0 < c ∧ (∀ w : HeightOneSpectrum (𝓞 K), ∀ P ∈ Formalism.L2.DIV.VV K lam, P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) ↔ ∀ J : KM.ColChoice n ν, ((c : K)⁻¹ * fockB (P * ∏ τ, frDet K n τ ^ e τ) (MvPolynomial.aeval (R := ℤ) (fun v : ι × ℕ × Fin n => if h : v.2.1 < n then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin n)) : Pol K ι n) else 0) (KM.nablaX n ν J))) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ∧ ∀ J : KM.ColChoice n ν, (∀ s (k : Fin ((ν s).rowLen 0)) (i : Fin ((ν s).colLen k)), (J s k i : ℕ) = i) → (c : K) = fockB (MvPolynomial.aeval (R := ℤ) (fun v : ι × ℕ × Fin n => if h : v.2.1 < n then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin n)) : Pol K ι n) else 0) (KM.nablaX n ν J)) (MvPolynomial.aeval (R := ℤ) (fun v : ι × ℕ × Fin n => if h : v.2.1 < n then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin n)) : Pol K ι n) else 0) (KM.nablaX n ν J)) := by
  classical
  intro K _ _ ι _ _ n ν lam e hrow hν
  set μ : ι → Fin n → ℕ := fun s r => (ν s).rowLen r with hμ
  have hμe : ∀ s, μ s = fun r => (lam s).natW r + e s := by
    intro s
    funext r
    have h1 := hrow s r
    have h2 := natW_cast (lam s) r
    simp only [hμ]
    omega
  have hanti : ∀ s, Antitone (μ s) := fun s a b hab => (ν s).rowLen_anti _ _ hab
  haveI : ∀ τ, Fintype (ssIdx n n (μ τ)) := fun τ => (sSIdxFinite n n _).fintype
  choose b d hb hd hbd using fun τ => GlobalTheory.StdDual.exists_dual_bases n (μ τ) (hanti τ)
  set N : ι → ℚ := fun s => fockQ (hw ℚ (le_refl n) (μ s)) (hw ℚ (le_refl n) (μ s)) with hN
  have hNpos : ∀ s, 0 < N s := fun s => (fockQPos _ _ (hw ℚ (le_refl n) (μ s))).2 (hwNe ℚ n n le_rfl _)
  have hc : 0 < ∏ s, N s := Finset.prod_pos fun s _ => hNpos s
  have hcK : ((∏ s, N s : ℚ) : K) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨∏ s, N s, hc, ?_, ?_⟩
  · intro w P hP
    set φ := algebraMap ℚ K with hφ
    set E : Pol K ι n := ∏ τ, frDet K n τ ^ e τ with hE
    have hEt : (ten fun τ => gdet K n ^ e τ) = E := ten_gdet n e
    have hE0 : E ≠ 0 := by
      rw [← hEt]
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
      exact (map_ne_zero_iff _ (rename_injective _ (Prod.mk_right_injective τ))).mpr
        (pow_ne_zero _ (gdet_ne_zero K n))
    have hB : Submodule.span (𝓞 K) (Set.range fun J : KM.ColChoice n ν =>
          ten fun s => colProd K n (ν s) (hν s) (J s)) =
        Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (b τ (i τ))) := by
      refine (tensorLat_span (fun s => colProd K n (ν s) (hν s))).symm.trans
        (Eq.trans ?_ (tensorLat_span (fun τ i => map φ (b τ i))))
      congr 1
      funext τ
      have h1 := GlobalTheory.StdDual.dualWeyl_toK K n (μ τ)
      rw [← GlobalTheory.StdDual.span_image_eq _ _ (hb τ), ← Set.range_comp, dualWeyl_eq_span_colProd _ _ _ (hν τ),
        Submodule.map_span, ← Set.range_comp] at h1
      refine Eq.trans ?_ h1
      congr 2
      funext J
      exact (fk_map_bidet (algebraMap (𝓞 K) K) _ _ _).symm
    have hD : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (d τ (i τ))) =
        (delStd K lam).map (LinearMap.mulRight (𝓞 K) E) := by
      rw [← tensorLat_span (fun τ i => map φ (d τ i)), ← hEt, delStd, ← tensorLat_map_mul]
      congr 1
      funext τ
      have h1 := GlobalTheory.StdDual.weyl_toK K n (μ τ)
      rw [← GlobalTheory.StdDual.span_image_eq _ _ (hd τ), ← Set.range_comp] at h1
      refine Eq.trans h1.symm ?_
      rw [hμe, weyl_add, delSq, ← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, GlobalTheory.StdLatSpan.toK_apply, map_mul, map_pow,
        map_gdet]
    have hx : P * E ∈ Submodule.span K
        (Set.range fun i : (∀ τ, ssIdx n n (μ τ)) => ten fun τ => map φ (d τ (i τ))) := by
      rw [← Submodule.span_span_of_tower (𝓞 K), hD]
      rw [← (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.2] at hP
      have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight K E) hP
      rw [Submodule.map_span] at h1
      exact h1
    have key := mem_localization_span_iff w.asIdeal ((((∏ s, N s : ℚ) : K))⁻¹ • fockBL) _ _ (by
      intro i j
      rw [LinearMap.smul_apply, LinearMap.smul_apply, fockBL_apply, fockB_ten, smul_eq_mul]
      simp only [hφ, fockB_map]
      have hs : ∀ τ, fockQ (d τ (i τ)) (b τ (j τ)) = if j τ = i τ then N τ else 0 := fun τ =>
        (fockQPos _ _ _).1.trans (hbd τ _ _)
      simp only [hs]
      split_ifs with hij
      · subst hij
        simp only [if_true]
        rw [← Rat.cast_prod]
        exact inv_mul_cancel₀ hcK
      · obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hij
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ τ)
          (by rw [if_neg (Ne.symm hτ), Rat.cast_zero])))
      _ hB _ hx
    simp only [aeval_nablaX n ν hν]
    refine Iff.trans ?_ key
    rw [hD]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [← smul_mul_assoc]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hye⟩
      rwa [← mul_right_cancel₀ hE0 hye]
  · intro J hJ
    rw [aeval_nablaX n ν hν, fockB_ten, Rat.cast_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have : colProd K n (ν s) (hν s) (J s) = map (algebraMap ℚ K) (hw ℚ (le_refl n) (μ s)) := by
      rw [lclosedeq_hw_map, colProd, bidet_lead K n _ _ _ (hJ s), shapeDeg_colLen]
    rw [this, fockB_map]

end GlobalTheory.WeylMinorDual
