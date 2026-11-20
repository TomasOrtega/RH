import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
Establish `hfil : (Finset.univ.filter (fun i : Fin n => i.val < l + 1)) = insert (⟨l, hl⟩ : Fin n) (Finset.univ.filter (fun i : Fin n => i.val < l))`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hfil, Finset.sum_insert (by simp)]`.
-/
theorem lc_c_filter_succ {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) (l : ℕ) (hl : l < n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l + 1), f i =
      f ⟨l, hl⟩ + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), f i := by
  have hfil : (Finset.univ.filter (fun i : Fin n => i.val < l + 1)) =
      insert (⟨l, hl⟩ : Fin n) (Finset.univ.filter (fun i : Fin n => i.val < l)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hfil, Finset.sum_insert (by simp)]

/- English proof (translation)
Establish `: (Finset.univ.filter (fun i : Fin n => i.val < 0)) = ∅`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this, Finset.sum_empty]`.
-/
theorem lc_c_filter_zero {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 0), f i = 0 := by
  have : (Finset.univ.filter (fun i : Fin n => i.val < 0)) = ∅ := by
    ext i; simp
  rw [this, Finset.sum_empty]

/- English proof (translation)
Establish `h2` using `casimir_content_holds q (fun b => (κ b : ℤ)) r`. Unfold `casVal`. Simplify using `only [Pi.add_apply, Pi.single_apply, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]`. Conclude with `h2`.
-/
theorem lc_c_casVal_step {q : ℕ} (κ : Fin q → ℕ) (r : Fin q) :
    casVal (κ + Pi.single r 1) - casVal κ - (q : ℤ) = 2 * ((κ r : ℤ) - (r.val : ℤ)) := by
  have h2 := casimir_content_holds q (fun b => (κ b : ℤ)) r
  unfold casVal
  simp only [Pi.add_apply, Pi.single_apply, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact h2

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero => intro _`. Rewrite using `[lc_c_filter_zero, add_zero, h0]`. Consider the case `succ l ih`.

Introduce `hl`. Establish `hl' : l < n` using `hl`. Rewrite using `[lc_c_filter_succ _ l hl']`. Establish `h1` using `lc_c_casVal_step (κ l) (ρ ⟨l, hl'⟩)`. Establish `h2` using `hs ⟨l, hl'⟩`.

Simplify using `only at h2`. Rewrite `h1` using `[← h2]`. Establish `h3` using `ih hl'.le`. Simplify using `only [cseq] at h3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lc_c_casVal_path {q n : ℕ} (lam2 : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (h0 : κ 0 = lam2)
    (hs : ∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) : ∀ l ≤ n,
    casVal (κ l) = casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * cseq κ ρ i + (q : ℤ)) := by
  intro l
  induction l with
  | zero => intro _; rw [lc_c_filter_zero, add_zero, h0]
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    rw [lc_c_filter_succ _ l hl']
    have h1 := lc_c_casVal_step (κ l) (ρ ⟨l, hl'⟩)
    have h2 := hs ⟨l, hl'⟩
    simp only at h2
    rw [← h2] at h1
    have h3 := ih hl'.le
    simp only [cseq] at h3 ⊢
    linarith

/- English proof (translation)
Use `LinearMap.congr_fun h.eq z` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[← this, hz, map_smul]`.
-/
theorem lc_c_eig {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {A T : Module.End K V} (h : Commute T A)
    {z : V} {a : K} (hz : A z = a • z) : A (T z) = a • T z := by
  have := LinearMap.congr_fun h.eq z
  simp only [Module.End.mul_apply] at this
  rw [← this, hz, map_smul]

/- English proof (translation)
Simplify using `[Dpart]`.
-/
theorem lc_c_Dpart0 {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    {n : ℕ} (EM : R → R → Module.End k M) (b b' : R) :
    (Dpart k EM 0 b b' : Module.End k (Tens R P M n)) = onM k (EM b b') := by
  simp [Dpart]

/- English proof (translation)
Unfold `Cas`. Simplify using `only [lc_c_Dpart0]`. Conclude with `Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => (h0 _ _).mul_right (h0 _ _)`.
-/
theorem commute_casimir_zero {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    [Fintype R] {n : ℕ} (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h0 : ∀ a b, Commute T (onM k (EM a b))) : Commute T (Cas k EM 0) := by
  unfold Cas
  simp only [lc_c_Dpart0]
  exact Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => (h0 _ _).mul_right (h0 _ _)

/- English proof (translation)
Introduce `K P M q _ _ _ _ EM n lam2 c z hz l`. Proceed by induction on `l with`. Consider the case `zero`. Introduce `_`. Rewrite using `[lc_c_filter_zero, add_zero]`.

Conclude with `hz.1`. Consider the case `succ l ih`. Introduce `hl`. Establish `hl' : l < n` using `hl`. Establish `h1` using `congrArg (fun T : Module.End K (Tens (Fin q) P M n) => T z) (casimir_jucys_murphy_holds K (Fin q) P M EM n ⟨l, hl'⟩)`.

Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Fintype.card_fin] at h1`. Rewrite using `[lc_c_filter_succ _ l hl']`. Rewrite `h1` using `[ih hl'.le, hz.2 ⟨l, hl'⟩, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]`. Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1, smul_smul, ← add_smul, ← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem casimir_from_x : CasFromX := by
  intro K P M q _ _ _ _ EM n lam2 c z hz l
  induction l with
  | zero =>
    intro _
    rw [lc_c_filter_zero, add_zero]
    exact hz.1
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    have h1 := congrArg (fun T : Module.End K (Tens (Fin q) P M n) => T z)
      (casimir_jucys_murphy_holds K (Fin q) P M EM n ⟨l, hl'⟩)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Fintype.card_fin] at h1
    rw [lc_c_filter_succ _ l hl']
    rw [ih hl'.le, hz.2 ⟨l, hl'⟩, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, smul_smul, ← add_smul, ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ EM n lam2 κ ρ h0 hs z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations. Use `hz 0 (Nat.zero_le _)` as an intermediate fact.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Conclude with `(path_eigen_holds K P M q EM n κ ρ hs z hz).1 j`. Introduce `hz j hj`. Rewrite using `[casimir_from_x K P M q EM n lam2 _ z hz j hj, lc_c_casVal_path lam2 κ ρ h0 hs j hj]`.
-/
theorem weight_iff_condition : WtIff := by
  intro K P M q _ _ _ _ _ EM n lam2 κ ρ h0 hs z
  constructor
  · intro hz
    refine ⟨?_, fun j => ?_⟩
    · have := hz 0 (Nat.zero_le _)
      rwa [h0] at this
    · exact (path_eigen_holds K P M q EM n κ ρ hs z hz).1 j
  · intro hz j hj
    rw [casimir_from_x K P M q EM n lam2 _ z hz j hj, lc_c_casVal_path lam2 κ ρ h0 hs j hj]

/- English proof (translation)
Introduce `K P M q _ _ _ _ EM n lam2 c z σ hz`. Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `lc_c_eig (commute_casimir_zero EM _ fun a b => permFirst_commute_onModule K σ _) hz.1`. Conclude with `lc_c_eig (commute_jucysMurphy_of_commute K EM _ (fun a b => permFirst_commute_onModule K σ _) (fun i a b => permFirst_commute_unitSecond K σ i a b) j) (hz.2 j)`.
-/
theorem permutation_weight_invariant : PermXWt := by
  intro K P M q _ _ _ _ EM n lam2 c z σ hz
  refine ⟨?_, fun j => ?_⟩
  · exact lc_c_eig (commute_casimir_zero EM _ fun a b => permFirst_commute_onModule K σ _) hz.1
  · exact lc_c_eig (commute_jucysMurphy_of_commute K EM _ (fun a b => permFirst_commute_onModule K σ _)
      (fun i a b => permFirst_commute_unitSecond K σ i a b) j) (hz.2 j)

/- English proof (translation)
Introduce `K R P M _ _ _ _ _ _ _ n σ z`. Rewrite using `[← toSym_perm_eq (k := K) (permX K σ⁻¹ z) σ]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `[permTensor_apply_comp, permFirst_apply, permSecond_apply]`.
-/
theorem to_symmetric_y_x : ToSymYX := by
  intro K R P M _ _ _ _ _ _ _ n σ z
  rw [← toSym_perm_eq (k := K) (permX K σ⁻¹ z) σ]
  congr 1
  funext g
  simp [permTensor_apply_comp, permFirst_apply, permSecond_apply]

/- English proof (translation)
Rewrite using `[← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one]`.
-/
theorem lc_c_ss {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} (a b : Fin n) :
    (permY k (Equiv.swap a b) * permY k (Equiv.swap a b) : Module.End k (Tens R P M n)) = 1 := by
  rw [← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one]

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ EM n lam2 c z j hj hz hne`. Use `set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'`. Use `set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs`. Establish `hH` using `hecke_relations_hold K (Fin q) P M EM n j hj`. Establish `h1 : s * xJM K EM j = xJM K EM j' * s - 1` using `hH.1`.

Establish `hss : s * s = 1` using `lc_c_ss j j'`. Establish `h2 : xJM K EM j * s = s * xJM K EM j' - 1`. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : xJM K EM j' (s z) = ((c j : ℤ) : K) • s z + z`. Use `LinearMap.congr_fun h1 z` as an intermediate fact.

Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this`. Rewrite `this` using `[hz.2 j, map_smul]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Establish `e2 : xJM K EM j (s z) = ((c j' : ℤ) : K) • s z - z`.

Use `LinearMap.congr_fun h2 z` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this`. Rewrite `this` using `[hz.2 j', map_smul]`. Conclude with `this`. Establish `hd : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0` using `Int.cast_ne_zero.2 (sub_ne_zero.2 hne)`.

Use `set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef`. Establish `hb : b * (((c j : ℤ) : K) - ((c j' : ℤ) : K)) = 1`. Rewrite using `[← Int.cast_sub]`. Conclude with `inv_mul_cancel₀ hd`. Establish `hjj' : j ≠ j'`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[hj'] at this`. Use `⟨?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, hz.1, lc_c_eig (commute_casimir_zero EM s fun a b => permSecond_commute_onModule K _ _) hz.1] module`.

Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Rewrite using `[Function.comp_apply, Equiv.swap_apply_left, map_add, map_smul, e2, hz.2 l]`. Establish `e : b * ((c l : ℤ) : K) - 1 = ((c j' : ℤ) : K) * b` using `by linear_combination hb`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `hl' : l = j'`. Rewrite using `[hl', Function.comp_apply, Equiv.swap_apply_right, map_add, map_smul, e1, hz.2 j']`. Establish `e : 1 + b * ((c j' : ℤ) : K) = ((c j : ℤ) : K) * b` using `by linear_combination (-1 : K) * hb`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hl hl', map_add, map_smul, hz.2 l, lc_c_eig (hH.2 l hl hl') (hz.2 l)] module`.
-/
theorem exchange' : Exchange := by
  intro K P M q _ _ _ _ _ EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  have hH := hecke_relations_hold K (Fin q) P M EM n j hj
  have h1 : s * xJM K EM j = xJM K EM j' * s - 1 := hH.1
  have hss : s * s = 1 := lc_c_ss j j'
  have h2 : xJM K EM j * s = s * xJM K EM j' - 1 := by
    calc xJM K EM j * s = (s * s) * xJM K EM j * s := by rw [hss, one_mul]
      _ = s * (s * xJM K EM j) * s := by simp only [mul_assoc]
      _ = s * (xJM K EM j' * s - 1) * s := by rw [h1]
      _ = s * xJM K EM j' * (s * s) - s * s := by noncomm_ring
      _ = s * xJM K EM j' - 1 := by rw [hss, mul_one]
  have e1 : xJM K EM j' (s z) = ((c j : ℤ) : K) • s z + z := by
    have := LinearMap.congr_fun h1 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j, map_smul] at this
    rw [this]; abel
  have e2 : xJM K EM j (s z) = ((c j' : ℤ) : K) • s z - z := by
    have := LinearMap.congr_fun h2 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j', map_smul] at this
    exact this
  have hd : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  have hb : b * (((c j : ℤ) : K) - ((c j' : ℤ) : K)) = 1 := by
    rw [← Int.cast_sub]; exact inv_mul_cancel₀ hd
  have hjj' : j ≠ j' := by
    intro e; have := congrArg Fin.val e; simp [hj'] at this
  refine ⟨?_, fun l => ?_⟩
  · rw [map_add, map_smul, hz.1, lc_c_eig (commute_casimir_zero EM s fun a b => permSecond_commute_onModule K _ _) hz.1]
    module
  · by_cases hl : l = j
    · subst hl
      rw [Function.comp_apply, Equiv.swap_apply_left, map_add, map_smul, e2, hz.2 l]
      have e : b * ((c l : ℤ) : K) - 1 = ((c j' : ℤ) : K) * b := by linear_combination hb
      calc _ = ((c j' : ℤ) : K) • s z + (b * ((c l : ℤ) : K) - 1) • z := by module
        _ = _ := by rw [e]; module
    · by_cases hl' : l = j'
      · rw [hl', Function.comp_apply, Equiv.swap_apply_right, map_add, map_smul, e1, hz.2 j']
        have e : 1 + b * ((c j' : ℤ) : K) = ((c j : ℤ) : K) * b := by linear_combination (-1 : K) * hb
        calc _ = ((c j : ℤ) : K) • s z + (1 + b * ((c j' : ℤ) : K)) • z := by module
          _ = _ := by rw [e]; module
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hl hl', map_add, map_smul, hz.2 l,
          lc_c_eig (hH.2 l hl hl') (hz.2 l)]
        module

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ _ EM n lam2 c j hj hd hgood z hz`. Establish `hne : c j ≠ c ⟨j.val + 1, hj⟩` using `by intro e; rw [e] at hd; omega`. Establish `hz'` using `exchange' K P M q EM n lam2 c z j hj hz hne`. Use `set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'`. Use `set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs`.

Use `set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef`. Use `set z' := s z + b • z with hz'def`. Establish `hss : s * s = 1` using `lc_c_ss j j'`. Establish `t1 : toSym K z' = 0` using `hgood z' hz'`. Establish `t2 : toSym K (s z') = 0`.

Rewrite using `[hs, to_symmetric_y_x K (Fin q) P M n (Equiv.swap j j') z']`. Conclude with `hgood _ (permutation_weight_invariant K P M q EM n lam2 _ z' _ hz')`. Establish `hssz : s (s z) = z`. Use `LinearMap.congr_fun hss z` as an intermediate fact. Simplify using `using this`.

Establish `e : s z' - b • z' = (1 - b * b) • z`. Rewrite using `[hz'def, map_add, map_smul, hssz]`. Use `module`. Establish `t3 : (1 - b * b) • toSym K z = 0`. Rewrite using `[← map_smul, ← e, map_sub, map_smul, t1, t2]`.

Simplify using the standard rewrite rules. Establish `hD : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0` using `Int.cast_ne_zero.2 (sub_ne_zero.2 hne)`. Establish `hb : b * (((c j - c j' : ℤ) : ℤ) : K) = 1` using `inv_mul_cancel₀ hD`. Establish `hbb : 1 - b * b ≠ 0`. Introduce `h0`.

Establish `h1 : (((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K) = 1`. Take the linear combination `((((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K)) * h0 + (b * (((c j - c j' : ℤ) : ℤ) : K) + 1) * hb`. Establish `h2 : (c j - c j') * (c j - c j') = 1` using `by exact_mod_cast h1`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(smul_eq_zero.1 t3).resolve_left hbb`.
-/
theorem good_swap_exists : GoodSwap := by
  intro K P M q _ _ _ _ _ _ EM n lam2 c j hj hd hgood z hz
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by intro e; rw [e] at hd; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  set z' := s z + b • z with hz'def
  have hss : s * s = 1 := lc_c_ss j j'
  have t1 : toSym K z' = 0 := hgood z' hz'
  have t2 : toSym K (s z') = 0 := by
    rw [hs, to_symmetric_y_x K (Fin q) P M n (Equiv.swap j j') z']
    exact hgood _ (permutation_weight_invariant K P M q EM n lam2 _ z' _ hz')
  have hssz : s (s z) = z := by
    have := LinearMap.congr_fun hss z
    simpa using this
  have e : s z' - b • z' = (1 - b * b) • z := by
    rw [hz'def, map_add, map_smul, hssz]
    module
  have t3 : (1 - b * b) • toSym K z = 0 := by
    rw [← map_smul, ← e, map_sub, map_smul, t1, t2]; simp
  have hD : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  have hb : b * (((c j - c j' : ℤ) : ℤ) : K) = 1 := inv_mul_cancel₀ hD
  have hbb : 1 - b * b ≠ 0 := by
    intro h0
    have h1 : (((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K) = 1 := by
      linear_combination ((((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K)) * h0 +
        (b * (((c j - c j' : ℤ) : ℤ) : K) + 1) * hb
    have h2 : (c j - c j') * (c j - c j') = 1 := by exact_mod_cast h1
    nlinarith
  exact (smul_eq_zero.1 t3).resolve_left hbb

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ EM n lam2 hp c z hz hc`. Set `TT : Set (Fin (n + 1) → K)` to `{t | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧ ∀ j : Fin (n + 1), t j = ((casVal (κ j.val) : ℤ) : K)}`. Set `E : Set (Tens (Fin q) P M n)` to `⋃ tau : Fin q → ℕ, {z | ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧ ∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z}`. Establish `hE : Submodule.span K E = ⊤`. Rewrite using `[← hp, Submodule.span_iUnion]`.

Both sides reduce to the same expression. Set `T0 : ℕ → ℤ` to `fun l => casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ))`. Use `h K (Tens (Fin q) P M n) (Fin (n + 1)) (fun j => Cas K EM j.val) TT E ?_ z (by rw [hE]; trivial) (fun j => ((T0 j.val : ℤ) : K)) ?_ ?_` and prove the remaining obligations. Introduce `e he`. Take `⟨tau, κ, ρ, hpath, hcas⟩` from `Set.mem_iUnion.1 he`.

Conclude with `⟨fun j => ((casVal (κ j.val) : ℤ) : K), ⟨tau, κ, ρ, hpath, fun _ => rfl⟩, fun j => hcas j.val (Nat.lt_succ_iff.1 j.2)⟩`. Introduce and unpack `⟨tau, κ, ρ, hpath, ht⟩`. Apply `hc` to reduce the goal to its premises. Use `⟨tau, κ, ρ, hpath, ?_⟩` and prove the remaining obligations. Establish `hT : ∀ l ≤ n, T0 l = casVal (κ l)`.

Introduce `l hl`. Establish `: ((T0 l : ℤ) : K) = ((casVal (κ l) : ℤ) : K)` using `ht ⟨l, Nat.lt_succ_iff.2 hl⟩`. Conclude with `Int.cast_injective this`. Use function extensionality and compare the values at `i`. Establish `a1` using `hT i.val i.2.le`.

Establish `a2` using `hT (i.val + 1) i.2`. Rewrite `a1` using `[lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2.le]`. Rewrite `a2` using `[lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2]`. Simplify using `only [T0] at a1 a2`. Rewrite `a2` using `[lc_c_filter_succ _ i.val i.2, lc_c_filter_succ _ i.val i.2]`.

Simplify using `only [Fin.eta] at a2`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j`. Conclude with `casimir_from_x K P M q EM n lam2 c z hz j.val (Nat.lt_succ_iff.1 j.2)`.
-/
theorem NoWt_of (h : NoTuple) : NoWt := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z hz hc
  let TT : Set (Fin (n + 1) → K) := {t | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j : Fin (n + 1), t j = ((casVal (κ j.val) : ℤ) : K)}
  let E : Set (Tens (Fin q) P M n) := ⋃ tau : Fin q → ℕ, {z | ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z}
  have hE : Submodule.span K E = ⊤ := by
    rw [← hp, Submodule.span_iUnion]; rfl
  let T0 : ℕ → ℤ := fun l => casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ))
  refine h K (Tens (Fin q) P M n) (Fin (n + 1)) (fun j => Cas K EM j.val) TT E ?_ z (by rw [hE]; trivial)
    (fun j => ((T0 j.val : ℤ) : K)) ?_ ?_
  · intro e he
    obtain ⟨tau, κ, ρ, hpath, hcas⟩ := Set.mem_iUnion.1 he
    exact ⟨fun j => ((casVal (κ j.val) : ℤ) : K), ⟨tau, κ, ρ, hpath, fun _ => rfl⟩,
      fun j => hcas j.val (Nat.lt_succ_iff.1 j.2)⟩
  · rintro ⟨tau, κ, ρ, hpath, ht⟩
    apply hc
    refine ⟨tau, κ, ρ, hpath, ?_⟩
    have hT : ∀ l ≤ n, T0 l = casVal (κ l) := by
      intro l hl
      have : ((T0 l : ℤ) : K) = ((casVal (κ l) : ℤ) : K) := ht ⟨l, Nat.lt_succ_iff.2 hl⟩
      exact Int.cast_injective this
    funext i
    have a1 := hT i.val i.2.le
    have a2 := hT (i.val + 1) i.2
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2.le] at a1
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2] at a2
    simp only [T0] at a1 a2
    rw [lc_c_filter_succ _ i.val i.2, lc_c_filter_succ _ i.val i.2] at a2
    simp only [Fin.eta] at a2
    linarith
  · intro j
    exact casimir_from_x K P M q EM n lam2 c z hz j.val (Nat.lt_succ_iff.1 j.2)

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ EM n lam2 hp c z j hj hz hc hn`. Establish `hne : c j ≠ c ⟨j.val + 1, hj⟩` using `by rw [hc]; omega`. Establish `hz'` using `exchange' K P M q EM n lam2 c z j hj hz hne`. Establish `h0` using `NoWt_of h K P M q EM n lam2 hp _ _ hz' hn`. Establish `h1 : c j - c ⟨j.val + 1, hj⟩ = 1` using `by rw [hc]; ring`.

Rewrite `h0` using `[h1]`. Simplify using `only [Int.cast_one, inv_one, one_smul] at h0`. Conclude with `eq_neg_of_add_eq_zero_left h0`.
-/
theorem AntiStep_of (h : NoTuple) : AntiStep := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z j hj hz hc hn
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by rw [hc]; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  have h0 := NoWt_of h K P M q EM n lam2 hp _ _ hz' hn
  have h1 : c j - c ⟨j.val + 1, hj⟩ = 1 := by rw [hc]; ring
  rw [h1] at h0
  simp only [Int.cast_one, inv_one, one_smul] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Formalism.CohomologicalDescent.LC
