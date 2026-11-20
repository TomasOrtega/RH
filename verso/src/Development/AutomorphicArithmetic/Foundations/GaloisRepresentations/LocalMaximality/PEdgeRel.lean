import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {ι E : Type} [LinearOrder ι] [AddCommGroup E]

private def tS (S : Finset ι) (k : ι) : ℤ := ∏ x ∈ S, if x < k then -1 else 1

private def uS (S : Finset ι) (k : ι) : ℤ := ∏ x ∈ S, if k < x then -1 else 1

private def shS (I J : Finset ι) : ℤ := ∏ i ∈ I, tS J i

/- English proof (translation)
Unfold `GlobalTheory.cubeSign tS`. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]`.
-/
private theorem cs_eq (S : Finset ι) (k : ι) : GlobalTheory.cubeSign S k = tS S k := by
  unfold GlobalTheory.cubeSign tS
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/- English proof (translation)
Unfold `tS`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `x _`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem tS_sq (S : Finset ι) (k : ι) : tS S k * tS S k = 1 := by
  unfold tS
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro x _
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `tS`. Rewrite using `[Finset.prod_union h]`.
-/
private theorem tS_union {S T : Finset ι} (h : Disjoint S T) (k : ι) :
    tS (S ∪ T) k = tS S k * tS T k := by
  unfold tS
  rw [Finset.prod_union h]

/- English proof (translation)
Simplify using `only [tS]`. Conclude with `Finset.prod_erase _ (by simp)`.
-/
private theorem tS_erase (S : Finset ι) (k : ι) : tS (S.erase k) k = tS S k := by
  simp only [tS]
  exact Finset.prod_erase _ (by simp)

/- English proof (translation)
Unfold `tS uS`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `trans ∏ _x ∈ S, (-1 : ℤ)`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `x hx`.

Establish `hne : x ≠ k` using `fun e => h (e ▸ hx)`. Break down `lt_or_gt_of_ne hne with hl | hl` into its components or cases. Simplify using `[hl, not_lt.2 hl.le]`. Simplify using `[hl, not_lt.2 hl.le]`. Simplify using the standard rewrite rules.
-/
private theorem tS_mul_uS {S : Finset ι} {k : ι} (h : k ∉ S) : tS S k * uS S k = (-1) ^ S.card := by
  unfold tS uS
  rw [← Finset.prod_mul_distrib]
  trans ∏ _x ∈ S, (-1 : ℤ)
  · apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ k := fun e => h (e ▸ hx)
    rcases lt_or_gt_of_ne hne with hl | hl
    · simp [hl, not_lt.2 hl.le]
    · simp [hl, not_lt.2 hl.le]
  · simp

/- English proof (translation)
Unfold `shS`. Conclude with `(Finset.mul_prod_erase I (fun i => tS J i) h).symm`.
-/
private theorem sg_left {I : Finset ι} (J : Finset ι) {k : ι} (h : k ∈ I) :
    shS I J = tS J k * shS (I.erase k) J := by
  unfold shS
  exact (Finset.mul_prod_erase I (fun i => tS J i) h).symm

/- English proof (translation)
Unfold `shS tS uS`. Conclude with `Finset.prod_comm`.
-/
private theorem sg_eq_u (I J : Finset ι) : shS I J = ∏ j ∈ J, uS I j := by
  unfold shS tS uS
  exact Finset.prod_comm

/- English proof (translation)
Rewrite using `[sg_eq_u, sg_eq_u]`. Conclude with `(Finset.mul_prod_erase J (fun j => uS I j) h).symm`.
-/
private theorem sg_right (I : Finset ι) {J : Finset ι} {k : ι} (h : k ∈ J) :
    shS I J = uS I k * shS I (J.erase k) := by
  rw [sg_eq_u, sg_eq_u]
  exact (Finset.mul_prod_erase J (fun j => uS I j) h).symm

private def ah (α : Finset ι → E) (I J : Finset ι) : E :=
  if Disjoint I J then shS I J • α (I ∪ J) else 0

/- English proof (translation)
Distinguish the cases in `hd : Disjoint I J`. Establish `e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J = ∑ i ∈ I, shS I J • (GlobalTheory.cubeSign (I ∪ J) i • α ((I ∪ J).erase i))`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hiJ : i ∉ J` using `Finset.disjoint_left.1 hd hi`. Establish `hdi : Disjoint (I.erase i) J` using `Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd`.

Establish `hset : I.erase i ∪ J = (I ∪ J).erase i`. Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y = i <;> simp [hy, hiJ]`. Unfold `ah`. Rewrite using `[if_pos hdi, hset, smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[cs_eq, cs_eq, tS_union hd, sg_left J hi]`. Take the linear combination `(-(tS I i * shS (I.erase i) J)) * tS_sq J i`. Establish `e2 : ∑ j ∈ J, ((-1 : ℤ) ^ I.card) • (GlobalTheory.cubeSign J j • ah α I (J.erase j)) = ∑ j ∈ J, shS I J • (GlobalTheory.cubeSign (I ∪ J) j • α ((I ∪ J).erase j))`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hjI : j ∉ I` using `Finset.disjoint_right.1 hd hj`. Establish `hdj : Disjoint I (J.erase j)` using `Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd`. Establish `hset : I ∪ J.erase j = (I ∪ J).erase j`. Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y = j <;> simp [hy, hjI]`.

Unfold `ah`. Rewrite using `[if_pos hdj, hset, smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[cs_eq, cs_eq, tS_union hd, sg_right I hj]`. Take the linear combination `(-(tS J j * shS I (J.erase j))) * tS_mul_uS hjI`.

Rewrite using `[e1, Finset.smul_sum, e2, ← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, ← Finset.sum_union hd, h, smul_zero]`. Take `⟨x, hxI, hxJ⟩` from `Finset.not_disjoint_iff.1 hd`. Establish `hsym : Disjoint I (J.erase x) ↔ Disjoint (I.erase x) J`. Rewrite using `[Finset.disjoint_left, Finset.disjoint_left]`. Prove the components needed by the constructor for the conclusion.

Introduce `h' y hy hyJ`. Conclude with `h' (Finset.mem_of_mem_erase hy) (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyJ⟩)`. Introduce `h' y hyI hy`. Conclude with `h' (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyI⟩) (Finset.mem_of_mem_erase hy)`. Establish `e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J = GlobalTheory.cubeSign I x • ah α (I.erase x) J`.

Use `Finset.sum_eq_single_of_mem x hxI fun i _ hne => ?_` and prove the remaining obligations. Unfold `ah`. Rewrite using `[if_neg, smul_zero]`. Introduce `hdi`. Conclude with `Finset.disjoint_left.1 hdi (Finset.mem_erase.2 ⟨hne.symm, hxI⟩) hxJ`.

Establish `e2 : ∑ j ∈ J, GlobalTheory.cubeSign J j • ah α I (J.erase j) = GlobalTheory.cubeSign J x • ah α I (J.erase x)`. Use `Finset.sum_eq_single_of_mem x hxJ fun j _ hne => ?_` and prove the remaining obligations. Unfold `ah`. Rewrite using `[if_neg, smul_zero]`. Introduce `hdj`.

Conclude with `Finset.disjoint_left.1 hdj hxI (Finset.mem_erase.2 ⟨hne.symm, hxJ⟩)`. Rewrite using `[e1, e2]`. Distinguish the cases in `hd2 : Disjoint (I.erase x) J`. Establish `hd3 : Disjoint I (J.erase x)` using `hsym.2 hd2`. Establish `s1 : I.erase x ∪ J = I ∪ J`.

Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y = x <;> simp [hy, hxJ]`. Establish `s2 : I ∪ J.erase x = I ∪ J`. Use extensionality with `y`. Apply the tactic sequence `by_cases hy : y = x <;> simp [hy, hxI]`.

Unfold `ah`. Rewrite using `[if_pos hd2, if_pos hd3, s1, s2, smul_smul, smul_smul, smul_smul, ← add_smul]`. Establish `hnot : x ∉ I.erase x` using `fun h' => Finset.ne_of_mem_erase h' rfl`. Take `⟨n, hn⟩ : ∃ n, I.card = n + 1` from `Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hxI)`. Establish `hcard : (I.erase x).card = n`.

Rewrite using `[Finset.card_erase_of_mem hxI, hn, Nat.add_sub_cancel]`. Establish `h1` using `tS_mul_uS hnot`. Rewrite `h1` using `[hcard]`. Establish `h2` using `tS_sq J x`. Establish `hz : GlobalTheory.cubeSign I x * shS (I.erase x) J + (-1 : ℤ) ^ I.card * GlobalTheory.cubeSign J x * shS I (J.erase x) = 0`.

Rewrite using `[cs_eq, cs_eq, sg_right (I.erase x) hxJ, sg_left (J.erase x) hxI, tS_erase, ← tS_erase I x, hn]`. Take the linear combination `(shS (I.erase x) (J.erase x)) * h1 + ((-1 : ℤ) ^ (n + 1) * shS (I.erase x) (J.erase x)) * h2`. Rewrite using `[hz, zero_smul]`. Unfold `ah`. Rewrite using `[if_neg hd2, if_neg (fun h' => hd2 (hsym.1 h'))]`.

Simplify using the standard rewrite rules.
-/
private theorem ah_cocycle (α : Finset ι → E)
    (h : ∀ s : Finset ι, ∑ k ∈ s, GlobalTheory.cubeSign s k • α (s.erase k) = 0) (I J : Finset ι) :
    ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J +
      ((-1 : ℤ) ^ I.card) • ∑ j ∈ J, GlobalTheory.cubeSign J j • ah α I (J.erase j) = 0 := by
  by_cases hd : Disjoint I J
  · have e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J =
        ∑ i ∈ I, shS I J • (GlobalTheory.cubeSign (I ∪ J) i • α ((I ∪ J).erase i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiJ : i ∉ J := Finset.disjoint_left.1 hd hi
      have hdi : Disjoint (I.erase i) J :=
        Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd
      have hset : I.erase i ∪ J = (I ∪ J).erase i := by
        ext y
        by_cases hy : y = i <;> simp [hy, hiJ]
      unfold ah
      rw [if_pos hdi, hset, smul_smul, smul_smul]
      congr 1
      rw [cs_eq, cs_eq, tS_union hd, sg_left J hi]
      linear_combination (-(tS I i * shS (I.erase i) J)) * tS_sq J i
    have e2 : ∑ j ∈ J, ((-1 : ℤ) ^ I.card) • (GlobalTheory.cubeSign J j • ah α I (J.erase j)) =
        ∑ j ∈ J, shS I J • (GlobalTheory.cubeSign (I ∪ J) j • α ((I ∪ J).erase j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjI : j ∉ I := Finset.disjoint_right.1 hd hj
      have hdj : Disjoint I (J.erase j) :=
        Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd
      have hset : I ∪ J.erase j = (I ∪ J).erase j := by
        ext y
        by_cases hy : y = j <;> simp [hy, hjI]
      unfold ah
      rw [if_pos hdj, hset, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [cs_eq, cs_eq, tS_union hd, sg_right I hj]
      linear_combination (-(tS J j * shS I (J.erase j))) * tS_mul_uS hjI
    rw [e1, Finset.smul_sum, e2, ← Finset.smul_sum, ← Finset.smul_sum, ← smul_add,
      ← Finset.sum_union hd, h, smul_zero]
  · obtain ⟨x, hxI, hxJ⟩ := Finset.not_disjoint_iff.1 hd
    have hsym : Disjoint I (J.erase x) ↔ Disjoint (I.erase x) J := by
      rw [Finset.disjoint_left, Finset.disjoint_left]
      constructor
      · intro h' y hy hyJ
        exact h' (Finset.mem_of_mem_erase hy) (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyJ⟩)
      · intro h' y hyI hy
        exact h' (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyI⟩) (Finset.mem_of_mem_erase hy)
    have e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J =
        GlobalTheory.cubeSign I x • ah α (I.erase x) J := by
      refine Finset.sum_eq_single_of_mem x hxI fun i _ hne => ?_
      unfold ah
      rw [if_neg, smul_zero]
      intro hdi
      exact Finset.disjoint_left.1 hdi (Finset.mem_erase.2 ⟨hne.symm, hxI⟩) hxJ
    have e2 : ∑ j ∈ J, GlobalTheory.cubeSign J j • ah α I (J.erase j) =
        GlobalTheory.cubeSign J x • ah α I (J.erase x) := by
      refine Finset.sum_eq_single_of_mem x hxJ fun j _ hne => ?_
      unfold ah
      rw [if_neg, smul_zero]
      intro hdj
      exact Finset.disjoint_left.1 hdj hxI (Finset.mem_erase.2 ⟨hne.symm, hxJ⟩)
    rw [e1, e2]
    by_cases hd2 : Disjoint (I.erase x) J
    · have hd3 : Disjoint I (J.erase x) := hsym.2 hd2
      have s1 : I.erase x ∪ J = I ∪ J := by
        ext y
        by_cases hy : y = x <;> simp [hy, hxJ]
      have s2 : I ∪ J.erase x = I ∪ J := by
        ext y
        by_cases hy : y = x <;> simp [hy, hxI]
      unfold ah
      rw [if_pos hd2, if_pos hd3, s1, s2, smul_smul, smul_smul, smul_smul, ← add_smul]
      have hnot : x ∉ I.erase x := fun h' => Finset.ne_of_mem_erase h' rfl
      obtain ⟨n, hn⟩ : ∃ n, I.card = n + 1 :=
        Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hxI)
      have hcard : (I.erase x).card = n := by
        rw [Finset.card_erase_of_mem hxI, hn, Nat.add_sub_cancel]
      have h1 := tS_mul_uS hnot
      rw [hcard] at h1
      have h2 := tS_sq J x
      have hz : GlobalTheory.cubeSign I x * shS (I.erase x) J +
          (-1 : ℤ) ^ I.card * GlobalTheory.cubeSign J x * shS I (J.erase x) = 0 := by
        rw [cs_eq, cs_eq, sg_right (I.erase x) hxJ, sg_left (J.erase x) hxI, tS_erase,
          ← tS_erase I x, hn]
        linear_combination (shS (I.erase x) (J.erase x)) * h1 +
          ((-1 : ℤ) ^ (n + 1) * shS (I.erase x) (J.erase x)) * h2
      rw [hz, zero_smul]
    · unfold ah
      rw [if_neg hd2, if_neg (fun h' => hd2 (hsym.1 h'))]
      simp

/- English proof (translation)
Use `split_ifs with h`. Take `⟨a, rfl⟩` from `Finset.card_eq_one.1 h`. Simplify using `[GlobalTheory.cubeSign_singleton]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[if_neg, smul_zero]`. Introduce `he`. Apply `h` to reduce the goal to its premises. Establish `h3` using `Finset.card_erase_of_mem hi`. Rewrite `h3` using `[he, Finset.card_empty]`.

Establish `h4` using `Finset.card_pos.2 ⟨i, hi⟩`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_single (I : Finset ι) (x : E) :
    ∑ i ∈ I, GlobalTheory.cubeSign I i • (if I.erase i = ∅ then x else 0) = if I.card = 1 then x else 0 := by
  split_ifs with h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign_singleton]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg, smul_zero]
    intro he
    apply h
    have h3 := Finset.card_erase_of_mem hi
    rw [he, Finset.card_empty] at h3
    have h4 := Finset.card_pos.2 ⟨i, hi⟩
    omega

/- English proof (translation)
Simplify using `[wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
private theorem wd_ap [Module ℂ E] (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]
end

/- English proof (translation)
Introduce `hU`. Unfold `EdgeRel`. Introduce `ι E _ _ _ _ G p _ α hα`. Unfold `cech Cx.Z at hα`. Simplify using `[cechC] at hα`.

Take `⟨hC, hδ⟩` from `hα`. Establish `hcoc : ∀ s : Finset ι, ∑ k ∈ s, GlobalTheory.cubeSign s k • α (s.erase k) = 0`. Introduce `s`. Simplify `congrFun hδ s` using `[deltaL, GlobalTheory.DI.delta]`. Establish `hα0 : α ∅ = 0` using `by simpa using hC ∅`.

Establish `hl : ∀ a b : Finset ι, lft (uni a b) = a` using `fun a b => (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.1`. Establish `hr : ∀ a b : Finset ι, rgt (uni a b) = b` using `fun a b => (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.2.1`. Establish `hsurj : ∀ s : Finset (ι ⊕ₗ ι), ∃ I J, s = uni I J` using `fun s => ⟨lft s, rgt s, ((hU ι ι E (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s).symm⟩`. Establish `key : ∀ I : Finset ι, ((-1 : ℤ) ^ I.card) • α I = -(((-1 : ℤ) ^ p) • α I)`. Introduce `I`.

Distinguish the cases in `hI : I.Nonempty ∧ ((I.card : ℕ) : ℤ) = (p : ℤ) + 1`. Establish `e : I.card = p + 1` using `by omega`. Rewrite using `[e, pow_succ, mul_neg_one, neg_smul]`. Establish `h0` using `hC I`. Rewrite `h0` using `[if_neg hI]`.

Establish `h1 : α I = 0` using `by simpa using h0`. Simplify using `[h1]`. Take `⟨c, hc⟩ : ∃ c : Finset (ι ⊕ₗ ι) → E, ∀ s, c s = if (lft s).Nonempty ∧ (rgt s).Nonempty then -ah α (lft s) (rgt s) else 0` from `⟨_, fun s => rfl⟩`. Unfold `acx Cx.B`. Use `Submodule.mem_map.2 ⟨c, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies]`. Introduce `s`. Take `⟨I, J, rfl⟩` from `hsurj s`. Rewrite using `[hc, hl, hr]`.

Establish `hcardU` using `(hU ι ι E (fun _ => 1) (fun _ => 0) I J).2.2.2.1`. Distinguish the cases in `hIJ : I.Nonempty ∧ J.Nonempty`. Rewrite using `[if_pos hIJ]`. Unfold `ah`. Distinguish the cases in `hd : Disjoint I J`.

Rewrite using `[if_pos hd]`. Establish `hα'` using `hC (I ∪ J)`. Distinguish the cases in `hcd : (I ∪ J).Nonempty ∧ (((I ∪ J).card : ℕ) : ℤ) = (p : ℤ) + 1`. Rewrite `hα'` using `[if_pos hcd]`. Establish `hk : (((uni I J).card : ℕ) : ℤ) = (p : ℤ) + 2 - 1`.

Rewrite using `[hcardU, ← Finset.card_union_of_disjoint hd]`. Use `hcd.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hk]`. Simplify using `only [mixF, hl, hr, if_pos hIJ]`.

Conclude with `neg_mem (zsmul_mem hα' _)`. Rewrite `hα'` using `[if_neg hcd]`. Establish `h0 : α (I ∪ J) = 0` using `by simpa using hα'`. Rewrite using `[h0, smul_zero, neg_zero]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[if_neg hd, neg_zero]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[if_neg hIJ]`. Conclude with `Submodule.zero_mem _`. Simplify using `only`.

Use function extensionality and compare the values at `s`. Take `⟨I, J, rfl⟩` from `hsurj s`. Establish `h` using `hU ι ι E (fun _ => 1) c I J`. Rewrite using `[h.1, wd_ap, wd_ap]`. Simplify using `only [hc, hl, hr, edge1, edge2, Pi.sub_apply, Pi.smul_apply, Module.End.one_apply]`.

Distinguish the cases in `hJ : J.Nonempty`. Use `swap`. Rewrite `hJ` using `[Finset.not_nonempty_iff_eq_empty]`. Substitute `hJ` using the available equality. Simplify using `[hα0]`.

Distinguish the cases in `hI : I.Nonempty`. Use `swap`. Rewrite `hI` using `[Finset.not_nonempty_iff_eq_empty]`. Substitute `hI` using the available equality. Simplify using `[hα0]`.

Establish `t1 : ∀ i ∈ I, GlobalTheory.cubeSign I i • (if (I.erase i).Nonempty ∧ J.Nonempty then -ah α (I.erase i) J else 0) = -(GlobalTheory.cubeSign I i • ah α (I.erase i) J) + GlobalTheory.cubeSign I i • (if I.erase i = ∅ then α J else 0)`. Introduce `i _`. Distinguish the cases in `he : I.erase i = ∅`. Rewrite using `[he]`. Simplify using `[ah, shS]`.

Establish `hne : (I.erase i).Nonempty` using `Finset.nonempty_iff_ne_empty.2 he`. Rewrite using `[if_pos ⟨hne, hJ⟩, if_neg he, smul_zero, add_zero, smul_neg]`. Establish `t2 : ∀ j ∈ J, GlobalTheory.cubeSign J j • (if I.Nonempty ∧ (J.erase j).Nonempty then -ah α I (J.erase j) else 0) = -(GlobalTheory.cubeSign J j • ah α I (J.erase j)) + GlobalTheory.cubeSign J j • (if J.erase j = ∅ then α I else 0)`. Introduce `j _`. Distinguish the cases in `he : J.erase j = ∅`.

Rewrite using `[he]`. Simplify using `[ah, shS, tS]`. Establish `hne : (J.erase j).Nonempty` using `Finset.nonempty_iff_ne_empty.2 he`. Rewrite using `[if_pos ⟨hI, hne⟩, if_neg he, smul_zero, add_zero, smul_neg]`. Rewrite using `[Finset.sum_congr rfl t1, Finset.sum_congr rfl t2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib, sum_single, sum_single]`.

Establish `hco` using `ah_cocycle α hcoc I J`. Rewrite using `[eq_neg_of_add_eq_zero_left hco, smul_add, smul_neg]`. Distinguish the cases in `hJ1 : J.card = 1`. Rewrite using `[if_pos hJ1, key]`. Normalize the expressions using the abelian group laws.

Rewrite using `[if_neg hJ1]`. Simplify using `only [smul_zero, add_zero, sub_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.Gal.productCup_of_system.edgeRel_of :
    WdUni → EdgeRel := by
  intro hU
  unfold EdgeRel
  intro ι E _ _ _ _ G p _ α hα
  unfold cech Cx.Z at hα
  simp [cechC] at hα
  obtain ⟨hC, hδ⟩ := hα
  have hcoc : ∀ s : Finset ι, ∑ k ∈ s, GlobalTheory.cubeSign s k • α (s.erase k) = 0 := by
    intro s
    simpa [deltaL, GlobalTheory.DI.delta] using congrFun hδ s
  have hα0 : α ∅ = 0 := by simpa using hC ∅
  have hl : ∀ a b : Finset ι, lft (uni a b) = a := fun a b =>
    (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.1
  have hr : ∀ a b : Finset ι, rgt (uni a b) = b := fun a b =>
    (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.2.1
  have hsurj : ∀ s : Finset (ι ⊕ₗ ι), ∃ I J, s = uni I J := fun s =>
    ⟨lft s, rgt s, ((hU ι ι E (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s).symm⟩
  have key : ∀ I : Finset ι, ((-1 : ℤ) ^ I.card) • α I = -(((-1 : ℤ) ^ p) • α I) := by
    intro I
    by_cases hI : I.Nonempty ∧ ((I.card : ℕ) : ℤ) = (p : ℤ) + 1
    · have e : I.card = p + 1 := by omega
      rw [e, pow_succ, mul_neg_one, neg_smul]
    · have h0 := hC I
      rw [if_neg hI] at h0
      have h1 : α I = 0 := by simpa using h0
      simp [h1]
  obtain ⟨c, hc⟩ : ∃ c : Finset (ι ⊕ₗ ι) → E, ∀ s, c s =
      if (lft s).Nonempty ∧ (rgt s).Nonempty then -ah α (lft s) (rgt s) else 0 :=
    ⟨_, fun s => rfl⟩
  unfold acx Cx.B
  refine Submodule.mem_map.2 ⟨c, ?_, ?_⟩
  · dsimp only
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
    intro s
    obtain ⟨I, J, rfl⟩ := hsurj s
    rw [hc, hl, hr]
    have hcardU := (hU ι ι E (fun _ => 1) (fun _ => 0) I J).2.2.2.1
    by_cases hIJ : I.Nonempty ∧ J.Nonempty
    · rw [if_pos hIJ]
      unfold ah
      by_cases hd : Disjoint I J
      · rw [if_pos hd]
        have hα' := hC (I ∪ J)
        by_cases hcd : (I ∪ J).Nonempty ∧ (((I ∪ J).card : ℕ) : ℤ) = (p : ℤ) + 1
        · rw [if_pos hcd] at hα'
          have hk : (((uni I J).card : ℕ) : ℤ) = (p : ℤ) + 2 - 1 := by
            rw [hcardU, ← Finset.card_union_of_disjoint hd]
            have := hcd.2
            omega
          rw [if_pos hk]
          simp only [mixF, hl, hr, if_pos hIJ]
          exact neg_mem (zsmul_mem hα' _)
        · rw [if_neg hcd] at hα'
          have h0 : α (I ∪ J) = 0 := by simpa using hα'
          rw [h0, smul_zero, neg_zero]
          exact Submodule.zero_mem _
      · rw [if_neg hd, neg_zero]
        exact Submodule.zero_mem _
    · rw [if_neg hIJ]
      exact Submodule.zero_mem _
  · dsimp only
    funext s
    obtain ⟨I, J, rfl⟩ := hsurj s
    have h := hU ι ι E (fun _ => 1) c I J
    rw [h.1, wd_ap, wd_ap]
    simp only [hc, hl, hr, edge1, edge2, Pi.sub_apply, Pi.smul_apply, Module.End.one_apply]
    by_cases hJ : J.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hJ
      subst hJ
      simp [hα0]
    by_cases hI : I.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hI
      subst hI
      simp [hα0]
    have t1 : ∀ i ∈ I, GlobalTheory.cubeSign I i •
        (if (I.erase i).Nonempty ∧ J.Nonempty then -ah α (I.erase i) J else 0) =
        -(GlobalTheory.cubeSign I i • ah α (I.erase i) J) +
          GlobalTheory.cubeSign I i • (if I.erase i = ∅ then α J else 0) := by
      intro i _
      by_cases he : I.erase i = ∅
      · rw [he]
        simp [ah, shS]
      · have hne : (I.erase i).Nonempty := Finset.nonempty_iff_ne_empty.2 he
        rw [if_pos ⟨hne, hJ⟩, if_neg he, smul_zero, add_zero, smul_neg]
    have t2 : ∀ j ∈ J, GlobalTheory.cubeSign J j •
        (if I.Nonempty ∧ (J.erase j).Nonempty then -ah α I (J.erase j) else 0) =
        -(GlobalTheory.cubeSign J j • ah α I (J.erase j)) +
          GlobalTheory.cubeSign J j • (if J.erase j = ∅ then α I else 0) := by
      intro j _
      by_cases he : J.erase j = ∅
      · rw [he]
        simp [ah, shS, tS]
      · have hne : (J.erase j).Nonempty := Finset.nonempty_iff_ne_empty.2 he
        rw [if_pos ⟨hI, hne⟩, if_neg he, smul_zero, add_zero, smul_neg]
    rw [Finset.sum_congr rfl t1, Finset.sum_congr rfl t2, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib, sum_single,
      sum_single]
    have hco := ah_cocycle α hcoc I J
    rw [eq_neg_of_add_eq_zero_left hco, smul_add, smul_neg]
    by_cases hJ1 : J.card = 1
    · rw [if_pos hJ1, key]
      abel
    · rw [if_neg hJ1]
      simp only [smul_zero, add_zero, sub_zero]
      abel
