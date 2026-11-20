import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CreqAnnqTopqSame

open Finset
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.SemiClass

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annL l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

/- English proof (translation)
Unfold `sgL`. Use `congr 2`. Use extensionality with `m`. Simplify using `only [Finset.mem_filter, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, hm⟩, hk⟩`. Conclude with `⟨hm, hk⟩`. Introduce and unpack `⟨hm, hk⟩`. Use `⟨⟨?_, hm⟩, hk⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hk`.
-/
theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext m
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hm⟩, hk⟩
    exact ⟨hm, hk⟩
  · rintro ⟨hm, hk⟩
    refine ⟨⟨?_, hm⟩, hk⟩
    rintro rfl
    exact lt_irrefl _ hk

/- English proof (translation)
Unfold `sgL`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

/- English proof (translation)
Rewrite using `[creL_app]`. Use `split_ifs with hB`. Rewrite using `[annL_app, if_neg (by simp), Finset.insert_erase hB, sgL_erase, smul_smul, sgL_sq, one_smul]`. Both sides reduce to the same expression.
-/
theorem creL_annL (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l (annL l x) B = if l ∈ B then x B else 0 := by
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app, if_neg (by simp), Finset.insert_erase hB, sgL_erase, smul_smul, sgL_sq, one_smul]
  · rfl

/- English proof (translation)
Simplify using `[omU]`.
-/
theorem mem_omU {lev : Fin n → ℕ} {l : Lt n} : l ∈ omU lev ↔ l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omU]

omit [Module ℂ V] in
/- English proof (translation)
Rewrite using `[Pi.single_apply]`.
-/
theorem top_app (lev : Fin n → ℕ) (x : V) (B : Finset (Lt n)) :
    (Pi.single (omU lev) x : Cq n V) B = if B = omU lev then x else 0 := by
  rw [Pi.single_apply]

/- English proof (translation)
Use extensionality with `B`. Simplify using `only [Pi.smul_apply, top_app]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem top_smul (lev : Fin n → ℕ) (c : ℂ) (x : V) :
    (Pi.single (omU lev) (c • x) : Cq n V) = c • (Pi.single (omU lev) x : Cq n V) := by
  ext B
  simp only [Pi.smul_apply, top_app]
  split_ifs <;> simp

omit [Module ℂ V] in
/- English proof (translation)
Conclude with `Pi.single_zero _`.
-/
theorem top_zero (lev : Fin n → ℕ) : (Pi.single (omU lev) (0 : V) : Cq n V) = 0 := by
  exact Pi.single_zero _

/- English proof (translation)
Use extensionality with `B`. Simplify using `only [liftL, LinearMap.compLeft_apply, Function.comp_apply, top_app]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem liftL_top (lev : Fin n → ℕ) (T : Module.End ℂ V) (x : V) :
    (liftL n T : Module.End ℂ (Cq n V)) (Pi.single (omU lev) x) = Pi.single (omU lev) (T x) := by
  ext B
  simp only [liftL, LinearMap.compLeft_apply, Function.comp_apply, top_app]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `B`. Rewrite using `[annL_app, top_app]`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Conclude with `absurd (by rw [← h2]; exact Finset.mem_insert_self l B) h`.

Simplify using the standard rewrite rules.
-/
theorem annL_top_of_notMem {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∉ omU lev) :
    annL l (Pi.single (omU lev) x : Cq n V) = 0 := by
  ext B
  rw [annL_app, top_app]
  split_ifs with h1 h2
  · rfl
  · exact absurd (by rw [← h2]; exact Finset.mem_insert_self l B) h
  · simp

/- English proof (translation)
Use extensionality with `B`. Rewrite using `[creL_annL]`. Use `split_ifs with hB`. Both sides reduce to the same expression. Rewrite using `[top_app, if_neg (fun e => hB (by rw [e]; exact h))]`.
-/
theorem creL_annL_top_same {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∈ omU lev) :
    creL l (annL l (Pi.single (omU lev) x : Cq n V)) = Pi.single (omU lev) x := by
  ext B
  rw [creL_annL]
  split_ifs with hB
  · rfl
  · rw [top_app, if_neg (fun e => hB (by rw [e]; exact h))]

/- English proof (translation)
Use extensionality with `B`. Rewrite using `[creL_app]`. Use `split_ifs with hB`. Rewrite using `[annL_app] split_ifs with hl`. Simplify using the standard rewrite rules.

Rewrite using `[top_app, if_neg]`. Simplify using the standard rewrite rules. Introduce `e`. Establish `hmem : m ∈ insert l (B.erase m)`. Rewrite using `[e]`.

Conclude with `hm`. Simplify using `[hne] at hmem`. Both sides reduce to the same expression.
-/
theorem creL_annL_top_ne {lev : Fin n → ℕ} {l m : Lt n} (x : V) (hm : m ∈ omU lev) (hne : m ≠ l) :
    creL m (annL l (Pi.single (omU lev) x : Cq n V)) = 0 := by
  ext B
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app]
    split_ifs with hl
    · simp
    · rw [top_app, if_neg]
      · simp
      · intro e
        have hmem : m ∈ insert l (B.erase m) := by
          rw [e]
          exact hm
        simp [hne] at hmem
  · rfl

/- English proof (translation)
Rewrite `hl`, the goal using `[mem_omU]`. Take `⟨hl1, hl2⟩` from `hl`. Establish `case1 : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) → k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2`. Introduce and unpack `⟨e1, e2, e3⟩`. Use `⟨by simp [e2, hl1], ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `case2 : (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) → k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2`. Introduce and unpack `⟨e1, e2, e3⟩`. Use `⟨by simp [e2, hl1], ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Unfold `adCL at h`. Use `split_ifs at h with c1 c2 c3`. Conclude with `case1 c1`. Conclude with `case1 c1`. Conclude with `case2 c3`.

Simplify using `at h`.
-/
theorem mem_omU_of_adCL_ne {lev : Fin n → ℕ} {p q : Fin n} {l k : Lt n} (hpq : lev p = lev q)
    (hl : l ∈ omU lev) (h : adCL false p q l k ≠ 0) : k ∈ omU lev := by
  rw [mem_omU] at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  have case1 : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev p := by rw [e3]
      _ = lev q := hpq
      _ = lev l.2.1.1 := by rw [e1]
      _ < lev l.2.1.2 := hl2
      _ = lev k.2.1.2 := by rw [e3]
  have case2 : (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev l.2.1.1 := by rw [e3]
      _ < lev l.2.1.2 := hl2
      _ = lev p := by rw [e1]
      _ = lev q := hpq
      _ = lev k.2.1.2 := by rw [e3]
  unfold adCL at h
  split_ifs at h with c1 c2 c3
  · exact case1 c1
  · exact case1 c1
  · exact case2 c3
  · simp at h

/- English proof (translation)
Simplify using `[adCL, adC]`.
-/
theorem adCL_self (p q : Fin n) (i : Pos n) :
    adCL false p q ((false, i) : Lt n) (false, i) = adC p q i i := by
  simp [adCL, adC]

/- English proof (translation)
Establish `key : ∀ l k : Lt n, ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 : Module.End ℂ (Cq n V)) (Pi.single (omU lev) x)) = if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0) else 0`. Introduce `l k`. Distinguish the cases in `hl : l ∈ omU lev`. Establish `hin : inUU lev l` using `(mem_omU.1 hl).2`. Rewrite using `[if_pos hin, LinearMap.smul_apply, Module.End.mul_apply]`.

Distinguish the cases in `hk : k = l`. Substitute `hk` using the available equality. Rewrite using `[creL_annL_top_same x hl, if_pos rfl, if_pos hl]`. Rewrite using `[if_neg hk]`. Distinguish the cases in `hkm : k ∈ omU lev`.

Rewrite using `[creL_annL_top_ne x hkm hk, smul_zero]`. Establish `h0 : adCL false p q l k = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hkm (mem_omU_of_adCL_ne hpq hl hne)`. Rewrite using `[h0, zero_smul]`.

Apply the tactic sequence `have hr : (if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0) else 0) = 0 := by split_ifs <;> rfl`. Rewrite using `[hr]`. Use `split_ifs`. Rewrite using `[LinearMap.smul_apply, Module.End.mul_apply, annL_top_of_notMem x hl, map_zero, smul_zero]`. Both sides reduce to the same expression.

Establish `hsum : (∑ l ∈ omU lev, adCL false p q l l) = ∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0`. Rewrite using `[omU, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]`. Simplify using `[adCL_self]`. Unfold `adLL`. Simplify using `only [LinearMap.sum_apply, key, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[← hsum, Finset.sum_smul, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `l`. Simplify using the standard rewrite rules.
-/
theorem adLL_top {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) (x : V) :
    adLL lev false p q (Pi.single (omU lev) x : Cq n V) =
      (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0) • (Pi.single (omU lev) x : Cq n V) := by
  have key : ∀ l k : Lt n, ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 :
      Module.End ℂ (Cq n V)) (Pi.single (omU lev) x)) =
      if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0) else 0 := by
    intro l k
    by_cases hl : l ∈ omU lev
    · have hin : inUU lev l := (mem_omU.1 hl).2
      rw [if_pos hin, LinearMap.smul_apply, Module.End.mul_apply]
      by_cases hk : k = l
      · subst hk
        rw [creL_annL_top_same x hl, if_pos rfl, if_pos hl]
      · rw [if_neg hk]
        by_cases hkm : k ∈ omU lev
        · rw [creL_annL_top_ne x hkm hk, smul_zero]
        · have h0 : adCL false p q l k = 0 := by
            by_contra hne
            exact hkm (mem_omU_of_adCL_ne hpq hl hne)
          rw [h0, zero_smul]
    · have hr : (if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0)
          else 0) = 0 := by
        split_ifs <;> rfl
      rw [hr]
      split_ifs
      · rw [LinearMap.smul_apply, Module.End.mul_apply, annL_top_of_notMem x hl, map_zero, smul_zero]
      · rfl
  have hsum : (∑ l ∈ omU lev, adCL false p q l l) =
      ∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0 := by
    rw [omU, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [adCL_self]
  unfold adLL
  simp only [LinearMap.sum_apply, key, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hsum, Finset.sum_smul, ← Finset.sum_filter]
  congr 1
  ext l
  simp

/- English proof (translation)
Simplify using `only [firstLeviFamily, secondLeviFamily, ← smul_add]`. Rewrite using `[add_add_sub_cancel, ← two_smul ℂ, smul_smul]`. Evaluate the numerical expressions.
-/
theorem leviFamilyOne_add_leviFamilyTwo (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a c : Fin n) :
    firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c = evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, a, c)) := by
  simp only [firstLeviFamily, secondLeviFamily, ← smul_add]
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

end GlobalTheory.CompanionTheory.SemiClass

namespace GlobalTheory.CompanionTheory.SemiClass

open GlobalTheory.CompanionTheory.PairMult.TopK (K_act sum_diag adC_diag_ne)

/- English proof (translation)
Introduce `n lam _ lev hl V _ _ E1 E2 hA v hv a c hac`. Rewrite using `[leviFamilyOne_add_leviFamilyTwo]`. Unfold `evLc`. Rewrite using `[FreeAlgebra.lift_ι_apply]`. Simplify using `only`.

Rewrite using `[if_pos hac]`. Simplify using `only [Bool.false_eq_true, if_false, ite_false]`. Rewrite using `[LinearMap.add_apply, liftL_top, adLL_top hac]`. Establish `hk : kA E1 E2 a c v = kF E1 E2 a c v` using `rfl`. Rewrite using `[hk, GlobalTheory.CompanionTheory.PairMult.TopK.K_act hl hA hv hac]`.

Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Rewrite using `[if_pos (rfl : a = a), if_pos (rfl : a = a), GlobalTheory.CompanionTheory.PairMult.TopK.sum_diag hl.1, top_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg h, top_zero, zero_add]`. Establish `h0 : (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC a c i i else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[GlobalTheory.CompanionTheory.PairMult.TopK.adC_diag_ne h i]`. Simplify using the standard rewrite rules. Rewrite using `[h0, zero_smul]`.
-/
theorem semiCls : SemiCls := by
  intro n lam _ lev hl V _ _ E1 E2 hA v hv a c hac
  rw [leviFamilyOne_add_leviFamilyTwo]
  unfold evLc
  rw [FreeAlgebra.lift_ι_apply]
  dsimp only
  rw [if_pos hac]
  simp only [Bool.false_eq_true, if_false, ite_false]
  rw [LinearMap.add_apply, liftL_top, adLL_top hac]
  have hk : kA E1 E2 a c v = kF E1 E2 a c v := rfl
  rw [hk, GlobalTheory.CompanionTheory.PairMult.TopK.K_act hl hA hv hac]
  by_cases h : a = c
  · subst h
    rw [if_pos (rfl : a = a), if_pos (rfl : a = a), GlobalTheory.CompanionTheory.PairMult.TopK.sum_diag hl.1, top_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · rw [if_neg h, if_neg h, top_zero, zero_add]
    have h0 : (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC a c i i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [GlobalTheory.CompanionTheory.PairMult.TopK.adC_diag_ne h i]
      simp
    rw [h0, zero_smul]

end GlobalTheory.CompanionTheory.SemiClass
