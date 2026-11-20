import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfLe.PrismComb

def stepMap (q n : ℕ) : Fin (q + 2) →o Fin 2 :=
  ⟨fun x ↦ if (x : ℕ) < n then 0 else 1, fun a b h ↦ by
    have h' : (a : ℕ) ≤ b := h
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Fin.zero_le _
    · omega
    · exact le_rfl⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(if x ≤ i.castSucc then (0 : Fin 2) else 1) = _`. Simplify using `only [Fin.le_def, Fin.val_castSucc]`.
-/
theorem th_apply (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    th q i x = if (x : ℕ) ≤ i then 0 else 1 := by
  change (if x ≤ i.castSucc then (0 : Fin 2) else 1) = _
  simp only [Fin.le_def, Fin.val_castSucc]

/- English proof (translation)
Unfold `Fin.succAbove`. Simplify using `only [Fin.lt_def, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    ((j.succAbove x : Fin (n + 1)) : ℕ) = if (x : ℕ) < j then (x : ℕ) else x + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

/- English proof (translation)
Unfold `Fin.predAbove`. Simplify using `only [Fin.lt_def, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem val_predAbove {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    ((Fin.predAbove i x : Fin n) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `val_predAbove i x`.
-/
theorem val_sg (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    ((sg q i x : Fin (q + 1)) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x :=
  val_predAbove i x

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x = th (q + 1) i (i.castSucc.succAbove x)` using `rfl`. Rewrite using `[e, th_apply]`. Express the relevant statement in the definitionally equal form `_ = ((if (x : ℕ) < i then (0 : Fin 2) else 1 : Fin 2) : ℕ)`. Rewrite using `[val_succAbove]`.

Simplify using `only [Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem th_diag (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = stepMap q i := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      th (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_castSucc]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x = th (q + 1) i (i.succ.succAbove x)` using `rfl`. Rewrite using `[e, th_apply]`. Express the relevant statement in the definitionally equal form `_ = ((if (x : ℕ) < i + 1 then (0 : Fin 2) else 1 : Fin 2) : ℕ)`. Rewrite using `[val_succAbove]`.

Simplify using `only [Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem th_next (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = stepMap q (i + 1) := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      th (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i + 1 then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_succ]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x = sg (q + 1) i (i.castSucc.succAbove x)` using `rfl`. Rewrite using `[e, val_sg, val_succAbove]`. Simplify using `only [Fin.val_castSucc, OrderHom.id_coe, id_eq]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem sg_diag (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      sg (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_castSucc, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x = sg (q + 1) i (i.succ.succAbove x)` using `rfl`. Rewrite using `[e, val_sg, val_succAbove]`. Simplify using `only [Fin.val_succ, OrderHom.id_coe, id_eq]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem sg_next (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      sg (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_succ, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

/- English proof (translation)
Use extensionality with `x`. Simplify using `[stepMap, cst]`. Both sides reduce to the same expression.
-/
theorem stepMap_zero (q : ℕ) : stepMap q 0 = cst (q + 1) 1 := by
  ext x
  simp [stepMap, cst]
  rfl

/- English proof (translation)
Use extensionality with `x`. Use `x.2` as an intermediate fact. Simplify using `[stepMap, cst, this]`. Both sides reduce to the same expression.
-/
theorem stepMap_top (q : ℕ) : stepMap q (q + 2) = cst (q + 1) 0 := by
  ext x
  have := x.2
  simp [stepMap, cst, this]
  rfl

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x = th (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x)` using `rfl`. Rewrite using `[e, th_apply, th_apply]`. Use `congr 2`. Simplify using `only [val_succAbove, val_predAbove, Fin.val_castSucc, eq_iff_iff]`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem th_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      th q (Fin.predAbove k i) := by
  ext x
  have e : ((th (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      th (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  rw [e, th_apply, th_apply]
  congr 2
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc, eq_iff_iff]
  split_ifs <;> omega

/- English proof (translation)
Use extensionality with `x`. Establish `e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x = sg (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x)` using `rfl`. Establish `e' : ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) x = (i.succAbove k).succAbove (sg q (Fin.predAbove k i) x)` using `rfl`. Rewrite using `[e, e']`. Simplify using `only [val_sg, val_succAbove, val_predAbove, Fin.val_castSucc]`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem sg_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      (Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)) := by
  ext x
  have e : ((sg (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      sg (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  have e' : ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) x =
      (i.succAbove k).succAbove (sg q (Fin.predAbove k i) x) := rfl
  rw [e, e']
  simp only [val_sg, val_succAbove, val_predAbove, Fin.val_castSucc]
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [val_succAbove, val_predAbove, Fin.val_castSucc]`. Distinguish the cases in `h : (k : ℕ) < i`. Take `⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1` from `⟨(i : ℕ) - 1, by omega⟩`. Rewrite using `[if_pos h, if_pos h, if_pos (by omega), hm]`. Simplify using `[pow_add, pow_succ]`.

Rewrite using `[if_neg h, if_neg (by omega), if_neg (by omega)]`. Simplify using `[pow_add, pow_succ]`.
-/
theorem sign_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) =
      -((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) := by
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc]
  by_cases h : (k : ℕ) < i
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [if_pos h, if_pos h, if_pos (by omega), hm]
    simp [pow_add, pow_succ]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega)]
    simp [pow_add, pow_succ]

def fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : Fin (q + 1) × Fin (q + 2) :=
  (Fin.predAbove p.2 p.1, p.1.succAbove p.2)

def bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : Fin (q + 2) × Fin (q + 1) :=
  (⟨if (p.2 : ℕ) ≤ p.1 then (p.1 : ℕ) + 1 else p.1, by have := p.1.2; split_ifs <;> omega⟩,
   ⟨if (p.2 : ℕ) ≤ p.1 then p.2 else (p.2 : ℕ) - 1, by have := p.1.2; have := p.2.2; split_ifs <;> omega⟩)

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>`. Apply the tactic sequence `simp only [bwd, fwd, val_succAbove, val_predAbove] split_ifs <;> omega`.
-/
theorem bwd_fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : bwd q (fwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>`. Apply the tactic sequence `simp only [bwd, fwd, val_succAbove, val_predAbove] split_ifs <;> omega`.
-/
theorem fwd_bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : fwd q (bwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

/- English proof (translation)
Establish `h1 : ∀ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) = (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) - ∑ k : Fin (q …`. Introduce `i`. Rewrite using `[Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i, Fin.succAbove_castSucc_self, th_diag, sg_diag, th_next, sg_next]`. Establish `e1 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc : Fin (q + 3)) : ℕ))) = 1`. Simplify using `[Even.neg_one_pow, ← two_mul]`.

Establish `e2 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.succ : Fin (q + 3)) : ℕ))) = -1`. Simplify using `[← add_assoc, ← two_mul, pow_succ]`. Rewrite using `[e1, e2, one_smul, neg_smul, one_smul]`. Establish `e3 : ∀ k : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) • B ((th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) ((sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.suc …`. Introduce `k`.

Rewrite using `[th_off, sg_off, sign_off, neg_smul]`. Simplify using `only [e3, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws. Establish `h2 : ∑ i : Fin (q + 2), (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) = B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun n ↦ B (stepMap q n) OrderHom.id - B (stepMap q (n + 1)) OrderHom.id), Finset.sum_range_sub', stepMap_zero, stepMap_top]`.

Establish `h3 : ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) • B (th q (Fin.predAbove k i)) ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) = ∑ j : Fin (q + 2), ∑ i : F …`. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin (q + 2)))) (t := (Finset.univ : Finset (Fin (q + 1)))) (f := fun j i ↦ ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i))), ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']`. Conclude with `Finset.sum_nbij' (fwd q) (bwd q) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ bwd_fwd q p) (fun p _ ↦ fwd_bwd q p) (fun _ _ ↦ rfl)`. Simplify using `only [h1, Finset.sum_sub_distrib] at h2 ⊢`. Rewrite using `[h2, h3]`.
-/
theorem prism_faces {A : Type} [AddCommGroup A] (q : ℕ)
    (B : (Fin (q + 2) →o Fin 2) → (Fin (q + 2) →o Fin (q + 2)) → A) :
    ∑ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id -
        ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
  have h1 : ∀ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) -
        ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) := by
    intro i
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i,
      Fin.succAbove_castSucc_self, th_diag, sg_diag, th_next, sg_next]
    have e1 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc : Fin (q + 3)) : ℕ))) = 1 := by
      simp [Even.neg_one_pow, ← two_mul]
    have e2 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.succ : Fin (q + 3)) : ℕ))) = -1 := by
      simp [← add_assoc, ← two_mul, pow_succ]
    rw [e1, e2, one_smul, neg_smul, one_smul]
    have e3 : ∀ k : Fin (q + 1),
        ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) •
          B ((th (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom)
            ((sg (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) =
        -(((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)))) := by
      intro k
      rw [th_off, sg_off, sign_off, neg_smul]
    simp only [e3, Finset.sum_neg_distrib]
    abel
  have h2 : ∑ i : Fin (q + 2), (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id := by
    rw [Fin.sum_univ_eq_sum_range (fun n ↦ B (stepMap q n) OrderHom.id - B (stepMap q (n + 1)) OrderHom.id),
      Finset.sum_range_sub', stepMap_zero, stepMap_top]
  have h3 : ∑ i : Fin (q + 2), ∑ k : Fin (q + 1),
        ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (q + 2))))
        (t := (Finset.univ : Finset (Fin (q + 1)))) (f := fun j i ↦ ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i))),
      ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Finset.sum_nbij' (fwd q) (bwd q) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _)
      (fun p _ ↦ bwd_fwd q p) (fun p _ ↦ fwd_bwd q p) (fun _ _ ↦ rfl)
  simp only [h1, Finset.sum_sub_distrib] at h2 ⊢
  rw [h2, h3]

end GlobalTheory.CompanionTheory.HopfLe.PrismComb
