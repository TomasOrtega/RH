import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

noncomputable section

open scoped Matrix

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

def pm (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => if f b = a then 1 else 0

/- English proof (translation)
Use extensionality with `a c`. Simplify using `[pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]`.
-/
theorem pm_mul (f h : Fin n → Fin n) : pm R f * pm R h = pm R (f ∘ h) := by
  ext a c
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[pm]`. Simplify using `[pm, Matrix.one_apply, h, Ne.symm h]`.
-/
theorem pm_id : pm R (id : Fin n → Fin n) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [pm]
  · simp [pm, Matrix.one_apply, h, Ne.symm h]

def pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) : GL (Fin n) R :=
  ⟨pm R f, pm R g, by rw [pm_mul, show f ∘ g = id from funext h1, pm_id],
    by rw [pm_mul, show g ∘ f = id from funext h2, pm_id]⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [pm, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `h : a = f k`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem pm_mulVec (f : Fin n → Fin n) (k : Fin n) :
    pm R f *ᵥ (fun a : Fin n => if a = k then (1 : R) else 0) = fun a => if a = f k then 1 else 0 := by
  funext a
  simp only [pm, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : a = f k
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `key : g c = k ↔ c = f k` using `⟨fun e => by rw [← e, h1], fun e => by rw [e, h2]⟩`. Simplify using `only [pm, Matrix.vecMul, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [key]`.
-/
theorem vecMul_pm (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (k : Fin n) :
    (fun a : Fin n => if a = k then (1 : R) else 0) ᵥ* pm R g = fun c => if c = f k then 1 else 0 := by
  funext c
  have key : g c = k ↔ c = f k := ⟨fun e => by rw [← e, h1], fun e => by rw [e, h2]⟩
  simp only [pm, Matrix.vecMul, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [key]

/- English proof (translation)
Establish `key : ∀ b, f b = a ↔ b = g a` using `fun b => ⟨fun e => by rw [← e, h2], fun e => by rw [e, h1]⟩`. Simplify using `only [pm, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem pm_mul_apply (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k)
    (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) : (pm R f * M) a c = M (g a) c := by
  have key : ∀ b, f b = a ↔ b = g a := fun b => ⟨fun e => by rw [← e, h2], fun e => by rw [e, h1]⟩
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Simplify using `[pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]`.
-/
theorem mul_pm_apply (f : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (M * pm R f) a c = M a (f c) := by
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

variable (m i : ℕ) (hmi : m + i < n)

def cyc (k : Fin n) : Fin n :=
  if h : m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then ⟨k + 1, by omega⟩
  else if (k : ℕ) = m + i then ⟨m, by omega⟩ else k

def cycInv (k : Fin n) : Fin n :=
  if h : m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then ⟨k - 1, by omega⟩
  else if (k : ℕ) = m then ⟨m + i, hmi⟩ else k

/- English proof (translation)
Apply the tactic sequence `unfold cyc; split_ifs <;> rfl`.
-/
theorem cyc_val (k : Fin n) : (cyc m i hmi k : ℕ) =
    if m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then (k : ℕ) + 1 else if (k : ℕ) = m + i then m else k := by
  unfold cyc; split_ifs <;> rfl

/- English proof (translation)
Apply the tactic sequence `unfold cycInv; split_ifs <;> rfl`.
-/
theorem cycInv_val (k : Fin n) : (cycInv m i hmi k : ℕ) =
    if m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then (k : ℕ) - 1 else if (k : ℕ) = m then m + i else k := by
  unfold cycInv; split_ifs <;> rfl

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[cyc_val, cycInv_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem cyc_cycInv (k : Fin n) : cyc m i hmi (cycInv m i hmi k) = k := by
  apply Fin.ext
  rw [cyc_val, cycInv_val]
  split_ifs <;> omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[cycInv_val, cyc_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem cycInv_cyc (k : Fin n) : cycInv m i hmi (cyc m i hmi k) = k := by
  apply Fin.ext
  rw [cycInv_val, cyc_val]
  split_ifs <;> omega

end GlobalTheory.HomStab.FacePerm

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

/- English proof (translation)
Substitute `hL` using the available equality. Establish `e1 : (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0) = fun a => if a = ⟨K, hK⟩ then 1 else 0`. Use function extensionality and compare the values at `a`. Simplify using `[Fin.ext_iff]`. Establish `e2 : (fun a : Fin n => if (a : ℕ) = (f ⟨K, hK⟩ : ℕ) then (1 : R) else 0) = fun a => if a = f ⟨K, hK⟩ then 1 else 0`.

Use function extensionality and compare the values at `a`. Simplify using `[Fin.ext_iff]`. Rewrite using `[e1, e2]`. Conclude with `Prod.ext (pm_mulVec R f ⟨K, hK⟩) (vecMul_pm R f g h1 h2 ⟨K, hK⟩)`.
-/
theorem pairAct_pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (K : ℕ)
    (hK : K < n) (L : ℕ) (hL : (f ⟨K, hK⟩ : ℕ) = L) :
    pairAct R n (pmU R f g h1 h2) ((fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0)) =
    ((fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0)) := by
  subst hL
  have e1 : (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0) = fun a => if a = ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  have e2 : (fun a : Fin n => if (a : ℕ) = (f ⟨K, hK⟩ : ℕ) then (1 : R) else 0) = fun a => if a = f ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  rw [e1, e2]
  exact Prod.ext (pm_mulVec R f ⟨K, hK⟩) (vecMul_pm R f g h1 h2 ⟨K, hK⟩)

end GlobalTheory.HomStab.FacePerm

open GlobalTheory.HomStab.FacePerm in

/- English proof (translation)
Introduce `R _ n p h i`. Establish `hi` using `i.isLt`. Establish `hmi : n - (p + 1) + (i : ℕ) < n` using `by omega`. Use `⟨pmU R (cyc (n - (p + 1)) i hmi) (cycInv (n - (p + 1)) i hmi) (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show ((stdList R n (p + 1)).eraseIdx i).map (pairAct R n _) = stdList R n p` to reduce the goal to its premises.

Apply `List.ext_getElem` to reduce the goal to its premises. Apply the tactic sequence `simp only [List.length_map, List.length_eraseIdx, stdList, List.length_ofFn] split_ifs <;> omega`. Introduce `j h1 h2`. Establish `hjp : j < p` using `by simpa [stdList] using h2`. Simplify using `only [List.getElem_map, List.getElem_eraseIdx, stdList, List.getElem_ofFn, Fin.val_mk]`.

Use `split_ifs with hj`. Apply the tactic sequence `exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)`. Apply the tactic sequence `exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)`. Introduce `x`. Establish `lo1 : ∀ k : Fin n, ((cyc (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1))`.

Introduce `k`. Rewrite using `[cyc_val]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `lo2 : ∀ k : Fin n, ((cycInv (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1))`. Introduce `k`.

Rewrite using `[cycInv_val]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `fx1 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cyc (n - (p + 1)) i hmi k = k`. Introduce `k hk`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[cyc_val]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `fx2 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cycInv (n - (p + 1)) i hmi k = k`. Introduce `k hk`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[cycInv_val]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `bij : ∀ a c : Fin n, cycInv (n - (p + 1)) i hmi a = c ↔ a = cyc (n - (p + 1)) i hmi c`. Introduce `a c`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Rewrite using `[cyc_cycInv]`. Introduce and unpack `rfl`. Rewrite using `[cycInv_cyc]`. Use extensionality with `a c`.

Rewrite using `[Units.val_mul, Units.val_mul]`. Use `show ((pm R (cyc (n - (p + 1)) i hmi) * padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) : Matrix (Fin n) (Fin n) R)) a c = ((padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) * pm R (cyc (n - (p + 1)) i hmi) : Matrix (Fin n) (Fin n) R)) a c`. Rewrite using `[pm_mul_apply R _ _ (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), mul_pm_apply]`. Distinguish the cases in `ha : (a : ℕ) < n - (p + 1)`. Distinguish the cases in `hc : (c : ℕ) < n - (p + 1)`.

Rewrite using `[fx2 a ha, fx1 c hc]`. Simplify using `only [padMat, Matrix.of_apply]`. Rewrite using `[dif_neg, dif_neg]`. Apply the tactic sequence `all_goals first`. Consider the case `simp only [bij]`.

Consider the case `(rw [lo1]; omega)`. Consider the case `(rw [lo2]; omega)`. Simplify using `only [padMat, Matrix.of_apply]`. Rewrite using `[dif_neg, dif_neg]`. Apply the tactic sequence `all_goals first`.

Consider the case `simp only [bij]`. Consider the case `(rw [lo1]; omega)`. Consider the case `(rw [lo2]; omega)`.
-/
theorem GlobalTheory.HomStab.exists_perm_face_stdSeq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  intro R _ n p h i
  have hi := i.isLt
  have hmi : n - (p + 1) + (i : ℕ) < n := by omega
  refine ⟨pmU R (cyc (n - (p + 1)) i hmi) (cycInv (n - (p + 1)) i hmi) (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), ?_, ?_⟩
  · apply Subtype.ext
    show ((stdList R n (p + 1)).eraseIdx i).map (pairAct R n _) = stdList R n p
    apply List.ext_getElem
    · simp only [List.length_map, List.length_eraseIdx, stdList, List.length_ofFn]
      split_ifs <;> omega
    · intro j h1 h2
      have hjp : j < p := by simpa [stdList] using h2
      simp only [List.getElem_map, List.getElem_eraseIdx, stdList, List.getElem_ofFn, Fin.val_mk]
      split_ifs with hj
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
  · intro x
    have lo1 : ∀ k : Fin n, ((cyc (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cyc_val]
      split_ifs <;> omega
    have lo2 : ∀ k : Fin n, ((cycInv (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cycInv_val]
      split_ifs <;> omega
    have fx1 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cyc (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cyc_val]
      split_ifs <;> omega
    have fx2 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cycInv (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cycInv_val]
      split_ifs <;> omega
    have bij : ∀ a c : Fin n, cycInv (n - (p + 1)) i hmi a = c ↔ a = cyc (n - (p + 1)) i hmi c := by
      intro a c
      constructor
      · rintro rfl
        rw [cyc_cycInv]
      · rintro rfl
        rw [cycInv_cyc]
    ext a c
    rw [Units.val_mul, Units.val_mul]
    show ((pm R (cyc (n - (p + 1)) i hmi) * padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) : Matrix (Fin n) (Fin n) R)) a c = ((padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) * pm R (cyc (n - (p + 1)) i hmi) : Matrix (Fin n) (Fin n) R)) a c
    rw [pm_mul_apply R _ _ (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), mul_pm_apply]
    by_cases ha : (a : ℕ) < n - (p + 1)
    · by_cases hc : (c : ℕ) < n - (p + 1)
      · rw [fx2 a ha, fx1 c hc]
      · simp only [padMat, Matrix.of_apply]
        rw [dif_neg, dif_neg]
        all_goals first
          | simp only [bij]
          | (rw [lo1]; omega)
          | (rw [lo2]; omega)
    · simp only [padMat, Matrix.of_apply]
      rw [dif_neg, dif_neg]
      all_goals first
        | simp only [bij]
        | (rw [lo1]; omega)
        | (rw [lo2]; omega)

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.exists_perm_face_stdSeq`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.pairAct_pmU`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.cycInv_cyc`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.cyc_cycInv`.

Consider the case `exact @GlobalTheory.HomStab.FacePerm.cycInv_val`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.cyc_val`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.mul_pm_apply`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.pm_mul_apply`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.vecMul_pm`.

Consider the case `exact @GlobalTheory.HomStab.FacePerm.pm_mulVec`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.pm_id`. Consider the case `exact @GlobalTheory.HomStab.FacePerm.pm_mul`.
-/
theorem _root_.GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  first
  | exact @GlobalTheory.HomStab.exists_perm_face_stdSeq
  | exact @GlobalTheory.HomStab.FacePerm.pairAct_pmU
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_cyc
  | exact @GlobalTheory.HomStab.FacePerm.cyc_cycInv
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_val
  | exact @GlobalTheory.HomStab.FacePerm.cyc_val
  | exact @GlobalTheory.HomStab.FacePerm.mul_pm_apply
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul_apply
  | exact @GlobalTheory.HomStab.FacePerm.vecMul_pm
  | exact @GlobalTheory.HomStab.FacePerm.pm_mulVec
  | exact @GlobalTheory.HomStab.FacePerm.pm_id
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul
end
