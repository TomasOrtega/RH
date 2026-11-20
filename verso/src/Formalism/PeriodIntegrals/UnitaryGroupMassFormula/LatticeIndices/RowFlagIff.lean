import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSpanSingle

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {K : Type} [Field K] {r k : ℕ}

def pf (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inr (Sum.inr (Fin.rev ⟨b, h⟩)) else zI

def RowFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), mᵀ *ᵥ Pi.single (pf b) 1 - Pi.single (pf b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b})

/- English proof (translation)
Unfold `RowFlag`. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Establish `himg : (fun a => Pi.single (pf (k` using `k) a) (1 : K)) '' {a | a < b} = (fun j => Pi.single j (1 : K)) '' (pf '' {a | a < b}) := by`. Rewrite using `[Set.image_image]`. Rewrite using `[himg, mem_span_single]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `h1 : i ∉ pf '' {a | a < b} ↔ ∀ a, a < b → i ≠ pf a`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]`. Conclude with `forall_congr' fun a => imp_congr_right fun _ => ne_comm`. Rewrite using `[h1]`.

Use `imp_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero, Matrix.transpose_apply]`.
-/
theorem rowFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    RowFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pf a) →
      m (pf b) i = if i = pf b then 1 else 0 := by
  classical
  unfold RowFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pf '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pf '' {a | a < b} ↔ ∀ a, a < b → i ≠ pf a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero, Matrix.transpose_apply]

/- English proof (translation)
Establish `h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r` using `i.isLt`. Unfold `pf`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem pf_castSucc (i : Fin r) : pf (k := k) (Fin.castSucc i) = Sum.inr (Sum.inr (Fin.rev i)) := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pf
  rw [dif_pos h]
  rfl

/- English proof (translation)
Unfold `pf`. Rewrite using `[dif_neg (by simp)]`.
-/
theorem pf_last : pf (r := r) (k := k) (Fin.last r) = zI := by
  unfold pf
  rw [dif_neg (by simp)]

/- English proof (translation)
Unfold `pf`. Rewrite using `[dif_pos (by omega)]`.
-/
theorem pf_of_lt {a b : Fin (r + 1)} (h : a < b) :
    pf (k := k) a = Sum.inr (Sum.inr (Fin.rev ⟨a, by have := b.isLt; omega⟩)) := by
  unfold pf
  rw [dif_pos (by omega)]

/- English proof (translation)
Rewrite using `[rowFlag_iff']`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `Hr : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inr (Sum.inr (Fin.rev a))) → m (Sum.inr (Sum.inr (Fin.rev j))) i = if i = Sum.inr (Sum.inr (Fin.rev j)) then 1 else 0`. Introduce `j i hi`.

Use `H (Fin.castSucc j) i (fun a ha => by` as an intermediate fact. Rewrite using `[pf_of_lt ha]`. Conclude with `hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))`. Rewrite `this` using `[pf_castSucc]`. Then use the resulting hypothesis. Establish `Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inr (Sum.inr (Fin.rev a))) → m zI i = if i = zI then 1 else 0`.

Introduce `i hi`. Use `H (Fin.last r) i (fun a ha => by` as an intermediate fact. Rewrite using `[pf_of_lt ha]`. Conclude with `hi _)`. Rewrite `this` using `[pf_last]`. Then use the resulting hypothesis.

Establish `Hf : ∀ (a : Fin r) (i : Idx r k), (∀ b : Fin r, i = Sum.inr (Sum.inr b) → b ≤ a) → m (Sum.inr (Sum.inr a)) i = if i = Sum.inr (Sum.inr a) then 1 else 0`. Introduce `a i hi`. Use `Hr (Fin.rev a) i (fun c hc h => by` as an intermediate fact. Establish `hle` using `hi _ h`. Rewrite `hle` using `[Fin.le_def, Fin.val_rev]`.

Rewrite `hc` using `[Fin.lt_def, Fin.val_rev]`. Use `a.isLt` as an intermediate fact. Use `c.isLt` as an intermediate fact. Use the proof step `omega)`. Simplify `this` using `only [Fin.rev_rev]`.

Unfold `RowC IsUpUni`. Use `⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `hab' : b < a` using `hab`. Use `Hf a (Sum.inr (Sum.inr b)) (fun c h => by` as an intermediate fact.

Consider the cases of `h`. Conclude with `hab'.le)`. Simplify `this` using `[b33, hab'.ne]`. Use `Hf a (Sum.inr (Sum.inr a)) (fun c h => by` as an intermediate fact. Consider the cases of `h`.

Conclude with `le_rfl)`. Simplify `this` using `[b33]`. Use extensionality with `a b`. Simplify `Hf a (Sum.inl b) (fun c h => absurd h Sum.inl_ne_inr)` using `[b31]`. Use extensionality with `a x`.

Simplify `Hf a (Sum.inr (Sum.inl x)) (fun c h => by simp at h)` using `[b32]`. Simplify `Hz (wI w) (fun a h => by simp [wI] at h)` using `[wI, zI]`. Simplify using `using Hz zI (fun a h => by simp [zI] at h)`. Simplify `Hz (Sum.inl j) (fun a h => Sum.inl_ne_inr h)` using `[zI]`. Introduce `hC`.

Unfold `RowC IsUpUni at hC`. Take `⟨⟨hup, hdiag⟩, h31, h32, hw, hzz, hl⟩` from `hC`. Introduce `b i hi`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[pf_last]`. Break down `i with c | ((w | u) | j)` into its components or cases. Simplify `hl c` using `[zI]`. Simplify `hw w` using `[wI, zI]`. Consider the cases of `u`.

Simplify `hzz` using `[zI]`. Conclude with `absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ (Fin.castSucc_lt_last (Fin.rev j)))`. Consider the case `cast j`. Rewrite using `[pf_castSucc]`. Break down `i with c | (x | j')` into its components or cases.

Simplify `congrFun (congrFun h31 (Fin.rev j)) c` using `[b31]`. Simplify `congrFun (congrFun h32 (Fin.rev j)) x` using `[b32]`. Break down `lt_trichotomy j' (Fin.rev j) with h | h | h` into its components or cases. Establish `h0 : m (Sum.inr (Sum.inr (Fin.rev j))) (Sum.inr (Sum.inr j')) = 0` using `hup h`. Rewrite using `[h0, if_neg]`.

Simplify using `[h.ne]`. Substitute `h` using the available equality. Simplify `hdiag (Fin.rev j)` using `[b33]`. Establish `hlt : Fin.castSucc (Fin.rev j') < Fin.castSucc j`. Rewrite using `[Fin.castSucc_lt_castSucc_iff, Fin.lt_def, Fin.val_rev]`.

Rewrite `h` using `[Fin.lt_def, Fin.val_rev]`. Use `j.isLt` as an intermediate fact. Use `j'.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ hlt)`.
-/
theorem rowFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : RowFlag m ↔ RowC m := by
  classical
  rw [rowFlag_iff']
  constructor
  · intro H
    have Hr : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m (Sum.inr (Sum.inr (Fin.rev j))) i = if i = Sum.inr (Sum.inr (Fin.rev j)) then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pf_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m zI i = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _)
      rwa [pf_last] at this
    have Hf : ∀ (a : Fin r) (i : Idx r k), (∀ b : Fin r, i = Sum.inr (Sum.inr b) → b ≤ a) →
        m (Sum.inr (Sum.inr a)) i = if i = Sum.inr (Sum.inr a) then 1 else 0 := by
      intro a i hi
      have := Hr (Fin.rev a) i (fun c hc h => by
        have hle := hi _ h
        rw [Fin.le_def, Fin.val_rev] at hle
        rw [Fin.lt_def, Fin.val_rev] at hc
        have := a.isLt
        have := c.isLt
        omega)
      simpa only [Fin.rev_rev] using this
    unfold RowC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have := Hf a (Sum.inr (Sum.inr b)) (fun c h => by
        cases h
        exact hab'.le)
      simpa [b33, hab'.ne] using this
    · have := Hf a (Sum.inr (Sum.inr a)) (fun c h => by
        cases h
        exact le_rfl)
      simpa [b33] using this
    · ext a b
      simpa [b31] using Hf a (Sum.inl b) (fun c h => absurd h Sum.inl_ne_inr)
    · ext a x
      simpa [b32] using Hf a (Sum.inr (Sum.inl x)) (fun c h => by simp at h)
    · simpa [wI, zI] using Hz (wI w) (fun a h => by simp [wI] at h)
    · simpa using Hz zI (fun a h => by simp [zI] at h)
    · simpa [zI] using Hz (Sum.inl j) (fun a h => Sum.inl_ne_inr h)
  · intro hC
    unfold RowC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h31, h32, hw, hzz, hl⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pf_last]
      rcases i with c | ((w | u) | j)
      · simpa [zI] using hl c
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ (Fin.castSucc_lt_last (Fin.rev j)))
    | cast j =>
      rw [pf_castSucc]
      rcases i with c | (x | j')
      · simpa [b31] using congrFun (congrFun h31 (Fin.rev j)) c
      · simpa [b32] using congrFun (congrFun h32 (Fin.rev j)) x
      · rcases lt_trichotomy j' (Fin.rev j) with h | h | h
        · have h0 : m (Sum.inr (Sum.inr (Fin.rev j))) (Sum.inr (Sum.inr j')) = 0 := hup h
          rw [h0, if_neg]
          simp [h.ne]
        · subst h
          simpa [b33] using hdiag (Fin.rev j)
        · have hlt : Fin.castSucc (Fin.rev j') < Fin.castSucc j := by
            rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def, Fin.val_rev]
            rw [Fin.lt_def, Fin.val_rev] at h
            have := j.isLt
            have := j'.isLt
            omega
          exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ hlt)

end MassDataIdxStIm
