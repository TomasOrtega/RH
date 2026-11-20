import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

section Span

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`.

Introduce `i hi`. Establish `hij : i ≠ j` using `fun h => hi (h ▸ hj)`. Simplify using `[Pi.single_apply, hij]`. Consider the case `zero => intro i _`. Both sides reduce to the same expression.

Consider the case `add x y _ _ hx hy => intro i hi`. Simplify using `[hx i hi, hy i hi]`. Consider the case `smul a x _ hx => intro i hi`. Simplify using `[hx i hi]`. Introduce `h`.

Establish `hv : v = ∑ i, v i • Pi.single i (1 : K)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i ∈ s`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)`. Simplify using `[h i hi]`.
-/
theorem mem_span_single (s : Set ι) (v : ι → K) :
    v ∈ Submodule.span K ((fun j => Pi.single j (1 : K)) '' s) ↔ ∀ i, i ∉ s → v i = 0 := by
  classical
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp [Pi.single_apply, hij]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro h
    have hv : v = ∑ i, v i • Pi.single i (1 : K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · simp [h i hi]

end Span

variable {K : Type} [Field K] {r k : ℕ}

def pe (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inl ⟨b, h⟩ else zI

def ColFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), m *ᵥ Pi.single (pe b) 1 - Pi.single (pe b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b})

/- English proof (translation)
Unfold `ColFlag`. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Establish `himg : (fun a => Pi.single (pe (k` using `k) a) (1 : K)) '' {a | a < b} = (fun j => Pi.single j (1 : K)) '' (pe '' {a | a < b}) := by`. Rewrite using `[Set.image_image]`. Rewrite using `[himg, mem_span_single]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `h1 : i ∉ pe '' {a | a < b} ↔ ∀ a, a < b → i ≠ pe a`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]`. Conclude with `forall_congr' fun a => imp_congr_right fun _ => ne_comm`. Rewrite using `[h1]`.

Use `imp_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero]`.
-/
theorem colFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    ColFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pe a) →
      m i (pe b) = if i = pe b then 1 else 0 := by
  classical
  unfold ColFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pe '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pe '' {a | a < b} ↔ ∀ a, a < b → i ≠ pe a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero]

/- English proof (translation)
Establish `h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r` using `i.isLt`. Unfold `pe`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem pe_castSucc (i : Fin r) : pe (k := k) (Fin.castSucc i) = Sum.inl i := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pe
  rw [dif_pos h]
  rfl

/- English proof (translation)
Unfold `pe`. Rewrite using `[dif_neg (by simp)]`.
-/
theorem pe_last : pe (r := r) (k := k) (Fin.last r) = zI := by
  unfold pe
  rw [dif_neg (by simp)]

/- English proof (translation)
Unfold `pe`. Rewrite using `[dif_pos (by omega)]`.
-/
theorem pe_inl_of_lt {a b : Fin (r + 1)} (h : a < b) : pe (k := k) a = Sum.inl ⟨a, by omega⟩ := by
  unfold pe
  rw [dif_pos (by omega)]

/- English proof (translation)
Rewrite using `[colFlag_iff']`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `Hc : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inl a) → m i (Sum.inl j) = if i = Sum.inl j then 1 else 0`. Introduce `j i hi`.

Use `H (Fin.castSucc j) i (fun a ha => by` as an intermediate fact. Rewrite using `[pe_inl_of_lt ha]`. Conclude with `hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))`. Rewrite `this` using `[pe_castSucc]`. Then use the resulting hypothesis. Establish `Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inl a) → m i zI = if i = zI then 1 else 0`.

Introduce `i hi`. Use `H (Fin.last r) i (fun a ha => by` as an intermediate fact. Rewrite using `[pe_inl_of_lt ha]`. Conclude with `hi _)`. Rewrite `this` using `[pe_last]`. Then use the resulting hypothesis.

Establish `Hinr : ∀ (j : Fin r) (x : Mid k ⊕ Fin r), m (Sum.inr x) (Sum.inl j) = 0`. Introduce `j x`. Use `Hc j (Sum.inr x) (fun a _ h => Sum.inr_ne_inl h)` as an intermediate fact. Simplify using `using this`. Unfold `ColC IsUpUni`.

Use `⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Use `Hc j (Sum.inl i) (fun a ha h => by` as an intermediate fact. Consider the cases of `h`.

Conclude with `lt_irrefl _ (ha.trans hij'))`. Simplify `this` using `[b11, hij'.ne']`. Use `Hc a (Sum.inl a) (fun a' ha' h => by` as an intermediate fact. Consider the cases of `h`. Conclude with `lt_irrefl _ ha')`.

Simplify `this` using `[b11]`. Use extensionality with `a b`. Simplify using `[b21, Hinr]`. Use extensionality with `a b`. Simplify using `[b31, Hinr]`.

Simplify `Hz (wI w) (fun a h => Sum.inr_ne_inl h)` using `[wI, zI]`. Simplify using `using Hz zI (fun a h => Sum.inr_ne_inl h)`. Simplify `Hz (Sum.inr (Sum.inr j)) (fun a h => Sum.inr_ne_inl h)` using `[zI]`. Introduce `hC`. Unfold `ColC IsUpUni at hC`.

Take `⟨⟨hup, hdiag⟩, h21, h31, hw, hzz, hf⟩` from `hC`. Introduce `b i hi`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[pe_last]`.

Break down `i with i' | ((w | u) | j)` into its components or cases. Conclude with `absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_last i'))`. Simplify `hw w` using `[wI, zI]`. Consider the cases of `u`. Simplify `hzz` using `[zI]`.

Simplify `hf j` using `[zI]`. Consider the case `cast j`. Rewrite using `[pe_castSucc]`. Break down `i with i' | (x | j')` into its components or cases. Break down `lt_trichotomy i' j with h | rfl | h` into its components or cases.

Conclude with `absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_castSucc_iff.mpr h))`. Simplify `hdiag i'` using `[b11]`. Use `hup h` as an intermediate fact. Simplify `this` using `[b11, h.ne']`. Simplify `congrFun (congrFun h21 x) j` using `[b21]`.

Simplify `congrFun (congrFun h31 j') j` using `[b31]`.
-/
theorem colFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : ColFlag m ↔ ColC m := by
  classical
  rw [colFlag_iff']
  constructor
  · intro H
    have Hc : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inl a) →
        m i (Sum.inl j) = if i = Sum.inl j then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pe_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inl a) → m i zI = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _)
      rwa [pe_last] at this
    have Hinr : ∀ (j : Fin r) (x : Mid k ⊕ Fin r), m (Sum.inr x) (Sum.inl j) = 0 := by
      intro j x
      have := Hc j (Sum.inr x) (fun a _ h => Sum.inr_ne_inl h)
      simpa using this
    unfold ColC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro i j hij
      have hij' : j < i := hij
      have := Hc j (Sum.inl i) (fun a ha h => by
        cases h
        exact lt_irrefl _ (ha.trans hij'))
      simpa [b11, hij'.ne'] using this
    · have := Hc a (Sum.inl a) (fun a' ha' h => by
        cases h
        exact lt_irrefl _ ha')
      simpa [b11] using this
    · ext a b
      simp [b21, Hinr]
    · ext a b
      simp [b31, Hinr]
    · simpa [wI, zI] using Hz (wI w) (fun a h => Sum.inr_ne_inl h)
    · simpa using Hz zI (fun a h => Sum.inr_ne_inl h)
    · simpa [zI] using Hz (Sum.inr (Sum.inr j)) (fun a h => Sum.inr_ne_inl h)
  · intro hC
    unfold ColC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h21, h31, hw, hzz, hf⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pe_last]
      rcases i with i' | ((w | u) | j)
      · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_last i'))
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · simpa [zI] using hf j
    | cast j =>
      rw [pe_castSucc]
      rcases i with i' | (x | j')
      · rcases lt_trichotomy i' j with h | rfl | h
        · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_castSucc_iff.mpr h))
        · simpa [b11] using hdiag i'
        · have := hup h
          simpa [b11, h.ne'] using this
      · simpa [b21] using congrFun (congrFun h21 x) j
      · simpa [b31] using congrFun (congrFun h31 j') j

end MassDataIdxStIm
