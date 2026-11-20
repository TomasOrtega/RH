import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Dich

open GlobalTheory.CompanionTheory.BZPhiPhi GlobalTheory.CompanionTheory.BZPhiPG.Cells

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `Fin.ext (blockIndex_false_val m j a)`.
-/
theorem blockIndex_false_eq (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (⟨a.1, by have := a.2; omega⟩ : Fin (m + j)) :=
  Fin.ext (blockIndex_false_val m j a)

/- English proof (translation)
The claim follows from `Fin.ext (blockIndex_true_val m (j + 1) _)`.
-/
theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ =
      Fin.castSucc (⟨m + b.1, by have := b.2; omega⟩ : Fin (m + (j + 1))) :=
  Fin.ext (blockIndex_true_val m (j + 1) _)

/- English proof (translation)
Rewrite using `[mem_mirabolicParabolic_iff]`. Introduce `b a`. Rewrite using `[blockIndex_false_eq]`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[blockIndex_true_last, (mem_Mir_iff k _).1 x.2]`. Conclude with `Pi.single_eq_of_ne (Fin.castSucc_ne_last _) _`. Consider the case `cast b`. Rewrite using `[blockIndex_true_castSucc]`. Conclude with `h _ _ (by simp) (by simp)`.
-/
theorem mem_mirabolicParabolic_of (m j : ℕ) (x : Mir k (m + (j + 1)))
    (h : ∀ r c : Fin (m + j + 1), ¬ r.val < m → c.val < m →
      ((x : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) = 0) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  rw [blockIndex_false_eq]
  induction b using Fin.lastCases with
  | last =>
    rw [blockIndex_true_last, (mem_Mir_iff k _).1 x.2]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last _) _
  | cast b =>
    rw [blockIndex_true_castSucc]
    exact h _ _ (by simp) (by simp)

/- English proof (translation)
Use `mem_mirabolicParabolic_of m j x fun r c hr hc => ?_` and prove the remaining obligations. Rewrite using `[hx]`. Use `unip_castSucc_castSucc _ v _ _ ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hr hc`.
-/
theorem unip_mem_HGP (m j : ℕ) (x : Mir k (m + (j + 1))) (v : Fin (m + (j + 1)) → k)
    (hx : (x : GL (Fin (m + (j + 1) + 1)) k) = unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  refine mem_mirabolicParabolic_of m j x fun r c hr hc => ?_
  rw [hx]
  refine unip_castSucc_castSucc _ v _ _ ?_
  rintro rfl
  exact hr hc

/- English proof (translation)
Use `show (1 + colMat k n v) i c = _`. Rewrite using `[Matrix.add_apply]`. Distinguish the cases in `hc : c = Fin.last n`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [colMat, hc]`.

Consider the case `cast r => simp [colMat, hc, h hc r rfl]`. Simplify using `[colMat, hc]`.
-/
theorem unip_entry (n : ℕ) (v : Fin n → k) (i c : Fin (n + 1))
    (h : c = Fin.last n → ∀ r : Fin n, i = Fin.castSucc r → v r = 0) :
    (unip k n (Multiplicative.ofAdd v)).val i c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i c := by
  show (1 + colMat k n v) i c = _
  rw [Matrix.add_apply]
  by_cases hc : c = Fin.last n
  · induction i using Fin.lastCases with
    | last => simp [colMat, hc]
    | cast r => simp [colMat, hc, h hc r rfl]
  · simp [colMat, hc]

/- English proof (translation)
Establish `hone : ∀ (x : Bool) (a b : Two (Fin m) (Fin (j + 1 + 1)) x), (1 : Matrix _ _ k) (eGP m (j + 1) ⟨x, a⟩) (eGP m (j + 1) ⟨x, b⟩) = (1 : Matrix (Two (Fin m) (Fin (j + 1 + 1)) x) _ k) a b`. Introduce `x a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne]`. Introduce `e`. Conclude with `hab (by simpa using (eGP m (j + 1)).injective e)`. Use `Prod.ext ?_ (Subtype.ext ?_)` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `a b`. Use `show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨false, a⟩) (eGP m (j + 1) ⟨false, b⟩) = _`. Rewrite using `[hy, unip_entry, hone]`. Both sides reduce to the same expression. Introduce `e`.

Conclude with `absurd e (blockIndex_false_ne_last m (j + 1) b)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨true, a⟩) (eGP m (j + 1) ⟨true, b⟩) = _`. Rewrite using `[hy, unip_entry, hone]`.

Both sides reduce to the same expression. Introduce `_ r e`. Use `hv r ?_` and prove the remaining obligations. Use `congrArg Fin.val e` as an intermediate fact. Rewrite `this` using `[blockIndex_true_val]`.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem gpProj_unip (m j : ℕ) (y : MirabolicParabolic k m (j + 1)) (v : Fin (m + (j + 1)) → k)
    (hv : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → v r = 0)
    (hy : ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) =
      unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    gpProj k m (j + 1) y = 1 := by
  have hone : ∀ (x : Bool) (a b : Two (Fin m) (Fin (j + 1 + 1)) x),
      (1 : Matrix _ _ k) (eGP m (j + 1) ⟨x, a⟩) (eGP m (j + 1) ⟨x, b⟩) =
        (1 : Matrix (Two (Fin m) (Fin (j + 1 + 1)) x) _ k) a b := by
    intro x a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro e
      exact hab (by simpa using (eGP m (j + 1)).injective e)
  refine Prod.ext ?_ (Subtype.ext ?_)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨false, a⟩)
      (eGP m (j + 1) ⟨false, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro e
      exact absurd e (blockIndex_false_ne_last m (j + 1) b)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨true, a⟩)
      (eGP m (j + 1) ⟨true, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro _ r e
      refine hv r ?_
      have := congrArg Fin.val e
      rw [blockIndex_true_val] at this
      simp at this
      omega

end

section

variable {k : Type} [Field k]

/- English proof (translation)
Take `⟨v, A, hp, hA⟩ : ∃ v A, (g : GL (Fin (n + 2)) k) = unip k (n + 1) v * glEmb k (n + 1) A ∧ A = mirabolicProjection k (n + 1) g` from `⟨_, _, eq_unip_glEmb g, rfl⟩`. Rewrite using `[map_inv (mirabolicProjection k (n + 1)), ← hA]`. Establish `e` using `glEmb_mul_unip' k (n + 1) A⁻¹ (Multiplicative.ofAdd w)`. Establish `c : (unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * unip k (n + 1) v = unip k (n + 1) (Multiplicative.ofAdd w)`. Rewrite using `[← map_inv, ← map_mul, ← map_mul]`.

Use `congr 1`. Rewrite using `[mul_comm _ (Multiplicative.ofAdd w), mul_assoc]`. Simplify using the standard rewrite rules. Simplify using `only [Subgroup.coe_mul, InvMemClass.coe_inv, unipM_val, hp]`. Simplify using `only [toAdd_ofAdd] at e`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[c, map_inv]`. Use `_ = _ := by`. Rewrite using `[e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]`.
-/
theorem conj_unip (n : ℕ) (g : Mir k (n + 1)) (w : Fin (n + 1) → k) :
    ((g⁻¹ * unipM k n (Multiplicative.ofAdd w) * g : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd
        (((mirabolicProjection k (n + 1) g⁻¹ : GL (Fin (n + 1)) k) : Matrix _ _ k).mulVec w)) := by
  obtain ⟨v, A, hp, hA⟩ : ∃ v A, (g : GL (Fin (n + 2)) k) = unip k (n + 1) v * glEmb k (n + 1) A ∧
      A = mirabolicProjection k (n + 1) g := ⟨_, _, eq_unip_glEmb g, rfl⟩
  rw [map_inv (mirabolicProjection k (n + 1)), ← hA]
  have e := glEmb_mul_unip' k (n + 1) A⁻¹ (Multiplicative.ofAdd w)
  have c : (unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * unip k (n + 1) v =
      unip k (n + 1) (Multiplicative.ofAdd w) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm _ (Multiplicative.ofAdd w), mul_assoc]
    simp
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unipM_val, hp]
  simp only [toAdd_ofAdd] at e
  calc (unip k (n + 1) v * glEmb k (n + 1) A)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
        (unip k (n + 1) v * glEmb k (n + 1) A)
      = (glEmb k (n + 1) A)⁻¹ * ((unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
          unip k (n + 1) v) * glEmb k (n + 1) A := by group
    _ = glEmb k (n + 1) A⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * glEmb k (n + 1) A := by
        rw [c, map_inv]
    _ = _ := by
        rw [e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

end

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ m j g`. Distinguish the cases in `hl : ∃ l : Fin (m + j + 1), l.val < m ∧ rowQ k (m + j) g⁻¹ l ≠ 0`. Take `⟨l, hlm, hrl⟩` from `hl`. Take `⟨t, ht⟩` from `(AddChar.ne_one_iff).1 hψ`. Set `w : Fin (m + j + 1) → k` to `Pi.single l (t / rowQ k (m + j) g⁻¹ l)`.

Set `X : Mir k (m + j + 1)` to `unipM k (m + j) (Multiplicative.ofAdd w)`. Establish `hu` using `conj_unip (m + j) g w`. Establish `hmem : g⁻¹ * X * g ∈ MirUin k (m + j + 1)` using `⟨_, hu.symm⟩`. Establish `hgx : g * (g⁻¹ * X * g) * g⁻¹ = X` using `by group`. Establish `hX : X ∈ MirabolicParabolic k m (j + 1)` using `unip_mem_HGP m j X w rfl`.

Establish `hw : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → w r = 0`. Introduce `r hr`. Use `Pi.single_eq_of_ne ?_ _` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hr hlm`.

Use `Or.inr ⟨⟨g⁻¹ * X * g, hmem⟩, hgx.symm ▸ hX, ?_, ?_⟩` and prove the remaining obligations. Use `gpProj_unip m j _ w hw ?_ show ((g * (g⁻¹ * X * g) * g⁻¹ : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = _` and prove the remaining obligations. Rewrite using `[hgx]`. Both sides reduce to the same expression. Rewrite using `[mirChar_eq k ψ (m + j) _ _ hu]`.

Establish `e : (((mirabolicProjection k (m + j + 1) g⁻¹ : GL (Fin (m + j + 1)) k) : Matrix _ _ k).mulVec w) (Fin.last (m + j)) = t` using `by show rowQ k (m + j) g⁻¹ ⬝ᵥ w = t`. Simplify using `only [w, dotProduct_single]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [toAdd_ofAdd, e]`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Use `congrArg Units.val h` as an intermediate fact. Conclude with `Circle.ext (by simpa using this)`. Establish `hr0 : ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0`. Introduce `l hlm`.

Assume the negation of the conclusion as `h`. Conclude with `hl ⟨l, hlm, h⟩`. Take `⟨c, hc⟩` from `row_ne_zero (mirabolicProjection k (m + j + 1) g⁻¹) (Fin.last (m + j))`. Establish `hc' : rowQ k (m + j) g⁻¹ c ≠ 0` using `hc`. Establish `hcs : ¬ c.val < m` using `fun h => hc' (hr0 c h)`.

Establish `hlast : ¬ (Fin.last (m + j)).val < m` using `by simp`. Take `⟨B, hBj, hB⟩` from `exists_row (fun x : Fin (m + j + 1) => x.val < m) (rowQ k (m + j) g⁻¹) c (Fin.last (m + j)) hc' (by simp only [hcs, hlast]) (fun _ x hx => hr0 x hx)`. Set `d : Mir k (m + j + 1)` to `levi k (m + j + 1) B`. Establish `hd : d ∈ MirabolicParabolic k m (j + 1)`. Use `mem_mirabolicParabolic_of m j d fun r c hr hc => ?_` and prove the remaining obligations.

Conclude with `(glEmb_castSucc_castSucc _ B _ _).trans (hB _ _ hr hc)`. Establish `hrow : rowQ k (m + j) g⁻¹ = rowQ k (m + j) d`. Use function extensionality and compare the values at `c`. Conclude with `(congrFun hBj c).symm.trans (glEmb_castSucc_castSucc _ B _ _).symm`. Establish `hQ` using `mul_inv_mem_Q_of_rowQ_eq (m + j) g⁻¹ d hrow`.

Establish `hQ' : d * g ∈ Q k (m + j)`. Use `(Q k (m + j)).inv_mem hQ` as an intermediate fact. Simplify using `using this`. Take `⟨v, hp⟩ : ∃ v, ((d * g : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = unip k (m + j + 1) (Multiplicative.ofAdd v) * glEmb k (m + j + 1) (mirabolicProjection k (m + j + 1) (d * g))` from `⟨_, eq_unip_glEmb (d * g)⟩`. Set `uM : Mir k (m + j + 1)` to `unipM k (m + j) (Multiplicative.ofAdd v)`.

Establish `huM : uM ∈ MirabolicParabolic k m (j + 1)` using `unip_mem_HGP m j uM v rfl`. Use `Or.inl ⟨d⁻¹ * uM, (MirabolicParabolic k m (j + 1)).mul_mem ((MirabolicParabolic k m (j + 1)).inv_mem hd) huM, qProj k (m + j) ⟨d * g, hQ'⟩, ?_⟩` and prove the remaining obligations. Establish `e : d * g = uM * embedding₂ k (m + j) (qProj k (m + j) ⟨d * g, hQ'⟩)` using `Subtype.ext hp`. Rewrite using `[mul_assoc, ← e]`. Use `group`.
-/
theorem dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  intro k _ _ _ _ ψ hψ m j g
  by_cases hl : ∃ l : Fin (m + j + 1), l.val < m ∧ rowQ k (m + j) g⁻¹ l ≠ 0
  · obtain ⟨l, hlm, hrl⟩ := hl
    obtain ⟨t, ht⟩ := (AddChar.ne_one_iff).1 hψ
    let w : Fin (m + j + 1) → k := Pi.single l (t / rowQ k (m + j) g⁻¹ l)
    let X : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd w)
    have hu := conj_unip (m + j) g w
    have hmem : g⁻¹ * X * g ∈ MirUin k (m + j + 1) := ⟨_, hu.symm⟩
    have hgx : g * (g⁻¹ * X * g) * g⁻¹ = X := by group
    have hX : X ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j X w rfl
    have hw : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → w r = 0 := by
      intro r hr
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      exact hr hlm
    refine Or.inr ⟨⟨g⁻¹ * X * g, hmem⟩, hgx.symm ▸ hX, ?_, ?_⟩
    · refine gpProj_unip m j _ w hw ?_
      show ((g * (g⁻¹ * X * g) * g⁻¹ : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = _
      rw [hgx]
      rfl
    · rw [mirChar_eq k ψ (m + j) _ _ hu]
      have e : (((mirabolicProjection k (m + j + 1) g⁻¹ : GL (Fin (m + j + 1)) k) : Matrix _ _ k).mulVec w)
          (Fin.last (m + j)) = t := by
        show rowQ k (m + j) g⁻¹ ⬝ᵥ w = t
        simp only [w, dotProduct_single]
        field_simp
      simp only [toAdd_ofAdd, e]
      intro h
      apply ht
      have := congrArg Units.val h
      exact Circle.ext (by simpa using this)
  · have hr0 : ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0 := by
      intro l hlm
      by_contra h
      exact hl ⟨l, hlm, h⟩
    obtain ⟨c, hc⟩ := row_ne_zero (mirabolicProjection k (m + j + 1) g⁻¹) (Fin.last (m + j))
    have hc' : rowQ k (m + j) g⁻¹ c ≠ 0 := hc
    have hcs : ¬ c.val < m := fun h => hc' (hr0 c h)
    have hlast : ¬ (Fin.last (m + j)).val < m := by simp
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin (m + j + 1) => x.val < m) (rowQ k (m + j) g⁻¹) c
      (Fin.last (m + j)) hc' (by simp only [hcs, hlast]) (fun _ x hx => hr0 x hx)
    let d : Mir k (m + j + 1) := levi k (m + j + 1) B
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      refine mem_mirabolicParabolic_of m j d fun r c hr hc => ?_
      exact (glEmb_castSucc_castSucc _ B _ _).trans (hB _ _ hr hc)
    have hrow : rowQ k (m + j) g⁻¹ = rowQ k (m + j) d := by
      funext c
      exact (congrFun hBj c).symm.trans (glEmb_castSucc_castSucc _ B _ _).symm
    have hQ := mul_inv_mem_Q_of_rowQ_eq (m + j) g⁻¹ d hrow
    have hQ' : d * g ∈ Q k (m + j) := by
      have := (Q k (m + j)).inv_mem hQ
      simpa using this
    obtain ⟨v, hp⟩ : ∃ v, ((d * g : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) =
        unip k (m + j + 1) (Multiplicative.ofAdd v) * glEmb k (m + j + 1) (mirabolicProjection k (m + j + 1) (d * g)) :=
      ⟨_, eq_unip_glEmb (d * g)⟩
    let uM : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd v)
    have huM : uM ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j uM v rfl
    refine Or.inl ⟨d⁻¹ * uM, (MirabolicParabolic k m (j + 1)).mul_mem ((MirabolicParabolic k m (j + 1)).inv_mem hd) huM,
      qProj k (m + j) ⟨d * g, hQ'⟩, ?_⟩
    have e : d * g = uM * embedding₂ k (m + j) (qProj k (m + j) ⟨d * g, hQ'⟩) := Subtype.ext hp
    rw [mul_assoc, ← e]
    group

end GlobalTheory.CompanionTheory.LeibPhi.Dich
