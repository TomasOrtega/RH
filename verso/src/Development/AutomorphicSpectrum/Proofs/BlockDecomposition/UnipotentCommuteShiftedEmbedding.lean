import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomy

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.DConj

open GlobalTheory.CompanionTheory.BZPhiPG.Cells GlobalTheory.CompanionTheory.LeibPhi GlobalTheory.CompanionTheory.BZPhiPhi
open GlobalTheory.CompanionTheory.BZMir.GpExists (unip_apply_of_ne_last unip_apply_last_last)

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_false_val]; simp)`.
-/
theorem blockIndex_false_eq_castAdd₂ (i t : ℕ) (a : Fin (i + 1)) :
    eGP (i + 1) t ⟨false, a⟩ = (Fin.castAdd (t + 1) a : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_false_val]; simp)

/- English proof (translation)
The claim follows from `Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val]; simp)`.
-/
theorem blockIndex_true_eq_natAdd₂ (i t : ℕ) (b : Fin (t + 1)) :
    eGP (i + 1) t ⟨true, b⟩ = (Fin.natAdd (i + 1) b : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val]; simp)

/- English proof (translation)
Use `show (leviProj k (eGP m j) (hgpIncl k m j g) true).val a b = _`. Rewrite using `[leviProj_apply]`. Both sides reduce to the same expression.
-/
theorem gpProj_snd_apply (m j : ℕ) (g : MirabolicParabolic k m j) (a b : Fin (j + 1)) :
    (((gpProj k m j g).2 : Mir k j) : GL (Fin (j + 1)) k).val a b =
      ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k).val (eGP m j ⟨true, a⟩) (eGP m j ⟨true, b⟩) := by
  show (leviProj k (eGP m j) (hgpIncl k m j g) true).val a b = _
  rw [leviProj_apply]
  rfl

/- English proof (translation)
Establish `hinv : ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k) = (((gpProj k (i + 1) t h⁻¹).2 : Mir k t) : GL (Fin (t + 1)) k)`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Establish `hcoe : (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) = (((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)` using `rfl`. Rewrite using `[hinv, hcoe]`.

Establish `hz : ∀ a : Fin (i + 1), ((((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)).val (Fin.natAdd (i + 1) x) (Fin.castAdd (t + 1) a) = 0`. Introduce `a`. Use `(mem_mirabolicParabolic_iff k _ _ _).1 (h⁻¹ : MirabolicParabolic k (i + 1) t).2 x a` as an intermediate fact. Rewrite `this` using `[blockIndex_true_eq_natAdd₂, blockIndex_false_eq_castAdd₂]`. Then use the resulting hypothesis. Use `show ∑ y : Fin ((i + 1) + (t + 1)), _ = ∑ y : Fin (t + 1), _`.

Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[gpProj_snd_apply, blockIndex_true_eq_natAdd₂, blockIndex_true_eq_natAdd₂]`.
-/
theorem inv_mulVec_natAdd (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) (x : Fin (t + 1)) :
    ((((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ
        (Fin.append (0 : Fin (i + 1) → k) d : Fin ((i + 1) + (t + 1)) → k)) (Fin.natAdd (i + 1) x) =
      (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) x := by
  have hinv : ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k) =
      (((gpProj k (i + 1) t h⁻¹).2 : Mir k t) : GL (Fin (t + 1)) k) := by
    rw [map_inv]
    rfl
  have hcoe : (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) =
      (((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) := rfl
  rw [hinv, hcoe]
  have hz : ∀ a : Fin (i + 1), ((((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) :
      GL (Fin ((i + 1) + t + 1)) k)).val (Fin.natAdd (i + 1) x) (Fin.castAdd (t + 1) a) = 0 := by
    intro a
    have := (mem_mirabolicParabolic_iff k _ _ _).1 (h⁻¹ : MirabolicParabolic k (i + 1) t).2 x a
    rwa [blockIndex_true_eq_natAdd₂, blockIndex_false_eq_castAdd₂] at this
  show ∑ y : Fin ((i + 1) + (t + 1)), _ = ∑ y : Fin (t + 1), _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gpProj_snd_apply, blockIndex_true_eq_natAdd₂, blockIndex_true_eq_natAdd₂]

/- English proof (translation)
Use `show (leviProj k (ePG I T) (hpgIncl k I T g) false).val a b = _`. Rewrite using `[leviProj_apply]`. Both sides reduce to the same expression.
-/
theorem pgProj_fst_apply (I T : ℕ) (g : HPG k I T) (a b : Fin (I + 1)) :
    (((pgProj k I T g).1 : Mir k I) : GL (Fin (I + 1)) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨false, a⟩) (ePG I T ⟨false, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) false).val a b = _
  rw [leviProj_apply]
  rfl

/- English proof (translation)
Use `show (leviProj k (ePG I T) (hpgIncl k I T g) true).val a b = _`. Rewrite using `[leviProj_apply]`. Both sides reduce to the same expression.
-/
theorem pgProj_snd_apply (I T : ℕ) (g : HPG k I T) (a b : Fin T) :
    ((pgProj k I T g).2 : GL (Fin T) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨true, a⟩) (ePG I T ⟨true, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) true).val a b = _
  rw [leviProj_apply]
  rfl

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne]`. Introduce `e`.

Conclude with `hab (by simpa using (ePG I T).injective e)`.
-/
theorem one_ePG (I T : ℕ) (x : Bool) (a b : Two (Fin (I + 1)) (Fin T) x) :
    (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨x, a⟩) (ePG I T ⟨x, b⟩) =
      (1 : Matrix (Two (Fin (I + 1)) (Fin T) x) (Two (Fin (I + 1)) (Fin T) x) k) a b := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro e
    exact hab (by simpa using (ePG I T).injective e)

variable (k) in

def uEl (i t : ℕ) (c : Fin (i + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

/- English proof (translation)
Use `mem_HPG_of (I := i + 1) (T := t + 1) (uEl k i t c) ?_ ?_` and prove the remaining obligations. Introduce `x y`. Use `unip_castSucc_castSucc _ _ _ _ ?_` and prove the remaining obligations. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Introduce `x`. Use `(unip_apply_castSucc_last k _ _ _).trans ?_` and prove the remaining obligations. Use `show (Fin.append c (0 : Fin (t + 1) → k)) (Fin.natAdd (i + 1) x) = 0`.

Simplify using the standard rewrite rules.
-/
theorem uEl_mem (i t : ℕ) (c : Fin (i + 1) → k) : uEl k i t c ∈ HPG k (i + 1) (t + 1) := by
  refine mem_HPG_of (I := i + 1) (T := t + 1) (uEl k i t c) ?_ ?_
  · intro x y
    refine unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro x
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show (Fin.append c (0 : Fin (t + 1) → k)) (Fin.natAdd (i + 1) x) = 0
    simp

/- English proof (translation)
Use `⟨Multiplicative.ofAdd c, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show (unip k (i + 1) (Multiplicative.ofAdd c)).val a b = (((pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k).val a b`. Rewrite using `[pgProj_fst_apply]`.

Use `show _ = (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[ePG_false_last]`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => rw [ePG_false_last, unip_apply_last_last, unip_apply_last_last]`. Consider the case `cast a`. Establish `e : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a)` using `Fin.ext (by rw [ePG_false_val]; simp)`. Rewrite using `[e, unip_apply_castSucc_last, unip_apply_castSucc_last]`. Simplify using the standard rewrite rules.

Consider the case `cast b`. Establish `hq : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc b⟩ ≠ Fin.last ((i + 1) + (t + 1))` using `fun h => Fin.castSucc_ne_last b ((ePG_false_eq_last_iff _ _ _).1 h)`. Rewrite using `[unip_apply_of_ne_last _ _ _ _ hq, unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last b), one_ePG]`.
-/
theorem uEl_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 ∈ MirUin k (i + 1) := by
  refine ⟨Multiplicative.ofAdd c, ?_⟩
  apply Units.ext
  ext a b
  show (unip k (i + 1) (Multiplicative.ofAdd c)).val a b =
    (((pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k).val a b
  rw [pgProj_fst_apply]
  show _ = (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _
  induction b using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    induction a using Fin.lastCases with
    | last => rw [ePG_false_last, unip_apply_last_last, unip_apply_last_last]
    | cast a =>
      have e : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) :=
        Fin.ext (by rw [ePG_false_val]; simp)
      rw [e, unip_apply_castSucc_last, unip_apply_castSucc_last]
      simp
  | cast b =>
    have hq : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := fun h =>
      Fin.castSucc_ne_last b ((ePG_false_eq_last_iff _ _ _).1 h)
    rw [unip_apply_of_ne_last _ _ _ _ hq, unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last b), one_ePG]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[pgProj_snd_apply]`. Use `show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _ = _`. Establish `hq : ePG (i + 1) (t + 1) ⟨true, b⟩ ≠ Fin.last ((i + 1) + (t + 1))`.

Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[ePG_true_val]`. Establish `hb` using `b.2`. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[unip_apply_of_ne_last _ _ _ _ hq, one_ePG]`. Both sides reduce to the same expression.
-/
theorem uEl_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  rw [pgProj_snd_apply]
  show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _ = _
  have hq : ePG (i + 1) (t + 1) ⟨true, b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := by
    intro h
    have := congrArg Fin.val h
    rw [ePG_true_val] at this
    have hb := b.2
    simp at this
    omega
  rw [unip_apply_of_ne_last _ _ _ _ hq, one_ePG]
  rfl

end

/- English proof (translation)
Introduce `k _ _ _ _ i t h d`. Set `A : GL (Fin ((i + 1) + t + 1)) k` to `((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)`. Set `v : Fin ((i + 1) + (t + 1)) → k` to `Fin.append (0 : Fin (i + 1) → k) d`. Set `w : Fin ((i + 1) + (t + 1)) → k` to `(A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v`. Set `c : Fin (i + 1) → k` to `fun x => w (Fin.castAdd (t + 1) x)`.

Set `e : Fin (t + 1) → k` to `((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d`. Set `a : Fin ((i + 1) + (t + 1)) → k` to `Fin.append c (0 : Fin (t + 1) → k)`. Set `b : Fin ((i + 1) + (t + 1)) → k` to `Fin.append (0 : Fin (i + 1) → k) e`. Establish `hsum : a + b = w`. Use function extensionality and compare the values at `x`.

Proceed by induction on `x using Fin.addCases with`. Consider the case `left x => simp [a, b, c]`. Consider the case `right x`. Simplify using `only [a, b, Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]`. Conclude with `(inv_mulVec_natAdd i t h d x).symm`.

Use `⟨⟨uEl k i t c, uEl_mem i t c⟩, uEl_fst i t c, uEl_snd i t c, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) = unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w)`. Rewrite using `[← map_mul, ← ofAdd_add, hsum]`. Establish `e3 : A.val *ᵥ w = v` using `by show A.val *ᵥ ((A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v) = v`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Establish `e2 : glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) = unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A`. Use `glEmb_mul_unip' k _ A (Multiplicative.ofAdd w)` as an intermediate fact. Rewrite `this` using `[toAdd_ofAdd, e3]`.

Conclude with `this`. Use `show unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A = glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b)`. Rewrite using `[mul_assoc, e1, e2]`.
-/
theorem dEmb_mul_sEmb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k), ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧ dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) * dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := by
  intro k _ _ _ _ i t h d
  let A : GL (Fin ((i + 1) + t + 1)) k := ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
  let v : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  let w : Fin ((i + 1) + (t + 1)) → k := (A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v
  let c : Fin (i + 1) → k := fun x => w (Fin.castAdd (t + 1) x)
  let e : Fin (t + 1) → k :=
    ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) e
  have hsum : a + b = w := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b, c]
    | right x =>
      simp only [a, b, Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]
      exact (inv_mulVec_natAdd i t h d x).symm
  refine ⟨⟨uEl k i t c, uEl_mem i t c⟩, uEl_fst i t c, uEl_snd i t c, ?_⟩
  apply Subtype.ext
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e3 : A.val *ᵥ w = v := by
    show A.val *ᵥ ((A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  have e2 : glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A := by
    have := glEmb_mul_unip' k _ A (Multiplicative.ofAdd w)
    rw [toAdd_ofAdd, e3] at this
    exact this
  show unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A =
    glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b)
  rw [mul_assoc, e1, e2]

end GlobalTheory.CompanionTheory.BZPhiPG.DConj

end
