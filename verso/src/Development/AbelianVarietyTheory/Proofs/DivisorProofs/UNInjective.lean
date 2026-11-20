import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev parB {a b n : ℕ} (h : a + b = n) (w : Pl E) : Subgroup (GLw n w) :=
  GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def levH {a b n : ℕ} (h : a + b = n) (w : Pl E) : parB h w →* GLw a w × GLw b w :=
  (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom.comp
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.mem_parab_two]`. Introduce `j i`. Rewrite using `[CtLevel.blk_val]`. Use `show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0`. Simplify using the standard rewrite rules.
-/
theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blk h w m X ∈ parB h w := by
  rw [GlobalTheory.SmGL.mem_parab_two]
  intro j i
  rw [CtLevel.blk_val]
  show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
    (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0
  simp

/- English proof (translation)
Use `ext1`. Rewrite using `[Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]`. Use `congr 1`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_add]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]`.
-/
theorem blk_mul_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  ext1
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]

/- English proof (translation)
Use `ext1`. Rewrite using `[CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one, reindex_apply, submatrix_one_equiv]`. Both sides reduce to the same expression.
-/
theorem blk_one_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) : blk h w 1 0 = 1 := by
  ext1
  rw [CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one,
    reindex_apply, submatrix_one_equiv]
  rfl

def sM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* parB h w where
  toFun m := ⟨blk h w m 0, blk_mem h w m 0⟩
  map_one' := Subtype.ext (blk_one_zero h w)
  map_mul' m m' := Subtype.ext (by simp [blk_mul_blk])

def uN {a b n : ℕ} (h : a + b = n) (w : Pl E) : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parB h w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), blk_mem h w 1 _⟩
  map_one' := Subtype.ext (by simpa using blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp [blk_mul_blk, add_comm])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    (sM h w m : GLw n w) = blk h w m 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uN_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    (uN h w X : GLw n w) = blk h w 1 (Multiplicative.toAdd X) := rfl

/- English proof (translation)
Rewrite using `[Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]`. Simplify using the standard rewrite rules.
-/
theorem sM_mul_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    ((sM h w m * uN h w X : parB h w) : GLw n w) = blk h w m (Multiplicative.toAdd X) := by
  rw [Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]
  simp

/- English proof (translation)
Establish `key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x), ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matri …`. Introduce `x i j`. Rewrite using `[GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]`. Consider the cases of `x`. Use `show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _`.

Simplify using `[GlobalTheory.SmGL.leviTwo]`. Use `show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _`. Simplify using `[GlobalTheory.SmGL.leviTwo]`. Establish `: GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m`. Use function extensionality and compare the values at `x`.

Conclude with `Units.ext (Matrix.ext fun i j => key x i j)`. Simplify using `only [levH, MonoidHom.coe_comp, Function.comp_apply, this]`. Simplify using the standard rewrite rules.
-/
theorem levH_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : levH h w ⟨blk h w m X, blk_mem h w m X⟩ = m := by
  have key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x :
        GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j = ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]
    cases x
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
  have : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ =
      GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    funext x; exact Units.ext (Matrix.ext fun i j => key x i j)
  simp only [levH, MonoidHom.coe_comp, Function.comp_apply, this]
  simp

/- English proof (translation)
The claim follows from `levH_blk h w m 0`.
-/
theorem levH_sM {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : levH h w (sM h w m) = m :=
  levH_blk h w m 0

/- English proof (translation)
The claim follows from `levH_blk h w 1 _`.
-/
theorem levH_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    levH h w (uN h w X) = 1 :=
  levH_blk h w 1 _

/- English proof (translation)
Introduce `X Y hXY`. Establish `h1` using `congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY`. Simplify using `only [uN_val, CtLevel.blk_val] at h1`. Establish `h2` using `congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)`. Simplify using `using h2`.
-/
theorem uN_injective {a b n : ℕ} (h : a + b = n) (w : Pl E) : Function.Injective (uN h w) := by
  intro X Y hXY
  have h1 := congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY
  simp only [uN_val, CtLevel.blk_val] at h1
  have h2 := congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)
  simpa using h2

/- English proof (translation)
Establish `hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1`. Use `congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp` as an intermediate fact. Simplify `this` using `[levH]`. Establish `hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x), ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) = (1 : Matrix (GlobalTheory.SmG …`. Introduce `x i j`.

Rewrite using `[← GlobalTheory.SmGL.leviProj_apply, hl]`. Both sides reduce to the same expression. Establish `h0` using `(GlobalTheory.SmGL.mem_parab_two _).1 p.2`. Use `⟨Multiplicative.ofAdd ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂), Subtype.ext (Units.ext ?_)⟩` and prove the remaining obligations. Rewrite using `[uN_val, CtLevel.blk_val]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(CtLevel.blkEq h).surjective i`. Take `⟨j, rfl⟩` from `(CtLevel.blkEq h).surjective j`. Rewrite using `[reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`.

Rewrite using `[fromBlocks_apply₁₁]`. Conclude with `(hd false i j).symm`. Simplify using `[toBlocks₁₂]`. Rewrite using `[fromBlocks_apply₂₁]`. Conclude with `(h0 i j).symm`.

Rewrite using `[fromBlocks_apply₂₂]`. Conclude with `(hd true i j).symm`.
-/
theorem exists_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (p : parB h w) (hp : levH h w p = 1) :
    ∃ X, uN h w X = p := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1 := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp
    simpa [levH] using this
  have hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) =
        (1 : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [← GlobalTheory.SmGL.leviProj_apply, hl]
    rfl
  have h0 := (GlobalTheory.SmGL.mem_parab_two _).1 p.2
  refine ⟨Multiplicative.ofAdd
    ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂),
    Subtype.ext (Units.ext ?_)⟩
  rw [uN_val, CtLevel.blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]
    exact (hd false i j).symm
  · simp [toBlocks₁₂]
  · rw [fromBlocks_apply₂₁]
    exact (h0 i j).symm
  · rw [fromBlocks_apply₂₂]
    exact (hd true i j).symm

end GlobalTheory.LeviFubini
