import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwO

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def uM (n : ℕ) (w : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd w), MirU_le_Mir k _ ⟨_, rfl⟩⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show unip k n (Multiplicative.ofAdd (v + w)) = unip k n (Multiplicative.ofAdd v) * unip k n (Multiplicative.ofAdd w)`. Rewrite using `[ofAdd_add, map_mul]`.
-/
theorem uM_add (n : ℕ) (v w : Fin n → k) : uM k n (v + w) = uM k n v * uM k n w := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (v + w)) = unip k n (Multiplicative.ofAdd v) * unip k n (Multiplicative.ofAdd w)
  rw [ofAdd_add, map_mul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `glEmb_mul_unip' k n g (Multiplicative.ofAdd v)`.
-/
theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (v : Fin n → k) :
    levi k n g * uM k n v = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec v) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd v)

/- English proof (translation)
Simplify using `[ePG]`.
-/
theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

/- English proof (translation)
Simplify using `[ePG, finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Establish `h1 : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = Fin.last (i + (t + 1))` using `Fin.ext (by simp)`. Establish `h2 : (ePG i (t + 1)).symm (Fin.last (i + (t + 1))) = ⟨false, Fin.last i⟩`. Rewrite using `[Equiv.symm_apply_eq, ePG_false_last]`. Use `show eGP (i + 1) t ((ePG i (t + 1)).symm ((finCongr _) (Fin.last ((i + 1) + t)))) = _`. Rewrite using `[h1, h2]`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[eGP, stdSum]`.
-/
theorem piPerm_last (i t : ℕ) : piPerm i t (Fin.last ((i + 1) + t)) = Fin.castAdd (t + 1) (Fin.last i) := by
  have h1 : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = Fin.last (i + (t + 1)) :=
    Fin.ext (by simp)
  have h2 : (ePG i (t + 1)).symm (Fin.last (i + (t + 1))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq, ePG_false_last]
  show eGP (i + 1) t ((ePG i (t + 1)).symm ((finCongr _) (Fin.last ((i + 1) + t)))) = _
  rw [h1, h2]
  apply Fin.ext
  simp [eGP, stdSum]

def cVec (i t : ℕ) (c : Fin (i + 1) → k) : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unip_entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[ePG_true_val]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  intro h
  have := congrArg Fin.val h
  rw [ePG_true_val] at this
  simp at this
  omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ePG_true_val]`. Simplify using the standard rewrite rules.
-/
theorem ePG_true_eq_natAdd (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
  apply Fin.ext
  rw [ePG_true_val]
  simp

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[ePG_false_castSucc_val]`. Simplify using the standard rewrite rules.
-/
theorem ePG_false_eq_castAdd (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) := by
  apply Fin.ext
  rw [ePG_false_castSucc_val]
  simp

/- English proof (translation)
Use `show ((uM k _ (cVec i t c) : Mir k _) : GL _ k) ∈ parab k (ePG (i + 1) (t + 1))`. Rewrite using `[mem_parab_iff]`. Introduce and unpack `(_ | _) (_ | _) x y hab`. Conclude with `absurd hab (by decide)`. Conclude with `absurd hab (by decide)`.

Rewrite using `[unip_entry]`. Establish `hne : ePG (i + 1) (t + 1) ⟨true, x⟩ ≠ ePG (i + 1) (t + 1) ⟨false, y⟩`. Introduce `h`. Simplify using `using (ePG (i + 1) (t + 1)).injective h`. Rewrite using `[Matrix.one_apply_ne hne, zero_add]`.

Simplify using `only [colMat]`. Use `split_ifs with hl`. Rewrite using `[ePG_true_eq_natAdd, Fin.lastCases_castSucc, cVec, Fin.append_right]`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Conclude with `absurd hab (by decide)`.
-/
theorem uM_mem_HPG (i t : ℕ) (c : Fin (i + 1) → k) : uM k _ (cVec i t c) ∈ HPG k (i + 1) (t + 1) := by
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  rintro (_ | _) (_ | _) x y hab
  · exact absurd hab (by decide)
  · exact absurd hab (by decide)
  · rw [unip_entry]
    have hne : ePG (i + 1) (t + 1) ⟨true, x⟩ ≠ ePG (i + 1) (t + 1) ⟨false, y⟩ := by
      intro h
      simpa using (ePG (i + 1) (t + 1)).injective h
    rw [Matrix.one_apply_ne hne, zero_add]
    simp only [colMat]
    split_ifs with hl
    · rw [ePG_true_eq_natAdd, Fin.lastCases_castSucc, cVec, Fin.append_right]
      rfl
    · rfl
  · exact absurd hab (by decide)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) = (1 : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b + colMat k (i + 1) c a b`. Rewrite using `[unip_entry]`.

Use `congr 1`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne]`.

Introduce `h`. Apply `hab` to reduce the goal to its premises. Simplify using `using (ePG (i + 1) (t + 1)).injective h`. Simplify using `only [colMat]`. Distinguish the cases in `hb : b = Fin.last (i + 1)`.

Substitute `hb` using the available equality. Rewrite using `[if_pos (ePG_false_last _ _), if_pos rfl]`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => rw [ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]`. Consider the case `cast a`.

Rewrite using `[ePG_false_eq_castAdd, Fin.lastCases_castSucc, Fin.lastCases_castSucc, cVec, Fin.append_left]`. Rewrite using `[if_neg (fun h => hb ((ePG_false_eq_last_iff _ _ _).1 h)), if_neg hb]`.
-/
theorem pgProj_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).1 = uM k (i + 1) c := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
    (1 : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b + colMat k (i + 1) c a b
  rw [unip_entry]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro h
      apply hab
      simpa using (ePG (i + 1) (t + 1)).injective h
  · simp only [colMat]
    by_cases hb : b = Fin.last (i + 1)
    · subst hb
      rw [if_pos (ePG_false_last _ _), if_pos rfl]
      induction a using Fin.lastCases with
      | last => rw [ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast a =>
        rw [ePG_false_eq_castAdd, Fin.lastCases_castSucc, Fin.lastCases_castSucc, cVec, Fin.append_left]
    · rw [if_neg (fun h => hb ((ePG_false_eq_last_iff _ _ _).1 h)), if_neg hb]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b`. Rewrite using `[unip_entry]`. Establish `h0 : colMat k _ (cVec i t c) (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = 0`.

Simplify using `only [colMat]`. Rewrite using `[if_neg (ePG_true_ne_last _ _ _)]`. Rewrite using `[h0, add_zero]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne]`. Introduce `h`. Apply `hab` to reduce the goal to its premises. Simplify using `using (ePG (i + 1) (t + 1)).injective h`.
-/
theorem pgProj_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) =
    (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
  rw [unip_entry]
  have h0 : colMat k _ (cVec i t c) (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = 0 := by
    simp only [colMat]
    rw [if_neg (ePG_true_ne_last _ _ _)]
  rw [h0, add_zero]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro h
    apply hab
    simpa using (ePG (i + 1) (t + 1)).injective h

/- English proof (translation)
Establish `h : Matrix.GeneralLinearGroup.det ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1`. Use `ext`. Use `show Matrix.det (1 + colMat k n w) = 1`. Establish `hT : (1 + colMat k n w).BlockTriangular id`. Introduce `a b hab`.

Establish `hab' : b < a` using `hab`. Establish `hb : b ≠ Fin.last n` using `fun h => by`. Rewrite `hab'` using `[h]`. Conclude with `absurd hab' (not_lt.2 (Fin.le_last a))`. Simplify using `[colMat, hb, Matrix.one_apply_ne hab'.ne']`.

Rewrite using `[Matrix.det_of_upperTriangular hT]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simp [colMat]`. Consider the case `cast a => simp [colMat, Fin.castSucc_ne_last]`.

Use `show detChar (Fin (n + 1)) (absPow k ((s : ℝ) : ℂ)) ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1`. Simplify using `[detChar, h]`.
-/
theorem det_uM (n : ℕ) (s : ℝ) (w : Fin n → k) : dpowM n s (uM k n w) = 1 := by
  have h : Matrix.GeneralLinearGroup.det ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    ext
    show Matrix.det (1 + colMat k n w) = 1
    have hT : (1 + colMat k n w).BlockTriangular id := by
      intro a b hab
      have hab' : b < a := hab
      have hb : b ≠ Fin.last n := fun h => by
        rw [h] at hab'
        exact absurd hab' (not_lt.2 (Fin.le_last a))
      simp [colMat, hb, Matrix.one_apply_ne hab'.ne']
    rw [Matrix.det_of_upperTriangular hT]
    refine Finset.prod_eq_one fun a _ => ?_
    induction a using Fin.lastCases with
    | last => simp [colMat]
    | cast a => simp [colMat, Fin.castSucc_ne_last]
  show detChar (Fin (n + 1)) (absPow k ((s : ℝ) : ℂ)) ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1
  simp [detChar, h]

/- English proof (translation)
Establish `hm : uM k (n + 1) w ∈ MirUin k (n + 1)` using `⟨_, rfl⟩`. Establish `hc` using `mirChar_eq k ψ n ⟨uM k (n + 1) w, hm⟩ (Multiplicative.ofAdd w) rfl`. Establish `hk : τ.ρ (uM k (n + 1) w) a - ((mirChar k ψ n ⟨uM k (n + 1) w, hm⟩ : ℂˣ) : ℂ) • a ∈ twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)` using `Submodule.subset_span ⟨⟨uM k (n + 1) w, hm⟩, a, rfl⟩`. Establish `h` using `(Submodule.Quotient.mk_eq_zero _).2 hk`. Rewrite `h` using `[Submodule.Quotient.mk_sub, sub_eq_zero, Submodule.Quotient.mk_smul, hc]`.

Conclude with `h`.
-/
theorem mk_twist {n : ℕ} (ψ : AddChar k Circle) (τ : MRep k (n + 1)) (w : Fin (n + 1) → k) (a : τ.V) :
    (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ (τ.ρ (uM k (n + 1) w) a) =
      ((Circle.toUnits (ψ (w (Fin.last n))) : ℂˣ) : ℂ) •
        (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ a := by
  have hm : uM k (n + 1) w ∈ MirUin k (n + 1) := ⟨_, rfl⟩
  have hc := mirChar_eq k ψ n ⟨uM k (n + 1) w, hm⟩ (Multiplicative.ofAdd w) rfl
  have hk : τ.ρ (uM k (n + 1) w) a - ((mirChar k ψ n ⟨uM k (n + 1) w, hm⟩ : ℂˣ) : ℂ) • a ∈
      twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n) :=
    Submodule.subset_span ⟨⟨uM k (n + 1) w, hm⟩, a, rfl⟩
  have h := (Submodule.Quotient.mk_eq_zero _).2 hk
  rw [Submodule.Quotient.mk_sub, sub_eq_zero, Submodule.Quotient.mk_smul, hc] at h
  exact h

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]`. Consider the case `tmul a b`. Establish `e : sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (a ⊗ₜ b) = τ.ρ (uM k (i + 1) c) a ⊗ₜ b`.

Establish `h1` using `extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) a b`. Rewrite `h1` using `[pgProj_fst, pgProj_snd, map_one]`. Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (uM k (i + 1) c) a = τ.ρ (uM k (i + 1) c) a` using `by show twist τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) (uM k (i + 1) c) a = _`. Simplify using `[twist, det_uM]`.

Rewrite using `[h2]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `show (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (uM k (i + 1) c) a) ⊗ₜ[ℂ] b = _`. Rewrite using `[mk_twist]`.

Conclude with `(TensorProduct.smul_tmul' _ _ _).symm`.
-/
theorem qO_sigX {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (c : Fin (i + 1) → k)
    (z : τ.V ⊗[ℂ] σ.V) :
    qO τ σ ψ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ z) =
      ((Circle.toUnits (ψ (c (Fin.last i))) : ℂˣ) : ℂ) • qO τ σ ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | tmul a b =>
    have e : sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (a ⊗ₜ b) = τ.ρ (uM k (i + 1) c) a ⊗ₜ b := by
      have h1 := extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) a b
      rw [pgProj_fst, pgProj_snd, map_one] at h1
      refine h1.trans ?_
      have h2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (uM k (i + 1) c) a = τ.ρ (uM k (i + 1) c) a := by
        show twist τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) (uM k (i + 1) c) a = _
        simp [twist, det_uM]
      rw [h2]
      rfl
    rw [e]
    show (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (uM k (i + 1) c) a) ⊗ₜ[ℂ] b = _
    rw [mk_twist]
    exact (TensorProduct.smul_tmul' _ _ _).symm

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp [cVec]`.
-/
theorem vec_split (i t : ℕ) (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k) :
    Fin.append (0 : Fin (i + 1) → k) d + Fin.append c d' =
      cVec i t c + Fin.append (0 : Fin (i + 1) → k) (d + d') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp [cVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) :
    dEmb k i t d = uM k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl

/- English proof (translation)
Establish `hy : wEl k i t * sEmb k _ m₀ = levi k _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k))` using `(map_mul (levi k _) _ _).symm`. Establish `h1` using `levi_mul_uM _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) v`. Rewrite `h1` using `[hw]`. Rewrite using `[hy, mul_assoc, h1, dEmb_eq, dEmb_eq, ← mul_assoc, ← mul_assoc]`. Use `congr 1`.

Establish `e1` using `uM_add (k := k) ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) (Fin.append c d')`. Establish `e2` using `uM_add (k := k) ((i + 1) + (t + 1)) (cVec i t c) (Fin.append (0 : Fin (i + 1) → k) (d + d'))`. Rewrite `e1` using `[vec_split]`. Conclude with `e1.symm.trans e2`.
-/
theorem mul_uM_eq (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k)
    (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    dEmb k i t d * (wEl k i t * sEmb k _ m₀) * uM k _ v =
      uM k ((i + 1) + (t + 1)) (cVec i t c) * (dEmb k i t (d + d') * (wEl k i t * sEmb k _ m₀)) := by
  have hy : wEl k i t * sEmb k _ m₀ = levi k _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) :=
    (map_mul (levi k _) _ _).symm
  have h1 := levi_mul_uM _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) v
  rw [hw] at h1
  rw [hy, mul_assoc, h1, dEmb_eq, dEmb_eq, ← mul_assoc, ← mul_assoc]
  congr 1
  have e1 := uM_add (k := k) ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) (Fin.append c d')
  have e2 := uM_add (k := k) ((i + 1) + (t + 1)) (cVec i t c) (Fin.append (0 : Fin (i + 1) → k) (d + d'))
  rw [vec_split] at e1
  exact e1.symm.trans e2

/- English proof (translation)
Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Use `show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹).mulVec _ _ = _`. Rewrite using `[Matrix.permMatrix_mulVec, ← piPerm_last]`. Establish `h : (piPerm i t)⁻¹ (piPerm i t (Fin.last ((i + 1) + t))) = Fin.last ((i + 1) + t)` using `by simp`. Simplify using `only [Function.comp, h]`.

Conclude with `mulVec_last_of_mem k _ m₀.2 v`.
-/
theorem w_coord (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v
      (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹).mulVec _ _ = _
  rw [Matrix.permMatrix_mulVec, ← piPerm_last]
  have h : (piPerm i t)⁻¹ (piPerm i t (Fin.last ((i + 1) + t))) = Fin.last ((i + 1) + t) := by simp
  simp only [Function.comp, h]
  exact mulVec_last_of_mem k _ m₀.2 v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evX_cInd {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + (t + 1))) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

/- English proof (translation)
The claim follows from `(f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h p`.
-/
theorem evX_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (p : Mir k ((i + 1) + (t + 1))) :
    evX f ((h : Mir k ((i + 1) + (t + 1))) * p) = sigX τ σ h (evX f p) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h p

/- English proof (translation)
Use `letI : MeasurableSpace (Fin (t + 1) → k) := borel _`. Use `haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩`. Use `haveI : (muD k (t + 1)).IsAddHaarMeasure := by`. Unfold `muD`. Use `infer_instance`.

Take `⟨hl, hc⟩` from `GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y`. Set `φ : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V` to `fun d => evX f (dEmb k i t d * y)`. Establish `hl' : IsLocallyConstant (φ ∘ (· + d'))` using `hl.comp_continuous (continuous_add_right d')`. Establish `hc' : HasCompactSupport (φ ∘ (· + d'))` using `hc.comp_homeomorph (Homeomorph.addRight d')`. Establish `e : F = T ∘ (φ ∘ (· + d'))` using `funext hF`.

Establish `h2 : GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) (φ ∘ (· + d')) = GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) φ` using `GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1)) (MeasureTheory.measurePreserving_add_right (muD k (t + 1)) d') hl`. Rewrite using `[e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T hl' hc', h2]`. Both sides reduce to the same expression.
-/
theorem intO_translate {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) (T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] τ.V ⊗[ℂ] σ.V) (d' : Fin (t + 1) → k)
    (F : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V) (hF : ∀ d, F d = T (evX f (dEmb k i t (d + d') * y))) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) F = T (intO f y) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  obtain ⟨hl, hc⟩ := GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y
  let φ : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V := fun d => evX f (dEmb k i t d * y)
  have hl' : IsLocallyConstant (φ ∘ (· + d')) := hl.comp_continuous (continuous_add_right d')
  have hc' : HasCompactSupport (φ ∘ (· + d')) := hc.comp_homeomorph (Homeomorph.addRight d')
  have e : F = T ∘ (φ ∘ (· + d')) := funext hF
  have h2 : GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) (φ ∘ (· + d')) = GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) φ :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1))
      (MeasureTheory.measurePreserving_add_right (muD k (t + 1)) d') hl
  rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T hl' hc', h2]
  rfl

/- English proof (translation)
Use `intO_translate f _ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) d' _ fun d => ?_` and prove the remaining obligations. Establish `e` using `mul_uM_eq i t m₀ v c d d' hw`. Use `(congrArg (evX f) e).trans ?_` and prove the remaining obligations. Conclude with `evX_mul f ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ _`.
-/
theorem intO_cInd_uM_eq_sigX_intO {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) (c : Fin (i + 1) → k) (d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀) =
      sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (intO f (wEl k i t * sEmb k _ m₀)) := by
  refine intO_translate f _ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) d' _ fun d => ?_
  have e := mul_uM_eq i t m₀ v c d d' hw
  refine (congrArg (evX f) e).trans ?_
  exact evX_mul f ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ _

def wV (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) : Fin ((i + 1) + (t + 1)) → k :=
  ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v

/- English proof (translation)
Establish `hsplit : wV i t m₀ v = Fin.append (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j)) (fun j => wV i t m₀ v (Fin.natAdd (i + 1) j))` using `(Fin.append_castAdd_natAdd).symm`. Establish `hc : wV i t m₀ v (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t))` using `w_coord i t m₀ v`. Establish `h1` using `intO_cInd_uM_eq_sigX_intO ψ τ σ f m₀ v _ _ hsplit`. Establish `h2` using `qO_sigX ψ τ σ (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j)) (intO f (wEl k i t * sEmb k _ m₀))`. Use `(congrArg (qO τ σ ψ) h1).trans (h2.trans ?_)` and prove the remaining obligations.

Conclude with `congrArg (fun x => ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀))) hc`.
-/
theorem qO_intO_cInd {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    qO τ σ ψ (intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀)) =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) •
        qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀)) := by
  have hsplit : wV i t m₀ v = Fin.append (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j))
      (fun j => wV i t m₀ v (Fin.natAdd (i + 1) j)) :=
    (Fin.append_castAdd_natAdd).symm
  have hc : wV i t m₀ v (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := w_coord i t m₀ v
  have h1 := intO_cInd_uM_eq_sigX_intO ψ τ σ f m₀ v _ _ hsplit
  have h2 := qO_sigX ψ τ σ (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j)) (intO f (wEl k i t * sEmb k _ m₀))
  refine (congrArg (qO τ σ ψ) h1).trans (h2.trans ?_)
  exact congrArg (fun x => ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀))) hc

/- English proof (translation)
The claim follows from `(congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • z) (qO_intO_cInd ψ τ σ f (castM k (by omega) m) v)).trans (smul_comm _ _ _)`.
-/
theorem eO_cInd_uM {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m :=
  (congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • z)
    (qO_intO_cInd ψ τ σ f (castM k (by omega) m) v)).trans (smul_comm _ _ _)

/- English proof (translation)
The claim follows from `u.2`.
-/
theorem exists_unip {n : ℕ} (u : MirUin k n) : ∃ v : Multiplicative (Fin n → k),
    unip k n v = ((u : Mir k n) : GL (Fin (n + 1)) k) := u.2

/- English proof (translation)
Substitute `hg` using the available equality. Conclude with `eO_cInd_uM ψ τ σ f v m`.
-/
theorem eO_of_eq {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (g : Mir k ((i + 1) + (t + 1))) (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1)))
    (hg : g = uM k ((i + 1) + (t + 1)) v) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m := by
  subst hg
  exact eO_cInd_uM ψ τ σ f v m

/- English proof (translation)
Use `Exists.elim (exists_unip u) fun v hv => ?_` and prove the remaining obligations. Establish `hu : (u : Mir k ((i + 1) + (t + 1))) = uM k ((i + 1) + (t + 1)) v.toAdd` using `Subtype.ext hv.symm`. Establish `hθ` using `mirChar_eq k ψ ((i + 1) + t) u v hv.symm`. Use `(eO_of_eq ψ τ σ f _ v.toAdd m hu).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun x : ℂˣ => (x : ℂ) • eO ψ f m) hθ.symm`.
-/
theorem eO_cInd_eq_mirChar_smul {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) m =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f m := by
  refine Exists.elim (exists_unip u) fun v hv => ?_
  have hu : (u : Mir k ((i + 1) + (t + 1))) = uM k ((i + 1) + (t + 1)) v.toAdd := Subtype.ext hv.symm
  have hθ := mirChar_eq k ψ ((i + 1) + t) u v hv.symm
  refine (eO_of_eq ψ τ σ f _ v.toAdd m hu).trans ?_
  exact congrArg (fun x : ℂˣ => (x : ℂ) • eO ψ f m) hθ.symm

/- English proof (translation)
Introduce `k _ _ _ _ i t ψ _ τ σ _ _ u f`. Use function extensionality and compare the values at `m`. Conclude with `eO_cInd_eq_mirChar_smul ψ τ σ u f m`.
-/
theorem eO_cInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ u f
  funext m
  exact eO_cInd_eq_mirChar_smul ψ τ σ u f m

end GlobalTheory.CompanionTheory.BZPhiPG.TwO

end
