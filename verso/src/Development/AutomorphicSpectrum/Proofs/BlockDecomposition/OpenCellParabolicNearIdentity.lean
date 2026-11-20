import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

/- English proof (translation)
The claim follows from `Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])`.
-/
theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

/- English proof (translation)
The claim follows from `(Units.continuous_val.comp continuous_subtype_val).matrix_elem a b`.
-/
theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

/- English proof (translation)
Establish `hh` using `(mem_Mir_iff k _).1 p.2`. Use `show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1`. Rewrite using `[hh]`. Simplify using `[eLast]`.
-/
theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]`. Simplify using `[colMat]`. Introduce `l _ hl`. Simplify using `[colMat, hl]`. Simplify using the standard rewrite rules.
-/
theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = Fin.last _`. Substitute `hb` using the available equality. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simpa [colMat] using continuous_const`.

Consider the case `cast a`. Proceed by induction on `a using Fin.addCases with`. Consider the case `left a => simpa [colMat] using continuous_const`. Consider the case `right a`. Establish `e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a`.

Introduce `d`. Unfold `colMat`. Rewrite using `[if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]`. Conclude with `(continuous_apply a).congr fun d => (e d).symm`. Simplify `continuous_const` using `[colMat, hb]`.
-/
theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

/- English proof (translation)
Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `continuous_const.add (continuous_colMat_append i t)`. Conclude with `continuous_const.sub (continuous_colMat_append i t)`.
-/
theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1`. Establish `: Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `induction a using Fin.addCases <;> simp`. Rewrite using `[this, colMat_zero, add_zero]`.
-/
theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

/- English proof (translation)
The claim follows from `continuous_pi fun b => (continuous_ent _ _).neg`.
-/
theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

/- English proof (translation)
Use function extensionality and compare the values at `b`. Establish `h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0` using `Matrix.one_apply_ne (Fin.castSucc_ne_last _)`. Use `show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0`. Rewrite using `[h0, neg_zero]`.
-/
theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Establish `hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))` using `hH`. Establish `hz` using `mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)`. Rewrite `hz` using `[ePG_true_rowD, ePG_false_last]`. Establish `hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val = (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) * ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val`.

Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (rowD i t b) (Fin.last _) = 0` using `hz`. Rewrite `hz'` using `[hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc]`. Establish `h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1` using `ent_last_last u`.

Rewrite `hz'` using `[h1, mul_one, Fin.append_right]`. Use `show d b = - ent (rowD i t b) (Fin.last _) u`. Conclude with `eq_neg_of_add_eq_zero_right hz'`.
-/
theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
/- English proof (translation)
Introduce `k _ _ _ _ i t O hO`. Set `w : Mir k ((i + 1) + (t + 1))` to `wEl k i t`. Set `f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1))` to `fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)`. Establish `hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹` using `(continuous_const.mul continuous_inv).mul continuous_const`. Establish `hf : Continuous f` using `((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu`.

Establish `f1 : f 1 = 1`. Establish `e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1` using `by group`. Use `show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1`. Rewrite using `[e, delta_one, dEmb_zero, one_mul]`. Use `⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩` and prove the remaining obligations.

Introduce `h hH d x hx e`. Establish `e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹)`. Establish `e2 : dEmb k i t d * w = h * w * x` using `e`. Combine the equalities or inequalities in the displayed calculation. Establish `hd` using `eq_delta i t h _ hH d e'`.

Establish `hfx : f x = h` using `by show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h`. Rewrite using `[← hd, ← e']`. Establish `: f x ∈ O` using `hx`. Rewrite `this` using `[hfx]`. Then use the resulting hypothesis.
-/
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
