import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨h, rfl⟩` from `hg`. Establish `hu : IsUnit (h.val.det)` using `(Matrix.isUnit_iff_isUnit_det _).1 h.isUnit`. Use `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu` as an intermediate fact. Express the relevant statement in the definitionally equal form `valuation k ((algebraMap 𝒪[k] k).mapMatrix h.val).det = 1`. Rewrite using `[← RingHom.map_det]`.

Conclude with `this`.
-/
private theorem valuation_det_of_mem_KO' {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, rfl⟩ := hg
  have hu : IsUnit (h.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  change valuation k ((algebraMap 𝒪[k] k).mapMatrix h.val).det = 1
  rw [← RingHom.map_det]
  exact this

/- English proof (translation)
Apply the tactic sequence `unfold ev; split_ifs <;> simp`.
-/
private theorem ev_one' (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

/- English proof (translation)
Unfold `minor Matrix.toSquareBlockProp Matrix.toBlock`. Use `Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin (n + 1) => i ≤ Fin.last n) (fun i => Fin.le_last i)) g.val` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
private theorem minor_last {n : ℕ} (g : GL (Fin (n + 1)) k) : minor g (Fin.last n) = g.val.det := by
  unfold minor Matrix.toSquareBlockProp Matrix.toBlock
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin (n + 1) => i ≤ Fin.last n)
    (fun i => Fin.le_last i)) g.val
  rw [← this]; rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Simplify using `only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]`. Introduce `_ i j _ u _ _`. Both sides reduce to the same expression.

Introduce `g hg`. Consider the cases of `n with`. Consider the case `zero`. Simplify using `[theta, detChar_apply]`. Establish `h0 : Matrix.GeneralLinearGroup.det g = 1` using `Units.ext (by simp [Matrix.det_isEmpty])`.

Rewrite using `[h0, map_one, Units.val_one]`. Consider the case `succ n`. Unfold `theta`. Rewrite using `[Fin.prod_univ_castSucc]`. Establish `h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1`.

Introduce `i`. Establish `: nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ`. Unfold `nxt; rw [dif_pos (by simp)]`. Rewrite using `[this, div_self']`. Conclude with `ev_one' _`.

Establish `h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1`. Unfold `nxt; rw [dif_neg (by simp)]`. Simplify using `only [h1, Finset.prod_const_one, one_mul, h2, div_one, minor_last]`. Establish `hv` using `valuation_det_of_mem_KO' hg`. Unfold `ev`.

Rewrite using `[dif_pos hv, detChar_apply]`. Use `congr 2`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem const_family (n : ℕ) (χ : kˣ →* ℂˣ) :
    grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧
      ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]
    intro _ i j _ u _ _
    rfl
  · intro g hg
    cases n with
    | zero =>
      simp [theta, detChar_apply]
      have h0 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      rw [h0, map_one, Units.val_one]
    | succ n =>
      unfold theta
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1 := by
        intro i
        have : nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ := by
          unfold nxt; rw [dif_pos (by simp)]
        rw [this, div_self']; exact ev_one' _
      have h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1 := by
        unfold nxt; rw [dif_neg (by simp)]
      simp only [h1, Finset.prod_const_one, one_mul, h2, div_one, minor_last]
      have hv := valuation_det_of_mem_KO' hg
      unfold ev
      rw [dif_pos hv, detChar_apply]
      congr 2
      ext; simp

/- English proof (translation)
Introduce `_ _ _ _ _ n χ` and use `const_family n χ`.
-/
theorem const_family_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) :=
  fun _ _ _ _ _ n χ => const_family n χ

end GlobalTheory.PsType
