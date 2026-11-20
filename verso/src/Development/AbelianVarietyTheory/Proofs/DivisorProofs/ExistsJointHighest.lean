import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

def zyW (P Q R S : ℕ) : Fin (R + S) × Fin (P + Q) → Ln P Q R S :=
  fun w => (finSumFinEquiv.symm w.2, finSumFinEquiv.symm w.1)

/- English proof (translation)
Introduce and unpack `⟨c, i⟩ ⟨d, j⟩ e`. Simplify using `only [zyW, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e`. Rewrite using `[e.1, e.2]`.
-/
theorem zyW_inj (P Q R S : ℕ) : Function.Injective (zyW P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [zyW, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

/- English proof (translation)
Simplify using `[GlobalTheory.Capelli.rowOp, zyW, zR, finSumFinEquiv_symm_apply_castAdd]`.
-/
theorem rowOp_zyW_castAdd (P Q R S : ℕ) (c d : Fin R) :
    GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) (Fin.castAdd S c) (Fin.castAdd S d) =
      GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d := by
  simp [GlobalTheory.Capelli.rowOp, zyW, zR, finSumFinEquiv_symm_apply_castAdd]

/- English proof (translation)
Simplify using `[GlobalTheory.Capelli.rowOp, zyW, yS, finSumFinEquiv_symm_apply_natAdd]`.
-/
theorem rowOp_zyW_natAdd (P Q R S : ℕ) (c d : Fin S) :
    GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) (Fin.natAdd R c) (Fin.natAdd R d) =
      GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d := by
  simp [GlobalTheory.Capelli.rowOp, zyW, yS, finSumFinEquiv_symm_apply_natAdd]

/- English proof (translation)
Rewrite using `[GlobalTheory.Capelli.rowOp_apply]`. Simplify using `only [MvPolynomial.X_mul_pderiv_monomial]`. Rewrite using `[← Finset.sum_smul, Int.cast_natCast, Nat.cast_smul_eq_nsmul]`.
-/
theorem rowOp_diag_monomial {σ I J : Type*} [Fintype J] (z : I × J → σ) (c : I) (s : σ →₀ ℕ)
    (a : ℂ) : GlobalTheory.Capelli.rowOp ℂ z c c (monomial s a) =
      (((∑ k, s (z (c, k)) : ℕ) : ℤ) : ℂ) • monomial s a := by
  classical
  rw [GlobalTheory.Capelli.rowOp_apply]
  simp only [MvPolynomial.X_mul_pderiv_monomial]
  rw [← Finset.sum_smul, Int.cast_natCast, Nat.cast_smul_eq_nsmul]

def blockOp (P Q R S : ℕ) (i j : Fin (R + S)) : Module.End ℂ (Pol P Q R S) :=
  if ((i : ℕ) < R ↔ (j : ℕ) < R) then GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) i j else 0

/- English proof (translation)
The claim follows from `if_pos Iff.rfl`.
-/
theorem blockOp_diag (P Q R S : ℕ) (i : Fin (R + S)) :
    blockOp P Q R S i i = GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) i i := if_pos Iff.rfl

/- English proof (translation)
Rewrite using `[blockOp, if_pos (by simp), rowOp_zyW_castAdd]`.
-/
theorem blockOp_castAdd (P Q R S : ℕ) (c d : Fin R) :
    blockOp P Q R S (Fin.castAdd S c) (Fin.castAdd S d) = GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d := by
  rw [blockOp, if_pos (by simp), rowOp_zyW_castAdd]

/- English proof (translation)
Rewrite using `[blockOp, if_pos (by simp), rowOp_zyW_natAdd]`.
-/
theorem blockOp_natAdd (P Q R S : ℕ) (c d : Fin S) :
    blockOp P Q R S (Fin.natAdd R c) (Fin.natAdd R d) = GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d := by
  rw [blockOp, if_pos (by simp), rowOp_zyW_natAdd]

/- English proof (translation)
Rewrite using `[blockOp, if_neg (by simp)]`.
-/
theorem blockOp_castAdd_natAdd (P Q R S : ℕ) (c : Fin R) (d : Fin S) :
    blockOp P Q R S (Fin.castAdd S c) (Fin.natAdd R d) = 0 := by
  rw [blockOp, if_neg (by simp)]

/- English proof (translation)
Rewrite using `[blockOp, if_neg (by simp)]`.
-/
theorem blockOp_natAdd_castAdd (P Q R S : ℕ) (c : Fin S) (d : Fin R) :
    blockOp P Q R S (Fin.natAdd R c) (Fin.castAdd S d) = 0 := by
  rw [blockOp, if_neg (by simp)]

/- English proof (translation)
Rewrite using `[blockOp_diag]`. Distinguish the cases in `hkl : ((k : ℕ) < R ↔ (l : ℕ) < R)`. Establish `e : blockOp P Q R S k l = GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) k l` using `if_pos hkl`. Rewrite using `[e, GlobalTheory.Capelli.rowOp_lie _ (zyW_inj P Q R S)]`. Apply the tactic sequence `by_cases hik : i = k <;> by_cases hil : i = l`.

Substitute `hik` using the available equality. Substitute `hil` using the available equality. Simplify using the standard rewrite rules. Substitute `hik` using the available equality. Simplify using `[hil, Ne.symm hil]`.

Substitute `hil` using the available equality. Simplify using `[hik]`. Simplify using `[hik, hil, Ne.symm hil]`. Establish `e : blockOp P Q R S k l = 0` using `if_neg hkl`. Rewrite using `[e]`.

Simplify using the standard rewrite rules.
-/
theorem blockOp_lie (P Q R S : ℕ) (i k l : Fin (R + S)) :
    blockOp P Q R S i i * blockOp P Q R S k l - blockOp P Q R S k l * blockOp P Q R S i i =
      ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) • blockOp P Q R S k l := by
  rw [blockOp_diag]
  by_cases hkl : ((k : ℕ) < R ↔ (l : ℕ) < R)
  · have e : blockOp P Q R S k l = GlobalTheory.Capelli.rowOp ℂ (zyW P Q R S) k l := if_pos hkl
    rw [e, GlobalTheory.Capelli.rowOp_lie _ (zyW_inj P Q R S)]
    by_cases hik : i = k <;> by_cases hil : i = l
    · subst hik; subst hil; simp
    · subst hik; simp [hil, Ne.symm hil]
    · subst hil; simp [hik]
    · simp [hik, hil, Ne.symm hil]
  · have e : blockOp P Q R S k l = 0 := if_neg hkl
    rw [e]; simp

/- English proof (translation)
Introduce `P Q R S N hN hN0 hz hy`. Establish `hW : ∀ (t : Unit) (i j : Fin (R + S)), ∀ w ∈ N, (fun _ : Unit => blockOp P Q R S) t i j w ∈ N`. Introduce `t i j w hw`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left c`.

Proceed by induction on `j using Fin.addCases with`. Consider the case `left d => simp only [blockOp_castAdd]`. Conclude with `hz c d w hw`. Consider the case `right d => simp only [blockOp_castAdd_natAdd]`. Conclude with `N.zero_mem`.

Consider the case `right c`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left d => simp only [blockOp_natAdd_castAdd]`. Conclude with `N.zero_mem`. Consider the case `right d => simp only [blockOp_natAdd]`.

Conclude with `hy c d w hw`. Establish `hdiag : ⨆ κ : Unit → Fin (R + S) → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace ((fun _ : Unit => blockOp P Q R S) t i i) (κ t i : ℂ)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `f _`. Rewrite using `[f.as_sum]`.

Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem (fun _ i => ((∑ k, s (zyW P Q R S (i, k)) : ℕ) : ℤ)) ?_` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`. Introduce `_ i`. Rewrite using `[Module.End.mem_eigenspace_iff, blockOp_diag, rowOp_diag_monomial]`.

Use `haveI := hN`. Take `⟨v, hvN, hv0, hup, κ, hκ⟩` from `GlobalTheory.exists_highest_vector (fun _ : Unit => blockOp P Q R S) (fun t t' i k l => by rw [if_pos (Subsingleton.elim t t')]; exact blockOp_lie P Q R S i k l) hdiag N hW hN0`. Use `⟨v, hvN, hv0, fun c d hcd => ?_, ⟨fun c => (κ () (Fin.castAdd S c) : ℂ), fun c => ?_⟩, fun c d hcd => ?_, ⟨fun d => (κ () (Fin.natAdd R d) : ℂ), fun d => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hup () (Fin.castAdd S c) (Fin.castAdd S d) (by show (Fin.castAdd S c : ℕ) < Fin.castAdd S d; simp only [Fin.val_castAdd]; exact hcd)`. Simplify `h` using `only [blockOp_castAdd]`.

Establish `h` using `hκ () (Fin.castAdd S c)`. Simplify `h` using `only [blockOp_castAdd]`. Establish `h` using `hup () (Fin.natAdd R c) (Fin.natAdd R d) (by show (Fin.natAdd R c : ℕ) < Fin.natAdd R d; simp only [Fin.val_natAdd]; exact Nat.add_lt_add_left hcd R)`. Simplify `h` using `only [blockOp_natAdd]`. Establish `h` using `hκ () (Fin.natAdd R d)`.

Simplify `h` using `only [blockOp_natAdd]`.
-/
theorem exists_joint_highest : ∀ (P Q R S : ℕ) (N : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S)), FiniteDimensional ℂ N → N ≠ ⊥ → (∀ (c d : Fin R), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c d w ∈ N) → (∀ (c d : Fin S), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) c d w ∈ N) → ∃ v ∈ N, v ≠ 0 ∧ (∀ c d : Fin R, c < d → GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c d v = 0) ∧ (∃ α : Fin R → ℂ, ∀ c, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c c v = α c • v) ∧ (∀ c d : Fin S, c < d → GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) c d v = 0) ∧ (∃ β : Fin S → ℂ, ∀ d, GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) d d v = β d • v) := by
  classical
  intro P Q R S N hN hN0 hz hy
  have hW : ∀ (t : Unit) (i j : Fin (R + S)), ∀ w ∈ N,
      (fun _ : Unit => blockOp P Q R S) t i j w ∈ N := by
    intro t i j w hw
    induction i using Fin.addCases with
    | left c =>
      induction j using Fin.addCases with
      | left d => simp only [blockOp_castAdd]; exact hz c d w hw
      | right d => simp only [blockOp_castAdd_natAdd]; exact N.zero_mem
    | right c =>
      induction j using Fin.addCases with
      | left d => simp only [blockOp_natAdd_castAdd]; exact N.zero_mem
      | right d => simp only [blockOp_natAdd]; exact hy c d w hw
  have hdiag : ⨆ κ : Unit → Fin (R + S) → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace
      ((fun _ : Unit => blockOp P Q R S) t i i) (κ t i : ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    refine Submodule.mem_iSup_of_mem (fun _ i => ((∑ k, s (zyW P Q R S (i, k)) : ℕ) : ℤ)) ?_
    simp only [Submodule.mem_iInf]
    intro _ i
    rw [Module.End.mem_eigenspace_iff, blockOp_diag, rowOp_diag_monomial]
  haveI := hN
  obtain ⟨v, hvN, hv0, hup, κ, hκ⟩ := GlobalTheory.exists_highest_vector (fun _ : Unit => blockOp P Q R S)
    (fun t t' i k l => by rw [if_pos (Subsingleton.elim t t')]; exact blockOp_lie P Q R S i k l)
    hdiag N hW hN0
  refine ⟨v, hvN, hv0, fun c d hcd => ?_, ⟨fun c => (κ () (Fin.castAdd S c) : ℂ), fun c => ?_⟩,
    fun c d hcd => ?_, ⟨fun d => (κ () (Fin.natAdd R d) : ℂ), fun d => ?_⟩⟩
  · have h := hup () (Fin.castAdd S c) (Fin.castAdd S d)
      (by show (Fin.castAdd S c : ℕ) < Fin.castAdd S d; simp only [Fin.val_castAdd]; exact hcd)
    simpa only [blockOp_castAdd] using h
  · have h := hκ () (Fin.castAdd S c)
    simpa only [blockOp_castAdd] using h
  · have h := hup () (Fin.natAdd R c) (Fin.natAdd R d)
      (by show (Fin.natAdd R c : ℕ) < Fin.natAdd R d; simp only [Fin.val_natAdd]; exact Nat.add_lt_add_left hcd R)
    simpa only [blockOp_natAdd] using h
  · have h := hκ () (Fin.natAdd R d)
    simpa only [blockOp_natAdd] using h

end GlobalTheory.LowIrr
