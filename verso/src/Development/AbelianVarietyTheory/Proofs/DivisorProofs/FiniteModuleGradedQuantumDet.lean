import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.MidBlock

section Alg

variable {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm`. Simplify using `only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 3`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem qdet_map (φ : A →ₐ[ℂ] A') {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`. Use `Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`. Unfold `Formalism.REAL.Tm`.

Use `Subalgebra.add_mem _ ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Subalgebra.algebraMap_mem _ _`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem qdet_mem (S : Subalgebra ℂ A) {n : ℕ} {E : Fin n → Fin n → A} (h : ∀ a b, E a b ∈ S) (u : ℂ) :
    Formalism.REAL.qdet E u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`. Use `Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_` and prove the remaining obligations. Use `Commute.list_prod_right _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hy`. Unfold `Formalism.REAL.Tm`.

Conclude with `Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)`.
-/
theorem comm_qdet {n : ℕ} {E : Fin n → Fin n → A} {z : A} (h : ∀ a b, Commute z (E a b)) (u : ℂ) :
    Commute z (Formalism.REAL.qdet E u) := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Formalism.REAL.Tm
  exact Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm`. Simplify using the standard rewrite rules.
-/
theorem qdet_one (E : Fin 1 → Fin 1 → A) (u : ℂ) : Formalism.REAL.qdet E u = algebraMap ℂ A u + E 0 0 := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp

/- English proof (translation)
Establish `h` using `hX a b c d`. Rewrite `h` using `[if_neg hbc, if_neg hda, sub_zero]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem glComm {n : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {a b c d : Fin n} (hbc : b ≠ c)
    (hda : d ≠ a) : Commute (X a b) (X c d) := by
  have h := hX a b c d
  rw [if_neg hbc, if_neg hda, sub_zero] at h
  exact sub_eq_zero.1 h

end Alg

section Stab

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ N, f x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => by simpa [Module.algebraMap_end_apply] using N.smul_mem c hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stab {N : Submodule ℂ M} {f : Module.End ℂ M} : f ∈ stab N ↔ ∀ x ∈ N, f x ∈ N := Iff.rfl

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨p, q, w, rfl⟩` from `hy`. Introduce `x hx`. Conclude with `hY p q _ (mem_stab.1 w.2 x hx)`.

Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb => intro x hx`. Simplify using `using K.add_mem (ha x hx) (hb x hx)`. Consider the case `smul c a _ ha => intro x hx`.

Simplify using `using K.smul_mem c (ha x hx)`.
-/
theorem upperSpan_maps {N K : Submodule ℂ M} {r m : ℕ} (Y : Fin (r + m) → Fin (r + m) → stab N)
    (hY : ∀ p q, ∀ x ∈ N, (Y (Fin.castAdd m p) (Fin.natAdd r q) : Module.End ℂ M) x ∈ K)
    {y : stab N} (hy : y ∈ GlobalTheory.CapHC.upperSpan Y) : ∀ x ∈ N, (y : Module.End ℂ M) x ∈ K := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    intro x hx
    exact hY p q _ (mem_stab.1 w.2 x hx)
  | zero => intro x _; simp
  | add a b _ _ ha hb => intro x hx; simpa using K.add_mem (ha x hx) (hb x hx)
  | smul c a _ ha => intro x hx; simpa using K.smul_mem c (ha x hx)

end Stab

section Main

/- English proof (translation)
Rewrite using `[blk_y]`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun k => ?_) p <;> simp [blk]`.
-/
theorem blk_castAdd_lt {n₁ : ℕ} (p : Fin (1 + n₁)) (q : Fin 1) :
    blk n₁ (Fin.castAdd 1 p) < blk n₁ (Fin.natAdd (1 + n₁) q) := by
  rw [blk_y]
  refine Fin.addCases (fun a => ?_) (fun k => ?_) p <;> simp [blk]

end Main

end GlobalTheory.LeviHC.MidBlock
