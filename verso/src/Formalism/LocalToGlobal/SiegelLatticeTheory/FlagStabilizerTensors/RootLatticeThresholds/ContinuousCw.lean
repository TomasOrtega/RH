import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousAdjugate

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j ∧ blkOf w.1 i.1 = blkOf w.1 j.1 then c ⟨(i, j), h⟩ else 0

/- English proof (translation)
Use `⟨fun i => by simp [Cw], fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `only [Cw, Matrix.of_apply] at hij`. Use `split_ifs at hij with h1 h2`. Substitute `h1` using the available equality. Conclude with `⟨le_rfl, rfl⟩`.

Conclude with `⟨h2.1.le, h2.2⟩`. Conclude with `absurd rfl hij`.
-/
theorem isUB_Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : IsUB (blkW w) (Cw w c) := by
  refine ⟨fun i => by simp [Cw], fun i j hij => ?_⟩
  simp only [Cw, Matrix.of_apply] at hij
  split_ifs at hij with h1 h2
  · subst h1; exact ⟨le_rfl, rfl⟩
  · exact ⟨h2.1.le, h2.2⟩
  · exact absurd rfl hij

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Cw, Matrix.of_apply]`. Use `split_ifs with h1 h2`. Conclude with `continuous_const`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`.
-/
theorem continuous_Cw (w : Point D.host.E (D.R.rS + 1)) : Continuous fun c : FreeE w → ℂ => Cw w c := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Cw, Matrix.of_apply]
  split_ifs with h1 h2
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

/- English proof (translation)
Simplify using `only [Cw, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_lt p.2.1), dif_pos p.2]`. Both sides reduce to the same expression.
-/
theorem Cw_apply_free (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (p : FreeE w) :
    Cw w c p.1.1 p.1.2 = c p := by
  simp only [Cw, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2.1), dif_pos p.2]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.inv_def, hC.det_eq_one, Ring.inverse_one, one_smul]`.
-/
theorem inv_eq_adj {m : ℕ} {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : C⁻¹ = C.adjugate := by
  rw [Matrix.inv_def, hC.det_eq_one, Ring.inverse_one, one_smul]

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `ha' : a.1 < D.R.rS` using `lt_of_lt_of_le ha hk`. Take `⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc` from `⟨⟨a.1, ha'⟩, Fin.ext rfl⟩`. Simplify using `only [frm, famSc, fam_castSucc, SetLike.mem_coe]`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `using ha`.
-/
theorem span_frm_le (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (k : ℕ)
    (hk : k ≤ D.R.rS) :
    Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.1 < D.R.rS := lt_of_lt_of_le ha hk
  obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, ha'⟩, Fin.ext rfl⟩
  simp only [frm, famSc, fam_castSucc, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa using ha

/- English proof (translation)
Simplify using `only [frm, famSc, fam_castSucc, Fin.val_castSucc]`.
-/
theorem frm_castSucc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b : Fin D.R.rS) :
    frm X w D.host.rdE v b.castSucc = (((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹) • rv X.B.I v (X.eR b) := by
  simp only [frm, famSc, fam_castSucc, Fin.val_castSucc]

/- English proof (translation)
Simplify using `only [frm, famSc, fam_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]`.
-/
theorem frm_last (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    frm X w D.host.rdE v (Fin.last D.R.rS) = rv X.B.I v (X.zR w) := by
  simp only [frm, famSc, fam_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

/- English proof (translation)
Use `Submodule.sum_mem _ fun a'' _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (A - 1) a'' a' = 0`. Rewrite using `[h, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hne : a'' ≠ a'` using `by intro he; subst he; apply h; simp [hA.1]`.

Establish `hA0 : A a'' a' ≠ 0` using `by intro h0; apply h; simp [h0, Matrix.one_apply, hne]`. Establish `hlt : a'' < a'` using `lt_of_le_of_ne (hA.2 _ _ hA0).1 hne`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a'', hlt, rfl⟩)`.
-/
theorem comb_mem (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    {blk : Fin (D.R.rS + 1) → ℕ} {A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hA : IsUB blk A)
    (a' : Fin (D.R.rS + 1)) :
    ∑ a'', (A - 1) a'' a' • frm X w D.host.rdE v a'' ∈ Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < a'.1}) := by
  refine Submodule.sum_mem _ fun a'' _ => ?_
  by_cases h : (A - 1) a'' a' = 0
  · rw [h, zero_smul]; exact Submodule.zero_mem _
  · have hne : a'' ≠ a' := by intro he; subst he; apply h; simp [hA.1]
    have hA0 : A a'' a' ≠ 0 := by intro h0; apply h; simp [h0, Matrix.one_apply, hne]
    have hlt : a'' < a' := lt_of_le_of_ne (hA.2 _ _ hA0).1 hne
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a'', hlt, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
