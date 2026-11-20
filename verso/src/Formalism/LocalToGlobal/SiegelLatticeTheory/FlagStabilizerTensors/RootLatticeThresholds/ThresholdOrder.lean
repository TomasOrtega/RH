import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf

noncomputable section

open scoped Classical
open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdOrder

/- English proof (translation)
Take `⟨m, hm, hmax⟩` from `Set.exists_max_image s id hs hne`. Establish `hm0 : 0 < m⁻¹` using `inv_pos.mpr (hpos m hm)`. Use `⟨m⁻¹ ^ ((f : ℝ)⁻¹), Real.rpow_pos_of_pos hm0 _, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_inv_natCast_pow hm0.le hf.ne', inv_inv]`. Conclude with `⟨hm, fun b hb => hmax b hb⟩`.
-/
theorem isGreatest_pow_inv {s : Set ℝ} (hs : s.Finite) (hne : s.Nonempty) (hpos : ∀ x ∈ s, 0 < x) {f : ℕ} (hf : 0 < f) :
    ∃ Th : ℝ, 0 < Th ∧ IsGreatest s ((Th ^ f)⁻¹) := by
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image s id hs hne
  have hm0 : 0 < m⁻¹ := inv_pos.mpr (hpos m hm)
  refine ⟨m⁻¹ ^ ((f : ℝ)⁻¹), Real.rpow_pos_of_pos hm0 _, ?_⟩
  rw [Real.rpow_inv_natCast_pow hm0.le hf.ne', inv_inv]
  exact ⟨hm, fun b hb => hmax b hb⟩

variable {ι : Type} [Fintype ι] (G : Sz.Glob ι)

/- English proof (translation)
Establish `key : G.thrSet C de de' T T' l ⊆ ⋃ i ∈ Finset.range (G.r + 2), ⋃ s ∈ Finset.range (G.r + 3), ({∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w), ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w), ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de d …`. Introduce and unpack `x ⟨i, hi1, hir, h⟩`. Simplify using `only [Set.mem_iUnion, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]`. Break down `h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨s, _, hsi, rfl⟩ | rfl` into its components or cases. Conclude with `⟨i, by omega, 0, by omega, Or.inl rfl⟩`.

Conclude with `⟨i, by omega, 0, by omega, Or.inr (Or.inl rfl)⟩`. Conclude with `⟨i, by omega, s, by omega, Or.inr (Or.inr (Or.inl rfl))⟩`. Conclude with `⟨i, by omega, 0, by omega, Or.inr (Or.inr (Or.inr rfl))⟩`. Use `Set.Finite.subset ?_ key` and prove the remaining obligations. Use `Set.Finite.biUnion (Finset.range _).finite_toSet fun i _ => ?_` and prove the remaining obligations.

Use `Set.Finite.biUnion (Finset.range _).finite_toSet fun s _ => ?_` and prove the remaining obligations. Conclude with `Set.toFinite _`.
-/
theorem thrSet_finite (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Finite := by
  have key : G.thrSet C de de' T T' l ⊆ ⋃ i ∈ Finset.range (G.r + 2), ⋃ s ∈ Finset.range (G.r + 3),
      ({∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w),
        ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')} : Set ℝ) := by
    rintro x ⟨i, hi1, hir, h⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨s, _, hsi, rfl⟩ | rfl
    · exact ⟨i, by omega, 0, by omega, Or.inl rfl⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, by omega, s, by omega, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inr (Or.inr rfl))⟩
  refine Set.Finite.subset ?_ key
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun i _ => ?_
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun s _ => ?_
  exact Set.toFinite _

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩`.
-/
theorem thrSet_nonempty (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Nonempty :=
  ⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces`. Use `isGreatest_pow_inv (thrSet_finite _ _ _ _ _ _ _) (thrSet_nonempty _ _ _ _ _ _ _) hpos ?_` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.Sz.Glob.f`. Conclude with `Fintype.card_pos`.
-/
theorem thrAt_of_pos (CA : ℝ) (D : D7) (u u' : D.what₂.Word)
    (hpos : ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm).thrSet CA
      (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x) :
    Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA D u u' := by
  unfold Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces
  refine isGreatest_pow_inv (thrSet_finite _ _ _ _ _ _ _) (thrSet_nonempty _ _ _ _ _ _ _) hpos ?_
  unfold Formalism.FourierDecayAlt.Sz.Glob.f
  exact Fintype.card_pos

end Formalism.L2.SG.Pf.ThresholdOrder
