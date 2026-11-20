import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLq
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

/- English proof (translation)
Conclude with `D.host.der.finrank_F`.
-/
theorem finrank_F_eq (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.der.finrank_F

/- English proof (translation)
Establish `h` using `splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)`. Rewrite `h` using `[finrank_F_eq]`. Conclude with `h`.
-/
theorem splitsF_g (D : D7) (i : Fin 2) : StandardLattice.SplitsF D (D.host.g i) := by
  have h := splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)
  rw [finrank_F_eq] at h
  exact h

/- English proof (translation)
The claim follows from `idxColTie_of D (splitsF_g D)`.
-/
theorem idxColTie_holds (D : D7) : IdxColTie D := idxColTie_of D (splitsF_g D)

/- English proof (translation)
The claim follows from `idxRowTie_of D (splitsF_g D)`.
-/
theorem idxRowTie_holds (D : D7) : IdxRowTie D := idxRowTie_of D (splitsF_g D)

def ColHyp0 (D : D7) : Prop :=
  StandardLattice.GBig D ∧ ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, splitsF_g D, h.2⟩`.
-/
theorem colHyp_of (D : D7) (h : ColHyp0 D) : ColHyp D := ⟨h.1, splitsF_g D, h.2⟩

/- English proof (translation)
Establish `hfk : D.R.f ≤ D.R.k` using `D.R.f_le_k`. Establish `hk : 5 ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hb : 1 < L.sc.b`. Establish `hL : 0 < L.sc.L`. Unfold `Formalism.BasicNotions.Scale.L`. Conclude with `Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _`. Unfold `Formalism.BasicNotions.Scale.b`.

Combine the equalities or inequalities in the displayed calculation. Unfold `Formalism.MainNotions.SizesAt at hS`. Establish `hG` using `hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Unfold `Formalism.MainNotions.SizeG at hG`. Establish `h1` using `(hG 0 0).1`.

Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `by positivity`. Establish `hkb : (D.R.k : ℝ) ≤ D.R.k * L.sc.b` using `by nlinarith`. Establish `h8 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8` using `by gcongr`. Establish `hk8N : D.R.k ^ 8 ≤ D.host.g 0`. Establish `: ((D.R.k ^ 8 : ℕ) : ℝ) ≤ (D.host.g 0 : ℝ)` using `by push_cast; linarith`.

Conclude with `this` after adjusting the coercions. Establish `h6 : 5 ^ 6 ≤ D.R.k ^ 6` using `Nat.pow_le_pow_left hk 6`. Establish `hsplit : D.R.k ^ 8 = D.R.k ^ 2 * D.R.k ^ 6` using `by ring`. Establish `hff : 2 * D.R.f * D.R.k ≤ 2 * D.R.k * D.R.k`. Use `Nat.mul_le_mul_right D.R.k hfk` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hkk : 2 * D.R.k * D.R.k + 2 < D.R.k ^ 8`. Rewrite using `[hsplit]`. Use polynomial arithmetic with `[Nat.mul_le_mul_left (D.R.k ^ 2) h6, Nat.mul_le_mul hk hk]`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Apply `Nat.lt_sub_of_add_lt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gBig_of_sizes {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : StandardLattice.GBig D := by
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega

  have hb : 1 < L.sc.b := by
    have hL : 0 < L.sc.L := by
      unfold Formalism.BasicNotions.Scale.L
      exact Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
    unfold Formalism.BasicNotions.Scale.b
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp L.sc.L := Real.exp_lt_exp.mpr hL
  unfold Formalism.MainNotions.SizesAt at hS
  have hG := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Formalism.MainNotions.SizeG at hG
  have h1 := (hG 0 0).1
  have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
  have hkb : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := by nlinarith
  have h8 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := by gcongr
  have hk8N : D.R.k ^ 8 ≤ D.host.g 0 := by
    have : ((D.R.k ^ 8 : ℕ) : ℝ) ≤ (D.host.g 0 : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h6 : 5 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk 6
  have hsplit : D.R.k ^ 8 = D.R.k ^ 2 * D.R.k ^ 6 := by ring
  have hff : 2 * D.R.f * D.R.k ≤ 2 * D.R.k * D.R.k := by
    have := Nat.mul_le_mul_right D.R.k hfk
    nlinarith
  have hkk : 2 * D.R.k * D.R.k + 2 < D.R.k ^ 8 := by
    rw [hsplit]
    nlinarith [Nat.mul_le_mul_left (D.R.k ^ 2) h6, Nat.mul_le_mul hk hk]
  refine ⟨0, ?_⟩
  apply Nat.lt_sub_of_add_lt
  linarith

/- English proof (translation)
The claim follows from `column_row_ranks D Lv h4 h2 hD (colHyp_of D hc) (idxColTie_holds D) (idxRowTie_holds D)`.
-/
theorem column_row_ranks_of_weak_columns (D : D7) (Lv : LevelData D) (h4 : StandardLattice.Conclusion4f D Lv) (h2 : StandardLattice.VolumeEqMass₂ D)
    (hD : StandardLattice.FactDstar D) (hc : ColHyp0 D) : LocalBesselAndTopKernel.FamilyMidVolume D :=
  column_row_ranks D Lv h4 h2 hD (colHyp_of D hc) (idxColTie_holds D) (idxRowTie_holds D)

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Apply `family_column_row_ranks Fm C0 Cg cb Cu cT CT` to reduce the goal to its premises. Use `⟨max x0 (Fm.x1 + 1), fun x hx i hyp => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x`. Use `le_max_right x0 (Fm.x1 + 1)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxx : x ≥ x0` using `le_trans (le_max_left _ _) hx`. Take `⟨hLv, h2, hs⟩` from `hx0 x hxx i hyp`. Conclude with `⟨hLv, h2, (Fm.ex x hx1 i).Dstar_def, colHyp_of _ ⟨gBig_of_sizes (Fm.L x i) (Fm.sizes x hx1 i), hs⟩, idxColTie_holds _, idxRowTie_holds _⟩`.
-/
theorem family_column_row_ranks_splitting {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 Cg cb Cu cT CT : ℝ)
    (h : S.OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      (∃ Lv : LevelData (Fm.D x i), StandardLattice.Conclusion4f (Fm.D x i) Lv) ∧ StandardLattice.VolumeEqMass₂ (Fm.D x i) ∧
        ∀ u : (Fm.D x i).what₂.Word, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u) :
    LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT := by
  obtain ⟨x0, hx0⟩ := h
  apply family_column_row_ranks Fm C0 Cg cb Cu cT CT
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hyp => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_max_right x0 (Fm.x1 + 1)
    linarith
  have hxx : x ≥ x0 := le_trans (le_max_left _ _) hx
  obtain ⟨hLv, h2, hs⟩ := hx0 x hxx i hyp

  exact ⟨hLv, h2, (Fm.ex x hx1 i).Dstar_def,
    colHyp_of _ ⟨gBig_of_sizes (Fm.L x i) (Fm.sizes x hx1 i), hs⟩,
    idxColTie_holds _, idxRowTie_holds _⟩

end Formalism.MainNotions.J

end
