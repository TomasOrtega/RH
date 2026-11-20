import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def FamilyAskBounds {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RequiresAll (X x i)

def RemainingCountingStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

def FamilyFourthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K

def RestW {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightVectorExists (Fm.D x i) (Fm.L x i) (X x i) K

def FamilyFifthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) → PointsLemma (Fm.D x i) (Fm.L x i) (X x i) K

def RestT {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C

/- English proof (translation)
Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.
-/
theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

/- English proof (translation)
Introduce `K hK C31 Ce Cm hC31 hCe hCm`. Take `⟨C, hC, hG⟩` from `h1 K hK C31 Ce Cm hC31 hCe hCm`. Use `⟨C, hC, fun X Y hA => ?_⟩` and prove the remaining obligations. Take `⟨a0, ha0⟩` from `h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA`. Take `⟨a1, ha1⟩` from `hG X Y hA`.

Take `⟨a2, ha2⟩` from `h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA`. Take `⟨aW, haW⟩` from `hW K hK C31 Ce Cm hC31 hCe hCm X Y hA`. Take `⟨a3, ha3⟩` from `h3 K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA`. Take `⟨aT, haT⟩` from `hT K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA`. Use `⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 (max a2 (max aW (max a3 aT)))), fun x hx i => ?_⟩` and prove the remaining obligations.

Conclude with `tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))`. Simplify using `only [ge_iff_le, max_le_iff] at hx`. Take `⟨e0, e1, e2, eW, e3, eT⟩` from `hx`. Establish `g0` using `ha0 x e0 i`. Establish `g1` using `ha1 x e1 i`.

Establish `g2` using `ha2 x e2 i`. Establish `gW` using `haW x eW i`. Establish `g3` using `ha3 x e3 i g1`. Establish `gT` using `haT x eT i`. Establish `g1'` using `g1 (aL (Fm.L x i)) (bL (Fm.L x i))`.

Use `⟨g1' ?_, g2, g3, gW, fun a b ha hb p hp _ => g0 a b ha hb p hp, gT⟩` and prove the remaining obligations. Introduce `t ht`. Unfold `aL bL`. Simplify using `only [dif_pos ht]`. Conclude with `⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩`.
-/
theorem stmtEF_of {eps : ℝ} (Fm : FamP eps) (h0 : FamilyAskBounds Fm) (h1 : RemainingCountingStatement Fm) (h2 : FamilyFourthBound Fm) (hW : RestW Fm)
    (h3 : FamilyFifthBound Fm) (hT : RestT Fm) : FamilyClosedForm Fm := by
  intro K hK C31 Ce Cm hC31 hCe hCm
  obtain ⟨C, hC, hG⟩ := h1 K hK C31 Ce Cm hC31 hCe hCm
  refine ⟨C, hC, fun X Y hA => ?_⟩
  obtain ⟨a0, ha0⟩ := h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a1, ha1⟩ := hG X Y hA
  obtain ⟨a2, ha2⟩ := h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨aW, haW⟩ := hW K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a3, ha3⟩ := h3 K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  obtain ⟨aT, haT⟩ := hT K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  refine ⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 (max a2 (max aW (max a3 aT)))), fun x hx i => ?_⟩
  · exact tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))
  · simp only [ge_iff_le, max_le_iff] at hx
    obtain ⟨e0, e1, e2, eW, e3, eT⟩ := hx
    have g0 := ha0 x e0 i
    have g1 := ha1 x e1 i
    have g2 := ha2 x e2 i
    have gW := haW x eW i
    have g3 := ha3 x e3 i g1
    have gT := haT x eT i
    have g1' := g1 (aL (Fm.L x i)) (bL (Fm.L x i))
    refine ⟨g1' ?_, g2, g3, gW, fun a b ha hb p hp _ => g0 a b ha hb p hp, gT⟩

    intro t ht
    unfold aL bL
    simp only [dif_pos ht]
    exact ⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩

/- English proof (translation)
Introduce `K hK X Y hA`. Take `⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩` from `hA`. Take `⟨C, hC, hP⟩` from `h K hK C31 Ce Cm hC31 hCe hCm`. Conclude with `⟨C, hP X Y hA'⟩`.
-/
theorem stmtF_of_stmtEF {eps : ℝ} (Fm : FamP eps) (h : FamilyClosedForm Fm) : KudlaFamilyStatement Fm := by
  intro K hK X Y hA
  obtain ⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩ := hA
  obtain ⟨C, hC, hP⟩ := h K hK C31 Ce Cm hC31 hCe hCm
  exact ⟨C, hP X Y hA'⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
