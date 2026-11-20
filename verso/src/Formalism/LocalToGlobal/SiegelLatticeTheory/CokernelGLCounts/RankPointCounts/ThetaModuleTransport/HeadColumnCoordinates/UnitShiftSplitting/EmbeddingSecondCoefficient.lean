import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SumMulInd

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem embedding_firstCoefficient (c : Ix r → M.L.O) (a : Fin (r + 1)) :
    g.e ((mOf1 hs c a : M.R) : E) = ((g.e (c (Sum.inr a) : E)).1,
      (g.e (c (Sum.inr a) : E)).1 + (g.q : F) * -(g.e (c (Sum.inl a) : E)).1) := by
  rw [mOf1, e_rOf]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem embedding_secondCoefficient (c : Ix r → M.L.O) (a : Fin (r + 1)) :
    g.e ((mOf2 hs c a : M.R) : E) = ((g.e (c (Sum.inr a) : E)).2,
      (g.e (c (Sum.inr a) : E)).2 + (g.q : F) * -(g.e (c (Sum.inl a) : E)).2) := by
  rw [mOf2, e_rOf]; rfl

variable {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {T T' : F} {TT : M.R} {Z Zσ : M.Mat (r + 1)}

include hs

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem e_Z (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (b a : Fin (r + 1)) :
    g.e (Z.Z b a : E) = ((g.e (Zh b a)).1 / (g.q : F) - ind r a b * (-T / (g.q : F)),
       -((g.e (Zh a b)).2 / (g.q : F)) - ind r a b * (T' / (g.q : F))) := by
  rw [show (Z.Z b a : E) = HermSp.ZZplusOf M Zh T T' b a from congrFun (congrFun hZ b) a, zz_comp hs,
    ite_ind, ite_ind]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem e_Zσ (hZ : Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T') (b a : Fin (r + 1)) :
    g.e (Zσ.Z b a : E) = ((g.e (Zh b a)).2 / (g.q : F) - ind r a b * (-T / (g.q : F)),
       -((g.e (Zh a b)).1 / (g.q : F)) - ind r a b * (T' / (g.q : F))) := by
  rw [show (Zσ.Z b a : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' b a from congrFun (congrFun hZ b) a,
    zz_comp hs, ite_ind, ite_ind]
  simp [e_cjA]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take a linear combination of the given relations to obtain the conclusion. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem gram_rows_firstEmbedding (hTT : g.e (TT : E) = (T, T')) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (c : Ix r → M.L.O) (b : Fin (r + 1)) :
    ((g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b))).1,
      (g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b))).1 +
        (g.q : F) * (g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inr b))).1) =
      g.e ((llMap hs Z TT (mOf1 hs c) b : M.R) : E) := by
  have hq := q_ne g
  rw [row_inl, row_inr, e_llMap]
  simp only [e_Z hs hZ, embedding_firstCoefficient, hTT]
  refine Prod.ext ?_ ?_
  · simp only
    have h : ∀ a, ((g.e (Zh b a)).1 / (g.q : F) - ind r a b * (-T / (g.q : F))) * (g.e (c (Sum.inr a) : E)).1 =
        (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 +
          (g.e (c (Sum.inr a) : E)).1 * (ind r a b * (T / (g.q : F))) := by
      intro a; ring
    rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, sum_mul_ind]
    split_ifs
    · field_simp; ring
    · ring
  · simp only
    have hL : ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 + (g.q : F) *
        ∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 +
          (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2) * (g.e (c (Sum.inr a) : E)).1) =
        ∑ a, ((g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 -
          (g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inr a) : E)).1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by field_simp; ring
    have hR : ∀ a, (-((g.e (Zh a b)).2 / (g.q : F)) - ind r a b * (T' / (g.q : F))) *
        ((g.e (c (Sum.inr a) : E)).1 + (g.q : F) * -(g.e (c (Sum.inl a) : E)).1) =
        ((g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 -
          (g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inr a) : E)).1) +
        ((g.e (c (Sum.inr a) : E)).1 * (ind r a b * (-(T' / (g.q : F)))) +
          (g.e (c (Sum.inl a) : E)).1 * (ind r a b * T')) := by
      intro a; field_simp; ring
    have hRs := Finset.sum_congr (s₁ := Finset.univ) rfl fun a _ => hR a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_mul_ind, sum_mul_ind] at hRs
    rw [hRs]
    split_ifs
    · linear_combination (norm := skip) hL
      field_simp
      ring
    · linear_combination (norm := skip) hL
      ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take a linear combination of the given relations to obtain the conclusion. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem gram_rows_secondEmbedding (hTT : g.e (TT : E) = (T, T')) (hZ : Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T')
    (c : Ix r → M.L.O) (b : Fin (r + 1)) :
    ((g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b))).2,
      (g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b))).2 +
        (g.q : F) * (g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inr b))).2) =
      g.e ((llMap hs Zσ TT (mOf2 hs c) b : M.R) : E) := by
  have hq := q_ne g
  rw [row_inl, row_inr, e_llMap]
  simp only [e_Zσ hs hZ, embedding_secondCoefficient, hTT]
  refine Prod.ext ?_ ?_
  · simp only
    have h : ∀ a, ((g.e (Zh b a)).2 / (g.q : F) - ind r a b * (-T / (g.q : F))) * (g.e (c (Sum.inr a) : E)).2 =
        (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 +
          (g.e (c (Sum.inr a) : E)).2 * (ind r a b * (T / (g.q : F))) := by
      intro a; ring
    rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, sum_mul_ind]
    split_ifs
    · field_simp; ring
    · ring
  · simp only
    have hL : ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 + (g.q : F) *
        ∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 +
          (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1) * (g.e (c (Sum.inr a) : E)).2) =
        ∑ a, ((g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 -
          (g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inr a) : E)).2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by field_simp; ring
    have hR : ∀ a, (-((g.e (Zh a b)).1 / (g.q : F)) - ind r a b * (T' / (g.q : F))) *
        ((g.e (c (Sum.inr a) : E)).2 + (g.q : F) * -(g.e (c (Sum.inl a) : E)).2) =
        ((g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 -
          (g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inr a) : E)).2) +
        ((g.e (c (Sum.inr a) : E)).2 * (ind r a b * (-(T' / (g.q : F)))) +
          (g.e (c (Sum.inl a) : E)).2 * (ind r a b * T')) := by
      intro a; field_simp; ring
    have hRs := Finset.sum_congr (s₁ := Finset.univ) rfl fun a _ => hR a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_mul_ind, sum_mul_ind] at hRs
    rw [hRs]
    split_ifs
    · linear_combination (norm := skip) hL
      field_simp
      ring
    · linear_combination (norm := skip) hL
      ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem firstComponent_gram_rows (hTT : g.e (TT : E) = (T, T')) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (c Y : Ix r → M.L.O) (hY : ∀ j, (Y j : E) = ∑ i, (c i : E) * GG (g := g) Zh T T' i j) :
    cmp1 hs Y = llMap hs Z TT (mOf1 hs c) := by
  funext b; apply Subtype.ext; apply g.e.injective
  rw [embedding_firstComponent, hY, hY]
  exact gram_rows_firstEmbedding hs hTT hZ c b

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem secondComponent_gram_rows (hTT : g.e (TT : E) = (T, T'))
    (hZ : Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T')
    (c Y : Ix r → M.L.O) (hY : ∀ j, (Y j : E) = ∑ i, (c i : E) * GG (g := g) Zh T T' i j) :
    cmp2 hs Y = llMap hs Zσ TT (mOf2 hs c) := by
  funext b; apply Subtype.ext; apply g.e.injective
  rw [embedding_secondComponent, hY, hY]
  exact gram_rows_secondEmbedding hs hTT hZ c b

end Formalism.L2.SG.LocalCountModules.AlgGSplit
