import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_linearIndependent_fin (K := K) (E := E.carrier)`. Set `s' : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier)` to `fun i ↦ ⟨s i, Submodule.mem_top⟩`. Establish `hs' : LinearIndependent (𝓞 K) s'` using `LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hs`. Establish `hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E.carrier)) = E.rank ⊤`. Rewrite using `[Fintype.card_fin, HermitianBundle.rank, finrank_top]`.

Rewrite using `[E.degree_eq_of_linearIndependent ⊤ hs' hcard, HermitianBundle.arithDegree, arithDegree_eq E.metric hs (Fintype.card_fin _), GroundTheory.Heights₂.Heights.degreeWith]`. Establish `hmap : (Submodule.span (𝓞 K) (Set.range s')).map (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) E.carrier) ≃ₗ[𝓞 K] E.carrier).toLinearMap = Submodule.span (𝓞 K) (Set.range s)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[Nat.card_congr (Submodule.Quotient.equiv _ _ Submodule.topEquiv hmap).toEquiv]`.
-/
theorem HermitianBundle.degree_top_eq_arithDegree {K : Type*} [Field K] [NumberField K]
    (E : HermitianBundle K) : E.degree ⊤ = E.arithDegree := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E.carrier)
  let s' : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i ↦ ⟨s i, Submodule.mem_top⟩
  have hs' : LinearIndependent (𝓞 K) s' :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hs
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E.carrier)) = E.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top]
  rw [E.degree_eq_of_linearIndependent ⊤ hs' hcard, HermitianBundle.arithDegree,
    arithDegree_eq E.metric hs (Fintype.card_fin _), GroundTheory.Heights₂.Heights.degreeWith]
  have hmap : (Submodule.span (𝓞 K) (Set.range s')).map
      (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) E.carrier) ≃ₗ[𝓞 K] E.carrier).toLinearMap =
      Submodule.span (𝓞 K) (Set.range s) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Submodule.topEquiv hmap).toEquiv]

/- English proof (translation)
Distinguish the cases in `hr : E.rank G = 0`. Establish `hbot : G = ⊥` using `(Submodule.finrank_eq_zero (R := 𝓞 K) (S := G)).mp hr`. Rewrite using `[hr, HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot]`. Simplify using the standard rewrite rules. Establish `hne : G ≠ ⊥`.

Introduce and unpack `rfl`. Apply `hr` to reduce the goal to its premises. Simplify using `[HermitianBundle.rank]`. Establish `hle : ((E.slope G : ℝ) : EReal) ≤ E.slopeMax` using `le_iSup₂_of_le G hne le_rfl`. Establish `hs : E.slope G ≤ m` using `EReal.coe_le_coe_iff.mp (hle.trans hm)`.

Establish `hrpos : (0 : ℝ) < E.rank G` using `by exact_mod_cast Nat.pos_of_ne_zero hr`. Establish `heq : E.normDegree G = E.rank G * E.slope G`. Unfold `HermitianBundle.slope`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`.

Conclude with `mul_le_mul_of_nonneg_left hs hrpos.le`.
-/
theorem HermitianBundle.normDegree_le_rank_mul {K : Type} [Field K] [NumberField K]
    (E : HermitianBundle.{0} K) (G : Submodule (𝓞 K) E.carrier) (m : ℝ)
    (hm : E.slopeMax ≤ (m : EReal)) : E.normDegree G ≤ E.rank G * m := by
  by_cases hr : E.rank G = 0
  · have hbot : G = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := G)).mp hr
    rw [hr, HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot]
    simp
  · have hne : G ≠ ⊥ := by
      rintro rfl
      apply hr
      simp [HermitianBundle.rank]
    have hle : ((E.slope G : ℝ) : EReal) ≤ E.slopeMax := le_iSup₂_of_le G hne le_rfl
    have hs : E.slope G ≤ m := EReal.coe_le_coe_iff.mp (hle.trans hm)
    have hrpos : (0 : ℝ) < E.rank G := by exact_mod_cast Nat.pos_of_ne_zero hr
    have heq : E.normDegree G = E.rank G * E.slope G := by
      unfold HermitianBundle.slope
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hs hrpos.le

/- English proof (translation)
Introduce `K _ _ E' E E'' X`. Use `show (⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((E.slope F : ℝ) : EReal)) ≤ _`. Use `iSup₂_le fun F hF ↦ ?_` and prove the remaining obligations. Break down `eq_or_ne (max E'.slopeMax E''.slopeMax) ⊤ with hM | hM` into its components or cases. Rewrite using `[hM]`.

Conclude with `le_top`. Establish `hrank` using `X.rank_sub_eq F`. Establish `hpos : 0 < E.rank F`. Break down `Nat.eq_zero_or_pos (E.rank F) with h | h` into its components or cases. Conclude with `absurd ((Submodule.finrank_eq_zero (R := 𝓞 K) (S := F)).mp h) hF`.

Conclude with `h`. Establish `hMbot : max E'.slopeMax E''.slopeMax ≠ ⊥`. Establish `: 0 < E'.rank (F.comap X.incl) ∨ 0 < E''.rank (F.map X.proj)` using `by omega`. Break down `this with h | h` into its components or cases. Establish `hne : F.comap X.incl ≠ ⊥`.

Introduce `h0`. Rewrite `h` using `[h0]`. Simplify using `[HermitianBundle.rank] at h`. Establish `h0 : ((E'.slope (F.comap X.incl) : ℝ) : EReal) ≤ E'.slopeMax` using `le_iSup₂_of_le (F.comap X.incl) hne le_rfl`. Establish `hle` using `h0.trans (le_max_left _ E''.slopeMax)`.

Conclude with `ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle`. Establish `hne : F.map X.proj ≠ ⊥`. Introduce `h0`. Rewrite `h` using `[h0]`. Simplify using `[HermitianBundle.rank] at h`.

Establish `h0 : ((E''.slope (F.map X.proj) : ℝ) : EReal) ≤ E''.slopeMax` using `le_iSup₂_of_le (F.map X.proj) hne le_rfl`. Establish `hle` using `h0.trans (le_max_right E'.slopeMax _)`. Conclude with `ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle`. Use `set m := (max E'.slopeMax E''.slopeMax).toReal`. Establish `hMm : max E'.slopeMax E''.slopeMax = (m : EReal)` using `(EReal.coe_toReal hM hMbot).symm`.

Establish `h1` using `E'.normDegree_le_rank_mul (F.comap X.incl) m ((le_max_left _ _).trans_eq hMm)`. Establish `h2` using `E''.normDegree_le_rank_mul (F.map X.proj) m ((le_max_right _ _).trans_eq hMm)`. Establish `hdeg` using `X.degree_submodule_le F`. Establish `hd : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hnd : E.normDegree F ≤ E'.normDegree (F.comap X.incl) + E''.normDegree (F.map X.proj)`.

Simplify using `only [HermitianBundle.normDegree]`. Rewrite using `[← add_div]`. Conclude with `div_le_div_of_nonneg_right hdeg hd.le`. Establish `hrpos : (0 : ℝ) < E.rank F` using `by exact_mod_cast hpos`. Establish `hr : (E.rank F : ℝ) = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj)`.

Conclude with `hrank` after adjusting the coercions. Establish `hs : E.slope F ≤ m`. Unfold `HermitianBundle.slope`. Rewrite using `[div_le_iff₀ hrpos, hr]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hMm]`. Conclude with `EReal.coe_le_coe_iff.mpr hs`.
-/
theorem slopeMaxExtension : SlopeMaxExtension.Statement := by
  intro K _ _ E' E E'' X
  show (⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((E.slope F : ℝ) : EReal)) ≤ _
  refine iSup₂_le fun F hF ↦ ?_
  rcases eq_or_ne (max E'.slopeMax E''.slopeMax) ⊤ with hM | hM
  · rw [hM]
    exact le_top
  have hrank := X.rank_sub_eq F
  have hpos : 0 < E.rank F := by
    rcases Nat.eq_zero_or_pos (E.rank F) with h | h
    · exact absurd ((Submodule.finrank_eq_zero (R := 𝓞 K) (S := F)).mp h) hF
    · exact h
  have hMbot : max E'.slopeMax E''.slopeMax ≠ ⊥ := by
    have : 0 < E'.rank (F.comap X.incl) ∨ 0 < E''.rank (F.map X.proj) := by omega
    rcases this with h | h
    · have hne : F.comap X.incl ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E'.slope (F.comap X.incl) : ℝ) : EReal) ≤ E'.slopeMax :=
        le_iSup₂_of_le (F.comap X.incl) hne le_rfl
      have hle := h0.trans (le_max_left _ E''.slopeMax)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
    · have hne : F.map X.proj ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E''.slope (F.map X.proj) : ℝ) : EReal) ≤ E''.slopeMax :=
        le_iSup₂_of_le (F.map X.proj) hne le_rfl
      have hle := h0.trans (le_max_right E'.slopeMax _)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  set m := (max E'.slopeMax E''.slopeMax).toReal
  have hMm : max E'.slopeMax E''.slopeMax = (m : EReal) := (EReal.coe_toReal hM hMbot).symm
  have h1 := E'.normDegree_le_rank_mul (F.comap X.incl) m ((le_max_left _ _).trans_eq hMm)
  have h2 := E''.normDegree_le_rank_mul (F.map X.proj) m ((le_max_right _ _).trans_eq hMm)
  have hdeg := X.degree_submodule_le F
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hnd : E.normDegree F ≤ E'.normDegree (F.comap X.incl) + E''.normDegree (F.map X.proj) := by
    simp only [HermitianBundle.normDegree]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hdeg hd.le
  have hrpos : (0 : ℝ) < E.rank F := by exact_mod_cast hpos
  have hr : (E.rank F : ℝ) = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) := by
    exact_mod_cast hrank
  have hs : E.slope F ≤ m := by
    unfold HermitianBundle.slope
    rw [div_le_iff₀ hrpos, hr]
    calc E.normDegree F ≤ E'.rank (F.comap X.incl) * m + E''.rank (F.map X.proj) * m := by linarith
      _ = m * (E'.rank (F.comap X.incl) + E''.rank (F.map X.proj)) := by ring
  rw [hMm]
  exact EReal.coe_le_coe_iff.mpr hs

end

end GroundTheory.Heights₂.Heights
