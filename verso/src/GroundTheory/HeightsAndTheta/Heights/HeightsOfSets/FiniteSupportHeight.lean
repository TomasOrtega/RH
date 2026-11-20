import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

/- English proof (translation)
Unfold `evalCone`. Rewrite using `[MvPolynomial.eval₂_comp_left φ]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.
-/
theorem evalCone_map {ι : Type} {n : ι → ℕ} {F F' : Type*} [CommRing F] [CommRing F'] (φ : F →+* F')
    (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone (fun k i ↦ φ (z k i)) f = φ (evalCone z f) := by
  unfold evalCone
  rw [MvPolynomial.eval₂_comp_left φ]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Use `⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1 : σ (coordVec x k i) = 0` using `congrFun h i`. Establish `h2 : coordVec x k i = 0` using `(map_eq_zero σ).mp h1`. Conclude with `congrArg Subtype.val h2`.

Rewrite using `[evalCone_map σ (coordVec x) f]`. Establish `h0 : evalCone x f = 0` using `hx.2 f hf`. Establish `h1` using `evalCone_map (coordField x).val.toRingHom (coordVec x) f`. Establish `h2 : evalCone (coordVec x) f = 0`. Apply `(coordField x).val.toRingHom.injective` to reduce the goal to its premises.

Rewrite using `[map_zero, ← h1]`. Conclude with `h0`. Rewrite using `[h2, map_zero]`.
-/
theorem sigma_mem_points {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (P : ArithVariety n)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ))
    (σ : coordField x →+* ℂ) : (fun k i ↦ σ (coordVec x k i)) ∈ P.points ℂ := by
  refine ⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩
  · funext i
    have h1 : σ (coordVec x k i) = 0 := congrFun h i
    have h2 : coordVec x k i = 0 := (map_eq_zero σ).mp h1
    exact congrArg Subtype.val h2
  · rw [evalCone_map σ (coordVec x) f]
    have h0 : evalCone x f = 0 := hx.2 f hf
    have h1 := evalCone_map (coordField x).val.toRingHom (coordVec x) f
    have h2 : evalCone (coordVec x) f = 0 := by
      apply (coordField x).val.toRingHom.injective
      rw [map_zero, ← h1]
      exact h0
    rw [h2, map_zero]

/- English proof (translation)
Set `c : Coord n → coordField x` to `fun p ↦ coordVec x p.1 p.2`. Establish `hT : (⋃ p ∈ {p | c p ≠ 0}, Function.mulSupport fun w : FinitePlace (coordField x) ↦ w (c p)).Finite` using `Set.Finite.biUnion (Set.toFinite _) fun p hp ↦ FinitePlace.hasFiniteMulSupport hp`. Use `hT.subset fun v hv ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvT`. Apply `hv` to reduce the goal to its premises.

Use `Finset.sum_eq_zero fun k _ ↦ ?_` and prove the remaining obligations. Establish `h1 : ∀ i, coordVec x k i ≠ 0 → v (coordVec x k i) = 1`. Introduce `i hi`. Assume the negation of the conclusion as `hne`. Conclude with `hvT (Set.mem_biUnion (x := (⟨k, i⟩ : Coord n)) hi hne)`.

Take `⟨i0, hi0⟩` from `Function.ne_iff.mp (hx k)`. Establish `hi0' : coordVec x k i0 ≠ 0` using `fun h ↦ hi0 (congrArg Subtype.val h)`. Establish `hs : (⨆ i, v (coordVec x k i)) = 1`. Use `le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)` and prove the remaining obligations. Distinguish the cases in `h : coordVec x k i = 0`.

Rewrite using `[h, map_zero]`. Conclude with `zero_le_one`. Conclude with `(h1 i h).le`. Conclude with `(h1 i0 hi0').ge`. Rewrite using `[hs, Real.log_one, mul_zero]`.
-/
theorem finite_support_height {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (A : HermLine n)
    (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    (Function.support fun v : FinitePlace (coordField x) ↦
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))).Finite := by
  classical
  let c : Coord n → coordField x := fun p ↦ coordVec x p.1 p.2
  have hT : (⋃ p ∈ {p | c p ≠ 0},
      Function.mulSupport fun w : FinitePlace (coordField x) ↦ w (c p)).Finite :=
    Set.Finite.biUnion (Set.toFinite _) fun p hp ↦ FinitePlace.hasFiniteMulSupport hp
  refine hT.subset fun v hv ↦ ?_
  by_contra hvT
  apply hv
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have h1 : ∀ i, coordVec x k i ≠ 0 → v (coordVec x k i) = 1 := by
    intro i hi
    by_contra hne
    exact hvT (Set.mem_biUnion (x := (⟨k, i⟩ : Coord n)) hi hne)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hx k)
  have hi0' : coordVec x k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
  have hs : (⨆ i, v (coordVec x k i)) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)
    · by_cases h : coordVec x k i = 0
      · rw [h, map_zero]; exact zero_le_one
      · exact (h1 i h).le
    · exact (h1 i0 hi0').ge
  rw [hs, Real.log_one, mul_zero]

/- English proof (translation)
Introduce `ι _ _ n P A A' hdeg B hB x hx`. Establish `key : height A x - height A' x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ * ∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) - Real.log (A'.metric fun k i ↦ σ (coordVec x k i)))`. Unfold `height`. Rewrite using `[hdeg, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpos : (0 : ℝ) < Module.finrank ℚ (coordField x)`. Conclude with `Module.finrank_pos (R := ℚ) (M := coordField x)` after adjusting the coercions. Rewrite using `[key, abs_mul, abs_of_pos (inv_pos.mpr hpos)]`. Establish `hs : |∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) - Real.log (A'.metric fun k i ↦ σ (coordVec x k i)))| ≤ Module.finrank ℚ (coordField x) * B`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations.

Use `(Finset.sum_le_card_nsmul _ _ B fun σ _ ↦ hB _ (sigma_mem_points P hx σ)).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem heightMetricChange : HeightMetricChange.Statement := by
  intro ι _ _ n P A A' hdeg B hB x hx
  have key : height A x - height A' x =
      ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
        ∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
          Real.log (A'.metric fun k i ↦ σ (coordVec x k i))) := by
    unfold height
    rw [hdeg, Finset.sum_sub_distrib]
    ring
  have hpos : (0 : ℝ) < Module.finrank ℚ (coordField x) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := coordField x)
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have hs : |∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
      Real.log (A'.metric fun k i ↦ σ (coordVec x k i)))| ≤
      Module.finrank ℚ (coordField x) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B fun σ _ ↦ hB _ (sigma_mem_points P hx σ)).trans ?_
    rw [Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  calc _ ≤ ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ * (Module.finrank ℚ (coordField x) * B) :=
        mul_le_mul_of_nonneg_left hs (inv_pos.mpr hpos).le
    _ = B := by field_simp

/- English proof (translation)
Unfold `HermitianBundle.degree HermitianBundle.degreeWith`. Establish `hc : Nat.card ((⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range (HermitianBundle.exists_linearIndependent_rank E ⊥).choose)) = 1`. Apply `Nat.card_eq_one_iff_unique.mpr` to reduce the goal to its premises. Conclude with `⟨inferInstance, inferInstance⟩`. Rewrite using `[hc]`.

Establish `hz : E.rank ⊥ = 0` using `by simp [HermitianBundle.rank]`. Establish `hg : ∀ (m : ℕ) (hm : m = 0) (σ : K →+* ℂ) (f : Fin m → E.carrier), ‖HermitianBundle.gramDet E σ f‖ = 1`. Introduce `m hm σ f`. Substitute `hm` using the available equality. Simplify using `[HermitianBundle.gramDet]`.

Simplify using `[hg _ hz]`.
-/
theorem HermitianBundle.degree_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) :
    E.degree ⊥ = 0 := by
  unfold HermitianBundle.degree HermitianBundle.degreeWith
  have hc : Nat.card ((⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range
      (HermitianBundle.exists_linearIndependent_rank E ⊥).choose)) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨inferInstance, inferInstance⟩
  rw [hc]
  have hz : E.rank ⊥ = 0 := by simp [HermitianBundle.rank]
  have hg : ∀ (m : ℕ) (hm : m = 0) (σ : K →+* ℂ) (f : Fin m → E.carrier),
      ‖HermitianBundle.gramDet E σ f‖ = 1 := by
    intro m hm σ f
    subst hm
    simp [HermitianBundle.gramDet]
  simp [hg _ hz]

/- English proof (translation)
Introduce `K _ _ E r F _ _ hr i`. Distinguish the cases in `hi : (i : ℕ) = 0`. Establish `hrk : E.rank (F i) = 0` using `by rw [hr i, hi]`. Establish `hbot : F i = ⊥` using `(Submodule.finrank_eq_zero (R := 𝓞 K) (S := F i)).mp hrk`. Establish `hdeg : E.normDegree (F i) = 0`.

Rewrite using `[HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot, zero_div]`. Rewrite using `[hdeg, hi]`. Simplify using the standard rewrite rules. Establish `hne : F i ≠ ⊥`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[← hr i, h]`. Simplify using `[HermitianBundle.rank]`. Establish `hle : ((E.slope (F i) : ℝ) : EReal) ≤ E.slopeMax` using `le_iSup₂_of_le (F i) hne le_rfl`. Establish `hipos : (0 : ℝ) < (i : ℕ)` using `by exact_mod_cast Nat.pos_of_ne_zero hi`.

Establish `hd : ((E.normDegree (F i) : ℝ) : EReal) = (((i : ℕ) : EReal)) * ((E.slope (F i) : ℝ) : EReal)`. Establish `: E.normDegree (F i) = ((i : ℕ) : ℝ) * E.slope (F i)`. Unfold `HermitianBundle.slope`. Rewrite using `[hr i]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[hd, ge_iff_le, EReal.neg_le_neg_iff]`. Conclude with `mul_le_mul_of_nonneg_left hle (by positivity)`.
-/
theorem flagDegreeBound : FlagDegreeBound.Statement := by
  intro K _ _ E r F _ _ hr i
  by_cases hi : (i : ℕ) = 0
  · have hrk : E.rank (F i) = 0 := by rw [hr i, hi]
    have hbot : F i = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := F i)).mp hrk
    have hdeg : E.normDegree (F i) = 0 := by
      rw [HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot, zero_div]
    rw [hdeg, hi]
    simp
  · have hne : F i ≠ ⊥ := by
      intro h
      apply hi
      rw [← hr i, h]
      simp [HermitianBundle.rank]
    have hle : ((E.slope (F i) : ℝ) : EReal) ≤ E.slopeMax :=
      le_iSup₂_of_le (F i) hne le_rfl
    have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hd : ((E.normDegree (F i) : ℝ) : EReal) =
        (((i : ℕ) : EReal)) * ((E.slope (F i) : ℝ) : EReal) := by
      have : E.normDegree (F i) = ((i : ℕ) : ℝ) * E.slope (F i) := by
        unfold HermitianBundle.slope
        rw [hr i]
        field_simp
      rw [this]
      simp
    rw [hd, ge_iff_le, EReal.neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end GroundTheory.Heights₂.Heights
