import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualPointLineDegreeAlt

/- English proof (translation)
Rewrite using `[← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]`. Use `congr 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

/- English proof (translation)
Introduce `m hm k`. Take `⟨⟩` from `k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Rewrite using `[Finset.sum_eq_single t]`.

Simplify using the standard rewrite rules. Introduce `c _ hc`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hc (sigma_mk_injective h).symm`.

Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_X {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']

/- English proof (translation)
Use `set σ := σ'.comp (algebraMap K K') with hσ`. Set `w : (K →+* ℂ) × Fin i → ℂ` to `fun q => if q.1 = σ then σ' (v q.2) else 0`. Establish `hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w`. Rewrite using `[dualRecover, LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `t`.

Simplify using `only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]`. Rewrite using `[Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]`. Simplify using `[hσ]`. Rewrite using `[dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]`. Simplify using `only [w, if_true, gramAt]`.

Both sides reduce to the same expression. Introduce `τ _ hτ`. Establish `h0 : (fun j => w (τ, j)) = 0`. Use function extensionality and compare the values at `j`. Simplify using `[w, hτ]`.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem dualNormSq_point (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (v : Fin i → K') (σ' : K' →+* ℂ) :
    dualNormSq b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) =
      (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
  classical
  set σ := σ'.comp (algebraMap K K') with hσ
  let w : (K →+* ℂ) × Fin i → ℂ := fun q => if q.1 = σ then σ' (v q.2) else 0
  have hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w := by
    rw [dualRecover, LinearEquiv.symm_apply_eq]
    funext t
    simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]
    simp [hσ]
  rw [dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]
  · simp only [w, if_true, gramAt]
    rfl
  · intro τ _ hτ
    have h0 : (fun j => w (τ, j)) = 0 := by
      funext j
      simp [w, hτ]
    rw [h0]
    simp
  · simp

end DualPointLineDegreeAlt

open DualPointLineDegreeAlt in

/- English proof (translation)
Introduce `K _ _ i F T _ _ b hb II hII W hW hbW`. Take `⟨K', _, _, _, v, hv, rfl⟩` from `hPt K i F T b W hW hbW`. Use `set y := dualPointCoord b v with hy`. Use `set A := dualLine F b hb with hA`. Use `⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩` and prove the remaining obligations.

Take `⟨t₀, ht₀⟩` from `hW.2.1.2.2 ()`. Use `set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs`. Establish `hs1 : IsMultiHomog s (fun _ => 1)` using `isMultiHomog_X t₀`. Establish `hsec : IsSectionOn (mCoordIdeal y) A s` using `⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩`. Establish `hsm : IsSmoothHerm A` using `(hSemi K i F T b hb).1`.

Establish `hy0 : y ⟨(), t₀⟩ ≠ 0`. Introduce `h`. Apply `ht₀` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `mConeMap y (X ⟨(), t₀⟩) = 0`. Simplify using `[mConeMap, h]`.

Establish `hR` using `(hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀`. Establish `hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (dualBlocks T)) A : Fin 1 → HermLine (dualBlocks T)) = ![A]`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression.

Rewrite `hR` using `[hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec]`. Establish `hV` using `hVert T K' y s hW hs1 ht₀`. Establish `hI` using `hAr T K' y A s hW hsec`. Establish `hL` using `hIdx K i F T b K' v hv`. Establish `hys : aeval y s = y ⟨(), t₀⟩` using `by simp [hs]`.

Establish `hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) = Real.log ‖σ' (y ⟨(), t₀⟩)‖ - 1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re`. Introduce `σ'`. Establish `hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) = (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re` using `dualNormSq_point b hb v σ'`. Establish `hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩))`. Use `A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)` as an intermediate fact.

Simplify `this` using `[hA, dualLine]`. Establish `hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0` using `norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)`. Simplify using `only [logNorm, hs, map_X, eval_X, hA, dualLine]`. Rewrite using `[Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hI` using `[Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib, sum_log_norm hy0, ← Finset.mul_sum]`. Rewrite `hV` using `[hys]`. Establish `hn : (0 : ℝ) < Module.finrank ℚ K'` using `by exact_mod_cast Module.finrank_pos`. Establish `hd : (0 : ℝ) < degC (mCoordIdeal y)` using `by exact_mod_cast hPos T K' y hW`. Rewrite `hL` using `[← hy]`.

Establish `hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ, Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) / Module.finrank ℚ K'`. Unfold `HermLattice.lineDegree subDegree normalise`. Rewrite using `[eq_inv_of_mul_eq_one_left hL, Real.log_inv]`. Establish `hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] = vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0` using `hR`. Establish `key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) * Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) + 1 / 2 * ∑ σ' : K' →+* ℂ, Real.log (gra …`.

Take the linear combination `hV - hI`. Rewrite using `[hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']`. Take the linear combination `key`.
-/
theorem DualPointLineDegree.proof (hPt : DualCurvePoint.Statement) (hPos : PointDegCPos.Statement)
    (hAr : PointArInt.Statement) (hVert : PointVertR.Statement) (hIdx : DualLineIndex.Statement)
    (hSemi : DualLineSemipositive.Statement) : DualPointLineDegree.Statement := by
  intro K _ _ i F T _ _ b hb II hII W hW hbW
  obtain ⟨K', _, _, _, v, hv, rfl⟩ := hPt K i F T b W hW hbW
  set y := dualPointCoord b v with hy
  set A := dualLine F b hb with hA
  refine ⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩
  obtain ⟨t₀, ht₀⟩ := hW.2.1.2.2 ()
  set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs
  have hs1 : IsMultiHomog s (fun _ => 1) := isMultiHomog_X t₀
  have hsec : IsSectionOn (mCoordIdeal y) A s := ⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩
  have hsm : IsSmoothHerm A := (hSemi K i F T b hb).1
  have hy0 : y ⟨(), t₀⟩ ≠ 0 := by
    intro h
    apply ht₀
    change mConeMap y (X ⟨(), t₀⟩) = 0
    simp [mConeMap, h]

  have hR := (hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW
    (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (dualBlocks T)) A : Fin 1 → HermLine (dualBlocks T)) =
      ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec] at hR

  have hV := hVert T K' y s hW hs1 ht₀
  have hI := hAr T K' y A s hW hsec
  have hL := hIdx K i F T b K' v hv
  have hys : aeval y s = y ⟨(), t₀⟩ := by simp [hs]
  have hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) =
      Real.log ‖σ' (y ⟨(), t₀⟩)‖ -
        1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
    intro σ'
    have hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) =
        (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re :=
      dualNormSq_point b hb v σ'
    have hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) := by
      have := A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)
      simpa [hA, dualLine] using this
    have hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)
    simp only [logNorm, hs, map_X, eval_X, hA, dualLine]
    rw [Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]
    ring
  rw [Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib,
    sum_log_norm hy0, ← Finset.mul_sum] at hI
  rw [hys] at hV
  have hn : (0 : ℝ) < Module.finrank ℚ K' := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < degC (mCoordIdeal y) := by exact_mod_cast hPos T K' y hW
  rw [← hy] at hL
  have hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ,
        Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) /
      Module.finrank ℚ K' := by
    unfold HermLattice.lineDegree subDegree normalise
    rw [eq_inv_of_mul_eq_one_left hL, Real.log_inv]
  have hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] =
      vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0 := hR
  have key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) *
      Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex
        (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) +
        1 / 2 * ∑ σ' : K' →+* ℂ,
          Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) := by
    linear_combination hV - hI
  rw [hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']
  linear_combination key

end

end GroundTheory.Heights₂.Heights
