import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneLeKappaMulPhase

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `Ext.GHadamard at hG`. Take `⟨x, u, hxu, hli, hnorm⟩` from `hI.u1`. Set `u' : Fin (Module.finrank ℝ (IR I)) → IR I` to `fun j => ⟨u j, (hxu j).2.1⟩`. Establish `hli' : LinearIndependent ℝ u'` using `LinearIndependent.of_comp (IR I).subtype (by exact hli)`. Establish `hU : IsUnit (ob.toBasis.det u')`.

Break down `isEmpty_or_nonempty (Fin (Module.finrank ℝ (IR I))) with hE | hN` into its components or cases. Rewrite using `[Module.Basis.det_apply, Matrix.det_isEmpty]`. Conclude with `isUnit_one`. Establish `hspan : Submodule.span ℝ (Set.range u') = ⊤` using `hli'.span_eq_top_of_card_eq_finrank (by simp)`. Establish `hU'` using `ob.toBasis.isUnit_det (Module.Basis.mk hli' hspan.ge)`.

Rewrite `hU'` using `[Module.Basis.coe_mk]`. Then use the resulting hypothesis. Establish `hint : ∀ j k, ∃ m : ℤ, (Hf (x j) (a k : Vsp X.dim)).im = m` using `fun j k => X.integral _ _ (hxu j).1 (hI.le (ha k))`. Set `Gz : Matrix (Fin (Module.finrank ℝ (IR I))) (Fin (Module.finrank ℝ (IR I))) ℤ` to `fun j k => (hint j k).choose`. Establish `hGjk : ∀ j k, inner ℝ (u' j) (a k) = (Gz j k : ℝ)` using `fun j k => by show _ = (((hint j k).choose : ℤ) : ℝ)`. Rewrite using `[← (hint j k).choose_spec]`.

Conclude with `(hxu j).2.2 _ (a k).2`. Establish `hmat : Matrix.transpose (ob.toBasis.toMatrix u') * ob.toBasis.toMatrix a = Gz.map (fun m : ℤ => (m : ℝ))`. Use extensionality with `j k`. Rewrite using `[Matrix.mul_apply, Matrix.map_apply, ← hGjk j k]`. Simplify using `only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]`.

Rewrite using `[← OrthonormalBasis.sum_inner_mul_inner ob]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[real_inner_comm (u' j) (ob i)]`. Establish `hdetG : ob.toBasis.det u' * ob.toBasis.det a = ((Gz.det : ℤ) : ℝ)`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_transpose (ob.toBasis.toMatrix u'), ← Matrix.det_mul, hmat]`.

Use `first`. Consider the case `exact (Int.cast_det Gz).symm`. Consider the case `exact (RingHom.map_det (Int.castRingHom ℝ) Gz).symm`. Consider the case `simp [Int.cast_det]`. Establish `hGz : Gz.det ≠ 0`.

Introduce `h0`. Establish `h00 : ob.toBasis.det u' * ob.toBasis.det a = 0` using `by rw [hdetG, h0, Int.cast_zero]`. Break down `mul_eq_zero.mp h00 with h | h` into its components or cases. Conclude with `hU.ne_zero h`. Conclude with `hdet h`.

Establish `h1 : (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a|`. Rewrite using `[← abs_mul, hdetG]`. Conclude with `Int.one_le_abs hGz` after adjusting the coercions. Establish `hH` using `hG (Module.finrank ℝ (IR I)) (ob.toBasis.toMatrix u')`. Rewrite `hH` using `[← Module.Basis.det_apply]`.

Establish `hcol : ∀ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E` using `E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) := fun j => by`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `hn : ∑ i, ob.toBasis.toMatrix u' i j ^ 2 = ‖u j‖ ^ 2`. Establish `hu : ‖u j‖ = ‖u' j‖` using `rfl`. Simplify using `only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]`.

Rewrite using `[hu, ← ob.repr.norm_map (u' j), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]`. Simplify using `[Real.norm_eq_abs, sq_abs]`. Rewrite using `[hn]`. Conclude with `hnorm j`. Establish `hprod : ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E` using `E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tof_covol_lb [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hG : Ext.GHadamard)
    (ob : OrthonormalBasis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I))
    (a : Fin (Module.finrank ℝ (IR I)) → IR I) (ha : ∀ i, (a i : Vsp X.dim) ∈ I)
    (hdet : ob.toBasis.det a ≠ 0) :
    1 ≤ |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph /
      (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
  unfold Ext.GHadamard at hG
  obtain ⟨x, u, hxu, hli, hnorm⟩ := hI.u1
  let u' : Fin (Module.finrank ℝ (IR I)) → IR I := fun j => ⟨u j, (hxu j).2.1⟩
  have hli' : LinearIndependent ℝ u' := LinearIndependent.of_comp (IR I).subtype (by exact hli)
  have hU : IsUnit (ob.toBasis.det u') := by
    rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ (IR I))) with hE | hN
    · rw [Module.Basis.det_apply, Matrix.det_isEmpty]
      exact isUnit_one
    · have hspan : Submodule.span ℝ (Set.range u') = ⊤ :=
        hli'.span_eq_top_of_card_eq_finrank (by simp)
      have hU' := ob.toBasis.isUnit_det (Module.Basis.mk hli' hspan.ge)
      rwa [Module.Basis.coe_mk] at hU'
  have hint : ∀ j k, ∃ m : ℤ, (Hf (x j) (a k : Vsp X.dim)).im = m := fun j k =>
    X.integral _ _ (hxu j).1 (hI.le (ha k))
  let Gz : Matrix (Fin (Module.finrank ℝ (IR I))) (Fin (Module.finrank ℝ (IR I))) ℤ :=
    fun j k => (hint j k).choose
  have hGjk : ∀ j k, inner ℝ (u' j) (a k) = (Gz j k : ℝ) := fun j k => by
    show _ = (((hint j k).choose : ℤ) : ℝ)
    rw [← (hint j k).choose_spec]
    exact (hxu j).2.2 _ (a k).2
  have hmat : Matrix.transpose (ob.toBasis.toMatrix u') * ob.toBasis.toMatrix a = Gz.map (fun m : ℤ => (m : ℝ)) := by
    ext j k
    rw [Matrix.mul_apply, Matrix.map_apply, ← hGjk j k]
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← OrthonormalBasis.sum_inner_mul_inner ob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (u' j) (ob i)]
  have hdetG : ob.toBasis.det u' * ob.toBasis.det a = ((Gz.det : ℤ) : ℝ) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_transpose (ob.toBasis.toMatrix u'),
      ← Matrix.det_mul, hmat]
    first
      | exact (Int.cast_det Gz).symm
      | exact (RingHom.map_det (Int.castRingHom ℝ) Gz).symm
      | simp [Int.cast_det]
  have hGz : Gz.det ≠ 0 := by
    intro h0
    have h00 : ob.toBasis.det u' * ob.toBasis.det a = 0 := by rw [hdetG, h0, Int.cast_zero]
    rcases mul_eq_zero.mp h00 with h | h
    · exact hU.ne_zero h
    · exact hdet h
  have h1 : (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := by
    rw [← abs_mul, hdetG]
    exact_mod_cast Int.one_le_abs hGz
  have hH := hG (Module.finrank ℝ (IR I)) (ob.toBasis.toMatrix u')
  rw [← Module.Basis.det_apply] at hH
  have hcol : ∀ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) := fun j => by
    apply Real.sqrt_le_sqrt
    have hn : ∑ i, ob.toBasis.toMatrix u' i j ^ 2 = ‖u j‖ ^ 2 := by
      have hu : ‖u j‖ = ‖u' j‖ := rfl
      simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
      rw [hu, ← ob.repr.norm_map (u' j), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact hnorm j
  have hprod : ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤
      Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
    calc ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2)
        ≤ ∏ _j : Fin (Module.finrank ℝ (IR I)), Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) :=
          Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _) (fun j _ => hcol j)
      _ = Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := h1
    _ ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) * |ob.toBasis.det a| :=
      mul_le_mul_of_nonneg_right (hH.trans hprod) (abs_nonneg _)
    _ = |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := mul_comm _ _

end

end ReciprocityTheory.ChartRestriction.G.I2
