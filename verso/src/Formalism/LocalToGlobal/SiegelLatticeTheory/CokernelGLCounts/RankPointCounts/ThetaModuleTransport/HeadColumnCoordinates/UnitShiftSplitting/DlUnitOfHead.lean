import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DetRel

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Unfold `Model.R at hx`. Simplify using `only [hs, Subring.mem_comap, Subring.mem_map] at hx`. Take `⟨p, hp, hpe⟩` from `hx`. Establish `e1 : (g.e x).1 = (p.1 : F)`. Use `congrArg Prod.fst hpe` as an intermediate fact.

Simplify using `using this.symm`. Establish `e2 : (g.e x).2 = (p.2 : F)`. Use `congrArg Prod.snd hpe` as an intermediate fact. Simplify using `using this.symm`. Rewrite `hp` using `[RingHom.mem_eqLocus]`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst, RingHom.coe_snd] at hp`. Rewrite `hp` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hp`. Use `⟨by rw [e1]; exact p.1.2, by rw [e2]; exact p.2.2, (c : F), c.2, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, e2, mul_comm]`.

Conclude with `hc.symm` after adjusting the coercions.
-/
theorem R_comp {g : SplitG M.L} (hs : M.split = some g) {x : E} (hx : x ∈ M.R) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] ∧ ∃ c ∈ 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c := by
  unfold Model.R at hx
  simp only [hs, Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨p, hp, hpe⟩ := hx
  have e1 : (g.e x).1 = (p.1 : F) := by
    have := congrArg Prod.fst hpe
    simpa using this.symm
  have e2 : (g.e x).2 = (p.2 : F) := by
    have := congrArg Prod.snd hpe
    simpa using this.symm
  rw [RingHom.mem_eqLocus] at hp
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst, RingHom.coe_snd] at hp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hp
  obtain ⟨c, hc⟩ := hp
  refine ⟨by rw [e1]; exact p.1.2, by rw [e2]; exact p.2.2, (c : F), c.2, ?_⟩
  rw [e1, e2, mul_comm]
  exact_mod_cast hc.symm

/- English proof (translation)
Rewrite using `[M.L.O_def]`. Establish `hx : x = ((g.e x).1 : F) • g.e.symm (1, 0) + ((g.e x).2 : F) • g.e.symm (0, 1)`. Apply `g.e.injective` to reduce the goal to its premises. Simplify using `only [map_add, map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]`. Establish `hid : ∀ y : F × F, y * y = y → IsIntegral 𝒪[F] (g.e.symm y)`.

Introduce `y hy`. Use `⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]`. Rewrite using `[sq, ← map_mul, hy, sub_self]`. Establish `hsc : ∀ (c : F) (hc : c ∈ 𝒪[F]) (y : E), IsIntegral 𝒪[F] y → IsIntegral 𝒪[F] (c • y)`.

Introduce `c hc y hy`. Establish `e : c • y = algebraMap 𝒪[F] E ⟨c, hc⟩ * y`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(isIntegral_algebraMap).mul hy`. Rewrite using `[hx]`. Conclude with `(hsc _ h1 _ (hid (1, 0) (by simp))).add (hsc _ h2 _ (hid (0, 1) (by simp)))`.
-/
theorem mem_O_of_comp (g : SplitG M.L) {x : E} (h1 : (g.e x).1 ∈ 𝒪[F]) (h2 : (g.e x).2 ∈ 𝒪[F]) :
    x ∈ M.L.O := by
  rw [M.L.O_def]
  have hx : x = ((g.e x).1 : F) • g.e.symm (1, 0) + ((g.e x).2 : F) • g.e.symm (0, 1) := by
    apply g.e.injective
    simp only [map_add, map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
      Prod.mk_add_mk, add_zero, zero_add]
  have hid : ∀ y : F × F, y * y = y → IsIntegral 𝒪[F] (g.e.symm y) := by
    intro y hy
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    rw [sq, ← map_mul, hy, sub_self]
  have hsc : ∀ (c : F) (hc : c ∈ 𝒪[F]) (y : E), IsIntegral 𝒪[F] y → IsIntegral 𝒪[F] (c • y) := by
    intro c hc y hy
    have e : c • y = algebraMap 𝒪[F] E ⟨c, hc⟩ * y := by
      rw [Algebra.smul_def]
      rfl
    rw [e]
    exact (isIntegral_algebraMap).mul hy
  rw [hx]
  exact (hsc _ h1 _ (hid (1, 0) (by simp))).add (hsc _ h2 _ (hid (0, 1) (by simp)))

/- English proof (translation)
Rewrite `hx`, the goal using `[M.L.O_def]`. Conclude with `hx.map ((M.L.cj : E ≃ₐ[F] E).toAlgHom.restrictScalars 𝒪[F])`.
-/
theorem cj_mem_O {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map ((M.L.cj : E ≃ₐ[F] E).toAlgHom.restrictScalars 𝒪[F])

/- English proof (translation)
Establish `h` using `hy.map g.e`. Rewrite `h` using `[Prod.isUnit_iff]`. Conclude with `⟨h.1.ne_zero, h.2.ne_zero⟩`.
-/
theorem isUnit_comp (g : SplitG M.L) {y : E} (hy : IsUnit y) : (g.e y).1 ≠ 0 ∧ (g.e y).2 ≠ 0 := by
  have h := hy.map g.e
  rw [Prod.isUnit_iff] at h
  exact ⟨h.1.ne_zero, h.2.ne_zero⟩

/- English proof (translation)
Set `f1 : E →+* F` to `(RingHom.fst F F).comp g.e.toRingEquiv.toRingHom`. Set `f2 : E →+* F` to `(RingHom.snd F F).comp g.e.toRingEquiv.toRingHom`. Establish `hd1 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).1 = (A.map f1).det` using `fun A => by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hd2 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).2 = (A.map f2).det` using `fun A => by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Both sides reduce to the same expression. Establish `hS1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f1 = ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map f1`. Use extensionality with `i j`.

Simplify using `[HermSp.ZZplusOf, hs, f1, Fin.castSucc_ne_last, div_eq_inv_mul]`. Establish `hS2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f2 = (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map f2).transpose`. Use extensionality with `i j`. Simplify using `[HermSp.ZZplusOf, hs, f2, Fin.castSucc_ne_last, div_eq_inv_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hd1, hS1, Matrix.det_smul, Fintype.card_fin, hd1]`. Rewrite using `[hd2, hS2, Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, hd2]`.
-/
theorem head_zz_comp {g : SplitG M.L} (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (g.e ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det).1 =
        ((g.q : F)⁻¹) ^ r * (g.e (Zh.submatrix Fin.castSucc Fin.castSucc).det).1 ∧
      (g.e ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det).2 =
        (-(g.q : F)⁻¹) ^ r * (g.e (Zh.submatrix Fin.castSucc Fin.castSucc).det).2 := by
  let f1 : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let f2 : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have hd1 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).1 = (A.map f1).det := fun A => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hd2 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).2 = (A.map f2).det := fun A => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hS1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f1 =
      ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map f1 := by
    ext i j
    simp [HermSp.ZZplusOf, hs, f1, Fin.castSucc_ne_last, div_eq_inv_mul]
  have hS2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f2 =
      (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map f2).transpose := by
    ext i j
    simp [HermSp.ZZplusOf, hs, f2, Fin.castSucc_ne_last, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · rw [hd1, hS1, Matrix.det_smul, Fintype.card_fin, hd1]
  · rw [hd2, hS2, Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, hd2]

/- English proof (translation)
Establish `hDl : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det`. Unfold `HermSp.Dl`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Both sides reduce to the same expression. Take `⟨h1, h2⟩` from `isUnit_comp g hu`.

Rewrite `h1` using `[(head_zz_comp hs (H.Zhat f f') T T').1]`. Rewrite `h2` using `[(head_zz_comp hs (H.Zhat f f') T T').2]`. Establish `h1' : (g.e (H.Dl f f' r)).1 ≠ 0`. Rewrite using `[hDl]`. Conclude with `right_ne_zero_of_mul h1`.

Establish `h2' : (g.e (H.Dl f f' r)).2 ≠ 0`. Rewrite using `[hDl]`. Conclude with `right_ne_zero_of_mul h2`. Establish `hU : IsUnit (g.e (H.Dl f f' r))` using `Prod.isUnit_iff.2 ⟨isUnit_iff_ne_zero.2 h1', isUnit_iff_ne_zero.2 h2'⟩`. Establish `h3` using `hU.map g.e.symm`.

Simplify using `using h3`.
-/
theorem dl_unit_of_head {g : SplitG M.L} (hs : M.split = some g) (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) (T T' : F)
    (hu : IsUnit ((HermSp.ZZplusOf M (H.Zhat f f') T T').submatrix Fin.castSucc Fin.castSucc).det) :
    IsUnit (H.Dl f f' r) := by
  have hDl : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
    rfl
  obtain ⟨h1, h2⟩ := isUnit_comp g hu
  rw [(head_zz_comp hs (H.Zhat f f') T T').1] at h1
  rw [(head_zz_comp hs (H.Zhat f f') T T').2] at h2
  have h1' : (g.e (H.Dl f f' r)).1 ≠ 0 := by
    rw [hDl]
    exact right_ne_zero_of_mul h1
  have h2' : (g.e (H.Dl f f' r)).2 ≠ 0 := by
    rw [hDl]
    exact right_ne_zero_of_mul h2
  have hU : IsUnit (g.e (H.Dl f f' r)) :=
    Prod.isUnit_iff.2 ⟨isUnit_iff_ne_zero.2 h1', isUnit_iff_ne_zero.2 h2'⟩
  have h3 := hU.map g.e.symm
  simpa using h3

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
