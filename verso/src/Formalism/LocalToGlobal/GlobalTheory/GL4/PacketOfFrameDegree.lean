import Formalism.LocalToGlobal.GlobalTheory.GL4.NfAllSelfEq

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def QFrameDeg (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ,
    (D.R.N 0 : ℝ) * (CV.Q c τ).mu =
      (D.R.N 0 : ℝ) * (latK D.what₂.LL (MQ CV c τ)).mu +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)

section T

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

/- English proof (translation)
Use `⟨(CV.Q_good c τ).2.1.map _, ?_⟩` and prove the remaining obligations. Unfold `MQ`. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars]`. Rewrite using `[show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]`. Rewrite using `[← LinearEquiv.coe_coe, Submodule.span_image, (CV.Q_good c τ).2.2, Submodule.map_top]`.

Conclude with `LinearEquiv.range _`.
-/
theorem MQ_lattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule.IsLattice D.what₂.LL (MQ CV c τ) := by
  refine ⟨(CV.Q_good c τ).2.1.map _, ?_⟩
  unfold MQ
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
  rw [← LinearEquiv.coe_coe, Submodule.span_image, (CV.Q_good c τ).2.2, Submodule.map_top]
  exact LinearEquiv.range _

/- English proof (translation)
Unfold `detTwK`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => ?_` and prove the remaining obligations. Unfold `detPow`. Conclude with `Units.ne_zero _`.
-/
theorem detTwK_inv_ne (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹ ≠ 0 := by
  unfold detTwK
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
  unfold detPow
  exact Units.ne_zero _

/- English proof (translation)
Simplify using `only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, invFr, brpGL]`. Use `show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det⁻¹ = _`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]`.
-/
theorem det_invFr_inv (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Matrix.GeneralLinearGroup.det ((invFr CV v c)⁻¹ τ) : ℂˣ) : ℂ) = ((CV.Q c τ).X v).det := by
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, invFr,
    brpGL]
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det⁻¹ = _
  rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]

/- English proof (translation)
Unfold `detTwK`. Simplify using `only [detPow, Units.val_zpow_eq_zpow_val, det_invFr_inv, norm_prod, norm_zpow]`. Establish `hne : ∀ τ, ((CV.Q c τ).X v).det ≠ 0` using `fun τ => by`. Rewrite using `[← det_invFr_inv CV v c τ]`. Conclude with `Units.ne_zero _`.

Rewrite using `[← Finset.prod_pow, Real.log_prod]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[show (‖((CV.Q c τ).X v).det‖ ^ ((D.fm u).lam 0 τ).detShift) ^ 2 = (‖((CV.Q c τ).X v).det‖ ^ 2) ^ ((D.fm u).lam 0 τ).detShift by rw [sq, sq, mul_zpow], Real.log_zpow]`. Introduce `τ _`. Conclude with `pow_ne_zero _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hne τ)))`.
-/
theorem log_detTw (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    Real.log (‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) =
      ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) := by
  unfold detTwK
  simp only [detPow, Units.val_zpow_eq_zpow_val, det_invFr_inv, norm_prod, norm_zpow]
  have hne : ∀ τ, ((CV.Q c τ).X v).det ≠ 0 := fun τ => by
    rw [← det_invFr_inv CV v c τ]
    exact Units.ne_zero _
  rw [← Finset.prod_pow, Real.log_prod]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show (‖((CV.Q c τ).X v).det‖ ^ ((D.fm u).lam 0 τ).detShift) ^ 2 =
        (‖((CV.Q c τ).X v).det‖ ^ 2) ^ ((D.fm u).lam 0 τ).detShift by rw [sq, sq, mul_zpow], Real.log_zpow]
  · intro τ _
    exact pow_ne_zero _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hne τ)))

/- English proof (translation)
Establish `hn` using `rank_zero_pos D`. Establish `hk` using `columnCount_pos D`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hn]`. Use `weight_eq_lamCol D u τ ⟨D.R.N 0 - 1, by omega⟩` as an intermediate fact.

Rewrite using `[this]`. Use `congr 3`. Simplify using `[Ranks.N_zero]`.
-/
theorem detShift_eq (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).detShift : ℤ) : ℝ) = ((lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hn := rank_zero_pos D
  have hk := columnCount_pos D
  unfold DomWeight.detShift
  rw [dif_pos hn]
  have := weight_eq_lamCol D u τ ⟨D.R.N 0 - 1, by omega⟩
  rw [this]
  congr 3
  simp [Ranks.N_zero]

/- English proof (translation)
Introduce `u CV c y hy`. Take `⟨hyd, hli, -⟩` from `hy`. Use `(columnHypotheses D u).tc` as an intermediate fact. Establish `hn : 0 < D.R.N 0` using `rank_zero_pos D`. Establish `hM : ∀ τ, Submodule.IsLattice D.what₂.LL (MQ CV c τ)` using `MQ_lattice CV c`.

Use `⟨cfMap ((D.fm u).lam 0) (gG CV c y hli) ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))), twIdeal ((D.fm u).lam 0) (MQ CV c) hM, fun v => ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2, ?_, twIde …` and prove the remaining obligations. Conclude with `injOn_NC CV c _ (cfMap_injective _ _)`. Introduce `x hx m`. Rewrite using `[twIdeal_coe]`. Conclude with `cf_mem_twId CV c y hyd (gG CV c y hli) (fun τ => gG_coe CV c y hli τ) hx m`.

Introduce `v`. Conclude with `pow_pos (norm_pos_iff.2 (detTwK_inv_ne CV c v)) 2`. Introduce `v x`. Conclude with `class_norm CV c y hli v x`. Rewrite using `[twisted_ideal_norm_formula D.what₂.LL hn _ _ hM]`.

Repeatedly rewrite using `[log_detTw CV c]`. Establish `hQ` using `fun τ => h u CV c τ`. Establish `hslope` using `fun τ => q_lattice_slope D u CV c τ`. Establish `hk : (D.R.N 0 : ℝ) = (D.R.k : ℝ)` using `by rw [Ranks.N_zero]`. Establish `hk0 : (0 : ℝ) < D.R.k` using `by exact_mod_cast columnCount_pos D`.

Establish `e1 : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) = ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2))`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]`. Use `le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_add, ← hQ τ, hslope τ, hk, detShift_eq]`. Clear the denominators using the available nonvanishing facts.
-/
theorem classMapT_of (h : QFrameDeg D) : ClassMapT D := by
  intro u CV c y hy
  obtain ⟨hyd, hli, -⟩ := hy
  have := (columnHypotheses D u).tc
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  have hM : ∀ τ, Submodule.IsLattice D.what₂.LL (MQ CV c τ) := MQ_lattice CV c
  refine ⟨cfMap ((D.fm u).lam 0) (gG CV c y hli) ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))), twIdeal ((D.fm u).lam 0) (MQ CV c) hM,
    fun v => ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2, ?_, twIdeal_ne_zero _ _ hM, ?_, ?_, ?_, ?_⟩
  · exact injOn_NC CV c _ (cfMap_injective _ _)
  · intro x hx m
    rw [twIdeal_coe]
    exact cf_mem_twId CV c y hyd (gG CV c y hli) (fun τ => gG_coe CV c y hli τ) hx m
  · intro v
    exact pow_pos (norm_pos_iff.2 (detTwK_inv_ne CV c v)) 2
  · intro v x
    exact class_norm CV c y hli v x
  · rw [twisted_ideal_norm_formula D.what₂.LL hn _ _ hM]
    simp_rw [log_detTw CV c]
    have hQ := fun τ => h u CV c τ
    have hslope := fun τ => q_lattice_slope D u CV c τ
    have hk : (D.R.N 0 : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
    have e1 : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) =
        ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [e1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)
    rw [← mul_add, ← hQ τ, hslope τ, hk, detShift_eq]
    field_simp

end T

/- English proof (translation)
Conclude with `third_link_of_archimedean fun D => classMapT_of (h D)`.
-/
theorem Link6F_of_frameDeg (h : ∀ D, QFrameDeg D) : Link6F := by
  exact third_link_of_archimedean fun D => classMapT_of (h D)

/- English proof (translation)
Conclude with `packetFamily_of_classMapT fun D => classMapT_of (h D)`.
-/
theorem packet_of_frame_degree (h : ∀ D, QFrameDeg D) : KudlaFamilyOfMinkowskiTransference := by
  exact packetFamily_of_classMapT fun D => classMapT_of (h D)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
