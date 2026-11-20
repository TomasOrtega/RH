import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.HodgeConj

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))`.
-/
theorem spMap_conj_conj' : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Apply the tactic sequence `exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap]))`.
-/
theorem spMap_dual_conj_conj' :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap]))

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]`.
-/
theorem smul_gram_map_conj {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((c : ℂ) • (Mᴴ * M)) a b = starRingEnd ℂ (((c : ℂ) • ((M.map (starRingEnd ℂ))ᴴ * M.map (starRingEnd ℂ))) a b) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]

/- English proof (translation)
Introduce `D A N j S κ s x σ σ' hσ h'`. Establish `hφ : σ' = (starRingEnd ℂ).comp σ` using `RingHom.ext fun a => by`. Rewrite using `[hσ]`. Simplify using the standard rewrite rules. Establish `hpt : ∀ y : CxPts (genStr s.T.Z) σ, (spMap (starRingEnd ℂ) ≫ y.1) ≫ genStr s.T.Z = spMap σ'` using `fun y => by`.

Establish `h0 : y.1 ≫ genStr s.T.Z = spMap σ` using `y.2`. Rewrite using `[Category.assoc, h0, hσ, spMap, spMap, spMap, ← Spec.map_comp]`. Use `congr 1`. Conclude with `CommRingCat.hom_ext (RingHom.ext fun a => by simp)`. Set `jm : CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ'` to `fun y => ⟨spMap (starRingEnd ℂ) ≫ y.1, hpt y⟩`.

Establish `hj : IsConjMap jm` using `fun _ => rfl`. Introduce `V φ F τ a b hV`. Take `⟨g', h1, h2, h3⟩` from `h' V φ F τ a b hV`. Use `set W' : Set (CxPts (genStr s.T.Z) σ') := {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ' V.1 with hW'`. Establish `hWo : IsOpen W'` using `(isOpen_not_liesIn _).inter (isOpen_ptsIn _)`.

Establish `hsub : {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ V.1 ⊆ jm ⁻¹' W'` using `fun y hy => ⟨fun h => hy.1 ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h), (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hy.2⟩`. Establish `k1` using `(smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h1).2.1.mono hsub`. Establish `k2` using `(smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h2).2.1.mono hsub`. Use `⟨fun y => starRingEnd ℂ (g' (jm y)), k1.congr fun y _ => by simp, (show (manifold s.T.Z σ).SmoothOn _ (fun y => -(g' (jm y)).im) from fun i => (k2 i).neg).congr fun y _ => by simp, fun y hy hyV f hf => ?_⟩` and prove the remaining obligations. Establish `hnb : ¬ LiesIn y (genBd s.T.Z)` using `hy`.

Establish `hjy : jm y ∈ ptsIn _ σ' V.1` using `(mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hyV`. Establish `hjnb : ¬ LiesIn (jm y) (genBd s.T.Z)` using `fun h => hnb ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h)`. Establish `hx : (jm y).1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z` using `Category.assoc _ _ _`. Take `⟨f', hf'⟩` from `f.exists_isMap (starRingEnd ℂ) hφ hx`. Establish `e : evHom hjy = (starRingEnd ℂ).comp (evHom hyV)` using `RingHom.ext fun c => by`.

Rewrite using `[← ev_eq, ev_conj' (y := y) (y' := jm y) rfl, ev_eq hyV]`. Both sides reduce to the same expression. Establish `hF' : F.IsMap (evHom hjy) f'` using `fun τ i => by`. Use `(hf' τ i).trans ((congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (hf τ i)).trans ?_)` and prove the remaining obligations. Use `(GlobalTheory.GradedPieces.dual_comp (evHom hyV) (starRingEnd ℂ) (F.v τ i)).trans ?_` and prove the remaining obligations.

Rewrite using `[e]`. Establish `k3` using `h3 (jm y) hjnb hjy f' hF'`. Take `⟨hh, hhH⟩` from `(FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y)).2 hnb`. Take `⟨hh', hhm⟩` from `hh.exists_isMap (starRingEnd ℂ) hφ hx`. Establish `hhH' : IsHodgeFrame s.U (jm y) hh'` using `hhH.conj hσ (by show y.1 = spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1`.

Rewrite using `[← Category.assoc, spMap_conj_conj', Category.id_comp])`. Use `fun τ i => by rw [hhm τ i, ← Category.assoc, spMap_dual_conj_conj', Category.id_comp]`. Establish `hco : hh'.co f' τ = (hh.co f τ).map (starRingEnd ℂ)` using `hhm.co τ hf' hx`. Use `show _ = starRingEnd ℂ (g' (jm y))`. Rewrite using `[← k3, x.hodge_gram hhH' f' τ, x.hodge_gram hhH f τ, hco]`.

Conclude with `smul_gram_map_conj _ _ a b`.
-/
theorem smoothOn_hodge_of_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  intro D A N j S κ s x σ σ' hσ h'
  have hφ : σ' = (starRingEnd ℂ).comp σ := RingHom.ext fun a => by
    rw [hσ]; simp
  have hpt : ∀ y : CxPts (genStr s.T.Z) σ, (spMap (starRingEnd ℂ) ≫ y.1) ≫ genStr s.T.Z = spMap σ' := fun y => by
    have h0 : y.1 ≫ genStr s.T.Z = spMap σ := y.2
    rw [Category.assoc, h0, hσ, spMap, spMap, spMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  let jm : CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ' := fun y => ⟨spMap (starRingEnd ℂ) ≫ y.1, hpt y⟩
  have hj : IsConjMap jm := fun _ => rfl
  intro V φ F τ a b hV
  obtain ⟨g', h1, h2, h3⟩ := h' V φ F τ a b hV
  set W' : Set (CxPts (genStr s.T.Z) σ') := {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ' V.1 with hW'
  have hWo : IsOpen W' := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hsub : {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ V.1 ⊆ jm ⁻¹' W' := fun y hy =>
    ⟨fun h => hy.1 ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h),
      (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hy.2⟩
  have k1 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h1).2.1.mono hsub
  have k2 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h2).2.1.mono hsub
  refine ⟨fun y => starRingEnd ℂ (g' (jm y)), k1.congr fun y _ => by simp, (show (manifold s.T.Z σ).SmoothOn _ (fun y => -(g' (jm y)).im) from fun i => (k2 i).neg).congr
    fun y _ => by simp, fun y hy hyV f hf => ?_⟩
  have hnb : ¬ LiesIn y (genBd s.T.Z) := hy
  have hjy : jm y ∈ ptsIn _ σ' V.1 := (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hyV
  have hjnb : ¬ LiesIn (jm y) (genBd s.T.Z) := fun h => hnb ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h)
  have hx : (jm y).1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z := Category.assoc _ _ _
  obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) hφ hx
  have e : evHom hjy = (starRingEnd ℂ).comp (evHom hyV) := RingHom.ext fun c => by
    rw [← ev_eq, ev_conj' (y := y) (y' := jm y) rfl, ev_eq hyV]
    rfl
  have hF' : F.IsMap (evHom hjy) f' := fun τ i => by
    refine (hf' τ i).trans ((congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (hf τ i)).trans ?_)
    refine (GlobalTheory.GradedPieces.dual_comp (evHom hyV) (starRingEnd ℂ) (F.v τ i)).trans ?_
    rw [e]
  have k3 := h3 (jm y) hjnb hjy f' hF'
  obtain ⟨hh, hhH⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y)).2 hnb
  obtain ⟨hh', hhm⟩ := hh.exists_isMap (starRingEnd ℂ) hφ hx
  have hhH' : IsHodgeFrame s.U (jm y) hh' := hhH.conj hσ
    (by show y.1 = spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1
        rw [← Category.assoc, spMap_conj_conj', Category.id_comp])
    fun τ i => by rw [hhm τ i, ← Category.assoc, spMap_dual_conj_conj', Category.id_comp]
  have hco : hh'.co f' τ = (hh.co f τ).map (starRingEnd ℂ) := hhm.co τ hf' hx
  show _ = starRingEnd ℂ (g' (jm y))
  rw [← k3, x.hodge_gram hhH' f' τ, x.hodge_gram hhH f τ, hco]
  exact smul_gram_map_conj _ _ a b

end GlobalTheory.ShFam.HodgeConj
