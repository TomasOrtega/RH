import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramIff

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ M hl _ e hes hO V _ _ H Λ π Ph hπ ϖ hϖ ι _ _ G₀ h1 h2 h3`. Use `haveI := hl`. Establish `hπa` using `hπ.1`. Establish `hπL` using `hπ.2.1`. Set `σ : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`.

Set `lift : (Fin (Module.finrank E V) → 𝓀[F]) → (Fin (Module.finrank E V) → 𝓀[F]) → V` to `fun X1 Y1 => π.symm ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k))`. Establish `hlift : ∀ X1 Y1, π (lift X1 Y1) = ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k))` using `fun _ _ => AddEquiv.apply_symm_apply _ _`. Establish `hliftL : ∀ X1 Y1, lift X1 Y1 ∈ Λ` using `fun X1 Y1 => (hπL _).2 (by rw [hlift]; exact ⟨fun k => liftF_mem F _, fun k => liftF_mem F _⟩)`. Establish `hred1 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).1 k) = X1 k`. Introduce `X1 Y1 k`.

Rewrite using `[hlift]`. Conclude with `resF_liftF F _`. Establish `hred2 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).2 k) = Y1 k`. Introduce `X1 Y1 k`. Rewrite using `[hlift]`.

Conclude with `resF_liftF F _`. Set `Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]` to `Matrix.of fun i j => resF F ((e (G₀ (σ.symm j) (σ.symm i))).1)`. Set `Ph'` to `Ph.map (IsLocalRing.residue 𝒪[F])`. Set `g : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) → (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ)` to `fun XY a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (lift (XY.1 (σ a)) (XY.2 (σ a)))`. Set `S : Set ((Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]))` to `{XY | LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph' k l * XY.2 j l = Gm i j}`.

Establish `hL` using `fun (v : ι → V) (hv : ∀ a, v a ∈ Λ) a => (hπL (v a)).1 (hv a)`. Establish `hR : Set.range (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} => fun a => Submodule.Quotient.mk (p` using `H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = g '' S := by`. Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨v, hP, hG⟩, rfl⟩`.

Establish `hv : ∀ a, v a ∈ Λ` using `hP.1`. Establish `hpr` using `(prim_iff e hO H Λ π hπa hπL hϖ v hv).1 hP`. Establish `hgr` using `(gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).1 hG`. Use `⟨((fun i k => resF F ((π (v (σ.symm i))).1 k)), fun i k => resF F ((π (v (σ.symm i))).2 k)), ⟨hpr.1.comp σ.symm σ.symm.injective, hpr.2.comp σ.symm σ.symm.injective, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Use `hgr (σ.symm j) (σ.symm i)` as an intermediate fact. Rewrite `this` using `[resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph]`. Conclude with `this`. Use function extensionality and compare the values at `a show Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hv a)]`.

Use `⟨fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hred1]`. Simplify using the standard rewrite rules. Rewrite using `[hred2]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨XY, ⟨hX, hY, hE⟩, rfl⟩`. Set `v : ι → V` to `fun a => lift (XY.1 (σ a)) (XY.2 (σ a))`. Establish `hv : ∀ a, v a ∈ Λ` using `fun a => hliftL _ _`. Establish `hr1 : (redM F fun a => (π (v a)).1) = XY.1 ∘ σ`. Use function extensionality and compare the values at `a k`.

Conclude with `hred1 _ _ k`. Establish `hr2 : (redM F fun a => (π (v a)).2) = XY.2 ∘ σ`. Use function extensionality and compare the values at `a k`. Conclude with `hred2 _ _ k`. Establish `hP : H.Prim Λ v` using `(prim_iff e hO H Λ π hπa hπL hϖ v hv).2 ⟨by rw [hr1]; exact hX.comp σ σ.injective, by rw [hr2]; exact hY.comp σ σ.injective⟩`.

Establish `hG` using `(gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).2 (by`. Introduce `a b`. Rewrite using `[resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph]`. Use `hE (σ b) (σ a)` as an intermediate fact. Simplify using `only [Gm, Matrix.of_apply, Equiv.symm_apply_apply] at this`.

Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hred1, hred2]`. Use the proof step `rfl)`. Conclude with `⟨⟨v, hP, hG⟩, rfl⟩`.

Establish `hinj : Set.InjOn g S`. Introduce `XY _ XY' _ heq`. Establish `hc : ∀ a, (∀ k, XY.1 (σ a) k = XY'.1 (σ a) k) ∧ ∀ k, XY.2 (σ a) k = XY'.2 (σ a) k`. Introduce `a`. Use `(mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hliftL _ _)).1 (congrFun heq a)` as an intermediate fact.

Simplify using `only [hred1, hred2] at this`. Conclude with `this`. Use `Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)` and prove the remaining obligations. Use `(hc (σ.symm i)).1 k` as an intermediate fact. Simplify using `using this`.

Use `(hc (σ.symm i)).2 k` as an intermediate fact. Simplify using `using this`. Establish `hrank : Gm.rank = Fintype.card ι`. Set `A : Matrix ι ι 𝒪[F]` to `Matrix.of fun a b => ⟨(e (G₀ a b)).1, ((hO _).1 (h1 a b)).1⟩`. Set `φ : E →+* F` to `(RingHom.fst F F).comp (e : E →+* F × F)`.

Establish `hA : ((A.det : 𝒪[F]) : F) = φ G₀.det`. Rewrite using `[← 𝒪[F].coe_subtype, RingHom.map_det, RingHom.map_det]`. Use `congr 1`. Take `⟨y, hy, hdy⟩` from `h3`. Establish `hyO` using `((hO y).1 hy).1`.

Establish `hAu : IsUnit A.det`. Use `isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, hA]`. Use `congrArg φ hdy` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`.

Simplify `this` using `[φ]`. Establish `hGm : Gm = Matrix.reindex σ σ (A.map (IsLocalRing.residue 𝒪[F])).transpose`. Use extensionality with `i j`. Simplify using `only [Gm, A, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[← resF_coe]`.

Rewrite using `[Matrix.rank_of_isUnit Gm ?_, Fintype.card_fin]`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, hGm, Matrix.det_reindex_self, Matrix.det_transpose]`. Establish `: (A.map (IsLocalRing.residue 𝒪[F])) = (IsLocalRing.residue 𝒪[F]).mapMatrix A` using `rfl`. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `hAu.map _`.

Use `⟨Gm, hrank, ?_⟩` and prove the remaining obligations. Establish `hq : (Nat.card 𝓀[F] : ℝ) ≠ 0`. Establish `: 0 < Nat.card 𝓀[F]` using `Nat.card_pos`. Conclude with `this.ne'` after adjusting the coercions. Unfold `Loc.HermSp.dens`.

Rewrite using `[div_mul_cancel₀ _ (zpow_ne_zero _ hq), hR, Nat.card_coe_set_eq, hinj.ncard_image]`. Both sides reduce to the same expression.
-/
theorem count_bijection : CountBij := by
  intro F E _ _ _ _ _ _ _ M hl _ e hes hO V _ _ H Λ π Ph hπ ϖ hϖ ι _ _ G₀ h1 h2 h3
  haveI := hl
  have hπa := hπ.1
  have hπL := hπ.2.1
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let lift : (Fin (Module.finrank E V) → 𝓀[F]) → (Fin (Module.finrank E V) → 𝓀[F]) → V := fun X1 Y1 =>
    π.symm ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k))
  have hlift : ∀ X1 Y1, π (lift X1 Y1) = ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k)) :=
    fun _ _ => AddEquiv.apply_symm_apply _ _
  have hliftL : ∀ X1 Y1, lift X1 Y1 ∈ Λ := fun X1 Y1 =>
    (hπL _).2 (by rw [hlift]; exact ⟨fun k => liftF_mem F _, fun k => liftF_mem F _⟩)
  have hred1 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).1 k) = X1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  have hred2 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).2 k) = Y1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  let Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F] := Matrix.of fun i j => resF F ((e (G₀ (σ.symm j) (σ.symm i))).1)
  let Ph' := Ph.map (IsLocalRing.residue 𝒪[F])
  let g : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) →
      (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ) := fun XY a =>
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (lift (XY.1 (σ a)) (XY.2 (σ a)))
  let S : Set ((Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F])) :=
    {XY | LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧
      ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph' k l * XY.2 j l = Gm i j}
  have hL := fun (v : ι → V) (hv : ∀ a, v a ∈ Λ) a => (hπL (v a)).1 (hv a)
  have hR : Set.range (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = g '' S := by
    ext c
    constructor
    · rintro ⟨⟨v, hP, hG⟩, rfl⟩
      have hv : ∀ a, v a ∈ Λ := hP.1
      have hpr := (prim_iff e hO H Λ π hπa hπL hϖ v hv).1 hP
      have hgr := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).1 hG
      refine ⟨((fun i k => resF F ((π (v (σ.symm i))).1 k)), fun i k => resF F ((π (v (σ.symm i))).2 k)),
        ⟨hpr.1.comp σ.symm σ.symm.injective, hpr.2.comp σ.symm σ.symm.injective, ?_⟩, ?_⟩
      · intro i j
        have := hgr (σ.symm j) (σ.symm i)
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph] at this
        exact this
      · funext a
        show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        rw [mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hv a)]
        refine ⟨fun k => ?_, fun k => ?_⟩
        · rw [hred1]; simp
        · rw [hred2]; simp
    · rintro ⟨XY, ⟨hX, hY, hE⟩, rfl⟩
      let v : ι → V := fun a => lift (XY.1 (σ a)) (XY.2 (σ a))
      have hv : ∀ a, v a ∈ Λ := fun a => hliftL _ _
      have hr1 : (redM F fun a => (π (v a)).1) = XY.1 ∘ σ := by
        funext a k; exact hred1 _ _ k
      have hr2 : (redM F fun a => (π (v a)).2) = XY.2 ∘ σ := by
        funext a k; exact hred2 _ _ k
      have hP : H.Prim Λ v := (prim_iff e hO H Λ π hπa hπL hϖ v hv).2
        ⟨by rw [hr1]; exact hX.comp σ σ.injective, by rw [hr2]; exact hY.comp σ σ.injective⟩
      have hG := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).2 (by
        intro a b
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph]
        have := hE (σ b) (σ a)
        simp only [Gm, Matrix.of_apply, Equiv.symm_apply_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hred1, hred2]
        rfl)
      exact ⟨⟨v, hP, hG⟩, rfl⟩
  have hinj : Set.InjOn g S := by
    intro XY _ XY' _ heq
    have hc : ∀ a, (∀ k, XY.1 (σ a) k = XY'.1 (σ a) k) ∧ ∀ k, XY.2 (σ a) k = XY'.2 (σ a) k := by
      intro a
      have := (mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hliftL _ _)).1 (congrFun heq a)
      simp only [hred1, hred2] at this
      exact this
    refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
    · have := (hc (σ.symm i)).1 k
      simpa using this
    · have := (hc (σ.symm i)).2 k
      simpa using this

  have hrank : Gm.rank = Fintype.card ι := by
    let A : Matrix ι ι 𝒪[F] := Matrix.of fun a b => ⟨(e (G₀ a b)).1, ((hO _).1 (h1 a b)).1⟩
    let φ : E →+* F := (RingHom.fst F F).comp (e : E →+* F × F)
    have hA : ((A.det : 𝒪[F]) : F) = φ G₀.det := by
      rw [← 𝒪[F].coe_subtype, RingHom.map_det, RingHom.map_det]
      congr 1
    obtain ⟨y, hy, hdy⟩ := h3
    have hyO := ((hO y).1 hy).1
    have hAu : IsUnit A.det := by
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
      rw [Subring.coe_mul, hA]
      have := congrArg φ hdy
      rw [map_mul, map_one] at this
      simpa [φ] using this
    have hGm : Gm = Matrix.reindex σ σ (A.map (IsLocalRing.residue 𝒪[F])).transpose := by
      ext i j
      simp only [Gm, A, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.map_apply]
      rw [← resF_coe]
    rw [Matrix.rank_of_isUnit Gm ?_, Fintype.card_fin]
    rw [Matrix.isUnit_iff_isUnit_det, hGm, Matrix.det_reindex_self, Matrix.det_transpose]
    have : (A.map (IsLocalRing.residue 𝒪[F])) = (IsLocalRing.residue 𝒪[F]).mapMatrix A := rfl
    rw [this, ← RingHom.map_det]
    exact hAu.map _
  refine ⟨Gm, hrank, ?_⟩
  have hq : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    have : 0 < Nat.card 𝓀[F] := Nat.card_pos
    exact_mod_cast this.ne'
  unfold Loc.HermSp.dens
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ hq), hR, Nat.card_coe_set_eq, hinj.ncard_image]
  rfl

end PI.UnitaryGroupMassFormula.CntFormula
