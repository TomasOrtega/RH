import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.ChgApply
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}
  (e : Fin d₁ ⊕ Bool ≃ Fin d)

/- English proof (translation)
Take `⟨⟨sec, h⟩, -⟩` from `section_statement F E σ hσ v t`. Take `⟨g, ha, h1, h2⟩` from `h.exists_gl (β := Unit) (GeneralLinearGroup.scalar _ x) 1`. Set `z : (AE F E)ˣ` to `GeneralLinearGroup.det g`. Establish `hz : (z : AE F E) = g.1 () ()` using `det_unique _`. Establish `za : At (evFin F v) ((z : AE F E) - 1)`.

Rewrite using `[hz]`. Simplify using `using kd_at_matrix.1 ha () ()`. Establish `z1 : piW t z = x`. Rewrite using `[hz]`. Simplify using `using congrFun (congrFun h1 ()) ()`.

Establish `z2 : piW (t.comp σ) z = 1`. Rewrite using `[hz]`. Simplify using `using congrFun (congrFun h2 ()) ()`. Use `⟨z, za, z1, z2, ?_, (h.idele z x za z1 z2).1⟩` and prove the remaining obligations. Establish `e1 : z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z)` using `Units.ext (by`.

Express the relevant statement in the definitionally equal form `(z : AE F E) = 1 - GlobalTheory.EmbChart.tensAt E v 1 + GlobalTheory.EmbChart.tensAt E v (compFin F E v z)`. Establish `o` using `off_of_at za`. Rewrite using `[← PositivityTheory.Member.ZakTransform.ep_smul, ← map_one (compFin F E v), ← PositivityTheory.Member.ZakTransform.ep_smul]`. Rewrite `o` using `[sub_smul, sub_smul, one_smul, one_smul]`. Rewrite using `[← o, sub_add_cancel])`.

Establish `n1 : evFin F v (Algebra.norm (AF F) (z : AE F E)) = x`. Rewrite using `[norm_eq hσ t za z1 z2, map_add, map_sub, map_one, ev_sgl, ev_sgl, sub_self, zero_add]`. Rewrite using `[e1, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_unitFin, n1]`. Use `(val_eq_one_iff _).1 hx` as an intermediate fact. Conclude with `NNReal.eq (le_antisymm (Valued.toNormedField.norm_le_one_iff.2 this.le) (Valued.toNormedField.one_le_norm_iff.2 this.ge))`.
-/
theorem idele_one (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) (hx : valuation (Fv F v) (x : Fv F v) = 1) :
    ∃ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) ∧ piW t z = x ∧ piW (t.comp σ) z = 1 ∧ absE F E z = 1 ∧
      ∀ χ : Chr F E, (χ z : ℂ) = chrW χ t x := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl (β := Unit) (GeneralLinearGroup.scalar _ x) 1
  let z : (AE F E)ˣ := GeneralLinearGroup.det g
  have hz : (z : AE F E) = g.1 () () := det_unique _
  have za : At (evFin F v) ((z : AE F E) - 1) := by
    rw [hz]
    simpa using kd_at_matrix.1 ha () ()
  have z1 : piW t z = x := by
    rw [hz]
    simpa using congrFun (congrFun h1 ()) ()
  have z2 : piW (t.comp σ) z = 1 := by
    rw [hz]
    simpa using congrFun (congrFun h2 ()) ()
  refine ⟨z, za, z1, z2, ?_, (h.idele z x za z1 z2).1⟩
  have e1 : z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := Units.ext (by
    change (z : AE F E) = 1 - GlobalTheory.EmbChart.tensAt E v 1 + GlobalTheory.EmbChart.tensAt E v (compFin F E v z)
    have o := off_of_at za
    rw [← PositivityTheory.Member.ZakTransform.ep_smul, ← map_one (compFin F E v), ← PositivityTheory.Member.ZakTransform.ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  have n1 : evFin F v (Algebra.norm (AF F) (z : AE F E)) = x := by
    rw [norm_eq hσ t za z1 z2, map_add, map_sub, map_one, ev_sgl, ev_sgl, sub_self, zero_add]
  rw [e1, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_unitFin, n1]
  have := (val_eq_one_iff _).1 hx
  exact NNReal.eq (le_antisymm (Valued.toNormedField.norm_le_one_iff.2 this.le) (Valued.toNormedField.one_le_norm_iff.2 this.ge))

/- English proof (translation)
Take `⟨z, a1, a2, a3, a4, a5⟩` from `idele_one hσ t x hx`. Take `⟨w, b1, b2, b3, b4, b5⟩` from `idele_one hσ (t.comp σ) y⁻¹ (by simp [hy])`. Rewrite `b3` using `[comp_comp hσ]`. Use `⟨z * w, ?_, by simp [a2, b3], by simp [a3, b2], by simp [a4, b4], fun χ K m hχ => ?_⟩` and prove the remaining obligations. Establish `: ((z * w : (AE F E)ˣ) : AE F E) - 1 = (z - 1) * w + (w - 1)` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `At.kd_add (fun u hu => by rw [← smul_mul_assoc, a1 u hu, zero_mul]) b1`. Rewrite using `[map_mul, Circle.coe_mul, a5, b5, chrW_conj hσ t hχ, map_mul, map_inv, inv_inv, Units.val_mul]`.
-/
theorem idele_two (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) (hx : valuation (Fv F v) (x : Fv F v) = 1)
    (hy : valuation (Fv F v) (y : Fv F v) = 1) :
    ∃ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) ∧ piW t z = x ∧ piW (t.comp σ) z = (y⁻¹ : (Fv F v)ˣ) ∧ absE F E z = 1 ∧
      ∀ (χ : Chr F E) (K : Subgroup (AF F)ˣ) (m : ℕ), ResEtaPow K χ m → (χ z : ℂ) = chrW χ t (x * y) := by
  obtain ⟨z, a1, a2, a3, a4, a5⟩ := idele_one hσ t x hx
  obtain ⟨w, b1, b2, b3, b4, b5⟩ := idele_one hσ (t.comp σ) y⁻¹ (by simp [hy])
  rw [comp_comp hσ] at b3
  refine ⟨z * w, ?_, by simp [a2, b3], by simp [a3, b2], by simp [a4, b4], fun χ K m hχ => ?_⟩
  · have : ((z * w : (AE F E)ˣ) : AE F E) - 1 = (z - 1) * w + (w - 1) := by push_cast; ring
    rw [this]
    exact At.kd_add (fun u hu => by rw [← smul_mul_assoc, a1 u hu, zero_mul]) b1
  · rw [map_mul, Circle.coe_mul, a5, b5, chrW_conj hσ t hχ, map_mul, map_inv, inv_inv, Units.val_mul]

variable (H) in

def fr : Matrix (Fin d) (Fin d) E := Matrix.of fun i c => Sum.elim (H.ι i) (fun b => cond b (H.y i) (H.x i)) (e.symm c)

variable (W₁) in

def gm : Matrix (Fin d) (Fin d) E := reindex e e (fromBlocks W₁.J 0 0 (Matrix.of fun b b' => cond b (cond b' 0 (-1)) (cond b' 1 0)))

variable {e}

/- English proof (translation)
Simplify using `only [form, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, hs, Vac.sigma_sigma hσ, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem form_swap (hσ : IsCMExt F E σ) (hs : ∀ i j, σ (W.J j i) = -W.J i j) (x y : Fin d → E) : form σ W.J y x = -σ (form σ W.J x y) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, hs, Vac.sigma_sigma hσ, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `k : ∀ a b, ((fr H e)ᵀ * W.J * (fr H e).map σ) a b = form σ W.J (fun i => fr H e i a) fun i => fr H e i b` using `fun a b => by`. Rewrite using `[Matrix.mul_assoc]`. Both sides reduce to the same expression. Establish `c : ∀ s, (fun i => H.ι i s) = H.ι *ᵥ Pi.single s 1` using `fun s => by rw [mulVec_single_one]; rfl`. Use extensionality with `a b`.

Take `⟨a, rfl⟩` from `e.surjective a`. Take `⟨b, rfl⟩` from `e.surjective b`. Rewrite using `[k]`. Apply the tactic sequence `rcases a with s | _ | _ <;> rcases b with s' | _ | _ <;> simp only [fr, gm, of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond, reindex_apply, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]`. Rewrite using `[← hH.gram, Matrix.mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[c]`. Conclude with `(hH.orth _).1`. Rewrite using `[c]`. Conclude with `(hH.orth _).2`.

Rewrite using `[c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.x i) = 0 from (hH.orth _).1, map_zero, neg_zero]`. Conclude with `hH.xx`. Conclude with `hH.xy`. Rewrite using `[c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.y i) = 0 from (hH.orth _).2, map_zero, neg_zero]`. Rewrite using `[form_swap hσ hs]`.

Simplify using `[hH.xy]`. Conclude with `hH.yy`.
-/
theorem fr_gram (hσ : IsCMExt F E σ) {B : Base F E} {i₀ i₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁) (hs : ∀ i j, σ (W.J j i) = -W.J i j) :
    (fr H e)ᵀ * W.J * (fr H e).map σ = gm W₁ e := by
  have k : ∀ a b, ((fr H e)ᵀ * W.J * (fr H e).map σ) a b = form σ W.J (fun i => fr H e i a) fun i => fr H e i b := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have c : ∀ s, (fun i => H.ι i s) = H.ι *ᵥ Pi.single s 1 := fun s => by rw [mulVec_single_one]; rfl
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [k]
  rcases a with s | _ | _ <;> rcases b with s' | _ | _ <;> simp only [fr, gm, of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
    cond, reindex_apply, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
  · rw [← hH.gram, Matrix.mul_assoc]; rfl
  · rw [c]; exact (hH.orth _).1
  · rw [c]; exact (hH.orth _).2
  · rw [c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.x i) = 0 from (hH.orth _).1, map_zero, neg_zero]
  · exact hH.xx
  · exact hH.xy
  · rw [c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.y i) = 0 from (hH.orth _).2, map_zero, neg_zero]
  · rw [form_swap hσ hs]; simp [hH.xy]
  · exact hH.yy

/- English proof (translation)
Rewrite using `[gm, det_reindex_self, det_fromBlocks_zero₂₁]`. Use `h.mul (isUnit_iff_ne_zero.2 ?_)` and prove the remaining obligations. Rewrite using `[← det_reindex_self finTwoEquiv.symm, det_fin_two]`. Simplify using `[finTwoEquiv]`.
-/
theorem gm_det (h : IsUnit W₁.J.det) : IsUnit (gm W₁ e).det := by
  rw [gm, det_reindex_self, det_fromBlocks_zero₂₁]
  refine h.mul (isUnit_iff_ne_zero.2 ?_)
  rw [← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv]

structure Fr (σ : E →ₐ[F] E) (t : E →ₐ[F] Fv F v) (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E d d₁) (e : Fin d₁ ⊕ Bool ≃ Fin d)
    (C : GL (Fin d) (Fv F v)) : Prop where
  val : C.val = (fr H e).map t
  gram : (fr H e)ᵀ * W.J * (fr H e).map σ = gm W₁ e
  det : IsUnit W.J.det

/- English proof (translation)
Establish `m2 : (incM F (fr H e)).map (piW (t.comp σ)) = ((fr H e).map σ).map t` using `Matrix.ext fun i j => incM_map' h _ i j`. Establish `e0 : (fun i => incM F (fr H e) i c) = incM F (fr H e) *ᵥ Pi.single c 1` using `by rw [mulVec_single_one]; rfl`. Establish `a1 : At (evFin F v) (mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω)` using `fun u hu => by`. Establish `: mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω = (mat g - 1) *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ (ω - Pi.single c 1)`. Rewrite using `[sub_mulVec, one_mulVec, mulVec_sub, ← e0]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_sub, ← smul_mulVec, hg u hu, ← mulVec_smul, ha u hu]`. Simplify using the standard rewrite rules. Establish `G : C.valᵀ * W.J.map t * ((fr H e).map σ).map t = (gm W₁ e).map t`. Rewrite using `[← hC.gram, Matrix.map_mul, Matrix.map_mul, hC.val, transpose_map]`.

Establish `u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t`. Use `h.unit_rel g` as an intermediate fact. Rewrite `this` using `[incM_map h]`. Then use the resulting hypothesis. Establish `c1 : (mat g).map (piW t) *ᵥ (fun i => C.val i c) = C.val *ᵥ fun i => piW t (ω i)`. Establish `: (fun i => C.val i c) = C.val *ᵥ Pi.single c 1` using `by rw [mulVec_single_one]; rfl`.

Rewrite using `[hp, this, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← mulVec_mulVec, mulVec_single_one]`. Conclude with `congrArg _ (funext fun i => (h1 i).symm)`. Establish `c2 : (mat g).map (piW (t.comp σ)) *ᵥ (fun i => (((fr H e).map σ).map t) i c) = ((fr H e).map σ).map t *ᵥ fun i => piW (t.comp σ) (ω i)`. Establish `un : IsUnit (p.valᵀ * C.valᵀ * W.J.map t)` using `(((isUnit_transpose _).2 p.isUnit).mul ((isUnit_transpose _).2 C.isUnit)).mul (((isUnit_iff_isUnit_det _).2 hC.det).map (t : E →+* Fv F v).mapMatrix)`. Apply `mulVec_injective_iff_isUnit.2 un` to reduce the goal to its premises.

Establish `: p.valᵀ * C.valᵀ = C.valᵀ * ((mat g).map (piW t))ᵀ`. Rewrite using `[← transpose_mul, ← transpose_mul, hp, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]`. Establish `e2 : (fun i => (((fr H e).map σ).map t) i c) = ((fr H e).map σ).map t *ᵥ Pi.single c 1` using `by rw [mulVec_single_one]; rfl`. Establish `k1 : p.valᵀ * C.valᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) * ((fr H e).map σ).map t = (gm W₁ e).map t`. Rewrite using `[this, Matrix.mul_assoc C.valᵀ, Matrix.mul_assoc C.valᵀ, u1, G]`.

Establish `k2 : p.valᵀ * C.valᵀ * W.J.map t * ((fr H e).map σ).map t = p.valᵀ * (gm W₁ e).map t`. Rewrite using `[← G]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e2]`. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc]`.

Rewrite using `[k1, k2, ← mulVec_mulVec, h2, mulVec_single_one]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Use `sub_eq_zero.1 (h.ext _ (fun u hu => congrFun (a1 u hu) i) ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, incM_map h, ← hC.val, sub_eq_zero]`.

Use `Eq.trans ?_ (congrFun c1 i)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[hC.val, ← incM_map h]`. Both sides reduce to the same expression.

Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, m2, sub_eq_zero]`. Use `Eq.trans ?_ (congrFun c2 i)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[← m2]`.

Both sides reduce to the same expression.
-/
theorem col_eq (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) (c : Fin d) (ω : Fin d → AE F E) (ha : At (evFin F v) (ω - Pi.single c 1))
    (h1 : ∀ i, piW t (ω i) = p.val i c)
    (h2 : p.valᵀ *ᵥ ((gm W₁ e).map t *ᵥ fun i => piW (t.comp σ) (ω i)) = fun i => t (gm W₁ e i c)) :
    mat g *ᵥ (fun i => incM F (fr H e) i c) = incM F (fr H e) *ᵥ ω := by
  have m2 : (incM F (fr H e)).map (piW (t.comp σ)) = ((fr H e).map σ).map t := Matrix.ext fun i j => incM_map' h _ i j
  have e0 : (fun i => incM F (fr H e) i c) = incM F (fr H e) *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
  have a1 : At (evFin F v) (mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω) := fun u hu => by
    have : mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω =
        (mat g - 1) *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ (ω - Pi.single c 1) := by
      rw [sub_mulVec, one_mulVec, mulVec_sub, ← e0]; abel
    rw [this, smul_sub, ← smul_mulVec, hg u hu, ← mulVec_smul, ha u hu]
    simp
  have G : C.valᵀ * W.J.map t * ((fr H e).map σ).map t = (gm W₁ e).map t := by
    rw [← hC.gram, Matrix.map_mul, Matrix.map_mul, hC.val, transpose_map]
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have c1 : (mat g).map (piW t) *ᵥ (fun i => C.val i c) = C.val *ᵥ fun i => piW t (ω i) := by
    have : (fun i => C.val i c) = C.val *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
    rw [hp, this, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← mulVec_mulVec, mulVec_single_one]
    exact congrArg _ (funext fun i => (h1 i).symm)
  have c2 : (mat g).map (piW (t.comp σ)) *ᵥ (fun i => (((fr H e).map σ).map t) i c) =
      ((fr H e).map σ).map t *ᵥ fun i => piW (t.comp σ) (ω i) := by
    have un : IsUnit (p.valᵀ * C.valᵀ * W.J.map t) :=
      (((isUnit_transpose _).2 p.isUnit).mul ((isUnit_transpose _).2 C.isUnit)).mul
        (((isUnit_iff_isUnit_det _).2 hC.det).map (t : E →+* Fv F v).mapMatrix)
    apply mulVec_injective_iff_isUnit.2 un
    have : p.valᵀ * C.valᵀ = C.valᵀ * ((mat g).map (piW t))ᵀ := by
      rw [← transpose_mul, ← transpose_mul, hp, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    have e2 : (fun i => (((fr H e).map σ).map t) i c) = ((fr H e).map σ).map t *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
    have k1 : p.valᵀ * C.valᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) * ((fr H e).map σ).map t = (gm W₁ e).map t := by
      rw [this, Matrix.mul_assoc C.valᵀ, Matrix.mul_assoc C.valᵀ, u1, G]
    have k2 : p.valᵀ * C.valᵀ * W.J.map t * ((fr H e).map σ).map t = p.valᵀ * (gm W₁ e).map t := by
      rw [← G]; simp only [Matrix.mul_assoc]
    rw [e2]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc]
    rw [k1, k2, ← mulVec_mulVec, h2, mulVec_single_one]
    rfl
  funext i
  refine sub_eq_zero.1 (h.ext _ (fun u hu => congrFun (a1 u hu) i) ?_ ?_)
  · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, incM_map h, ← hC.val, sub_eq_zero]
    refine Eq.trans ?_ (congrFun c1 i)
    congr 1
    funext j
    rw [hC.val, ← incM_map h]; rfl
  · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, m2, sub_eq_zero]
    refine Eq.trans ?_ (congrFun c2 i)
    congr 1
    funext j
    rw [← m2]; rfl

/- English proof (translation)
Rewrite using `[← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]`.
-/
theorem sum_e' {R : Type} [AddCommMonoid R] (a : Fin d → R) : ∑ j, a j = ∑ s, a (e (.inl s)) + (a (e (.inr true)) + a (e (.inr false))) := by
  rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_e' (e := e)]`. Simplify using `[incM, incV, fr, mul_comm, mulVec, dotProduct]`.
-/
theorem fr_mulVec (ω : Fin d → AE F E) : incM F (fr H e) *ᵥ ω = incM F H.ι *ᵥ (fun s => ω (e (.inl s))) +
    (ω (e (.inr true)) • incV F H.y + ω (e (.inr false)) • incV F H.x) := by
  funext i
  simp only [mulVec, dotProduct]
  rw [sum_e' (e := e)]
  simp [incM, incV, fr, mul_comm, mulVec, dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases c with s | _ | _ <;> simp [incM, incV, fr]`.
-/
theorem fr_col (c : Fin d₁ ⊕ Bool) : (fun i => incM F (fr H e) i (e c)) =
    Sum.elim (fun s i => incM F H.ι i s) (fun b => cond b (incV F H.y) (incV F H.x)) c := by
  funext i
  rcases c with s | _ | _ <;> simp [incM, incV, fr]

/- English proof (translation)
Introduce `u hu` and use `by rw [add_sub_cancel_left, ← Pi.single_smul, ha u hu, Pi.single_zero]`.
-/
theorem at_single (c c' : Fin d) {a : AE F E} (ha : At (evFin F v) a) :
    At (evFin F v) ((Pi.single c 1 + Pi.single c' a : Fin d → AE F E) - Pi.single c 1) := fun u hu => by
  rw [add_sub_cancel_left, ← Pi.single_smul, ha u hu, Pi.single_zero]

/- English proof (translation)
Use `Subgroup.subset_closure ⟨?_, fun z => ?_⟩` and prove the remaining obligations. Use `col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) 1) (fun u _ => by simp) (fun i => by` as an intermediate fact. Apply the tactic sequence `rw [p1, Pi.single_apply]; split_ifs <;> simp) (by`. Use function extensionality and compare the values at `i`. Take `⟨i, rfl⟩` from `e.surjective i`.

Simplify using `only [mulVec, dotProduct, sum_e' (e := e)]`. Apply the tactic sequence `rcases i with s | _ | _ <;> simp [gm, p1, p2, p4])`. Rewrite `this` using `[fr_col, fr_mulVec]`. Simplify `this` using `[← Pi.zero_def]`. Establish `k : ∀ s, ∃ a : AE F E, mat g *ᵥ (fun i => incM F H.ι i s) = (fun i => incM F H.ι i s) + a • incV F H.x` using `fun s => by`.

Set `a` to `sec (p.val (e (.inr false)) (e (.inl s)), ∑ s', p.val (e (.inl s')) (e (.inr true)) * t (W₁.J s' s))`. Use `col_eq h hC hg hp (e (.inl s)) (Pi.single (e (.inl s)) 1 + Pi.single (e (.inr false)) a) (at_single _ _ (h.at' _)) (fun i => by` as an intermediate fact. Take `⟨i, rfl⟩` from `e.surjective i`. Break down `i with s' | _ | _` into its components or cases. Apply the tactic sequence `by_cases hs : s' = s <;> simp [p3, hs]`.

Simplify using `[a, h.fst]`. Simplify using `[p4]) (by`. Use function extensionality and compare the values at `i`. Take `⟨i, rfl⟩` from `e.surjective i`. Simplify using `only [mulVec, dotProduct, sum_e' (e := e)]`.

Apply the tactic sequence `rcases i with s' | _ | _ <;> simp [gm, p1, p2, p3, p4, a, h.snd, Pi.single_apply, apply_ite])`. Rewrite `this` using `[fr_col, fr_mulVec]`. Use `⟨a, this.trans ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`.

Use `choose a ha using k`. Use `⟨∑ s, z s * a s, ?_⟩` and prove the remaining obligations. Establish `e1 : incM F H.ι *ᵥ z = ∑ s, z s • fun i => incM F H.ι i s`. Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, mul_comm]`.

Rewrite using `[e1, mulVec_sum, Finset.sum_smul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun s _ => by rw [mulVec_smul, ha, smul_add, smul_smul]`.
-/
theorem mem_unip (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) (p1 : ∀ i, p.val i (e (.inr false)) = if i = e (.inr false) then 1 else 0)
    (p2 : p.val (e (.inr true)) (e (.inr true)) = 1) (p3 : ∀ s s', p.val (e (.inl s)) (e (.inl s')) = if s = s' then 1 else 0)
    (p4 : ∀ s, p.val (e (.inr true)) (e (.inl s)) = 0) : g ∈ unip σ W H := by
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · have := col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) 1) (fun u _ => by simp) (fun i => by
      rw [p1, Pi.single_apply]; split_ifs <;> simp) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, p1, p2, p4])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have k : ∀ s, ∃ a : AE F E, mat g *ᵥ (fun i => incM F H.ι i s) = (fun i => incM F H.ι i s) + a • incV F H.x := fun s => by
      let a := sec (p.val (e (.inr false)) (e (.inl s)), ∑ s', p.val (e (.inl s')) (e (.inr true)) * t (W₁.J s' s))
      have := col_eq h hC hg hp (e (.inl s)) (Pi.single (e (.inl s)) 1 + Pi.single (e (.inr false)) a) (at_single _ _ (h.at' _)) (fun i => by
        obtain ⟨i, rfl⟩ := e.surjective i
        rcases i with s' | _ | _
        · by_cases hs : s' = s <;> simp [p3, hs]
        · simp [a, h.fst]
        · simp [p4]) (by
        funext i
        obtain ⟨i, rfl⟩ := e.surjective i
        simp only [mulVec, dotProduct, sum_e' (e := e)]
        rcases i with s' | _ | _ <;> simp [gm, p1, p2, p3, p4, a, h.snd, Pi.single_apply, apply_ite])
      rw [fr_col, fr_mulVec] at this
      refine ⟨a, this.trans ?_⟩
      funext i
      simp [mulVec, dotProduct, Pi.single_apply]
    choose a ha using k
    refine ⟨∑ s, z s * a s, ?_⟩
    have e1 : incM F H.ι *ᵥ z = ∑ s, z s • fun i => incM F H.ι i s := by
      funext i; simp [mulVec, dotProduct, mul_comm]
    rw [e1, mulVec_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [mulVec_smul, ha, smul_add, smul_smul]

variable (e) in

def bl {k : Type} [Field k] (g : Matrix (Fin d₁) (Fin d₁) k) (x y : k) : Matrix (Fin d) (Fin d) k :=
  reindex e e (fromBlocks g 0 0 (diagonal fun b => cond b y x))

/- English proof (translation)
Rewrite using `[bl, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fintype.prod_bool, mul_comm x]`. Both sides reduce to the same expression.
-/
theorem usage₄ {k : Type} [Field k] (g : Matrix (Fin d₁) (Fin d₁) k) (x y : k) : (bl e g x y).det = g.det * (x * y) := by
  rw [bl, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fintype.prod_bool, mul_comm x]
  rfl

/- English proof (translation)
Establish `i1 : piW t (z⁻¹).val = (x⁻¹ : (Fv F v)ˣ)`. Rewrite using `[Units.val_inv_eq_inv_val, ← z1]; exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)`. Establish `i2 : piW (t.comp σ) (z⁻¹).val = y`. Establish `: piW (t.comp σ) (z⁻¹).val * piW (t.comp σ) z = 1` using `by rw [← map_mul]; simp`. Rewrite `this` using `[z2]`.

Simplify using `using eq_inv_of_mul_eq_one_left this`. Establish `sg : ∀ (c : Fin d) (a : AE F E), At (evFin F v) (a - 1) → At (evFin F v) ((Pi.single c a : Fin d → AE F E) - Pi.single c 1)` using `fun c a ha u hu => by`. Rewrite using `[← Pi.single_sub, ← Pi.single_smul, ha u hu, Pi.single_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) z) (sg _ _ za) (fun i => by` as an intermediate fact.

Take `⟨i, rfl⟩` from `e.surjective i`. Apply the tactic sequence `rcases i with s | _ | _ <;> simp [pe, bl, z1]) (by`. Use function extensionality and compare the values at `i`. Take `⟨i, rfl⟩` from `e.surjective i`. Simplify using `only [mulVec, dotProduct, sum_e' (e := e)]`.

Apply the tactic sequence `rcases i with s | _ | _ <;> simp [gm, pe, bl, z2])`. Rewrite `this` using `[fr_col, fr_mulVec]`. Simplify `this` using `[← Pi.zero_def]`. Establish `a2 : At (evFin F v) (cA σ (z⁻¹).val - 1)`. Establish `: At (evFin F v) ((z⁻¹).val - 1)` using `fun u hu => by`.

Rewrite using `[show (z⁻¹).val - 1 = -((z.val - 1) * (z⁻¹).val) by rw [sub_mul]; simp, smul_neg, ← smul_mul_assoc, za u hu]; simp`. Simplify using `using h.atConj _ this`. Use `col_eq h hC hg hp (e (.inr true)) (Pi.single (e (.inr true)) (cA σ (z⁻¹).val)) (sg _ _ a2) (fun i => by` as an intermediate fact. Take `⟨i, rfl⟩` from `e.surjective i`. Apply the tactic sequence `rcases i with s | _ | _ <;> simp [pe, bl, (h.conj _).1, i2]) (by`.

Use function extensionality and compare the values at `i`. Take `⟨i, rfl⟩` from `e.surjective i`. Simplify using `only [mulVec, dotProduct, sum_e' (e := e)]`. Apply the tactic sequence `rcases i with s | _ | _ <;> simp [gm, pe, bl, (h.conj _).2, i1])`. Rewrite `this` using `[fr_col, fr_mulVec]`.

Simplify `this` using `[← Pi.zero_def]`. Establish `u1` using `h.unit_rel g₁`. Rewrite `u1` using `[incM_map h]`. Use extensionality with `i s`. Use `col_eq h hC hg hp (e (.inl s)) (fun c => Sum.elim (fun s' => mat g₁ s' s) 0 (e.symm c)) (fun u hu => by` as an intermediate fact.

Use function extensionality and compare the values at `c`. Take `⟨c, rfl⟩` from `e.surjective c`. Break down `c with s' | b` into its components or cases. Simplify `congrFun (congrFun (hg₁ u hu) s') s` using `[Matrix.one_apply, Pi.single_apply]`. Use the proof step `simp) (fun i => by`.

Take `⟨i, rfl⟩` from `e.surjective i`. Apply the tactic sequence `rcases i with s | _ | _ <;> simp [pe, bl]) (by`. Use function extensionality and compare the values at `i`. Take `⟨i, rfl⟩` from `e.surjective i`. Simplify using `only [mulVec, dotProduct, sum_e' (e := e)]`.

Break down `i with s' | _ | _` into its components or cases. Use `congrFun (congrFun u1 s') s` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc]`. Simplify `this` using `[gm, pe, bl, Matrix.mul_apply, mat]`. Simplify using `[gm, pe, bl]`.

Simplify using `[gm, pe, bl])`. Rewrite `this` using `[fr_col, fr_mulVec]`. Simplify `congrFun this i` using `[Matrix.mul_apply, mulVec, dotProduct]`.
-/
theorem is_levi (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) {g₁ : UA σ W₁.J} (hg₁ : g₁ ∈ UAt σ W₁ (evFin F v)) {x y : (Fv F v)ˣ}
    (pe : p.val = bl e ((mat g₁).map (piW t)) x y) {z : (AE F E)ˣ} (za : At (evFin F v) ((z : AE F E) - 1)) (z1 : piW t z = x)
    (z2 : piW (t.comp σ) z = (y⁻¹ : (Fv F v)ˣ)) : IsLevi H z g₁ g := by
  have i1 : piW t (z⁻¹).val = (x⁻¹ : (Fv F v)ˣ) := by
    rw [Units.val_inv_eq_inv_val, ← z1]; exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
  have i2 : piW (t.comp σ) (z⁻¹).val = y := by
    have : piW (t.comp σ) (z⁻¹).val * piW (t.comp σ) z = 1 := by rw [← map_mul]; simp
    rw [z2] at this
    simpa using eq_inv_of_mul_eq_one_left this
  have sg : ∀ (c : Fin d) (a : AE F E), At (evFin F v) (a - 1) →
      At (evFin F v) ((Pi.single c a : Fin d → AE F E) - Pi.single c 1) := fun c a ha u hu => by
    rw [← Pi.single_sub, ← Pi.single_smul, ha u hu, Pi.single_zero]
  refine ⟨?_, ?_, ?_⟩
  · have := col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) z) (sg _ _ za) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl, z1]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, pe, bl, z2])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have a2 : At (evFin F v) (cA σ (z⁻¹).val - 1) := by
      have : At (evFin F v) ((z⁻¹).val - 1) := fun u hu => by
        rw [show (z⁻¹).val - 1 = -((z.val - 1) * (z⁻¹).val) by rw [sub_mul]; simp, smul_neg, ← smul_mul_assoc, za u hu]; simp
      simpa using h.atConj _ this
    have := col_eq h hC hg hp (e (.inr true)) (Pi.single (e (.inr true)) (cA σ (z⁻¹).val)) (sg _ _ a2) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl, (h.conj _).1, i2]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, pe, bl, (h.conj _).2, i1])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have u1 := h.unit_rel g₁
    rw [incM_map h] at u1
    ext i s
    have := col_eq h hC hg hp (e (.inl s)) (fun c => Sum.elim (fun s' => mat g₁ s' s) 0 (e.symm c)) (fun u hu => by
      funext c
      obtain ⟨c, rfl⟩ := e.surjective c
      rcases c with s' | b
      · simpa [Matrix.one_apply, Pi.single_apply] using congrFun (congrFun (hg₁ u hu) s') s
      · simp) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s' | _ | _
      · have := congrFun (congrFun u1 s') s
        rw [Matrix.mul_assoc] at this
        simpa [gm, pe, bl, Matrix.mul_apply, mat] using this
      · simp [gm, pe, bl]
      · simp [gm, pe, bl])
    rw [fr_col, fr_mulVec] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun this i

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
