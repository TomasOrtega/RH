import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7}

abbrev finf (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

/- English proof (translation)
Use `show infHom V g = 1 ↔ _`. Rewrite using `[Units.ext_iff]`. Both sides reduce to the same expression.
-/
theorem mem_GfC_iff (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finf D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

/- English proof (translation)
Establish `e1 : (x ⬝ m ⬝ y).map (finf D) = x.map (finf D) ⬝ m.map (finf D) ⬝ y.map (finf D)`. Rewrite using `[Matrix.map_mul (f := finf D), Matrix.map_mul (f := finf D)]`. Establish `e2 : (x ⬝ y).map (finf D) = x.map (finf D) ⬝ y.map (finf D)` using `Matrix.map_mul (f := finf D)`. Rewrite using `[e1, e2, hm, Matrix.mul_one]`.
-/
theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n)
    (y : Mx D n k) (hm : m.map (finf D) = 1) :
    (x ⬝ m ⬝ y).map (finf D) = (x ⬝ y).map (finf D) := by
  have e1 : (x ⬝ m ⬝ y).map (finf D) = x.map (finf D) ⬝ m.map (finf D) ⬝ y.map (finf D) := by
    rw [Matrix.map_mul (f := finf D), Matrix.map_mul (f := finf D)]
  have e2 : (x ⬝ y).map (finf D) = x.map (finf D) ⬝ y.map (finf D) := Matrix.map_mul (f := finf D)
  rw [e1, e2, hm, Matrix.mul_one]

/- English proof (translation)
Rewrite `ha`, the goal using `[mem_GfC_iff]`. Rewrite using `[OrthDec.mt_emb, Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one, ← Matrix.map_add _ (map_add (finf D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem orth_emb_mem_GfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one, ← Matrix.map_add _ (map_add (finf D)),
    o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_GfC_iff]`. Rewrite using `[HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finf D)), Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ hg, ← Matrix.map_add _ (map_add (finf D)), ← Matrix.map_add _ (map_add (finf D)), d.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem witt_embedding_mem_finite_unitary_points {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finf D)), Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ hg, ← Matrix.map_add _ (map_add (finf D)), ← Matrix.map_add _ (map_add (finf D)),
    d.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[embA_apply]`. Conclude with `witt_embedding_mem_finite_unitary_points d (orth_emb_mem_GfC o ha)`.
-/
theorem embA_mem_GfC {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (ha : a ∈ GfC A) : embA d o a ∈ GfC S := by
  rw [embA_apply]
  exact witt_embedding_mem_finite_unitary_points d (orth_emb_mem_GfC o ha)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `Iff.rfl`.
-/
theorem castGA_fst {I I' : AutInst} (e : I = I') (x : I.GA) : (castGA e x).1 = 1 ↔ x.1 = 1 := by
  subst e
  exact Iff.rfl

/- English proof (translation)
Establish `e` using `(Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)).1 (by simpa using hk)`. Conclude with `(castGA_fst h.symm (Formalism.IndefR.RationalEmbedding.iota D k)).2 e`.
-/
theorem iotaX_fst {X : HidaSetting D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) {k : GA D (D.sp.Y 0)}
    (hk : k ∈ GfC (D.sp.Y 0)) : (iotaX X h k).1 = 1 := by
  have e := (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)).1 (by simpa using hk)
  exact (castGA_fst h.symm (Formalism.IndefR.RationalEmbedding.iota D k)).2 e

end GlobalTheory.Core.Mi.CenAct

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7} {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

/- English proof (translation)
Use `Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)` and prove the remaining obligations. Use `show (iotaX X h (embA B.d B.o (a * b))).1 = (iotaX X h (embA B.d B.o a)).1 * (iotaX X h (embA B.d B.o b)).1`. Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression. Use `show (iotaX X h (embA B.d B.o (a * b))).2 = (iotaX X h (embA B.d B.o a)).2 * (iotaX X h (embA B.d B.o b)).2`.

Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem toH_mul (B : SBes X h u ψ A) (a b : GA D A) : B.toH (a * b) = B.toH a * B.toH b := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (iotaX X h (embA B.d B.o (a * b))).1 = (iotaX X h (embA B.d B.o a)).1 * (iotaX X h (embA B.d B.o b)).1
    rw [map_mul, map_mul]
    rfl
  · show (iotaX X h (embA B.d B.o (a * b))).2 = (iotaX X h (embA B.d B.o a)).2 * (iotaX X h (embA B.d B.o b)).2
    rw [map_mul, map_mul]
    rfl

/- English proof (translation)
The claim follows from `Subtype.ext (iotaX_fst h (embA_mem_GfC B.d B.o ha))`.
-/
theorem toH_fst (B : SBes X h u ψ A) {a : GA D A} (ha : a ∈ GfC A) : (B.toH a).1 = 1 :=
  Subtype.ext (iotaX_fst h (embA_mem_GfC B.d B.o ha))

/- English proof (translation)
Take `⟨a, ha⟩` from `(B.tieH ((iotaX X h).symm (1, (k : X.B.I.Gf)))).2 (by`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`. Conclude with `⟨one_mem _, k.2⟩)`. Use `⟨a, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩` and prove the remaining obligations. Use `show (iotaX X h (embA B.d B.o a)).1 = 1`.

Rewrite using `[ha, ContinuousMulEquiv.apply_symm_apply]`. Use `show (iotaX X h (embA B.d B.o a)).2 = k`. Rewrite using `[ha, ContinuousMulEquiv.apply_symm_apply]`.
-/
theorem toH_surj (B : SBes X h u ψ A) (k : Hfin X u) : ∃ a : GA D A, B.toH a = (1, k) := by
  obtain ⟨a, ha⟩ := (B.tieH ((iotaX X h).symm (1, (k : X.B.I.Gf)))).2 (by
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact ⟨one_mem _, k.2⟩)
  refine ⟨a, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · show (iotaX X h (embA B.d B.o a)).1 = 1
    rw [ha, ContinuousMulEquiv.apply_symm_apply]
  · show (iotaX X h (embA B.d B.o a)).2 = k
    rw [ha, ContinuousMulEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨a', ha'⟩` from `toH_surj B k`. Establish `e : B.toH (a * a') = B.toH (a' * a)` using `by rw [(Subgroup.mem_center_iff.1 hc a').symm]`. Rewrite `e` using `[toH_mul, toH_mul, ha']`. Conclude with `congrArg Prod.snd e`.
-/
theorem toH_snd_comm (B : SBes X h u ψ A) {a : GA D A} (hc : a ∈ Subgroup.center (GA D A)) (k : Hfin X u) :
    (B.toH a).2 * k = k * (B.toH a).2 := by
  obtain ⟨a', ha'⟩ := toH_surj B k
  have e : B.toH (a * a') = B.toH (a' * a) := by rw [(Subgroup.mem_center_iff.1 hc a').symm]
  rw [toH_mul, toH_mul, ha'] at e
  exact congrArg Prod.snd e

/- English proof (translation)
Take `⟨h1, h2⟩` from `hT`. Use `⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩` and prove the remaining obligations. Use `show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))`. Rewrite using `[mul_assoc]`. Conclude with `(h1 ξ).1 γ _`.

Establish `hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ : Hfin X u))` using `Prod.ext rfl (hδ κ).symm`. Establish `e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ : Hfin X u))`. Rewrite using `[mul_assoc, mul_assoc, hc]`. Conclude with `(congrArg (T ξ) e).trans ((h1 ξ).2 _ κ)`. Establish `hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1)` using `Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)`.

Establish `e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1)`. Rewrite using `[mul_assoc, mul_assoc, hc]`. Conclude with `(h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)`.
-/
theorem rtr_mem_Cu (hK : X.LevelSubgroupCharacter) {δ : Hfin X u} (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) :
    Formalism.L2.SG.ColDict.rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ : Hfin X u)) :=
      Prod.ext rfl (hδ κ).symm
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (congrArg (T ξ) e).trans ((h1 ξ).2 _ κ)
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

/- English proof (translation)
Use extensionality with `ξ y`. Establish `hc : ((1 : Hinf X u), δ⁻¹) * (1, δ) = 1` using `Prod.ext (mul_one 1) (inv_mul_cancel δ)`. Establish `e : y * (1, δ⁻¹) * (1, δ) = y` using `by rw [mul_assoc, hc, mul_one]`. Conclude with `congrArg (T ξ) e`.
-/
theorem rtr_inv_rtr (δ : Hfin X u) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    Formalism.L2.SG.ColDict.rtr X δ⁻¹ (Formalism.L2.SG.ColDict.rtr X δ T) = T := by
  ext ξ y
  have hc : ((1 : Hinf X u), δ⁻¹) * (1, δ) = 1 := Prod.ext (mul_one 1) (inv_mul_cancel δ)
  have e : y * (1, δ⁻¹) * (1, δ) = y := by rw [mul_assoc, hc, mul_one]
  exact congrArg (T ξ) e

end GlobalTheory.Core.Mi.CenAct

open GlobalTheory.Core.Mi.CenAct in

/- English proof (translation)
Introduce `D X h u ψ A B hK a _ haf hac`. Use `set δ : Hfin X u := (B.toH a).2 with hδdef`. Establish `hδ : ∀ k : Hfin X u, δ * k = k * δ` using `toH_snd_comm B hac`. Establish `hta : B.toH a = (1, δ)` using `Prod.ext (toH_fst B haf) rfl`. Use `⟨(Formalism.L2.SG.ColDict.rtr X δ).restrict (fun T hT => rtr_mem_Cu hK hδ hT), fun T₁ T₂ e => ?_, fun T ξ => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `e'` using `congrArg (fun S : Cu X u hK => Formalism.L2.SG.ColDict.rtr X δ⁻¹ (S : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))) e`. Simplify `e'` using `only [LinearMap.restrict_apply, rtr_inv_rtr]`. Use function extensionality and compare the values at `a' show T.1 ξ (B.toH a' * (1, δ)) = T.1 ξ (B.toH (a' * a))`. Rewrite using `[toH_mul, hta]`.
-/
theorem GlobalTheory.Core.Mi.central_acts_on_columns : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (a : GA D A), GlobalTheory.Core.Mi.IdE X → a ∈ GfC A → a ∈ Subgroup.center (GA D A) → ∃ R : Cu X u hK →ₗ[ℂ] Cu X u hK, Function.Injective R ∧ ∀ (T : Cu X u hK) ξ, B.colForm (R T).1 ξ = rTrans a (B.colForm T.1 ξ) := by
  intro D X h u ψ A B hK a _ haf hac
  set δ : Hfin X u := (B.toH a).2 with hδdef
  have hδ : ∀ k : Hfin X u, δ * k = k * δ := toH_snd_comm B hac
  have hta : B.toH a = (1, δ) := Prod.ext (toH_fst B haf) rfl
  refine ⟨(Formalism.L2.SG.ColDict.rtr X δ).restrict (fun T hT => rtr_mem_Cu hK hδ hT), fun T₁ T₂ e => ?_, fun T ξ => ?_⟩
  · apply Subtype.ext
    have e' := congrArg (fun S : Cu X u hK => Formalism.L2.SG.ColDict.rtr X δ⁻¹ (S : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))) e
    simpa only [LinearMap.restrict_apply, rtr_inv_rtr] using e'
  · funext a'
    show T.1 ξ (B.toH a' * (1, δ)) = T.1 ξ (B.toH (a' * a))
    rw [toH_mul, hta]

end
