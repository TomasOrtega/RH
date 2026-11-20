import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleComponentsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearFunctionalTripleAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFunctionalTripleTranslateEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLocalIdeleCharacterCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFunctionalTripleSchwartzEvaluationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacBridge

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FullRankCoinv

/- English proof (translation)
Set `φ : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k` to `{ toFun := fun Y => Y * P invFun := fun Y => Y * P' left_inv := fun Y => by simp only [Matrix.mul_assoc, h1, Matrix.mul_one] right_inv := fun Y => by simp only [Matrix.mul_assoc, h2, Matrix.mul_one] continuous_toFun := continuous_id.matrix_mul continuous_const continuous_invFun : …`. Conclude with `⟨hΨ.1.comp_continuous φ.continuous, hΨ.2.comp_homeomorph φ⟩`.
-/
theorem sb_comp_mul {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ}
    (P P' : Matrix (Fin d) (Fin d) k) (h1 : P * P' = 1) (h2 : P' * P = 1) (Ψ : Matrix (Fin n) (Fin d) k → ℂ)
    (hΨ : Ψ ∈ SB (Matrix (Fin n) (Fin d) k)) : (fun Y => Ψ (Y * P)) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  let φ : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := fun Y => Y * P
      invFun := fun Y => Y * P'
      left_inv := fun Y => by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun Y => by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  exact ⟨hΨ.1.comp_continuous φ.continuous, hΨ.2.comp_homeomorph φ⟩

/- English proof (translation)
Use function extensionality and compare the values at `Y`. Simplify using `only [lact, Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem lact_comp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (P : Matrix (Fin d) (Fin d) k) :
    (fun Y => lact ν g Ψ (Y * P)) = lact ν g (fun Y => Ψ (Y * P)) := by
  funext Y; simp only [lact, Matrix.mul_assoc]; rfl

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[hu.1]`. Introduce `i j hij`. Use `hu.2 i j (ne_of_gt hij) ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.JacBlock₂.blk]`.

Establish `hj : (j : ℕ) < i` using `hij`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem det_of_isUnipStd {k : Type} [Field k] {d : ℕ} (u : GL (Fin d) k) (hu : GlobalTheory.JacBlock₂.IsUnipStd u) :
    (u.1).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hu.1]
  · intro i j hij
    refine hu.2 i j (ne_of_gt hij) ?_
    simp only [GlobalTheory.JacBlock₂.blk]
    have hj : (j : ℕ) < i := hij
    split_ifs <;> omega

/- English proof (translation)
Use `show (Matrix.diagonal _).det = _`. Rewrite using `[Matrix.det_diagonal, Fintype.prod_eq_single (⟨0, hd⟩ : Fin d)]`. Simplify using the standard rewrite rules. Introduce `i hi`. Establish `: i.1 ≠ 0` using `fun h => hi (Fin.ext h)`.

Simplify using `[this]`.
-/
theorem det_diagFirst {k : Type} [Field k] {d : ℕ} (hd : 0 < d) (x : kˣ) :
    ((GlobalTheory.JacBlock₂.diagFirst (d := d) x).1).det = x := by
  show (Matrix.diagonal _).det = _
  rw [Matrix.det_diagonal, Fintype.prod_eq_single (⟨0, hd⟩ : Fin d)]
  · simp
  · intro i hi
    have : i.1 ≠ 0 := fun h => hi (Fin.ext h)
    simp [this]

/- English proof (translation)
Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc Y Qi Q, h, Matrix.mul_one]`.
-/
theorem mul_conj_cancel {k : Type} [Field k] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) k) (Q Qi D : Matrix (Fin d) (Fin d) k)
    (h : Qi * Q = 1) : Y * Qi * (Q * D * Qi) = Y * D * Qi := by
  simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc Y Qi Q, h, Matrix.mul_one]

end GlobalTheory.JacBridge

namespace GlobalTheory.JacBridge

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FullRankCoinv

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' v hv w hw`. Establish `hP : GlobalTheory.FunPr.Hypotheses₂` using `hK.base`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`. Take `⟨t, e, he1, he2, he3, heχ, heabs⟩` from `GlobalTheory.T.local_idele_components_at_place F E σ hcm v hv.2 w hw`. Take `⟨ι₀, hι₀⟩` from `GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t`.

Take `⟨hQ, hLevi, hUnip⟩` from `GlobalTheory.T.adapted_plane_local_idele_character_compat F E σ B hcm (a + a') d₁ _ _ G.W W₁ H' i₀ i₁ hT.geo.hW hH' v t w e he1 he2 he3`. Take `⟨hsm, hun, hV1, hV2⟩` from `GlobalTheory.T.local_linear_functional_triple_at_good_place hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀`. Establish `hW` using `GlobalTheory.T.local_functional_triple_translate_equivariant hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀`. Use `set Q := adaptQ t H' with hQdef`. Establish `hQQ : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q hQ`.

Establish `hQQ' : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q hQ`. Set `Qg : GL (Fin (a + a')) (Fv F v)` to `⟨Q, Q⁻¹, hQQ, hQQ'⟩`. Establish `hQu : IsUnit Q` using `(Matrix.isUnit_iff_isUnit_det Q).mpr hQ`. Set `ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a') ) (Fv F v) → ℂ)` to `(LinearMap.funLeft ℂ ℂ (fun Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) => Y * Q⁻¹)) ∘ₗ ι₀`. Establish `hιd : ∀ φ, ι φ = fun Y => ι₀ φ (Y * Q⁻¹)` using `fun φ => rfl`.

Establish `skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j` using `fun i j => by`. Rewrite using `[map_neg, map_one, neg_one_mul]`. Conclude with `hT.geo.hW.skew i j`. Take `⟨wI⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdetW : IsUnit (G.W.J.map t).det` using `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb wI).1 Complex.I Complex.I_ne_zero (G.W.θ wI) (hT.geo.hW.cartan wI)`.

Establish `hd : 0 < a + a'` using `by have := hT.geo.lt; omega`. Establish `hbij : Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _)`. Use `⟨fun φ hφ => ?_, fun φ hφ φ' hφ' h => ?_, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Rewrite using `[hιd]`. Conclude with `sb_comp_mul _ _ hQQ' hQQ _ (hι₀.bij.mapsTo hφ)`.

Use `hι₀.bij.injOn hφ hφ' ?_` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Use `congrFun h (Y * Q)` as an intermediate fact. Simplify `this` using `[hιd, Matrix.mul_assoc, hQQ]`. Take `⟨φ, hφ, hφe⟩` from `hι₀.bij.surjOn (sb_comp_mul Q Q⁻¹ hQQ hQQ' Ψ hΨ)`.

Use `⟨φ, hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Rewrite using `[hιd]`. Simplify using `only [hφe, Matrix.mul_assoc, hQQ', Matrix.mul_one]`. Use `⟨ι, chrW X.ν t, e, hsm, hun, hbij, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `Ψ hΨ`. Take `⟨φ, hφ, rfl⟩` from `hbij.surjOn hΨ`. Take `⟨φ₀, hφ₀, hdiff⟩` from `GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv (GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT v hv) t φ hφ`. Use `⟨ι φ₀, ⟨hbij.mapsTo hφ₀.1, fun Y hY => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hιd]`.

Use `GlobalTheory.T.local_functional_triple_schwartz_evaluation hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀ φ₀ hφ₀ _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det Q hQ)]` and apply the resulting hypothesis. Establish `hspan : augAt om' v ≤ (Submodule.span ℂ {z | ∃ (g : GL (Fin a') (Fv F v)) (Ψ' : Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ), Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) ∧ z = lact (chrW X.ν t) g Ψ' - Ψ'}).comap ι`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, hg, φ₂, hφ₂, φ₃, hφ₃, hA, rfl⟩`.

Take `⟨g₀, hg₀⟩` from `hV2 g hg`. Use `Submodule.subset_span ⟨g₀, ι φ₂, hbij.mapsTo hφ₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hιd φ₃, hιd φ₂, hg₀ φ₂ hφ₂ φ₃ hφ₃ hA]`. Use `congr 1`. Conclude with `lact_comp_mul _ _ _ _`.

Use `hspan hdiff` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, map_sub]`. Then use the resulting hypothesis. Introduce `g₀`. Take `⟨g, hg, hgφ⟩` from `hV1 g₀`. Use `⟨g, hg, fun φ hφ => ?_⟩` and prove the remaining obligations.

Take `⟨φ₁, hφ₁, hA, he⟩` from `hgφ φ hφ`. Use `⟨φ₁, hφ₁, hA, ?_⟩` and prove the remaining obligations. Rewrite using `[hιd, hιd, he]`. Conclude with `lact_comp_mul _ _ _ _`. Introduce `u₀ hu₀`.

Set `h₀ : GL (Fin (a + a')) (Fv F v)` to `Qg * u₀ * Qg⁻¹`. Establish `hh₀ : h₀.1 = Q * u₀.1 * Q⁻¹` using `rfl`. Use `set n := GlobalTheory.SplitUnitLift.liftU hcm t G.W.J (-1) skew hdetW h₀ with hn`. Establish `hnat : n ∈ UAt σ G.W (evFin F v)` using `GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) skew hdetW h₀`. Establish `hnt : (mat n).map (piW t) = h₀.1` using `GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) skew hdetW h₀`.

Establish `hdet : GlobalTheory.SplitFlip.gdet h₀ = 1`. Use `ext`. Rewrite using `[GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, hh₀, Matrix.det_conj hQu, det_of_isUnipStd u₀ hu₀]`. Both sides reduce to the same expression. Use `⟨n, hUnip u₀ hu₀ n hnat (hnt.trans hh₀), hnat, fun φ hφ => ?_⟩` and prove the remaining obligations.

Take `⟨⟨φ₁, hφ₁, hA⟩, hform⟩` from `hW n hnat h₀ hnt φ hφ`. Use `⟨φ₁, hφ₁, hA, ?_⟩` and prove the remaining obligations. Rewrite using `[hιd, hιd, hform φ₁ hφ₁ hA, hdet, map_one, Units.val_one, GlobalTheory.SplitFlip.apow_one, mul_one, one_smul]`. Use function extensionality and compare the values at `Y`. Simplify using `only [hh₀, ← Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_assoc Y Q⁻¹ Q, hQQ', Matrix.mul_one]`. Introduce `x m hm φ hφ φ₁ hφ₁ hA`. Take `⟨hmat, hmt⟩` from `hLevi x m hm`. Set `h₀ : GL (Fin (a + a')) (Fv F v)` to `Qg * GlobalTheory.JacBlock₂.diagFirst (e x) * Qg⁻¹`. Establish `hh₀ : h₀.1 = Q * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * Q⁻¹` using `rfl`.

Establish `hdet : GlobalTheory.SplitFlip.gdet h₀ = e x`. Use `ext`. Rewrite using `[GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, hh₀, Matrix.det_conj hQu, det_diagFirst hd]`. Establish `hform' : ι₀ φ₁ = ((X.α (locIdele F w x) : ℂ) * ((((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ^ ((a' : ℂ) / 2))) • fun Y => ι₀ φ (Y * (Q * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * Q⁻¹))`. Apply the tactic sequence `rw [(hW m hmat h₀ (hmt.trans hh₀.symm) φ hφ).2 φ₁ hφ₁ hA, hdet, heχ, heabs] <;> rfl`.

Establish `hexp : (((a' : ℝ) / 2 : ℝ) : ℂ) = (a' : ℂ) / 2` using `by push_cast; ring`. Rewrite using `[hιd, hιd, hform', GlobalTheory.CtTyp.coe_twAbs, Complex.ofReal_cpow (NNReal.coe_nonneg _), hexp]`. Use function extensionality and compare the values at `(Y : Matrix (Fin a') (Fin (a + a')) (Fv F v))`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_conj_cancel _ _ _ _ hQQ']`.

Both sides reduce to the same expression. Introduce `x`. Establish `hA0 : (((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ≠ 0`. Conclude with `(GlobalTheory.CtTyp.absE_pos (locIdele F w x)).ne'` after adjusting the coercions. Establish `hν : ((chrW X.ν t (e x) : ℂˣ) : ℂ) = (X.α (locIdele F w x) : ℂ) / (X.β (locIdele F w x) : ℂ)`.

Rewrite using `[heχ, Chars.ν, MonoidHom.div_apply, Circle.coe_div]`. Establish `hα0 : (X.α (locIdele F w x) : ℂ) ≠ 0` using `Circle.coe_ne_zero _`. Establish `hβ0 : (X.β (locIdele F w x) : ℂ) ≠ 0` using `Circle.coe_ne_zero _`. Rewrite using `[GlobalTheory.CtTyp.coe_twAbs, GlobalTheory.CtTyp.coe_twAbs, Units.val_inv_eq_inv_val, hν, heabs, Complex.ofReal_cpow (NNReal.coe_nonneg _), Complex.ofReal_cpow (NNReal.coe_nonneg _)]`. Establish `hs : (((a : ℝ) / 2 : ℝ) : ℂ) = (((a' : ℝ) / 2 : ℝ) : ℂ) + ((((a + a' : ℕ) : ℂ) - 2 * (a' : ℂ)) / 2)` using `by push_cast; ring`.

Rewrite using `[hs, Complex.cpow_add _ _ hA0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem bridge : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
  ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)) (ν₀ : (Fv F v)ˣ →* ℂˣ) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
    Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
    (∀ Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∃ Ψ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a'),
      Ψ - Ψ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a') (Fv F v)) (Ψ' : Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
        Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.FullRankCoinv.lact ν₀ g Ψ' - Ψ'}) ∧
    (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
    (∀ u₀ : GL (Fin (a + a')) (Fv F v), GlobalTheory.JacBlock₂.IsUnipStd u₀ → ∃ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) ∧
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, n)) φ φ₁ ∧ ι φ₁ = fun Y => ι φ (Y * u₀.1)) ∧
    (∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, m)) φ φ₁ →
        ι φ₁ = ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) • fun Y => ι φ (Y * (GlobalTheory.JacBlock₂.diagFirst (e x)).1)) ∧
    ∀ x : (w.adicCompletion E)ˣ, ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) * (((ν₀ (e x))⁻¹ : ℂˣ) : ℂ) *
        GlobalTheory.SplitFlip.apow (e x) ((((a + a' : ℕ) : ℂ) - 2 * (a' : ℂ)) / 2) = ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' v hv w hw
  have hP : GlobalTheory.FunPr.Hypotheses₂ := hK.base
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨t, e, he1, he2, he3, heχ, heabs⟩ := GlobalTheory.T.local_idele_components_at_place F E σ hcm v hv.2 w hw
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  obtain ⟨hQ, hLevi, hUnip⟩ := GlobalTheory.T.adapted_plane_local_idele_character_compat F E σ B hcm (a + a') d₁ _ _ G.W W₁ H' i₀ i₁ hT.geo.hW hH' v t w e he1 he2 he3
  obtain ⟨hsm, hun, hV1, hV2⟩ := GlobalTheory.T.local_linear_functional_triple_at_good_place hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀
  have hW := GlobalTheory.T.local_functional_triple_translate_equivariant hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀
  set Q := adaptQ t H' with hQdef
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  let Qg : GL (Fin (a + a')) (Fv F v) := ⟨Q, Q⁻¹, hQQ, hQQ'⟩
  have hQu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hQ
  let ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a') ) (Fv F v) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) => Y * Q⁻¹)) ∘ₗ ι₀
  have hιd : ∀ φ, ι φ = fun Y => ι₀ φ (Y * Q⁻¹) := fun φ => rfl
  have skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hT.geo.hW.skew i j
  obtain ⟨wI⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdetW : IsUnit (G.W.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb wI).1 Complex.I Complex.I_ne_zero (G.W.θ wI) (hT.geo.hW.cartan wI)
  have hd : 0 < a + a' := by have := hT.geo.lt; omega

  have hbij : Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) := by
    refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' h => ?_, fun Ψ hΨ => ?_⟩
    · rw [hιd]; exact sb_comp_mul _ _ hQQ' hQQ _ (hι₀.bij.mapsTo hφ)
    · refine hι₀.bij.injOn hφ hφ' ?_
      funext Y
      have := congrFun h (Y * Q)
      simpa [hιd, Matrix.mul_assoc, hQQ] using this
    · obtain ⟨φ, hφ, hφe⟩ := hι₀.bij.surjOn (sb_comp_mul Q Q⁻¹ hQQ hQQ' Ψ hΨ)
      refine ⟨φ, hφ, ?_⟩
      funext Y
      rw [hιd]; simp only [hφe, Matrix.mul_assoc, hQQ', Matrix.mul_one]
  refine ⟨ι, chrW X.ν t, e, hsm, hun, hbij, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ψ hΨ
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
    obtain ⟨φ₀, hφ₀, hdiff⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv
      (GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT v hv) t φ hφ
    refine ⟨ι φ₀, ⟨hbij.mapsTo hφ₀.1, fun Y hY => ?_⟩, ?_⟩
    · rw [hιd]
      refine GlobalTheory.T.local_functional_triple_schwartz_evaluation hP F E σ B a a' G X om om' hT v hv t ι₀ hι₀ φ₀ hφ₀ _ ?_
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det Q hQ)]
    · have hspan : augAt om' v ≤ (Submodule.span ℂ {z | ∃ (g : GL (Fin a') (Fv F v)) (Ψ' : Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
          Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) ∧ z = lact (chrW X.ν t) g Ψ' - Ψ'}).comap ι := by
        refine Submodule.span_le.mpr ?_
        rintro z ⟨g, hg, φ₂, hφ₂, φ₃, hφ₃, hA, rfl⟩
        obtain ⟨g₀, hg₀⟩ := hV2 g hg
        refine Submodule.subset_span ⟨g₀, ι φ₂, hbij.mapsTo hφ₂, ?_⟩
        rw [map_sub, hιd φ₃, hιd φ₂, hg₀ φ₂ hφ₂ φ₃ hφ₃ hA]
        congr 1
        exact lact_comp_mul _ _ _ _
      have := hspan hdiff
      rwa [Submodule.mem_comap, map_sub] at this
  · intro g₀
    obtain ⟨g, hg, hgφ⟩ := hV1 g₀
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hgφ φ hφ
    refine ⟨φ₁, hφ₁, hA, ?_⟩
    rw [hιd, hιd, he]
    exact lact_comp_mul _ _ _ _
  · intro u₀ hu₀
    let h₀ : GL (Fin (a + a')) (Fv F v) := Qg * u₀ * Qg⁻¹
    have hh₀ : h₀.1 = Q * u₀.1 * Q⁻¹ := rfl
    set n := GlobalTheory.SplitUnitLift.liftU hcm t G.W.J (-1) skew hdetW h₀ with hn
    have hnat : n ∈ UAt σ G.W (evFin F v) := GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) skew hdetW h₀
    have hnt : (mat n).map (piW t) = h₀.1 := GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) skew hdetW h₀
    have hdet : GlobalTheory.SplitFlip.gdet h₀ = 1 := by
      ext
      rw [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, hh₀, Matrix.det_conj hQu, det_of_isUnipStd u₀ hu₀]
      rfl
    refine ⟨n, hUnip u₀ hu₀ n hnat (hnt.trans hh₀), hnat, fun φ hφ => ?_⟩
    obtain ⟨⟨φ₁, hφ₁, hA⟩, hform⟩ := hW n hnat h₀ hnt φ hφ
    refine ⟨φ₁, hφ₁, hA, ?_⟩
    rw [hιd, hιd, hform φ₁ hφ₁ hA, hdet, map_one, Units.val_one, GlobalTheory.SplitFlip.apow_one, mul_one, one_smul]
    funext Y
    simp only [hh₀, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Y Q⁻¹ Q, hQQ', Matrix.mul_one]
  · intro x m hm φ hφ φ₁ hφ₁ hA
    obtain ⟨hmat, hmt⟩ := hLevi x m hm
    let h₀ : GL (Fin (a + a')) (Fv F v) := Qg * GlobalTheory.JacBlock₂.diagFirst (e x) * Qg⁻¹
    have hh₀ : h₀.1 = Q * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * Q⁻¹ := rfl
    have hdet : GlobalTheory.SplitFlip.gdet h₀ = e x := by
      ext
      rw [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, hh₀, Matrix.det_conj hQu, det_diagFirst hd]
    have hform' : ι₀ φ₁ = ((X.α (locIdele F w x) : ℂ) * ((((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ^ ((a' : ℂ) / 2))) •
        fun Y => ι₀ φ (Y * (Q * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * Q⁻¹)) := by
      rw [(hW m hmat h₀ (hmt.trans hh₀.symm) φ hφ).2 φ₁ hφ₁ hA, hdet, heχ, heabs] <;> rfl
    have hexp : (((a' : ℝ) / 2 : ℝ) : ℂ) = (a' : ℂ) / 2 := by push_cast; ring
    rw [hιd, hιd, hform', GlobalTheory.CtTyp.coe_twAbs, Complex.ofReal_cpow (NNReal.coe_nonneg _), hexp]
    funext (Y : Matrix (Fin a') (Fin (a + a')) (Fv F v))
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_conj_cancel _ _ _ _ hQQ']
    rfl
  · intro x
    have hA0 : (((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (GlobalTheory.CtTyp.absE_pos (locIdele F w x)).ne'
    have hν : ((chrW X.ν t (e x) : ℂˣ) : ℂ) = (X.α (locIdele F w x) : ℂ) / (X.β (locIdele F w x) : ℂ) := by
      rw [heχ, Chars.ν, MonoidHom.div_apply, Circle.coe_div]
    have hα0 : (X.α (locIdele F w x) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hβ0 : (X.β (locIdele F w x) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [GlobalTheory.CtTyp.coe_twAbs, GlobalTheory.CtTyp.coe_twAbs, Units.val_inv_eq_inv_val, hν, heabs,
      Complex.ofReal_cpow (NNReal.coe_nonneg _), Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    have hs : (((a : ℝ) / 2 : ℝ) : ℂ) = (((a' : ℝ) / 2 : ℝ) : ℂ) + ((((a + a' : ℕ) : ℂ) - 2 * (a' : ℂ)) / 2) := by
      push_cast; ring
    rw [hs, Complex.cpow_add _ _ hA0]
    field_simp

end GlobalTheory.JacBridge
