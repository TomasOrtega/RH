import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorBaseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDiagonalStabilizerGeneratedHermitianDoStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ`. Take `⟨t, ht₀⟩` from `hpd`. Establish `ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E))` using `ht₀`. Establish `hF` using `hT.base.cm.1`. Use `set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ`.

Establish `hS` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)`. Establish `hl` using `lDiag_box_ne_zero hF hr.2 h0`. Establish `hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0` using `fun h => hl (by rw [h, map_zero])`. Establish `hn` using `norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ`. Establish `hrule` using `hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by`.

Establish `e : z * (diagCols (Fin a) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z`. Rewrite using `[diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[e, Darboux.rho, hdd]`. Conclude with `DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS`. Establish `hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (AE F E)), GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * s → ∀ z, (GlobalTheory.DblVac.matD g *ᵥ Su …` using `fun g s hs z => by`.

Establish `e : ∀ z : Fin a → AE F E, (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) *ᵥ z = Sum.elim z z` using `fun z => by`. Rewrite using `[diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]`. Rewrite using `[← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]`. Both sides reduce to the same expression. Establish `ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E))`.

Establish `e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1` using `p.1.inv_mul`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]`. Use `_ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]`. Establish `hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P` using `fun P hP => by`.

Establish `hPT : P ∉ above E (X.T : Set (Pl F))` using `fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))`. Rewrite using `[div_eq_mul_inv]`. Conclude with `(hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv`. Establish `hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1`. Use `GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_` and prove the remaining obligations.

Establish `e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1)`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]`. Establish `e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (u • ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1)) = 0`. Rewrite using `[Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]`. Rewrite `e2` using `[diagCols, Matrix.fromRows_mul, Matrix.one_mul]`.

Use extensionality with `i j`. Conclude with `congrFun (congrFun e2 (Sum.inl i)) j`. Establish `hz'` using `hp.2 (Sum.elim z z) ⟨hz, hz⟩`. Conclude with `⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩`. Rewrite `hrule` using `[hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul]`.

Establish `hμ'` using `mul_right_cancel₀ hl hrule`. Rewrite `hn` using `[hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`. Rewrite using `[hμ', hn, Complex.ofReal_one]`.
-/
theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → AE F E, (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E))) *
          ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl F)) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (u • ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd k hk c hc`. Take `⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩` from `hT.weil.2.1`. Establish `hvac` using `hT.geo.hM.vac v`. Take `⟨r, hr, hr0⟩` from `GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1`. Use `set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀`.

Use `set S := boxFun V₀ (fun x => star (V₀ x)) with hS`. Establish `hS0 : ∃ x, S x ≠ 0`. Take `⟨x, hx⟩` from `Function.ne_iff.mp hr0`. Use `⟨Sum.elim x x, ?_⟩` and prove the remaining obligations. Simplify using `only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢`.

Conclude with `mul_ne_zero hx (star_ne_zero.mpr hx)`. Set `H : Subgroup (GlobalTheory.DblVac.UD σ G.V)` to `{ carrier := {g | omd g S = S} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`.

Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H` using `fun p hp hpd => by`. Take `⟨μ, hμ⟩` from `GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr p hp`.

Establish `h1` using `siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 p hp hpd μ hμ`. Use `show omd p S = S`. Rewrite using `[hμ, h1, one_smul]`. Establish `hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H` using `fun q hq hqa => by`. Take `⟨w₀, hw₀, hW⟩` from `GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v`.

Take `⟨h1, h2⟩` from `hW q hq hqa`. Establish `hq' : omd (w₀ * q * w₀⁻¹) S = S` using `hD _ h1 h2`. Take `⟨μ, hμ⟩` from `GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr w₀ hw₀`. Establish `hinv : μ • omd w₀⁻¹ S = S`. Rewrite using `[← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Establish `e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀` using `by group`. Use `show omd q S = S`. Rewrite using `[e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq', LinearMap.map_smul, hinv]`. Take `⟨gd, hgd, hgdK⟩` from `GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk`. Establish `hfix : omd gd S = S` using `GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling σ B G.V _ _ hT.base hT.geo.hV v hsp₀ hψ htwo H hD hA gd hgdK`.

Establish `hb` using `hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)`. Establish `hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]`. Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`.

Rewrite `hb` using `[hk1]`. Establish `hcS : c • S = S`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `x`. Simplify using `[hS, boxFun, mul_assoc]`.

Use `_ = omd gd S := hb.symm`. Use `_ = S := hfix`. Take `⟨x, hx⟩` from `hS0`. Use `congrFun hcS x` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`.

Conclude with `mul_right_cancel₀ hx (this.trans (one_mul _).symm)`.
-/
theorem eigen_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr p hp
    have h1 := siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S :=
    GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling σ B G.V _ _ hT.base hT.geo.hV v hsp₀ hψ htwo H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.SplitVacV

end
