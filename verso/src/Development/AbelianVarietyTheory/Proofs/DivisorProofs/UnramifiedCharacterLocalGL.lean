import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingEquivariantStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinBarChar

open Matrix

/- English proof (translation)
Establish `cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl` using `continuous_pi fun i => continuous_apply _`. Establish `cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr` using `continuous_pi fun i => continuous_apply _`. Use `⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩` and prove the remaining obligations. Set `e` to `(Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))`. Use `HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂` using `fun h => hx ⟨e x, h, e.symm_apply_apply x⟩`. Rewrite `hx'` using `[Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or]`. Simplify using `only [boxFun]`. Break down `hx' with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h, zero_mul]`.

Rewrite using `[image_eq_zero_of_notMem_tsupport h, mul_zero]`.
-/
theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

/- English proof (translation)
Rewrite using `[← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]`. Simplify using `[sub_eq_add_neg]`.
-/
theorem fromBlocks_diag_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A - 1 = Matrix.fromBlocks (A - 1) 0 0 (A - 1) := by
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) j <;> simp [diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply]`.
-/
theorem fromBlocks_diag_mul_diagCols {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A * (diagCols n : Matrix (n ⊕ n) n R) = (diagCols n : Matrix (n ⊕ n) n R) * A := by
  ext (i | i) j <;> simp [diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hχ t K hK S hS ν α ι hι hint m hm r hr`. Take `⟨-, ⟨d', hd', hBw⟩, -⟩` from `hT.weil'`. Take `⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩` from `hBw`. Use `haveI : Nonempty (Fin a') := ⟨⟨0, by have := hT.geo.aBig; omega⟩⟩`. Take `⟨g₀, hg₀⟩` from `Matrix.GeneralLinearGroup.det_surjective (n := Fin a') (R := Fv F v) (unifAt v)`.

Use `set k := K g₀ with hk`. Establish `hkU : (mat k)ᵀ * incM F G.V'.J * (mat k).map (cA σ) = incM F G.V'.J` using `k.2`. Use `set mi : Matrix (Fin a') (Fin a') (AE F E) := ((k : GL (Fin a') (AE F E))⁻¹).1`. Establish `h1 : mat k * mi = 1` using `Units.mul_inv (k : GL (Fin a') (AE F E))`. Establish `h2 : mi * mat k = 1` using `Units.inv_mul (k : GL (Fin a') (AE F E))`.

Set `P₀ : GL (Fin a' ⊕ Fin a') (AE F E)` to `⟨Matrix.fromBlocks (mat k) 0 0 (mat k), Matrix.fromBlocks mi 0 0 mi, by rw [Matrix.fromBlocks_multiply, h1]; simp [Matrix.fromBlocks_one], by rw [Matrix.fromBlocks_multiply, h2]; simp [Matrix.fromBlocks_one]⟩`. Establish `hP₀ : P₀ ∈ UG (cA σ) (dbl (incM F G.V'.J))` using `by show (Matrix.fromBlocks (mat k) 0 0 (mat k))ᵀ * dbl (incM F G.V'.J) * (Matrix.fromBlocks (mat k) 0 0 (mat k)).map (cA σ) = _`. Establish `hn : (mat k)ᵀ * (-incM F G.V'.J) * (mat k).map (cA σ) = -incM F G.V'.J`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hkU]`. Rewrite using `[dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`.

Simplify using `only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.map_zero _ (map_zero (cA σ))]`. Rewrite using `[hkU, hn]`. Set `p : UG (cA σ) (dbl (incM F G.V'.J))` to `⟨P₀, hP₀⟩`. Establish `hpm : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k) 0 0 (mat k)` using `rfl`. Establish `hAt : At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1)`.

Introduce `u hu`. Establish `hk1 : u • (mat k - 1) = 0` using `(hK g₀).1 u hu`. Rewrite using `[hpm, fromBlocks_diag_sub_one, Matrix.fromBlocks_smul]`. Simplify using `[hk1]`. Establish `hpt : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) = (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) * (((k : UA σ G.V'.J) : GL (Fin a') (AE F E)) : …`.

Rewrite using `[hpm]`. Conclude with `fromBlocks_diag_mul_diagCols _`. Take `⟨l, hl, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hlφ, φ₀, hφ₀, hI⟩` from `GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v`. Establish `hbox` using `boxFun_mem_SB hφ₀ hφ₀`. Take `⟨φ'', hφ'', hact⟩` from `GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hAt _ hbox`.

Establish `h4` using `GlobalTheory.T.triple_local_gl_embedding_integral hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl (fun g gd hgd φ₁ h₁ φ₂ h₂ => hres g gd hgd φ₁ h₁ φ₂ h₂) g₀ p hpm φ₀ hφ₀ φ₀ hφ₀ φ'' hφ'' hact μ hμ`. Establish `hs` using `hsieg l hl hinv p _ hpt _ (hr₀ _ hbox).2`. Rewrite `hs` using `[hact r₀ (hr₀ _ hbox), hlφ _ hφ'', hlφ _ hbox, h4]`. Establish `hbd : (∫ x, boxFun φ₀ φ₀ (Sum.elim x x) ∂μ) = ∫ x, φ₀ x * φ₀ x ∂μ` using `rfl`. Rewrite `hs` using `[hbd]`.

Use `set I := ∫ x, φ₀ x * φ₀ x ∂μ`. Use `set val := ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^ ((Fintype.card (Fi …`. Use `set u : ℂ := (ν (GlobalTheory.SplitFlip.gdet g₀) : ℂ) with hu`. Establish `hratio : u / starRingEnd ℂ u = val`. Establish `: c₀ * I * (u / starRingEnd ℂ u) = c₀ * I * val` using `by linear_combination hs`.

Conclude with `mul_left_cancel₀ (mul_ne_zero hc₀ hI) this`. Establish `h6` using `GlobalTheory.T.triple_local_gl_embedding_equivariant F E σ B a a' G X om om' hT v hv t K hK g₀`. Establish `hgd : GlobalTheory.SplitFlip.gdet g₀ = unifAt v` using `hg₀`. Rewrite `hu`, `h6` using `[hgd]`. Establish `hu0 : u ≠ 0` using `by rw [hu]; exact Units.ne_zero _`.

Establish `hr' : u ^ m = (r : ℂ)` using `by rw [hu]; exact hr`. Establish `hrc : starRingEnd ℂ u ^ m = (r : ℂ)` using `by rw [← map_pow, hr', Complex.conj_ofReal]`. Establish `hr0 : (r : ℂ) ≠ 0` using `by rw [← hr']; exact pow_ne_zero _ hu0`. Establish `hone : val ^ m = 1`. Rewrite using `[← hratio, div_pow, hr', hrc, div_self hr0]`.

Use `set z := chrW X.ν t (unifAt v) with hz`. Break down `h6 with h | h` into its components or cases. Establish `e1 : ((z ^ (2 * m) : ℂˣ) : ℂ) = 1`. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul, ← h, hone]`. Apply `hχ t (((2 * m : ℕ) : ℤ)) (by omega)` to reduce the goal to its premises.

Rewrite using `[zpow_natCast]`. Conclude with `Units.ext e1`. Establish `e1 : (((z⁻¹) ^ (2 * m) : ℂˣ) : ℂ) = 1`. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul, ← h, hone]`. Apply `hχ t (-((2 * m : ℕ) : ℤ)) (by omega)` to reduce the goal to its premises.

Rewrite using `[_root_.zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `Units.ext e1`.
-/
theorem unif_pow_ne_real : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hχ t K hK S hS ν α ι hι hint m hm r hr
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw

  haveI : Nonempty (Fin a') := ⟨⟨0, by have := hT.geo.aBig; omega⟩⟩
  obtain ⟨g₀, hg₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a') (R := Fv F v) (unifAt v)

  set k := K g₀ with hk
  have hkU : (mat k)ᵀ * incM F G.V'.J * (mat k).map (cA σ) = incM F G.V'.J := k.2
  set mi : Matrix (Fin a') (Fin a') (AE F E) := ((k : GL (Fin a') (AE F E))⁻¹).1
  have h1 : mat k * mi = 1 := Units.mul_inv (k : GL (Fin a') (AE F E))
  have h2 : mi * mat k = 1 := Units.inv_mul (k : GL (Fin a') (AE F E))
  let P₀ : GL (Fin a' ⊕ Fin a') (AE F E) := ⟨Matrix.fromBlocks (mat k) 0 0 (mat k), Matrix.fromBlocks mi 0 0 mi,
    by rw [Matrix.fromBlocks_multiply, h1]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply, h2]; simp [Matrix.fromBlocks_one]⟩
  have hP₀ : P₀ ∈ UG (cA σ) (dbl (incM F G.V'.J)) := by
    show (Matrix.fromBlocks (mat k) 0 0 (mat k))ᵀ * dbl (incM F G.V'.J) * (Matrix.fromBlocks (mat k) 0 0 (mat k)).map (cA σ) = _
    have hn : (mat k)ᵀ * (-incM F G.V'.J) * (mat k).map (cA σ) = -incM F G.V'.J := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hkU]
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.map_zero _ (map_zero (cA σ))]
    rw [hkU, hn]
  let p : UG (cA σ) (dbl (incM F G.V'.J)) := ⟨P₀, hP₀⟩
  have hpm : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 (mat k) := rfl
  have hAt : At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g₀).1 u hu
    rw [hpm, fromBlocks_diag_sub_one, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpt : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) *
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) =
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) *
        (((k : UA σ G.V'.J) : GL (Fin a') (AE F E)) : Matrix (Fin a') (Fin a') (AE F E)) := by
    rw [hpm]
    exact fromBlocks_diag_mul_diagCols _

  obtain ⟨l, hl, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hlφ, φ₀, hφ₀, hI⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  have hbox := boxFun_mem_SB hφ₀ hφ₀
  obtain ⟨φ'', hφ'', hact⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hAt _ hbox
  have h4 := GlobalTheory.T.triple_local_gl_embedding_integral hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl
    (fun g gd hgd φ₁ h₁ φ₂ h₂ => hres g gd hgd φ₁ h₁ φ₂ h₂) g₀ p hpm φ₀ hφ₀ φ₀ hφ₀ φ'' hφ'' hact μ hμ
  have hs := hsieg l hl hinv p _ hpt _ (hr₀ _ hbox).2
  rw [hact r₀ (hr₀ _ hbox), hlφ _ hφ'', hlφ _ hbox, h4] at hs
  have hbd : (∫ x, boxFun φ₀ φ₀ (Sum.elim x x) ∂μ) = ∫ x, φ₀ x * φ₀ x ∂μ := rfl
  rw [hbd] at hs
  set I := ∫ x, φ₀ x * φ₀ x ∂μ
  set val := ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) with hval
  set u : ℂ := (ν (GlobalTheory.SplitFlip.gdet g₀) : ℂ) with hu
  have hratio : u / starRingEnd ℂ u = val := by
    have : c₀ * I * (u / starRingEnd ℂ u) = c₀ * I * val := by linear_combination hs
    exact mul_left_cancel₀ (mul_ne_zero hc₀ hI) this
  have h6 := GlobalTheory.T.triple_local_gl_embedding_equivariant F E σ B a a' G X om om' hT v hv t K hK g₀

  have hgd : GlobalTheory.SplitFlip.gdet g₀ = unifAt v := hg₀
  rw [hgd] at hu h6
  have hu0 : u ≠ 0 := by rw [hu]; exact Units.ne_zero _
  have hr' : u ^ m = (r : ℂ) := by rw [hu]; exact hr
  have hrc : starRingEnd ℂ u ^ m = (r : ℂ) := by rw [← map_pow, hr', Complex.conj_ofReal]
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr']; exact pow_ne_zero _ hu0
  have hone : val ^ m = 1 := by
    rw [← hratio, div_pow, hr', hrc, div_self hr0]
  set z := chrW X.ν t (unifAt v) with hz
  rcases h6 with h | h
  · have e1 : ((z ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (((2 * m : ℕ) : ℤ)) (by omega)
    rw [zpow_natCast]
    exact Units.ext e1
  · have e1 : (((z⁻¹) ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (-((2 * m : ℕ) : ℤ)) (by omega)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact Units.ext e1

end GlobalTheory.LinBarChar
