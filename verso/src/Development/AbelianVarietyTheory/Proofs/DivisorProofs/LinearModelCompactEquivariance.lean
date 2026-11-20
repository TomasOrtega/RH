import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalBox

open Matrix

section Local

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl` using `continuous_pi fun i => continuous_apply _`. Establish `cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr` using `continuous_pi fun i => continuous_apply _`. Use `⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩` and prove the remaining obligations. Set `e` to `(Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))`. Use `HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂` using `fun h => hx ⟨e x, h, e.symm_apply_apply x⟩`. Rewrite `hx'` using `[Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or]`. Simplify using `only [boxFun]`. Break down `hx' with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h, zero_mul]`.

Rewrite using `[image_eq_zero_of_notMem_tsupport h, mul_zero]`.
-/
theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
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
Assemble the required witnesses or components as `⟨h.1.comp _, h.2.comp_left (map_zero _)⟩`.
-/
theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [tens, boxFun, Function.comp_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tens_box (v : Pl F) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

/- English proof (translation)
Use `⟨fun x z hz => ?_, ?_⟩` and prove the remaining obligations. Establish `hz1 : At (evFin F v) (z ∘ Sum.inl)` using `fun u hu => by`. Use function extensionality and compare the values at `i`. Conclude with `congrFun (hz u hu) (Sum.inl i)`. Establish `hz2 : At (evFin F v) (z ∘ Sum.inr)` using `fun u hu => by`.

Use function extensionality and compare the values at `i`. Conclude with `congrFun (hz u hu) (Sum.inr i)`. Use `show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)`. Rewrite using `[show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl, show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]`. Rewrite using `[tens_box]`.

Conclude with `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2`.
-/
theorem rest_box (v : Pl F) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

/- English proof (translation)
Use function extensionality and compare the values at `y`. Set `z : κ → AF F` to `fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))`. Establish `hz : At (evFin F v) z`. Introduce `u hu`. Use function extensionality and compare the values at `i`.

Conclude with `GlobalTheory.LatVac.at_liftV v _ u hu`. Establish `hev : (fun i => evFin F v ((x₀ + z) i)) = y`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]`. Normalize the expressions using the abelian group laws.

Establish `e` using `congrFun h (x₀ + z)`. Simplify using `only [tens, hev, hr x₀ z hz] at e`. Conclude with `mul_right_cancel₀ h0 e`.
-/
theorem eq_of_tens_ne (v : Pl F) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

end Local

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd hcd h hh gd hgd`. Establish `hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι` using `hι`. Use `set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def`. Establish `h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v)` using `GlobalTheory.StdVacuum.indicator_mem_SB v`. Establish `hφ₀0 : φ₀ (fun _ => 0) = 1`.

Rewrite using `[hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]`. Both sides reduce to the same expression. Establish `hne : ι φ₀ ≠ 0`. Introduce `e`. Establish `e0 : φ₀ = 0` using `hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])`.

Establish `e1` using `congrFun e0 (fun _ => 0)`. Rewrite `e1` using `[hφ₀0]`. Conclude with `one_ne_zero e1`. Choose the witnesses or unpack the hypotheses as in `⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hne (funext hc)`. Use `set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def`. Establish `h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v)` using `conj_mem_SB h0`. Establish `hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀` using `funext fun x => Complex.conj_conj _`.

Establish `h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v)`. Introduce `u _`. Establish `e : mat (1 : UA σ X.J) = 1` using `rfl`. Rewrite using `[e, sub_self, smul_zero]`. Take `⟨φ₁, ⟨h1, hA1⟩, -⟩` from `(GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0`.

Establish `hk` using `hκ h hh φ₀ h0 φ₁ h1 hA1`. Establish `hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v)`. Introduce `u hu`. Rewrite using `[hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]`. Simplify using the standard rewrite rules.

Take `⟨Φ₁, hΦ₁, hAd⟩` from `hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v`. Establish `hRb` using `rest_box v (hR φ₀ h0) (hR φ₂ h2)`. Establish `e` using `hAd _ hRb`. Rewrite `e` using `[tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box]`.

Establish `h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0` using `by show R 0 * R 0 ≠ 0`. Conclude with `mul_ne_zero hR0 hR0`. Establish `eΦ : Φ₁ = boxFun φ₁ φ₂` using `eq_of_tens_ne v hRb.1 h0r e.symm`. Establish `hs` using `hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd`. Rewrite `hs` using `[eΦ]`.

Use `set L := locMat t c h with hL`. Establish `hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1` using `by show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) * (GlobalTheory.DblScal.dsum c).val = _`. Rewrite using `[hgd, hL, locMat_val, fromBlocks_map]`. Simplify using `only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)), Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]`. Use `congr 1`.

Simplify using `[Units.mul_inv]`. Establish `hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1`. Establish `hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1`. Rewrite using `[hD, fromBlocks_multiply]`. Simplify using `[← fromBlocks_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Establish `hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val = Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1`. Rewrite using `[GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]`. Simplify using the standard rewrite rules.

Establish `hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀`. Rewrite using `[GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]`. Establish `hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A`. Introduce `A Bm`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm`. Introduce `A Bm`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val = Matrix.fromCols Y₀ Y₀`. Rewrite using `[hT, Matrix.fromCols_mul_fromBlocks]`. Simplify using `[hY]`. Establish `eY` using `congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)`. Rewrite `eY` using `[hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2]`.

Simplify using `only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY`. Establish `hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0` using `mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)`. Apply `mul_right_cancel₀ hP0` to reduce the goal to its premises. Take the linear combination `eY`.
-/
theorem scal_diag_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd
    hcd h hh gd hgd
  have hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι

  set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def
  have h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ (fun _ => 0) = 1 := by
    rw [hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
      {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hne : ι φ₀ ≠ 0 := by
    intro e
    have e0 : φ₀ = 0 := hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])
    have e1 := congrFun e0 (fun _ => 0)
    rw [hφ₀0] at e1
    exact one_ne_zero e1
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def
  have h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v) := conj_mem_SB h0
  have hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀ := funext fun x => Complex.conj_conj _

  have h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    have e : mat (1 : UA σ X.J) = 1 := rfl
    rw [e, sub_self, smul_zero]
  obtain ⟨φ₁, ⟨h1, hA1⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0
  have hk := hκ h hh φ₀ h0 φ₁ h1 hA1

  have hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v) := by
    intro u hu
    rw [hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]
    simp
  obtain ⟨Φ₁, hΦ₁, hAd⟩ := hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v
  have hRb := rest_box v (hR φ₀ h0) (hR φ₂ h2)
  have e := hAd _ hRb
  rw [tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box] at e
  have h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0 := by
    show R 0 * R 0 ≠ 0
    exact mul_ne_zero hR0 hR0
  have eΦ : Φ₁ = boxFun φ₁ φ₂ := eq_of_tens_ne v hRb.1 h0r e.symm

  have hs := hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd
  rw [eΦ] at hs
  set L := locMat t c h with hL
  have hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1 := by
    show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) *
      (GlobalTheory.DblScal.dsum c).val = _
    rw [hgd, hL, locMat_val, fromBlocks_map]
    simp only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  have hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
    have hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1 := by
      rw [hD, fromBlocks_multiply]
      simp [← fromBlocks_one]
    calc ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val
        = (Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val) *
            ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val := by rw [hm, Matrix.one_mul]
      _ = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1 := by
    rw [GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]
    simp
  have hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀ := by
    rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  have hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A := by
    intro A Bm; ext i j; rfl
  have hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm := by
    intro A Bm; ext i j; rfl
  have hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromCols Y₀ Y₀ := by
    rw [hT, Matrix.fromCols_mul_fromBlocks]
    simp [hY]
  have eY := congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)
  rw [hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2] at eY
  simp only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY
  have hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0 := mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)
  apply mul_right_cancel₀ hP0
  linear_combination eY

end GlobalTheory.DblScalBox

end
