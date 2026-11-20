import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdditiveCharacterProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormulaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

open GlobalTheory.SympChange in

/- English proof (translation)
Introduce `F _ _ ψ hψ hunr hnt κ _ _`. Establish `hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)), spAct (weylM (F` using `F) (κ := κ)) w = (w.2, -w.1) := by`. Introduce `R _ _ w`. Use extensionality with `k`. Simplify using `[spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]`.

Simplify using `[spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]`. Establish `hSB` using `fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ`. Establish `hInv` using `fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ`. Establish `hLaw` using `GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ`. Establish `hInd` using `fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ`.

Establish `hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ`. Introduce `v c φ`. Use function extensionality and compare the values at `y`. Simplify using `only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul c _`.

Establish `h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0`. Introduce `v`. Use function extensionality and compare the values at `y`. Simplify using `[fourV]`. Use `choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))`.

Set `P : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)` to `fun v => (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)`. Establish `hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v)` using `fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2`. Establish `hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ` using `fun v φ hφ => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)`. Set `ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)` to `fun v => { toFun := fun φ => fourV ψ v (P v φ) map_add' := fun φ χ => by`. Rewrite using `[map_add]`.

Conclude with `(hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)`. Use the proof step `map_smul' := fun c φ => by`. Rewrite using `[map_smul, RingHom.id_apply]`. Conclude with `hsmV v c _ }`. Establish `hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ` using `fun v φ hφ => by show fourV ψ v (P v φ) = _`.

Rewrite using `[hPid v φ hφ]`. Establish `hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v)` using `fun v φ hφ => ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩`. Establish `hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _`. Introduce `v`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Rewrite using `[hev v φ hφ]`. Conclude with `(hSB v).1 φ hφ`. Introduce `φ hφ`. Establish `h1` using `hneg v φ hφ`.

Use `⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩` and prove the remaining obligations. Rewrite using `[hev v _ ((hSB v).1 _ h1), hInv v _ h1]`. Simplify using the standard rewrite rules. Establish `hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0`. Introduce `v φ hφ h`.

Rewrite `h` using `[hev v φ hφ]`. Establish `h2` using `hInv v φ hφ`. Rewrite `h2` using `[h, h0V]`. Use function extensionality and compare the values at `x`. Establish `h3` using `congrFun h2 (-x)`.

Simplify using `only [Pi.zero_apply, neg_neg] at h3`. Conclude with `h3.symm`. Take `⟨ei, hsurj, hei, hcont⟩` from `GlobalTheory.T.finite_fourier_transform_surjective_integral F κ`. Take `⟨μ, hμ, hprod⟩` from `GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ`. Use `haveI := hμ`.

Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Establish `hspan` using `GlobalTheory.T.schwartz_adelic_eq_span_pure F κ`. Set `fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ` to `fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ`. Establish `hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧ fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y`. Introduce `f φ hφ hae y`.

Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae`. Establish `e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x => (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) * ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i))`. Use function extensionality and compare the values at `h3`. Take `⟨hc, hi⟩` from `hcont f (fun i => evI F (y i))`. Take `⟨j1, j2⟩` from `hprod _ _ hc hi h1 h2`.

Use `⟨e ▸ j1, ?_⟩` and prove the remaining obligations. Use `show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _`. Rewrite using `[e, j2, ← hei]`. Both sides reduce to the same expression. Establish `hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ`.

Introduce `Φ hΦ y`. Rewrite `hΦ` using `[hspan]`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, φ, hφ, hae, rfl⟩` from `h`.

Conclude with `(hpure f φ hφ hae y).1`. Consider the case `zero => simp`. Consider the case `add Φ Ψ _ _ h1 h2`. Use `(h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[add_mul]`.

Consider the case `smul c Φ _ h => simpa [mul_assoc] using h.const_mul c`. Establish `hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ`. Introduce `Φ hΦ Ψ hΨ`. Use function extensionality and compare the values at `y`. Simplify using `only [fA, Pi.add_apply, add_mul]`.

Conclude with `integral_add (hint Φ hΦ y) (hint Ψ hΨ y)`. Establish `hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ`. Introduce `c Φ`. Use function extensionality and compare the values at `y`. Simplify using `only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]`.

Conclude with `integral_const_mul c _`. Establish `hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ`. Introduce `Φ hΦ`. Rewrite `hΦ`, the goal using `[hspan]`. Proceed by induction on `hΦ using Submodule.span_induction with`.

Consider the case `mem Φ h`. Take `⟨f, φ, hφ, hae, rfl⟩` from `h`. Establish `e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v))` using `funext fun y => (hpure f φ hφ hae y).2`. Rewrite using `[e]`. Use `Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩` and prove the remaining obligations.

Use `filter_upwards [hae, hunr] with v h1 h2`. Rewrite using `[h1, (hInd v).2 h2]`. Consider the case `zero`. Establish `: fA 0 = 0` using `by funext y; simp [fA]`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Consider the case `add Φ Ψ hΦ hΨ h1 h2`. Rewrite using `[hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]`. Conclude with `add_mem h1 h2`. Consider the case `smul c Φ _ h`.

Rewrite using `[hsmul]`. Conclude with `Submodule.smul_mem _ c h`. Establish `hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ)`. Introduce `w Φ`. Use function extensionality and compare the values at `y`.

Simplify using `only [fA, schr]`. Establish `h1` using `integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1`. Simplify using `only [add_sub_cancel_right] at h1`. Rewrite using `[h1, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Establish `h2 : (⅟(2 : AF F)) + ⅟2 = 1` using `invOf_two_add_invOf_two`. Establish `key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y = (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2)`. Simplify using `only [sub_dotProduct, dotProduct_add, dotProduct_neg]`. Rewrite using `[dotProduct_comm w.2 w.1, dotProduct_comm y w.1]`.

Take the linear combination `(w.1 ⬝ᵥ w.2) * h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`.

Rewrite using `[key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨D, hD⟩` from `Submodule.exists_isCompl (schA F κ)`. Set `Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)` to `(schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD`. Establish `hQmem : ∀ Φ, Q Φ ∈ schA F κ` using `fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2`.

Establish `hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ` using `fun Φ hΦ => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)`. Set `e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ` to `{ toFun := fun Φ => fA (Q Φ) map_add' := fun Φ Ψ => by rw [map_add]; exact hadd _ (hQmem Φ) _ (hQmem Ψ) map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }`. Establish `he : ∀ Φ ∈ schA F κ, e Φ = fA Φ` using `fun Φ hΦ => by show fA (Q Φ) = _`. Rewrite using `[hQid Φ hΦ]`. Use `⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[he Φ hΦ]`. Conclude with `hkeep Φ hΦ`. Rewrite using `[he _ (GlobalTheory.T.schrodinger_preserves_schwartz F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]`. Rewrite using `[hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]`. Use `filter_upwards [hunr] with v hv`.

Rewrite using `[hev v _ (hInd v).1, (hInd v).2 hv]`. Introduce `f φ hφ hae`. Establish `hm : pure f φ ∈ schA F κ`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩`.

Establish `e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v)` using `funext fun v => hev v _ (hφ v)`. Rewrite using `[he _ hm, e2]`. Conclude with `funext fun y => (hpure f φ hφ hae y).2`.
-/
theorem GlobalTheory.WeylFour.weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr hnt κ _ _
  classical

  have hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)),
      spAct (weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
    intro R _ _ w
    ext k
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]

  have hSB := fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ
  have hInv := fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ
  have hLaw := GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ
  have hInd := fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ
  have hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ := by
    intro v c φ; funext y
    simp only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0 := by
    intro v; funext y; simp [fourV]
  choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))
  let P : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)
  have hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v) := fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2
  have hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ := fun v φ hφ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)
  let ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    { toFun := fun φ => fourV ψ v (P v φ)
      map_add' := fun φ χ => by
        rw [map_add]; exact (hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)
      map_smul' := fun c φ => by
        rw [map_smul, RingHom.id_apply]; exact hsmV v c _ }
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ := fun v φ hφ => by
    show fourV ψ v (P v φ) = _
    rw [hPid v φ hφ]
  have hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v) := fun v φ hφ =>
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  have hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _ := by
    intro v
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      rw [hev v φ hφ]; exact (hSB v).1 φ hφ
    · intro φ hφ
      have h1 := hneg v φ hφ
      refine ⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩
      rw [hev v _ ((hSB v).1 _ h1), hInv v _ h1]
      simp
  have hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0 := by
    intro v φ hφ h
    rw [hev v φ hφ] at h
    have h2 := hInv v φ hφ
    rw [h, h0V] at h2
    funext x
    have h3 := congrFun h2 (-x)
    simp only [Pi.zero_apply, neg_neg] at h3
    exact h3.symm

  obtain ⟨ei, hsurj, hei, hcont⟩ := GlobalTheory.T.finite_fourier_transform_surjective_integral F κ
  obtain ⟨μ, hμ, hprod⟩ := GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ
  haveI := hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hspan := GlobalTheory.T.schwartz_adelic_eq_span_pure F κ
  let fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ
  have hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧
        fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y := by
    intro f φ hφ hae y
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae
    have e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) *
          ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i)) :=
      funext h3
    obtain ⟨hc, hi⟩ := hcont f (fun i => evI F (y i))
    obtain ⟨j1, j2⟩ := hprod _ _ hc hi h1 h2
    refine ⟨e ▸ j1, ?_⟩
    show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _
    rw [e, j2, ← hei]
    rfl
  have hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ := by
    intro Φ hΦ y
    rw [hspan] at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      exact (hpure f φ hφ hae y).1
    | zero => simp
    | add Φ Ψ _ _ h1 h2 =>
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [add_mul]
    | smul c Φ _ h => simpa [mul_assoc] using h.const_mul c
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ := by
    intro Φ hΦ Ψ hΨ; funext y
    simp only [fA, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ y) (hint Ψ hΨ y)
  have hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ := by
    intro c Φ; funext y
    simp only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ := by
    intro Φ hΦ
    rw [hspan] at hΦ ⊢
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      have e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v)) := funext fun y => (hpure f φ hφ hae y).2
      rw [e]
      refine Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩
      filter_upwards [hae, hunr] with v h1 h2
      rw [h1, (hInd v).2 h2]
    | zero =>
      have : fA 0 = 0 := by funext y; simp [fA]
      rw [this]; exact zero_mem _
    | add Φ Ψ hΦ hΨ h1 h2 =>
      rw [hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]; exact add_mem h1 h2
    | smul c Φ _ h =>
      rw [hsmul]; exact Submodule.smul_mem _ c h
  have hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ) := by
    intro w Φ; funext y
    simp only [fA, schr]
    have h1 := integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) *
      Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1
    simp only [add_sub_cancel_right] at h1
    rw [h1, ← integral_const_mul]
    congr 1; funext z
    have h2 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
    have key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y =
        (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2) := by
      simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
      rw [dotProduct_comm w.2 w.1, dotProduct_comm y w.1]
      linear_combination (w.1 ⬝ᵥ w.2) * h2
    calc ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)
        = Φ z * ψ (((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y) := by
          rw [AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]; ring
      _ = _ := by
          rw [key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]; ring
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (schA F κ)
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD
  have hQmem : ∀ Φ, Q Φ ∈ schA F κ := fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2
  have hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ := fun Φ hΦ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)
  let e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ :=
    { toFun := fun Φ => fA (Q Φ)
      map_add' := fun Φ Ψ => by rw [map_add]; exact hadd _ (hQmem Φ) _ (hQmem Ψ)
      map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }
  have he : ∀ Φ ∈ schA F κ, e Φ = fA Φ := fun Φ hΦ => by
    show fA (Q Φ) = _
    rw [hQid Φ hΦ]
  refine ⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩
  · rw [he Φ hΦ]; exact hkeep Φ hΦ
  · rw [he _ (GlobalTheory.T.schrodinger_preserves_schwartz F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]
  · rw [hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]
  · filter_upwards [hunr] with v hv
    rw [hev v _ (hInd v).1, (hInd v).2 hv]
  · intro f φ hφ hae
    have hm : pure f φ ∈ schA F κ := by
      rw [hspan]; exact Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩
    have e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v) := funext fun v => hev v _ (hφ v)
    rw [he _ hm, e2]
    exact funext fun y => (hpure f φ hφ hae y).2
