import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateOrderConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigKIsInternalOfCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingEigenspaceOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerPairFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondenceTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowerCx

/- English proof (translation)
Establish `key : ψx * be = ψe * bu` using `mul_left_cancel₀ hlam (by linear_combination be * hX - bu * hE)`. Clear the denominators using the available nonvanishing facts. Take the linear combination `Dc * key`.
-/
theorem numeric_product_inequality (Dc ψe ψx lam n' bu be : ℂ) (hlam : lam ≠ 0) (hψe : ψe ≠ 0) (hbe : be ≠ 0)
    (hX : lam * ψx = n' * bu) (hE : lam * ψe = n' * be) : Dc / ψe * ψx = Dc * (bu / be) := by
  have key : ψx * be = ψe * bu :=
    mul_left_cancel₀ hlam (by linear_combination be * hX - bu * hE)
  field_simp
  linear_combination Dc * key

/- English proof (translation)
Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem baseChange_inK {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {H : Type} [AddCommGroup H]
    [Module R H] (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H v) = algebraMap R K (B u v) := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Take `⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩` from `IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ`. Take `⟨φ₂, hsq, hiso⟩` from `hX.pol`. Establish `e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left`.

Rewrite using `[Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left, lift_fst]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `_ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left`. Rewrite using `[Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left, lift_snd]`. Simplify using the standard rewrite rules.

Establish `hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left))` using `GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm`. Conclude with `⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _) (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩`.
-/
theorem polForm_bc' {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

/- English proof (translation)
Introduce `hADR E _ _ _ 𝔠 R X₀ X p hpull m c₀ c₁ hc₁ ψ₀ ψ hψ₀ hψ`. Take `⟨ψ₀', hψ₀', hcorr⟩` from `polForm_bc' (algebraMap R ℂ) hpull m c₀ hψ₀`. Take `⟨n', t, hn', ht⟩` from `GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hADR (FR E) 𝔠 ℂ X c₀ c₁ hc₁ ψ₀' ψ hψ₀' hψ`. Conclude with `⟨n', t, hn', fun x₀ y₀ x y hx hy ↦ by rw [← ht, hcorr x₀ x y₀ y hx hy]⟩`.
-/
theorem formRel : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p) (c₀ c₁ : 𝔠.elt),
    (c₁ : FR E) ≠ 0 → ∀ (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)) (ψ : LinearMap.BilinForm ℂ (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ψ₀ → IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag c₁) ψ →
    ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
  intro hADR E _ _ _ 𝔠 R X₀ X p hpull m c₀ c₁ hc₁ ψ₀ ψ hψ₀ hψ
  obtain ⟨ψ₀', hψ₀', hcorr⟩ := polForm_bc' (algebraMap R ℂ) hpull m c₀ hψ₀
  obtain ⟨n', t, hn', ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hADR (FR E) 𝔠 ℂ X c₀ c₁ hc₁ ψ₀' ψ hψ₀' hψ
  exact ⟨n', t, hn', fun x₀ y₀ x y hx hy ↦ by rw [← ht, hcorr x₀ x y₀ y hx hy]⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hPC hADR hADC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hpull hcm hα j hj φK hφK n eH c₀ ψ₀ hc₀ hψ₀ hlat hcmt D hD e' f' hgens N M hlow hscal m hbc ψ hψ yv ev hyv hev i`. Use `set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ`. Use `set B := (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) with hB`. Establish `hc : c ≠ ⊥` using `GlobalTheory.Div.ConjugateOrderConductor.main E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hgens (hlow i)`. Establish `hcard : 2 * Fintype.card I = Module.finrank ℚ E`.

Rewrite using `[← Fintype.card_congr U.e, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]`. Establish `hint` using `GlobalTheory.EigLineSumCM.eigK_isInternal_of_cmType E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat hcmt hcard`. Establish `horth` using `GlobalTheory.Div.PairingEigenspaceOrthogonal.pairing_eig_orth E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat`. Take `⟨hBef, hN⟩` from `GlobalTheory.Div.LowerPairFormula.lower_pair_formula E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hint horth hgens (hlow i)`. Establish `hU : ((U.c : FR E)) ≠ 0`.

Introduce `h0`. Take `⟨w⟩` from `(inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))`. Establish `hw : w.IsReal` using `NumberField.IsTotallyReal.isReal w`. Use `U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`.

Conclude with `lt_irrefl _ this`. Choose the witnesses or unpack the hypotheses as in `⟨n', t, hn', hrel⟩ : ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y → ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by`. Take `⟨n₁, t, hn₁, h⟩` from `formRel hADR E 𝔠 R X₀ X p hpull m c₀ U.c hU _ ψ hψ₀ hψ`. Use `⟨n₁ * 2, t, mul_ne_zero hn₁ two_ne_zero, fun x₀ y₀ x y hx hy ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[h x₀ y₀ x y hx hy, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_ofNat]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set a : orderC c := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t`. Establish `hact : ∀ y₀ y', m.Corr y₀ y' → m.Corr (act (dp0 R) (𝟙 _) X₀.rm t y₀) (act (dp0 ℂ) (𝟙 _) X.rm t y')`. Introduce `y₀ y' h`.

Use `haveI := X₀.rm.hom t`. Use `haveI := X.rm.hom t`. Conclude with `GrpMor.Corr.push m (X₀.rm.act t) (X.rm.act t) (hpull.act t).symm h`. Establish `hcmt' : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm a` using `by haveI := X₀.rm.hom t haveI := cm.hom a`. Rewrite using `[act_apply, act_apply]`.

Conclude with `push_congr _ _ (hcm t).symm`. Establish `hρa : ∀ v, eH.symm (ρ a v) = act (dp0 R) (𝟙 _) cm a (eH.symm v)`. Introduce `v`. Simplify using `[hρ, LinearEquiv.conjRingEquiv]`. Establish `hfmem : f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K` using `FractionRing R) ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := by`.

Rewrite using `[(hgens i).2]`. Conclude with `Submodule.mem_span_singleton_self _`. Establish `hinKa : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O` using `R) (FractionRing R) (Fin n → R) (ρ a (f' i)) = (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E) • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuatio …`. Rewrite using `[GlobalTheory.EigenLattice.inK_apply_map]`. Conclude with `GlobalTheory.LowerOps.act_of_mem_eigK hfmem a`.

Use `set lam := j ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E))`. Establish `hty : act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = lam • yv i`. Use `GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (ρ a (f' i)) (f' i) _ hinKa _ _ ?_ (hyv i)` and prove the remaining obligations. Rewrite using `[hρa, ← hcmt']`. Conclude with `hact _ _ (hyv i)`.

Establish `hrel' : ∀ x₀ x, m.Corr x₀ x → lam * ψ x (yv i) = n' * algebraMap R ℂ (ψ₀ x₀ (eH.symm (f' i)))`. Introduce `x₀ x hx`. Rewrite using `[← hrel x₀ _ x (yv i) hx (hyv i), hty, map_smul, smul_eq_mul]`. Establish `hE` using `hrel' _ _ (hev i)`. Establish `hσB : ∀ u, algebraMap R ℂ (ψ₀ (eH.symm u) (eH.symm (f' i))) = j (algebraMap R (FractionRing R) (B u (f' i)))` using `fun u ↦ (hj _).symm`.

Establish `hBne : j (algebraMap R (FractionRing R) (B (e' i) (f' i))) ≠ 0`. Rewrite using `[hj]`. Introduce `h0`. Conclude with `hBef (Subtype.ext (by simpa using h0))`. Establish `hne : (n' : ℂ) * algebraMap R ℂ (ψ₀ (eH.symm (e' i)) (eH.symm (f' i))) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 hn') (by rw [hσB]; exact hBne)`.

Rewrite `hne` using `[← hE]`. Establish `hlam : lam ≠ 0` using `left_ne_zero_of_mul hne`. Establish `hψne : ψ (ev i) (yv i) ≠ 0` using `right_ne_zero_of_mul hne`. Use `⟨hψne, fun x₀ x hx ↦ ?_⟩` and prove the remaining obligations. Establish `hx₀ : x₀ = eH.symm (eH x₀)` using `(eH.symm_apply_apply x₀).symm`.

Establish `hX` using `hrel' x₀ x hx`. Rewrite `hX` using `[hx₀, hσB]`. Rewrite `hE` using `[hσB]`. Establish `hMK : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O` using `R) (FractionRing R) (Fin n → R) (M i (eH x₀)) = (algebraMap R (FractionRing R) D * (algebraMap R (FractionRing R) (B (eH x₀) (f' i)) / algebraMap R (FractionRing R) (B (e' i) (f' i)))) • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRi …`. Rewrite using `[hscal i (eH x₀), hN, smul_smul]`.

Rewrite using `[baseChange_inK]`. Take `⟨Z, hZ⟩` from `hbc.exists (eH.symm (M i (eH x₀)))`. Establish `hZ'` using `GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (M i (eH x₀)) (f' i) _ hMK Z (yv i) hZ (hyv i)`. Establish `hL : eH.symm.conjRingEquiv (M i) x₀ = eH.symm (M i (eH x₀))`. Simplify using `[LinearEquiv.conjRingEquiv]`.

Rewrite using `[hL]`. Use `hZ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hZ', LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.BilinForm.flip_apply, smul_smul, map_mul, map_div₀, hj D]`. Use `congr 1`. Conclude with `numeric_product_inequality _ _ _ _ _ _ _ hlam hψne hBne hX hE`.
-/
theorem lower_cx : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
    ∀ (D : R), D ≠ 0 →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
    ∀ (N : I → Module.End (FractionRing R) (FractionRing R ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (e' i) (f' i) (N i)) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A), (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
    ∀ i, ψ (ev i) (yv i) ≠ 0 ∧ ∀ x₀ x, m.Corr x₀ x →
      m.Corr (eH.symm.conjRingEquiv (M i) x₀) ((((D : ℂ) / ψ (ev i) (yv i)) • (ψ.flip (yv i)).smulRight (yv i)) x) := by
  intro hPC hADR hADC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hpull hcm hα j hj φK hφK n eH c₀ ψ₀ hc₀ hψ₀ hlat hcmt D hD
    e' f' hgens N M hlow hscal m hbc ψ hψ yv ev hyv hev i
  classical
  set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ
  set B := (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) with hB
  have hc : c ≠ ⊥ := GlobalTheory.Div.ConjugateOrderConductor.main E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hgens (hlow i)
  have hcard : 2 * Fintype.card I = Module.finrank ℚ E := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ (FR E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hint := GlobalTheory.EigLineSumCM.eigK_isInternal_of_cmType E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat hcmt hcard
  have horth := GlobalTheory.Div.PairingEigenspaceOrthogonal.pairing_eig_orth E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat
  obtain ⟨hBef, hN⟩ := GlobalTheory.Div.LowerPairFormula.lower_pair_formula E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hint horth hgens (hlow i)
  have hU : ((U.c : FR E)) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    have := U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨n', t, hn', hrel⟩ : ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
    obtain ⟨n₁, t, hn₁, h⟩ := formRel hADR E 𝔠 R X₀ X p hpull m c₀ U.c hU _ ψ hψ₀ hψ
    refine ⟨n₁ * 2, t, mul_ne_zero hn₁ two_ne_zero, fun x₀ y₀ x y hx hy ↦ ?_⟩
    rw [h x₀ y₀ x y hx hy, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    push_cast
    ring
  set a : orderC c := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t
  have hact : ∀ y₀ y', m.Corr y₀ y' →
      m.Corr (act (dp0 R) (𝟙 _) X₀.rm t y₀) (act (dp0 ℂ) (𝟙 _) X.rm t y') := by
    intro y₀ y' h
    haveI := X₀.rm.hom t
    haveI := X.rm.hom t
    exact GrpMor.Corr.push m (X₀.rm.act t) (X.rm.act t) (hpull.act t).symm h
  have hcmt' : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm a := by
    haveI := X₀.rm.hom t
    haveI := cm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm t).symm
  have hρa : ∀ v, eH.symm (ρ a v) = act (dp0 R) (𝟙 _) cm a (eH.symm v) := by
    intro v
    simp [hρ, LinearEquiv.conjRingEquiv]
  have hfmem : f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := FractionRing R) ρ
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := by
    rw [(hgens i).2]; exact Submodule.mem_span_singleton_self _
  have hinKa : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (ρ a (f' i)) =
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [GlobalTheory.EigenLattice.inK_apply_map]
    exact GlobalTheory.LowerOps.act_of_mem_eigK hfmem a
  set lam := j ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E))
  have hty : act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = lam • yv i := by
    refine GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (ρ a (f' i)) (f' i) _ hinKa _ _ ?_ (hyv i)
    rw [hρa, ← hcmt']
    exact hact _ _ (hyv i)
  have hrel' : ∀ x₀ x, m.Corr x₀ x → lam * ψ x (yv i) = n' * algebraMap R ℂ (ψ₀ x₀ (eH.symm (f' i))) := by
    intro x₀ x hx
    rw [← hrel x₀ _ x (yv i) hx (hyv i), hty, map_smul, smul_eq_mul]
  have hE := hrel' _ _ (hev i)
  have hσB : ∀ u, algebraMap R ℂ (ψ₀ (eH.symm u) (eH.symm (f' i))) = j (algebraMap R (FractionRing R) (B u (f' i))) :=
    fun u ↦ (hj _).symm
  have hBne : j (algebraMap R (FractionRing R) (B (e' i) (f' i))) ≠ 0 := by
    rw [hj]
    intro h0
    exact hBef (Subtype.ext (by simpa using h0))
  have hne : (n' : ℂ) * algebraMap R ℂ (ψ₀ (eH.symm (e' i)) (eH.symm (f' i))) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn') (by rw [hσB]; exact hBne)
  rw [← hE] at hne
  have hlam : lam ≠ 0 := left_ne_zero_of_mul hne
  have hψne : ψ (ev i) (yv i) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨hψne, fun x₀ x hx ↦ ?_⟩
  have hx₀ : x₀ = eH.symm (eH x₀) := (eH.symm_apply_apply x₀).symm
  have hX := hrel' x₀ x hx
  rw [hx₀, hσB] at hX
  rw [hσB] at hE
  have hMK : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (M i (eH x₀)) =
      (algebraMap R (FractionRing R) D * (algebraMap R (FractionRing R) (B (eH x₀) (f' i)) /
        algebraMap R (FractionRing R) (B (e' i) (f' i)))) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [hscal i (eH x₀), hN, smul_smul]
    rw [baseChange_inK]
  obtain ⟨Z, hZ⟩ := hbc.exists (eH.symm (M i (eH x₀)))
  have hZ' := GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (M i (eH x₀)) (f' i) _ hMK Z (yv i) hZ (hyv i)
  have hL : eH.symm.conjRingEquiv (M i) x₀ = eH.symm (M i (eH x₀)) := by
    simp [LinearEquiv.conjRingEquiv]
  rw [hL]
  convert hZ using 1
  rw [hZ', LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.BilinForm.flip_apply, smul_smul, map_mul, map_div₀, hj D]
  congr 1
  exact numeric_product_inequality _ _ _ _ _ _ _ hlam hψne hBne hX hE

end GlobalTheory.LowerCx
