import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanJac

/- English proof (translation)
Use `haveI : Algebra.FormallyEtale ℤ ℚ := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℤ)`. Use `haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F`. Use `haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F`. Rewrite using `[← δ.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D ℤ F a) 0, map_zero]`.
-/
theorem derivation_eq_zero {F N : Type} [Field F] [NumberField F] [AddCommGroup N] [Module F N]
    (δ : Derivation ℤ F N) (a : F) : δ a = 0 := by
  haveI : Algebra.FormallyEtale ℤ ℚ := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  rw [← δ.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D ℤ F a) 0,
    map_zero]

/- English proof (translation)
Use `letI : Module F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp χ).toModule`. Set `δ : Derivation ℤ F K` to `Derivation.mk' { toFun := fun x => (χ x).snd map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add] map_smul' := fun n x => by`. Rewrite using `[map_zsmul, TrivSqZeroExt.snd_smul]`. Use `rfl }`. Use the proof step `(fun x y => by`.

Express the relevant statement in the definitionally equal form `(χ (x * y)).snd = (χ x).fst * (χ y).snd + (χ y).fst * (χ x).snd`. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_comm (χ x).snd])`. Conclude with `derivation_eq_zero δ a`.
-/
theorem snd_eq_zero {F K : Type} [Field F] [NumberField F] [Field K] (χ : F →+* DualNumber K)
    (a : F) : (χ a).snd = 0 := by
  letI : Module F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp χ).toModule
  let δ : Derivation ℤ F K := Derivation.mk'
    { toFun := fun x => (χ x).snd
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun n x => by
        rw [map_zsmul, TrivSqZeroExt.snd_smul]
        rfl }
    (fun x y => by
      change (χ (x * y)).snd = (χ x).fst * (χ y).snd + (χ y).fst * (χ x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mul_comm (χ x).snd])
  exact derivation_eq_zero δ a

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `letI := ψ.toAlgebra`. Use `letI : Algebra k K := (ψ.comp α).toAlgebra`. Use `haveI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `δ (f : A) : Fin D → K` to `fun b => (φ b f).snd`.

Establish `hmul (f g : A) : δ (f * g) = f • δ g + g • δ f`. Use function extensionality and compare the values at `b`. Rewrite using `[Pi.add_apply, Pi.smul_apply, Pi.smul_apply]`. Simplify using `only [δ, map_mul, TrivSqZeroExt.snd_mul, hφ, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Express the relevant statement in the definitionally equal form `_ = ψ f * _ + ψ g * _`.

Expand and normalize the polynomial expressions, which then agree. Establish `hδc (a : k) : δ (algebraMap k A a) = 0` using `funext fun b => hc b a`. Set `d : Derivation k A (Fin D → K)` to `Derivation.mk' { toFun := δ map_add' := fun f g => by`. Use function extensionality and compare the values at `b`. Simplify using `only [δ, map_add, TrivSqZeroExt.snd_add, Pi.add_apply]`.

Use the proof step `map_smul' := fun a f => by`. Rewrite using `[Algebra.smul_def, hmul, hδc, smul_zero, add_zero, algebraMap_smul]`. Use `rfl } hmul`. Set `det : (Fin D → K) [⋀^Fin D]→ₗ[A] K` to `{ (Matrix.detRowAlternating (n := Fin D) (R := K)).toMultilinearMap.restrictScalars A with map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := K)).map_eq_zero_of_eq }`. Set `Λ` to `exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)`.

Use `⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩` and prove the remaining obligations. Use `(exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_` and prove the remaining obligations. Simplify using `only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]`. Both sides reduce to the same expression.
-/
theorem exists_forms_map {k A K : Type} [CommRing k] [CommRing A] [Field K] {D : ℕ}
    (α : k →+* A) (ψ : A →+* K) (φ : Fin D → A →+* DualNumber K)
    (hφ : ∀ b x, (φ b x).fst = ψ x) (hc : ∀ b a, (φ b (α a)).snd = 0) :
    ∃ Λ : Forms α D →ₛₗ[ψ] K,
      ∀ f, Λ (dForm α f) = (Matrix.of fun a b => (φ b (f a)).snd).det := by
  letI := α.toAlgebra
  letI := ψ.toAlgebra
  letI : Algebra k K := (ψ.comp α).toAlgebra
  haveI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let δ (f : A) : Fin D → K := fun b => (φ b f).snd
  have hmul (f g : A) : δ (f * g) = f • δ g + g • δ f := by
    funext b
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp only [δ, map_mul, TrivSqZeroExt.snd_mul, hφ, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    change _ = ψ f * _ + ψ g * _
    ring
  have hδc (a : k) : δ (algebraMap k A a) = 0 := funext fun b => hc b a
  let d : Derivation k A (Fin D → K) := Derivation.mk'
    { toFun := δ
      map_add' := fun f g => by
        funext b
        simp only [δ, map_add, TrivSqZeroExt.snd_add, Pi.add_apply]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, hmul, hδc, smul_zero, add_zero, algebraMap_smul]
        rfl } hmul
  let det : (Fin D → K) [⋀^Fin D]→ₗ[A] K :=
    { (Matrix.detRowAlternating (n := Fin D) (R := K)).toMultilinearMap.restrictScalars A with
      map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := K)).map_eq_zero_of_eq }
  let Λ := exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)
  refine ⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩
  refine (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_
  simp only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end GlobalTheory.TanJac

namespace GlobalTheory.TanJac

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y X Z M K _ z i w hw O O' hO hO' g g' hz hz' hwO hwO'`. Set `x0` to `z.base (IsLocalRing.closedPoint K)`. Establish `hx0 : x0 ∈ O ⊓ O'` using `⟨hz (Set.mem_univ _), hz' (Set.mem_univ _)⟩`. Take `⟨V, hV, hxV, hVle⟩` from `Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hx0`. Establish `hV' : IsAffineOpen V` using `hV`.

Establish `hVO : V ≤ O` using `hVle.trans inf_le_left`. Establish `hVO' : V ≤ O'` using `hVle.trans inf_le_right`. Establish `hzV : ⊤ ≤ z ⁻¹ᵁ V` using `((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ V)).1 hxV).ge`. Establish `hwV : ∀ b, ⊤ ≤ w b ⁻¹ᵁ V` using `fun b => GlobalTheory.CompHS.le_preimage_of_dualNumber _ (w b) V (by rw [hw b]; exact hzV)`. Establish `hfst : ∀ b f, (evalPt (w b) V (hwV b) f).fst = evalPt z V hzV f`.

Introduce `b f`. Establish `e` using `evalPt_spMap_comp (TrivSqZeroExt.fstHom K K K).toRingHom (w b) V (hwV b) (by rw [hw b]; exact hzV) f`. Establish `e' : ∀ (x : Sp K ⟶ M.X) (_ : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = x) (h₁ : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ V) (h₂ : ⊤ ≤ x ⁻¹ᵁ V), evalPt (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) V h₁ f = evalPt x V h₂ f`. Introduce and unpack `x rfl h₁ h₂`. Both sides reduce to the same expression.

Rewrite using `[← e' z (hw b) (by rw [hw b]; exact hzV) hzV, e]`. Both sides reduce to the same expression. Take `⟨Λ, hΛ⟩` from `exists_forms_map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V) (evalPt z V hzV) (fun b => evalPt (w b) V (hwV b)) hfst (fun b a => snd_eq_zero ((evalPt (w b) V (hwV b)).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V)) a)`. Establish `hVi : V ≤ M.K.bundle.U i` using `hVO.trans hO`. Establish `key : ∀ (P : M.X.Opens) (hP : P ≤ M.K.bundle.U i) (hVP : V ≤ P) (f : Fin (dimFlag Dw) → Γ(M.X, P)) (hzP : ⊤ ≤ z ⁻¹ᵁ P) (hwP : ∀ b, ⊤ ≤ w b ⁻¹ᵁ P), (Matrix.of fun a b => (evalPt (w b) P (hwP b) (f a)).snd).det = evalPt z P hzP (M.K.jacobian i hP f) * Λ (resForm hVi (M.K.om i))`.

Introduce `P hP hVP f hzP hwP`. Establish `e` using `congrArg Λ (M.K.jacobian_smul_om i hV' hVi (fun a => resG M.X hVP (f a)))`. Establish `e1 : Λ (dOn M.str (fun a => resG M.X hVP (f a))) = (Matrix.of fun a b => (evalPt (w b) V (hwV b) (resG M.X hVP (f a))).snd).det` using `hΛ (fun a => resG M.X hVP (f a))`. Establish `e2 : Λ (M.K.jacobian i hVi (fun a => resG M.X hVP (f a)) • resForm hVi (M.K.om i)) = evalPt z V hzV (M.K.jacobian i hVi (fun a => resG M.X hVP (f a))) * Λ (resForm hVi (M.K.om i))` using `Λ.map_smulₛₗ _ _`. Rewrite using `[← evalPt_res z hVP hzP hzV, GlobalTheory.CanonLB.resG_jacobian, ← e2, e, e1]`.

Use `congr 1`. Use extensionality with `a b`. Conclude with `(congrArg TrivSqZeroExt.snd (evalPt_res (w b) hVP (hwP b) (hwV b) (f a))).symm`. Establish `alg : ∀ (d d' A B C : K), d = A * C → d' = B * C → d * B = d' * A`. Introduce `d d' A B C h h'`.

Rewrite using `[h, h']`. Expand and normalize the polynomial expressions, which then agree. Conclude with `alg _ _ _ _ _ (key O hO hVO g hz hwO) (key O' hO' hVO' g' hz' hwO')`.
-/
theorem det_mul_jacobian_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι)
    (w : Fin (dimFlag Dw) → (Sp (DualNumber K) ⟶ M.X))
    (hw : ∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z)
    (O O' : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (hO' : O' ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (g' : Fin (dimFlag Dw) → Γ(M.X, O'))
    (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ z ⁻¹ᵁ O') (hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O) (hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O'), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det * evalPt z O' hz' (M.K.jacobian i hO' g') =
      (Matrix.of fun a b => (evalPt (w b) O' (hwO' b) (g' a)).snd).det * evalPt z O hz (M.K.jacobian i hO g) := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ z i w hw O O' hO hO' g g' hz hz' hwO hwO'
  let x0 := z.base (IsLocalRing.closedPoint K)
  have hx0 : x0 ∈ O ⊓ O' := ⟨hz (Set.mem_univ _), hz' (Set.mem_univ _)⟩
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hx0
  have hV' : IsAffineOpen V := hV
  have hVO : V ≤ O := hVle.trans inf_le_left
  have hVO' : V ≤ O' := hVle.trans inf_le_right
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (z ⁻¹ᵁ V)).1 hxV).ge
  have hwV : ∀ b, ⊤ ≤ w b ⁻¹ᵁ V := fun b =>
    GlobalTheory.CompHS.le_preimage_of_dualNumber _ (w b) V (by rw [hw b]; exact hzV)
  have hfst : ∀ b f, (evalPt (w b) V (hwV b) f).fst = evalPt z V hzV f := by
    intro b f
    have e := evalPt_spMap_comp (TrivSqZeroExt.fstHom K K K).toRingHom (w b) V (hwV b)
      (by rw [hw b]; exact hzV) f
    have e' : ∀ (x : Sp K ⟶ M.X) (_ : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = x)
        (h₁ : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ V) (h₂ : ⊤ ≤ x ⁻¹ᵁ V),
        evalPt (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) V h₁ f = evalPt x V h₂ f := by
      rintro x rfl h₁ h₂
      rfl
    rw [← e' z (hw b) (by rw [hw b]; exact hzV) hzV, e]
    rfl
  obtain ⟨Λ, hΛ⟩ := exists_forms_map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V) (evalPt z V hzV)
    (fun b => evalPt (w b) V (hwV b)) hfst
    (fun b a => snd_eq_zero ((evalPt (w b) V (hwV b)).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str V)) a)
  have hVi : V ≤ M.K.bundle.U i := hVO.trans hO
  have key : ∀ (P : M.X.Opens) (hP : P ≤ M.K.bundle.U i) (hVP : V ≤ P)
      (f : Fin (dimFlag Dw) → Γ(M.X, P)) (hzP : ⊤ ≤ z ⁻¹ᵁ P) (hwP : ∀ b, ⊤ ≤ w b ⁻¹ᵁ P),
      (Matrix.of fun a b => (evalPt (w b) P (hwP b) (f a)).snd).det =
        evalPt z P hzP (M.K.jacobian i hP f) * Λ (resForm hVi (M.K.om i)) := by
    intro P hP hVP f hzP hwP
    have e := congrArg Λ (M.K.jacobian_smul_om i hV' hVi (fun a => resG M.X hVP (f a)))
    have e1 : Λ (dOn M.str (fun a => resG M.X hVP (f a))) =
        (Matrix.of fun a b => (evalPt (w b) V (hwV b) (resG M.X hVP (f a))).snd).det :=
      hΛ (fun a => resG M.X hVP (f a))
    have e2 : Λ (M.K.jacobian i hVi (fun a => resG M.X hVP (f a)) • resForm hVi (M.K.om i)) =
        evalPt z V hzV (M.K.jacobian i hVi (fun a => resG M.X hVP (f a))) *
          Λ (resForm hVi (M.K.om i)) :=
      Λ.map_smulₛₗ _ _
    rw [← evalPt_res z hVP hzP hzV, GlobalTheory.CanonLB.resG_jacobian, ← e2, e, e1]
    congr 1
    ext a b
    exact (congrArg TrivSqZeroExt.snd (evalPt_res (w b) hVP (hwP b) (hwV b) (f a))).symm
  have alg : ∀ (d d' A B C : K), d = A * C → d' = B * C → d * B = d' * A := by
    intro d d' A B C h h'
    rw [h, h']
    ring
  exact alg _ _ _ _ _ (key O hO hVO g hz hwO) (key O' hO' hVO' g' hz' hwO')

end GlobalTheory.TanJac
