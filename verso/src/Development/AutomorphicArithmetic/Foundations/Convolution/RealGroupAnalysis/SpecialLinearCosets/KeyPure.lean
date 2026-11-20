import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsClosedEmbeddingSlVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.SgZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilActionUnipotentNull
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilLiftEquivariance
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.NonzeroPlacesInvariant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ThetaIntegralExistsBilinear
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FstDetFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PtL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private noncomputable def trB {F : Type} [Field F] [NumberField F] {v : P F} (x : GLv v)
    (a : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => (x⁻¹).val * m * (dd x).val
      invFun := fun m => x.val * m * ((dd x)⁻¹).val
      left_inv := fun m => by
        show x.val * ((x⁻¹).val * m * (dd x).val) * ((dd x)⁻¹).val = m
        have h1 : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h2 : (dd x).val * ((dd x)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      right_inv := fun m => by
        show (x⁻¹).val * (x.val * m * ((dd x)⁻¹).val) * (dd x).val = m
        have h1 : (x⁻¹).val * x.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h2 : ((dd x)⁻¹).val * (dd x).val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  ⟨fun m => a.1 (e m), a.2.1.comp_continuous e.continuous, a.2.2.comp_homeomorph e⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `UpperTheory.ConvolutionTheory.R2.I.ptMem F v`. Establish `h : ∀ a : SB (M2 v), ∃ φ : Fock (F` using `F) D.δ, φ.1.1 = ten v θ u (Pt a.1) := by`. Introduce `a`. Take `⟨φ, hφ, e⟩` from `hu (P a) (P a).2`. Conclude with `⟨⟨φ, hφ⟩, by rw [e, hP]⟩`.

Use `choose t ht using h`. Use `⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩` and prove the remaining obligations. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (t (a + b)).1.1 = (t a).1.1 + (t b).1.1`. Rewrite using `[ht, ht, ht, ← hP, ← hP, ← hP, map_add]`. Use function extensionality and compare the values at `X`. Simplify using `[ten, mul_add]`. Introduce `c a`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (t (c • a)).1.1 = c • (t a).1.1`. Rewrite using `[ht, ht, ← hP, ← hP, map_smul]`. Use function extensionality and compare the values at `X`.

Simplify using `[ten, mul_left_comm]`.
-/
private theorem exT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (D : Dat F E) (v : P F) (θ : Kv v) (u : V4 F → ℂ) (hu : GoodU v D.δ θ u) :
    ∃ T : SB (M2 v) →ₗ[ℂ] Fock (F := F) D.δ, ∀ a, (T a).1.1 = ten v θ u (Pt a.1) := by
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have h : ∀ a : SB (M2 v), ∃ φ : Fock (F := F) D.δ, φ.1.1 = ten v θ u (Pt a.1) := by
    intro a
    obtain ⟨φ, hφ, e⟩ := hu (P a) (P a).2
    exact ⟨⟨φ, hφ⟩, by rw [e, hP]⟩
  choose t ht using h
  refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
  · intro a b
    apply Subtype.ext
    apply Subtype.ext
    show (t (a + b)).1.1 = (t a).1.1 + (t b).1.1
    rw [ht, ht, ht, ← hP, ← hP, ← hP, map_add]
    funext X
    simp [ten, mul_add]
  · intro c a
    apply Subtype.ext
    apply Subtype.ext
    show (t (c • a)).1.1 = c • (t a).1.1
    rw [ht, ht, ← hP, ← hP, map_smul]
    funext X
    simp [ten, mul_left_comm]

/- English proof (translation)
Take `⟨hnu, hact⟩` from `UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hθ hθ0 s`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `X`. Take `⟨e1, e2⟩` from `hact X`. Establish `hab : ab (1 : (A F)ˣ) = 1` using `by simp [ab]`.

Establish `ha2 : a' = fun m => ψl v (-(s * m.det)) * a m` using `funext ha'`. Rewrite using `[W.L_apply, hφ, hφ', hnu, hab]`. Simplify using `only [ten]`. Rewrite using `[e1, e2, (UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).2 s, ha2]`. Simplify using the standard rewrite rules.
-/
private theorem L_nbar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (hθ0 : θ ≠ 0) (u : V4 F → ℂ) (a a' : M2 v → ℂ) (s : Kv v)
    (ha' : ∀ m, a' m = ψl v (-(s * m.det)) * a m) (φ φ' : S4 F)
    (hφ : φ.1 = ten v θ u (Pt a)) (hφ' : φ'.1 = ten v θ u (Pt a')) :
    W.L (nbar D v θ s) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hθ hθ0 s
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ab (1 : (A F)ˣ) = 1 := by simp [ab]
  have ha2 : a' = fun m => ψl v (-(s * m.det)) * a m := funext ha'
  rw [W.L_apply, hφ, hφ', hnu, hab]
  simp only [ten]
  rw [e1, e2, (UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).2 s, ha2]
  simp

/- English proof (translation)
Take `⟨hnu, hact⟩` from `UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `X`. Take `⟨e1, e2⟩` from `hact X`. Establish `hab : ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) ≠ 0`.

Establish `: 0 < ab (idl v (Matrix.GeneralLinearGroup.det x))` using `(IdeleGroup.ideleModule F _).2`. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[W.L_apply, hφ, hφ', hnu]`. Simplify using `only [ten]`. Rewrite using `[e1, e2, UpperTheory.ConvolutionTheory.R2.I.ptL F v a x (mat v θ X)]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem L_J {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (J : GLv v →* GL (Fin 2) (A E)) (hJ : Splt D v θ J) (u : V4 F → ℂ) (a : M2 v → ℂ) (x : GLv v)
    (φ φ' : S4 F) (hφ : φ.1 = ten v θ u (Pt a))
    (hφ' : φ'.1 = ten v θ u (Pt fun m => a ((x⁻¹).val * m * (dd x).val))) :
    W.L (J x) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab (idl v (Matrix.GeneralLinearGroup.det x)) := (IdeleGroup.ideleModule F _).2
    exact_mod_cast this.ne'
  rw [W.L_apply, hφ, hφ', hnu]
  simp only [ten]
  rw [e1, e2, UpperTheory.ConvolutionTheory.R2.I.ptL F v a x (mat v θ X)]
  push_cast
  field_simp

/- English proof (translation)
Establish `hadd` using `(sgLaws F v).1`. Establish `h0 : sg v 0 = 0`. Use `hadd 0 0` as an intermediate fact. Simplify using `using this`. Establish `e : -(2 * sg v (s / 2)) = sg v (-s)`.

Establish `h1` using `hadd (s / 2) (s / 2)`. Establish `h2` using `hadd s (-s)`. Rewrite `h2` using `[add_neg_cancel, h0]`. Rewrite `h1` using `[add_halves]`. Rewrite using `[two_mul, ← h1]`.

Conclude with `neg_eq_of_add_eq_zero_right h2.symm`. Rewrite using `[e]`. Conclude with `(UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.1 _`.
-/
private theorem psi_nbar {F : Type} [Field F] [NumberField F] (v : P F) (s : Kv v) :
    ψ (-(2 * sg v (s / 2))) = ψl v (-s) := by
  have hadd := (sgLaws F v).1
  have h0 : sg v 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have e : -(2 * sg v (s / 2)) = sg v (-s) := by
    have h1 := hadd (s / 2) (s / 2)
    have h2 := hadd s (-s)
    rw [add_neg_cancel, h0] at h2
    rw [add_halves] at h1
    rw [two_mul, ← h1]
    exact neg_eq_of_add_eq_zero_right h2.symm
  rw [e]
  exact (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.1 _

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π v θ J hJ h' hcomm u hu a ha φ hφ f hf`. Take `⟨hsm, hloc, -⟩` from `UpperTheory.ConvolutionTheory.R2.I.locSm F π v`. Take `⟨T, hT⟩` from `exT D v θ u hu.1`. Take `⟨B, hB⟩` from `UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear F E D W M π h'`. Establish `hfun : ∀ (x : GLv v) (f : π.V), (fun g => f.1.1 (g * lc v x)) = (π.locRep v x f).1.1` using `fun x f => funext fun g => (hloc x f g).symm`.

Establish `hyp1 : ∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) → (B.compl₂ T) (π.locRep v (Matrix.SpecialLinearGroup.toGL g) f) a' = (B.compl₂ T) f a`. Introduce `g f a a' ha'`. Take `⟨j, hj⟩` from `(jEx F v).1`. Establish `h1 : W.Om (j g) (T a).1 = (T a').1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hu.2 j hj g a.1 a.2 (T a).1 (hT a), hT a']`. Use `congr 2`. Conclude with `(funext ha').symm`. Establish `h2` using `UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance F E D W M π f.1 f.2 (T a).1 (T a).2 h' (j g)`. Rewrite `h2` using `[hj g, hfun, h1]`.

Rewrite using `[LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB]`. Conclude with `h2`. Establish `hyp2 : ∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → (B.compl₂ T) f a' = ψl v (-s) * (B.compl₂ T) f a`. Introduce `f s a a' ha'`. Establish `h1` using `L_nbar W v θ hJ.sq hJ.ne u a.1 a'.1 s ha' (T a).1 (T a').1 (hT a) (hT a')`.

Establish `h2` using `((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').1 (nbar D v θ s))`. Establish `h3` using `((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').2 (sg v (s / 2)) (sg v (-(s / (2 * θ)))))`. Establish `hnu` using `(UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hJ.sq hJ.ne s).1`. Establish `hd1 : dM (1 : (A F)ˣ) = 1`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dM]`. Rewrite `h2` using `[hnu, hd1, h1]`. Simplify using `only [mul_one] at h2`. Rewrite using `[LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB, ← h2, (hcomm s).eq]`. Rewrite using `[← psi_nbar]`.

Conclude with `h3`. Establish `key` using `UpperTheory.ConvolutionTheory.R2.I.absM F v π.V (π.locRep v) hsm (B.compl₂ T) hyp1 hyp2 ⟨f, hf⟩ ⟨a, ha⟩ (fun x => trB x ⟨a, ha⟩) (fun x m => rfl)`. Establish `hfin : (fun x => W1 W M f.1 φ (h' * J x)) = fun x => (B.compl₂ T) (π.locRep v (dd x) ⟨f, hf⟩) (trB x ⟨a, ha⟩)`. Use function extensionality and compare the values at `x`. Establish `h1` using `L_J W v θ J hJ u a x φ (T (trB x ⟨a, ha⟩)).1 hφ (hT _)`.

Establish `h2` using `((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1 φ h').1 (J x))`. Establish `h3 : dM (nu F (J x)) = lc v (dd x)`. Rewrite using `[(UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x).1]`. Conclude with `((lcLaws F v).2.2.1 _).symm`. Rewrite `h2` using `[h3, h1]`.

Rewrite using `[h2, LinearMap.compl₂_apply, hB, ← hfun]`. Rewrite using `[hfin]`. Conclude with `key`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.keyPure :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J →
      ∀ h', (∀ s, Commute h' (nbar D v θ s)) → ∀ u, Mod v θ W u → ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
      ∀ f ∈ π.V, (fun x => W1 W M f.1 φ (h' * J x)) ∈ MC (π.locRep v) := by
  intro F E _ _ _ _ _ _ _ D W M π v θ J hJ h' hcomm u hu a ha φ hφ f hf
  obtain ⟨hsm, hloc, -⟩ := UpperTheory.ConvolutionTheory.R2.I.locSm F π v
  obtain ⟨T, hT⟩ := exT D v θ u hu.1
  obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear F E D W M π h'
  have hfun : ∀ (x : GLv v) (f : π.V), (fun g => f.1.1 (g * lc v x)) = (π.locRep v x f).1.1 :=
    fun x f => funext fun g => (hloc x f g).symm
  have hyp1 : ∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) →
      (B.compl₂ T) (π.locRep v (Matrix.SpecialLinearGroup.toGL g) f) a' = (B.compl₂ T) f a := by
    intro g f a a' ha'
    obtain ⟨j, hj⟩ := (jEx F v).1
    have h1 : W.Om (j g) (T a).1 = (T a').1 := by
      apply Subtype.ext
      rw [hu.2 j hj g a.1 a.2 (T a).1 (hT a), hT a']
      congr 2
      exact (funext ha').symm
    have h2 := UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance F E D W M π f.1 f.2 (T a).1 (T a).2 h' (j g)
    rw [hj g, hfun, h1] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB]
    exact h2
  have hyp2 : ∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) →
      (B.compl₂ T) f a' = ψl v (-s) * (B.compl₂ T) f a := by
    intro f s a a' ha'
    have h1 := L_nbar W v θ hJ.sq hJ.ne u a.1 a'.1 s ha' (T a).1 (T a').1 (hT a) (hT a')
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').1 (nbar D v θ s))
    have h3 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').2 (sg v (s / 2)) (sg v (-(s / (2 * θ)))))
    have hnu := (UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hJ.sq hJ.ne s).1
    have hd1 : dM (1 : (A F)ˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM]
    rw [hnu, hd1, h1] at h2
    simp only [mul_one] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB, ← h2, (hcomm s).eq]
    rw [← psi_nbar]
    exact h3
  have key := UpperTheory.ConvolutionTheory.R2.I.absM F v π.V (π.locRep v) hsm (B.compl₂ T) hyp1 hyp2 ⟨f, hf⟩ ⟨a, ha⟩
    (fun x => trB x ⟨a, ha⟩) (fun x m => rfl)
  have hfin : (fun x => W1 W M f.1 φ (h' * J x)) =
      fun x => (B.compl₂ T) (π.locRep v (dd x) ⟨f, hf⟩) (trB x ⟨a, ha⟩) := by
    funext x
    have h1 := L_J W v θ J hJ u a x φ (T (trB x ⟨a, ha⟩)).1 hφ (hT _)
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1 φ h').1 (J x))
    have h3 : dM (nu F (J x)) = lc v (dd x) := by
      rw [(UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x).1]
      exact ((lcLaws F v).2.2.1 _).symm
    rw [h3, h1] at h2
    rw [h2, LinearMap.compl₂_apply, hB, ← hfun]
  rw [hfin]
  exact key
