import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SignSym

section Move
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Take `⟨w, hw⟩` from `U.ext`. Set `π : A.A ⟶ (Over.pullback (jK R)).obj G` to `U.gen.inv`. Take `⟨a, ha, -⟩` from `H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw) φ (fun k => (π ≫ (Over.pullback (jK R)).map (fG k)).left) ε (π.left ≫ pullback.fst G.hom (jK R)) (fun k => by`. Rewrite using `[hφ k]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.assoc _ _ _).symm)) t ht`.

Take `⟨b, hb⟩` from `PsiPull.exists_gen_flat _ _ _ a ha`. Take `⟨α, hα, -⟩` from `exists_gen A.isLB (φ' := φA) (ε' := ε) (fun V _ h => Finset.prod_congr rfl fun k _ => by`. Establish `e : π ≫ (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = fA k`. Rewrite using `[hf k, ← Category.assoc, U.gen.inv_hom_id, Category.id_comp]`. Rewrite using `[hφA k]`.

Conclude with `congrArg (fun q : A.A ⟶ A.A => h q.left ^ ε k) e) b hb`. Conclude with `⟨α, hα⟩`.
-/
theorem exists_gen_onA (U : UnifPre I D A G) {n : ℕ} (fG : Fin n → (G ⟶ G)) (fA : Fin n → (A.A ⟶ A.A))
    (hf : ∀ k, (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = U.gen.hom ≫ fA k) (ε : Fin n → ℤ)
    (φ : Fin n → (G.left ⟶ G.left)) (hφ : ∀ k, φ k = (fG k).left)
    (φA : Fin n → (A.A.left ⟶ A.A.left)) (hφA : ∀ k, φA k = (fA k).left)
    (t : LB.Gen (LB.LinComb U.LG.L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb A.L φA ε), a.IsGen := by
  obtain ⟨w, hw⟩ := U.ext
  let π : A.A ⟶ (Over.pullback (jK R)).obj G := U.gen.inv
  obtain ⟨a, ha, -⟩ := H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw)
    φ (fun k => (π ≫ (Over.pullback (jK R)).map (fG k)).left) ε (π.left ≫ pullback.fst G.hom (jK R))
    (fun k => by
      rw [hφ k]
      exact (Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)) t ht
  obtain ⟨b, hb⟩ := PsiPull.exists_gen_flat _ _ _ a ha
  obtain ⟨α, hα, -⟩ := exists_gen A.isLB (φ' := φA) (ε' := ε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by
      have e : π ≫ (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = fA k := by
        rw [hf k, ← Category.assoc, U.gen.inv_hom_id, Category.id_comp]
      rw [hφA k]
      exact congrArg (fun q : A.A ⟶ A.A => h q.left ^ ε k) e) b hb
  exact ⟨α, hα⟩

end Move
end GlobalTheory.SignSym

namespace GlobalTheory.SignSym

/- English proof (translation)
Introduce `R _ _ _ I hI D A G _ _ hG U O _ _ _ o oA oG hlin w hw`. Establish `hL` using `GlobalTheory.firstFiveLaws`. Establish `hGF` using `hL.1.globalFns`. Use `U.gen_hom` as an intermediate fact. Use `haveI := oG.hom w`.

Use `haveI := oA.hom w`. Take `⟨-, E, eG, eA, -, -, -⟩` from `IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U`. Establish `rId : (Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom = U.gen.hom ≫ 𝟙 A.A`. Rewrite using `[(Over.pullback (jK R)).map_id, Category.id_comp, Category.comp_id]`. Establish `rW : (Over.pullback (jK R)).map (oG.act w) ≫ U.gen.hom = U.gen.hom ≫ oA.act w` using `hlin.ext w`.

Establish `rInv : (Over.pullback (jK R)).map (ι[G]) ≫ U.gen.hom = U.gen.hom ≫ ι[A.A]`. Establish `h` using `E.ext`. Rewrite `h` using `[eG, eA, Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp]`. Conclude with `h`. Establish `rOne : (Over.pullback (jK R)).map (1 : G ⟶ G) ≫ U.gen.hom = U.gen.hom ≫ (1 : A.A ⟶ A.A)`.

Rewrite using `[(Over.pullback (jK R)).map_one, MonObj.one_comp, MonObj.comp_one]`. Establish `rSum : (Over.pullback (jK R)).map (𝟙 G * oG.act w) ≫ U.gen.hom = U.gen.hom ≫ (𝟙 A.A * oA.act w)`. Rewrite using `[(Over.pullback (jK R)).map_mul, MonObj.mul_comp, MonObj.comp_mul, rId, rW]`. Apply the tactic sequence `obtain ⟨σ₀, hσ₀⟩ := exists_gen_onA U.toUnifPre ![ι[G], 𝟙 G] ![ι[A.A], 𝟙 A.A] (fun k => by fin_cases k; exacts [rInv, rId]) ![1, -1] _ (fun k => by fin_cases k <;> rfl) ![(ι[A.A]).left, 𝟙 A.A.left] (fun k => by fin_cases k <;> rfl) U.symG U.symG_gen`. Take `⟨⟨ρ, hρ, -⟩, -⟩` from `GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hw`.

Apply the tactic sequence `obtain ⟨β, hβ⟩ := exists_gen_onA U.toUnifPre ![𝟙 G, 𝟙 G * oG.act w, 𝟙 G, oG.act w, 1] ![𝟙 A.A, 𝟙 A.A * oA.act w, 𝟙 A.A, oA.act w, 1] (fun k => by fin_cases k; exacts [rId, rSum, rId, rW, rOne]) GlobalTheory.JetSer.primε (GlobalTheory.JetSer.primφ (oG.act w)) (fun k => by fin_case …`. Set `z₀ : A.A ⟶ A.A` to `1`. Establish `o₁ : z₀.left ≫ (ι[A.A]).left = z₀.left`. Rewrite using `[← Over.comp_left, ← Hom.inv_def, inv_one]`. Establish `o₂ : z₀.left ≫ 𝟙 A.A.left = z₀.left` using `Category.comp_id _`.

Take `⟨σ, hσ, vσ⟩` from `exists_gen A.isLB (φ' := ![(ι[A.A]).left, 𝟙 A.A.left]) (ε' := ![1, -1]) (fun V _ h => by`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, o₁, o₂]`. Rewrite using `[neg_neg, ← zpow_add, neg_add_cancel, zpow_zero, _root_.mul_one])`. Use the proof step `(LB.mulGen A.L _ _ _ _ σ₀ (LB.invGen A.L _ _ (LB.pullGen A.L _ _ σ₀ z₀.left)))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ hσ₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hσ₀ _)))`.

Establish `vσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) z J, Good A.L z J → val σ r z J = val σ₀ r z J * (val σ₀ (r ≫ z₀.left) z J)⁻¹` using `fun Z r z J hJ => (vσ Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))`. Establish `e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A) = η[A.A]` using `by simp [Hom.one_def]`. Establish `e₀ : eSec A.A ≫ z₀.left = eSec A.A` using `by show η[A.A].left ≫ (1 : A.A ⟶ A.A).left = η[A.A].left`. Rewrite using `[← Over.comp_left, MonObj.comp_one, e₁]`. Establish `hσ1 : ∀ y J, Good A.L y J → val σ (eSec A.A) y J = 1` using `fun y J hJ => by`.

Rewrite using `[vσ' _ _ y J hJ, e₀, mul_inv_cancel]`. Establish `hσn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L)` using `corr_of_val A.isLB fun y J hJ => by`. Rewrite using `[val_pull hJ, Category.id_comp, val_one]`. Conclude with `hσ1 y J hJ`. Use `⟨σ, hσ, hσn, fun T x hx z J hJ => ?_⟩` and prove the remaining obligations.

Establish `hY : Function.Surjective A.A.hom.appTop.hom` using `(hGF _ _ A.isAb).2`. Establish `hι : ι[A.A] = (𝟙 A.A)⁻¹` using `by rw [Hom.inv_def, Category.id_comp]`. Establish `hinv : ∀ {Y : Over (Spec (CommRingCat.of (FractionRing R)))} (f : Y ⟶ A.A), f ≫ ι[A.A] = f⁻¹` using `fun f => by`. Rewrite using `[Hom.inv_def]`. Establish `c₁ : ι[A.A] ≫ oA.act w = oA.act w ≫ ι[A.A]`.

Use `IntEnd.id_zpow_comm (oA.act w) (-1)` as an intermediate fact. Rewrite `this` using `[zpow_neg_one, ← hι]`. Conclude with `this`. Establish `c₂ : ι[A.A] ≫ (𝟙 A.A * oA.act w) = (𝟙 A.A * oA.act w) ≫ ι[A.A]`. Rewrite using `[MonObj.comp_mul, Category.comp_id, c₁, hinv, hinv, mul_inv, hι]`.

Establish `nv : ∀ y I, Good A.L y I → val σ (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A).left y I = 1` using `fun y I hI => by rw [e₁]; exact hσ1 y I hI`. Establish `H` using `((SymFrame.hasGen_pull hβ (𝟙 A.A)).mul (SymFrame.hasGen_pull hβ (ι[A.A])).inv).unique A.isLB ((((SymFrame.hasGen_pull hσ (𝟙 A.A * oA.act w)).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (oA.act w)).inv) (fun V …`. Establish `xi : x ≫ ι[A.A] = x`. Rewrite using `[hinv]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)`. Establish `xs : x ≫ (𝟙 A.A * oA.act w) = x * (x ≫ oA.act w)` using `by rw [MonObj.comp_mul, Category.comp_id]`.

Rewrite `H` using `[xi, xs, Category.comp_id, mul_inv_cancel]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a` using `congrArg Additive.ofMul H`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a ⊢`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, Fin.prod_univ_five, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, M …`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Normalize the expressions using the abelian group laws. Rewrite using `[Category.comp_id, hinv, inv_one, MonObj.comp_mul, Category.comp_id, MonObj.one_comp, _root_.mul_one, mul_inv_cancel, nv y I hI]`.

Simplify using the standard rewrite rules.
-/
theorem sign_sym : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  intro R _ _ _ I hI D A G _ _ hG U O _ _ _ o oA oG hlin w hw
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := U.gen_hom
  haveI := oG.hom w
  haveI := oA.hom w
  obtain ⟨-, E, eG, eA, -, -, -⟩ := IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U
  have rId : (Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom = U.gen.hom ≫ 𝟙 A.A := by
    rw [(Over.pullback (jK R)).map_id, Category.id_comp, Category.comp_id]
  have rW : (Over.pullback (jK R)).map (oG.act w) ≫ U.gen.hom = U.gen.hom ≫ oA.act w := hlin.ext w
  have rInv : (Over.pullback (jK R)).map (ι[G]) ≫ U.gen.hom = U.gen.hom ≫ ι[A.A] := by
    have h := E.ext
    rw [eG, eA, Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at h
    exact h
  have rOne : (Over.pullback (jK R)).map (1 : G ⟶ G) ≫ U.gen.hom = U.gen.hom ≫ (1 : A.A ⟶ A.A) := by
    rw [(Over.pullback (jK R)).map_one, MonObj.one_comp, MonObj.comp_one]
  have rSum : (Over.pullback (jK R)).map (𝟙 G * oG.act w) ≫ U.gen.hom = U.gen.hom ≫ (𝟙 A.A * oA.act w) := by
    rw [(Over.pullback (jK R)).map_mul, MonObj.mul_comp, MonObj.comp_mul, rId, rW]

  obtain ⟨σ₀, hσ₀⟩ := exists_gen_onA U.toUnifPre ![ι[G], 𝟙 G] ![ι[A.A], 𝟙 A.A]
    (fun k => by fin_cases k; exacts [rInv, rId]) ![1, -1] _ (fun k => by fin_cases k <;> rfl)
    ![(ι[A.A]).left, 𝟙 A.A.left] (fun k => by fin_cases k <;> rfl) U.symG U.symG_gen
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hw
  obtain ⟨β, hβ⟩ := exists_gen_onA U.toUnifPre ![𝟙 G, 𝟙 G * oG.act w, 𝟙 G, oG.act w, 1]
    ![𝟙 A.A, 𝟙 A.A * oA.act w, 𝟙 A.A, oA.act w, 1]
    (fun k => by fin_cases k; exacts [rId, rSum, rId, rW, rOne]) GlobalTheory.JetSer.primε (GlobalTheory.JetSer.primφ (oG.act w)) (fun k => by fin_cases k <;> rfl)
    (GlobalTheory.JetSer.primφ (oA.act w)) (fun k => by fin_cases k <;> rfl) ρ hρ

  let z₀ : A.A ⟶ A.A := 1
  have o₁ : z₀.left ≫ (ι[A.A]).left = z₀.left := by
    rw [← Over.comp_left, ← Hom.inv_def, inv_one]
  have o₂ : z₀.left ≫ 𝟙 A.A.left = z₀.left := Category.comp_id _
  obtain ⟨σ, hσ, vσ⟩ := exists_gen A.isLB (φ' := ![(ι[A.A]).left, 𝟙 A.A.left]) (ε' := ![1, -1])
    (fun V _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂]
      rw [neg_neg, ← zpow_add, neg_add_cancel, zpow_zero, _root_.mul_one])
    (LB.mulGen A.L _ _ _ _ σ₀ (LB.invGen A.L _ _ (LB.pullGen A.L _ _ σ₀ z₀.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hσ₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hσ₀ _)))
  have vσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) z J, Good A.L z J →
      val σ r z J = val σ₀ r z J * (val σ₀ (r ≫ z₀.left) z J)⁻¹ :=
    fun Z r z J hJ => (vσ Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A) = η[A.A] := by simp [Hom.one_def]
  have e₀ : eSec A.A ≫ z₀.left = eSec A.A := by
    show η[A.A].left ≫ (1 : A.A ⟶ A.A).left = η[A.A].left
    rw [← Over.comp_left, MonObj.comp_one, e₁]
  have hσ1 : ∀ y J, Good A.L y J → val σ (eSec A.A) y J = 1 := fun y J hJ => by
    rw [vσ' _ _ y J hJ, e₀, mul_inv_cancel]
  have hσn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) :=
    corr_of_val A.isLB fun y J hJ => by
      rw [val_pull hJ, Category.id_comp, val_one]
      exact hσ1 y J hJ
  refine ⟨σ, hσ, hσn, fun T x hx z J hJ => ?_⟩

  have hY : Function.Surjective A.A.hom.appTop.hom := (hGF _ _ A.isAb).2
  have hι : ι[A.A] = (𝟙 A.A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have hinv : ∀ {Y : Over (Spec (CommRingCat.of (FractionRing R)))} (f : Y ⟶ A.A), f ≫ ι[A.A] = f⁻¹ := fun f => by
    rw [Hom.inv_def]
  have c₁ : ι[A.A] ≫ oA.act w = oA.act w ≫ ι[A.A] := by
    have := IntEnd.id_zpow_comm (oA.act w) (-1)
    rw [zpow_neg_one, ← hι] at this
    exact this
  have c₂ : ι[A.A] ≫ (𝟙 A.A * oA.act w) = (𝟙 A.A * oA.act w) ≫ ι[A.A] := by
    rw [MonObj.comp_mul, Category.comp_id, c₁, hinv, hinv, mul_inv, hι]
  have nv : ∀ y I, Good A.L y I → val σ (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A).left y I = 1 :=
    fun y I hI => by rw [e₁]; exact hσ1 y I hI
  have H := ((SymFrame.hasGen_pull hβ (𝟙 A.A)).mul (SymFrame.hasGen_pull hβ (ι[A.A])).inv).unique A.isLB
    ((((SymFrame.hasGen_pull hσ (𝟙 A.A * oA.act w)).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul
      (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (oA.act w)).inv)
    (fun V _ h => ?_) hY 1 (fun y I hI => ?_) T x z J hJ
  · have xi : x ≫ ι[A.A] = x := by
      rw [hinv]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
    have xs : x ≫ (𝟙 A.A * oA.act w) = x * (x ≫ oA.act w) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [xi, xs, Category.comp_id, mul_inv_cancel] at H
    apply Additive.ofMul.injective
    have a := congrArg Additive.ofMul H
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a ⊢
    calc _ = (Additive.ofMul (val σ (x * x ≫ oA.act w).left z J) + -Additive.ofMul (val σ x.left z J) +
          -Additive.ofMul (val σ x.left z J) + -Additive.ofMul (val σ (x ≫ oA.act w).left z J)) +
          (2 • Additive.ofMul (val σ x.left z J) + Additive.ofMul (val σ (x ≫ oA.act w).left z J)) := by abel
      _ = _ := by rw [← a, zero_add]
  · simp only [GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, Fin.prod_univ_five, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
      Over.id_left, Category.id_comp, Category.comp_id, ← Over.comp_left, c₁, c₂, MonObj.comp_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  · rw [Category.comp_id, hinv, inv_one, MonObj.comp_mul, Category.comp_id, MonObj.one_comp, _root_.mul_one,
      mul_inv_cancel, nv y I hI]
    simp

end GlobalTheory.SignSym
