import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.MulInt

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation GlobalTheory.FamPull

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def rigV {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig T.hom z J

/- English proof (translation)
Use `cPoint_nsmul D T 0 0` as an intermediate fact. Rewrite `this` using `[zero_nsmul, pow_zero]`. Then use the resulting hypothesis.
-/
theorem cPoint_zero' (T : Over (Spec (CommRingCat.of R))) : cP D T 0 = 1 := by
  have := cPoint_nsmul D T 0 0
  rwa [zero_nsmul, pow_zero] at this

/- English proof (translation)
Use `cPoint_add D T (-y) y` as an intermediate fact. Rewrite `this` using `[neg_add_cancel, cPoint_zero']`. Conclude with `eq_inv_of_mul_eq_one_left this.symm`.
-/
theorem cPoint_neg' (T : Over (Spec (CommRingCat.of R))) (y : D.X) : cP D T (-y) = (cP D T y)⁻¹ := by
  have := cPoint_add D T (-y) y
  rw [neg_add_cancel, cPoint_zero'] at this
  exact eq_inv_of_mul_eq_one_left this.symm

section Values

variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
  (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

/- English proof (translation)
The claim follows from `(val_pull hJ _ _ _).trans (congrArg (fun q => val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z J) ((Category.assoc _ _ _).trans (Over.w σ)))`.
-/
theorem val_rigK : val D.rigK (σ.left ≫ jFK (R := R) F) z J = rigV D z J :=
  (val_pull hJ _ _ _).trans (congrArg (fun q => val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1)
    D.rig q z J) ((Category.assoc _ _ _).trans (Over.w σ)))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, add_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ k ih`. Establish `e` using `tau_mul σ hJ hB (a + k • mu) mu b`.

Rewrite `e` using `[cPoint_add, cPoint_nsmul]`. Rewrite using `[succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ, ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]`.
-/
theorem tau_nsmul (hB : D.TauBimult) (a mu b : D.X) (k : ℕ) :
    val (D.tau (a + k • mu) b) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k (cP D T a) (cP D T mu) (cP D T b) =
      val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.tau mu b) (σ.left ≫ jFK (R := R) F) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := tau_mul σ hJ hB (a + k • mu) mu b
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

/- English proof (translation)
Establish `e` using `tau_mul σ hJ hB 0 0 b`. Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Rewrite `e` using `[add_zero, cPoint_zero', C.face]`. Conclude with `(mul_left_cancel e).symm`.
-/
theorem tau_zero (hB : D.TauBimult) (b : D.X) : val (D.tau 0 b) (σ.left ≫ jFK (R := R) F) z J = 1 := by
  have e := tau_mul σ hJ hB 0 0 b
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  rw [add_zero, cPoint_zero', C.face] at e
  exact (mul_left_cancel e).symm

/- English proof (translation)
Establish `e` using `tau_zero σ hJ hB 0`. Rewrite `e` using `[TauPull.val_tau _ hJ, add_zero, val_rigK σ hJ, mul_inv_cancel, _root_.one_mul, ← mul_inv]`. Conclude with `inv_eq_one.1 e`.
-/
theorem psi_zero (hB : D.TauBimult) : val (D.psi 0) (σ.left ≫ jFK (R := R) F) z J * rigV D z J = 1 := by
  have e := tau_zero σ hJ hB 0
  rw [TauPull.val_tau _ hJ, add_zero, val_rigK σ hJ, mul_inv_cancel, _root_.one_mul, ← mul_inv] at e
  exact inv_eq_one.1 e

/- English proof (translation)
Establish `e` using `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans (val_corr hJ (hE χ) (σ.left ≫ jFK (R := R) F))`. Establish `h : (σ.left ≫ jFK (R` using `R) F) ≫ D.xK χ = (cP D T χ).left := by`. Rewrite using `[← comp_cP D σ]`. Conclude with `(Category.assoc _ _ _).trans (congrArg (σ.left ≫ ·) (Category.assoc _ _ _).symm)`. Rewrite using `[← h]`.

Conclude with `e`.
-/
theorem psi_even (hE : D.PsiEven) (χ : D.X) :
    val (D.psi (-χ)) (σ.left ≫ jFK (R := R) F) z J * val D.sym (cP D T χ).left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J := by
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE χ) (σ.left ≫ jFK (R := R) F))
  have h : (σ.left ≫ jFK (R := R) F) ≫ D.xK χ = (cP D T χ).left := by
    rw [← comp_cP D σ]
    exact (Category.assoc _ _ _).trans (congrArg (σ.left ≫ ·) (Category.assoc _ _ _).symm)
  rw [← h]; exact e

omit σ in
/- English proof (translation)
Establish `e` using `val_corr hJ D.sym_rig T.hom`. Rewrite `e` using `[val_pull hJ, val_one]`. Conclude with `e`.
-/
theorem sym_one : val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have e := val_corr hJ D.sym_rig T.hom
  rw [val_pull hJ, val_one] at e
  exact e

end Values

/- English proof (translation)
Set `ρ` to `LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom`. Establish `hρ : ρ.IsGen` using `pullGen_isGen _ _ _ _ D.rig_gen _`. Establish `vρ : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → val ρ x.left z J = rigV D z J` using `fun T x z J hJ => by`. Rewrite using `[val_pull hJ, Over.w]`. Both sides reduce to the same expression.

Establish `e1 : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left` using `rfl`. Proceed by induction on `n with`. Consider the case `zero`. Take `⟨s, hs, vs⟩` from `exists_gen D.P.isLB (K' := Fin 2) (φ' := ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (𝟙 D.P.A ^ 0 : D.P.A ⟶ D.P.A).left]) (ε' := ![((0 ^ 2 : ℕ) : ℤ), -1]) (fun U _ h => by simp [Fin.prod_univ_two, e1]) (LB.invGen D.P.L _ _ ρ) (invGen_isGen _ _ _ _ hρ)`. Use `⟨s, hs, fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩` and prove the remaining obligations.

Rewrite using `[vs _ _ z J hJ, val_inv, vρ _ _ z J hJ]`. Simplify using the standard rewrite rules. Rewrite using `[vs _ _ z J hJ, val_inv, vρ _ _ z J hJ, zero_nsmul, eq_inv_of_mul_eq_one_left (psi_zero σ hJ hB)]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Take `⟨s, hs, s₁, s₂⟩` from `ih`. Take `⟨t, ht, vt⟩` from `exists_cubN D.cub (𝟙 D.P.A) (𝟙 D.P.A) (𝟙 D.P.A)⁻¹ n`. Establish `ei : (ι[D.P.A]).left = ((𝟙 D.P.A)⁻¹ : D.P.A ⟶ D.P.A).left` using `congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (Category.id_comp ι[D.P.A]).symm`. Take `⟨s', hs', vs'⟩` from `exists_gen D.P.isLB (K' := Fin 2) (φ' := ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (𝟙 D.P.A ^ (n + 1) : D.P.A ⟶ D.P.A).left]) (ε' := ![(((n + 1) ^ 2 : ℕ) : ℤ), -1]) (fun U _ h => by`. Establish `a : 𝟙 D.P.A ^ (n + 1) * (𝟙 D.P.A)⁻¹ = 𝟙 D.P.A ^ n` using `by rw [pow_succ, mul_inv_cancel_right]`.

Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two, Fin.prod_univ_eight, e1, ei, a, mul_inv_cancel, ← pow_succ', Matrix.cons_val, Over.id_left]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `push_cast`. Use the proof step `module)`.

Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s t) (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (LB.invGen D.P.L _ _ D.sym) n) (GeneratorPullback.powGen D.P.L _ _ ρ (2 * n + 1))))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hs ht) (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ D.sym_gen) _) (powGen_isGen _ _ _ _ hρ _)))`. Establish `ev : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → val s' x.left z J = val s x.left z J * cubN (th D z J) n x x x⁻¹ * ((val D.sym x.left z J)⁻¹ ^ n * rigV D z J ^ (2 * n + 1))` using `fun T x z J hJ => by`. Rewrite using `[vs' _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pow, val_pow, val_inv, vρ _ _ z J hJ, vt _ _ z J hJ, GrpObj.comp_inv, Category.comp_id]`. Use `⟨s', hs', fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩` and prove the remaining obligations.

Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Rewrite using `[ev _ _ z J hJ, inv_one, C.N_one, sym_one hJ, inv_one, one_pow, _root_.mul_one, _root_.one_mul, mul_right_comm, s₁ T z J hJ, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `f₁` using `tau_nsmul σ hJ hB mu mu (-mu) n`.

Rewrite `f₁` using `[TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, cPoint_neg', add_neg_cancel, val_rigK σ hJ, add_comm mu, add_neg_cancel_right, ← succ_nsmul]`. Establish `f₂` using `congrArg (· ^ n) (psi_even σ hJ hE mu)`. Establish `f₃` using `congrArg (· ^ (n + 1)) (psi_zero σ hJ hB)`. Establish `f₄` using `s₂ T σ mu z J hJ`. Rewrite using `[ev _ _ z J hJ]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `E` using `fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e`. Establish `g₁` using `E f₁`. Establish `g₂` using `E f₂`. Establish `g₃` using `E f₃`.

Establish `g₄` using `E f₄`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at g₁ g₂ g₃ g₄ ⊢`. Take the linear combination `(norm := module) g₁ - g₂ + g₃ + g₄`.
-/
theorem exists_sq (hB : D.TauBimult) (hE : D.PsiEven) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (𝟙 D.P.A ^ n : D.P.A ⟶ D.P.A).left]
      ![((n ^ 2 : ℕ) : ℤ), -1]), s.IsGen ∧
      (∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J), Good D.P.L z J →
        val s (1 : T ⟶ D.P.A).left z J * rigV D z J = rigV D z J ^ (n ^ 2)) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (mu : D.X) (z : T.left) (J), Good D.P.L z J →
        val s (cP D T mu).left z J * val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J ^ (n ^ 2) =
          val (D.psi (n • mu)) (σ.left ≫ jFK (R := R) F) z J := by
  let ρ := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  have vρ : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val ρ x.left z J = rigV D z J := fun T x z J hJ => by
    rw [val_pull hJ, Over.w]; rfl
  have e1 : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := rfl
  induction n with
  | zero =>
    obtain ⟨s, hs, vs⟩ := exists_gen D.P.isLB (K' := Fin 2)
      (φ' := ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (𝟙 D.P.A ^ 0 : D.P.A ⟶ D.P.A).left]) (ε' := ![((0 ^ 2 : ℕ) : ℤ), -1])
      (fun U _ h => by simp [Fin.prod_univ_two, e1]) (LB.invGen D.P.L _ _ ρ) (invGen_isGen _ _ _ _ hρ)
    refine ⟨s, hs, fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩
    · rw [vs _ _ z J hJ, val_inv, vρ _ _ z J hJ]; simp
    · rw [vs _ _ z J hJ, val_inv, vρ _ _ z J hJ, zero_nsmul, eq_inv_of_mul_eq_one_left (psi_zero σ hJ hB)]; simp
  | succ n ih =>
    obtain ⟨s, hs, s₁, s₂⟩ := ih
    obtain ⟨t, ht, vt⟩ := exists_cubN D.cub (𝟙 D.P.A) (𝟙 D.P.A) (𝟙 D.P.A)⁻¹ n
    have ei : (ι[D.P.A]).left = ((𝟙 D.P.A)⁻¹ : D.P.A ⟶ D.P.A).left :=
      congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (Category.id_comp ι[D.P.A]).symm
    obtain ⟨s', hs', vs'⟩ := exists_gen D.P.isLB (K' := Fin 2)
      (φ' := ![(𝟙 D.P.A : D.P.A ⟶ D.P.A).left, (𝟙 D.P.A ^ (n + 1) : D.P.A ⟶ D.P.A).left])
      (ε' := ![(((n + 1) ^ 2 : ℕ) : ℤ), -1])
      (fun U _ h => by
        have a : 𝟙 D.P.A ^ (n + 1) * (𝟙 D.P.A)⁻¹ = 𝟙 D.P.A ^ n := by rw [pow_succ, mul_inv_cancel_right]
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
          Fin.prod_univ_eight, e1, ei, a, mul_inv_cancel, ← pow_succ', Matrix.cons_val, Over.id_left]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        push_cast
        module)
      (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s t) (LB.mulGen D.P.L _ _ _ _
        (GeneratorPullback.powGen D.P.L _ _ (LB.invGen D.P.L _ _ D.sym) n) (GeneratorPullback.powGen D.P.L _ _ ρ (2 * n + 1))))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hs ht) (mulGen_isGen _ _ _ _ _ _ _
        (powGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ D.sym_gen) _) (powGen_isGen _ _ _ _ hρ _)))
    have ev : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val s' x.left z J = val s x.left z J * cubN (th D z J) n x x x⁻¹ *
          ((val D.sym x.left z J)⁻¹ ^ n * rigV D z J ^ (2 * n + 1)) := fun T x z J hJ => by
      rw [vs' _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pow, val_pow, val_inv, vρ _ _ z J hJ, vt _ _ z J hJ,
        GrpObj.comp_inv, Category.comp_id]
    refine ⟨s', hs', fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩
    · have C : IsCub (th D z J) := isCub_cubV D.cub hJ
      rw [ev _ _ z J hJ, inv_one, C.N_one, sym_one hJ, inv_one, one_pow, _root_.mul_one, _root_.one_mul, mul_right_comm,
        s₁ T z J hJ, ← pow_add]
      congr 1; ring
    · have f₁ := tau_nsmul σ hJ hB mu mu (-mu) n
      rw [TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, cPoint_neg', add_neg_cancel, val_rigK σ hJ, add_comm mu,
        add_neg_cancel_right, ← succ_nsmul] at f₁
      have f₂ := congrArg (· ^ n) (psi_even σ hJ hE mu)
      have f₃ := congrArg (· ^ (n + 1)) (psi_zero σ hJ hB)
      have f₄ := s₂ T σ mu z J hJ
      rw [ev _ _ z J hJ]
      apply Additive.ofMul.injective
      have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
      have g₁ := E f₁; have g₂ := E f₂; have g₃ := E f₃; have g₄ := E f₄
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at g₁ g₂ g₃ g₄ ⊢
      linear_combination (norm := module) g₁ - g₂ + g₃ + g₄

/- English proof (translation)
Establish `e : x.left ≫ (mulA D.P.A m).left = (x ^ m).left`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Establish `p` using `FamPull.prod_famB D (x ^ m) χ k h`. Rewrite `p` using `[← e]`. Simplify using `only [Category.assoc] at p`.

Rewrite `p` using `[e]`. Conclude with `prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (FamPull.prod_famB D x (m • χ) k' h) (prod_neg _ _ p)`.
-/
theorem prod_mulB {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (m : ℕ) (χ : D.X) (k k' : ℕ) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (x.left ≫ mulφB D m χ i) ^ mulεB k k' i =
      h x.left ^ ((k' : ℤ) - 1) * h (cP D T (m • χ) * x).left * (h (cP D T (m • χ)).left)⁻¹ * h (1 : T ⟶ D.P.A).left *
        (h (x ^ m).left ^ ((k : ℤ) - 1) * h (cP D T χ * x ^ m).left * (h (cP D T χ).left)⁻¹ *
          h (1 : T ⟶ D.P.A).left)⁻¹ := by
  have e : x.left ≫ (mulA D.P.A m).left = (x ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have p := FamPull.prod_famB D (x ^ m) χ k h
  rw [← e] at p
  simp only [Category.assoc] at p
  rw [e] at p
  exact prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (FamPull.prod_famB D x (m • χ) k' h) (prod_neg _ _ p)

/- English proof (translation)
Take `⟨s, hs, s₁, s₂⟩` from `exists_sq D hB hE F m`. Take `⟨t, ht, vt⟩` from `exists_cubN D.cub 1 (cP D D.P.A χ) (𝟙 D.P.A) m`. Take `⟨t', ht', vt'⟩` from `exists_cubN D.cub 1 (𝟙 D.P.A) (cP D D.P.A χ) m`. Take `⟨u, hu, vu⟩` from `exists_gen D.P.isLB (φ' := mulφB D m χ) (ε' := mulεB 1 (m ^ 2)) (fun U _ h => by`. Establish `p` using `prod_mulB D (𝟙 D.P.A) m χ 1 (m ^ 2) h`.

Simplify using `only [Over.id_left, Category.id_comp] at p`. Rewrite using `[p, cPoint_nsmul]`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_eight, Matrix.cons_val, Over.id_left, _root_.one_mul, Matrix.cons_val_zero, Matrix.cons_val_one]`. Rewrite using `[mul_comm (𝟙 D.P.A ^ m) (cP D D.P.A χ), mul_comm (𝟙 D.P.A) (cP D D.P.A χ)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `push_cast`. Use the proof step `module)`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s t) (LB.invGen D.P.L _ _ t'))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hs ht) (invGen_isGen _ _ _ _ ht'))`.

Establish `ev : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → val u x.left z J = val s x.left z J * cubN (th D z J) m 1 (cP D T χ) x * (cubN (th D z J) m 1 x (cP D T χ))⁻¹` using `fun T x z J hJ => by`. Rewrite using `[vu _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, vt _ _ z J hJ, vt' _ _ z J hJ, MonObj.comp_one, comp_cP, Category.comp_id]`. Use `⟨u, hu, fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩` and prove the remaining obligations. Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Establish `c : cubN (th D z J) m 1 1 (cP D T χ) = 1` using `Finset.prod_eq_one fun _ _ => C.face₂ _ _`.

Rewrite using `[ev _ _ z J hJ, C.N_one, c, inv_one, _root_.mul_one, _root_.mul_one, s₁ T z J hJ]`. Establish `f₁` using `tau_nsmul σ hJ hB 0 χ mu m`. Establish `f₂` using `tau_nsmul σ hJ hB 0 mu χ m`. Rewrite `f₁`, `f₂` using `[zero_add, cPoint_zero', tau_zero σ hJ hB]`. Rewrite `f₁` using `[tau_symm σ hJ, tau_symm σ hJ χ]`.

Establish `f₄` using `s₂ T σ mu z J hJ`. Rewrite using `[ev _ _ z J hJ]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `E` using `fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e`. Establish `g₁` using `E f₁`.

Establish `g₂` using `E f₂`. Establish `g₄` using `E f₄`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at g₁ g₂ g₄ ⊢`. Take the linear combination `(norm := module) g₁ - g₂ + g₄`.
-/
theorem exists_mulGen (hB : D.TauBimult) (hE : D.PsiEven) (F : Type) [Field F] [Algebra (FractionRing R) F] (m : ℕ)
    (χ : D.X) : ∃ u : LB.Gen (LB.LinComb D.P.L (mulφB D m χ) (mulεB 1 (m ^ 2))), u.IsGen ∧
      (∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J), Good D.P.L z J →
        val u (1 : T ⟶ D.P.A).left z J * rigV D z J = rigV D z J ^ (m ^ 2)) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (mu : D.X) (z : T.left) (J), Good D.P.L z J →
        val u (cP D T mu).left z J * val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J ^ (m ^ 2) *
            val (D.tau mu (m • χ)) (σ.left ≫ jFK (R := R) F) z J =
          val (D.psi (m • mu)) (σ.left ≫ jFK (R := R) F) z J * val (D.tau (m • mu) χ) (σ.left ≫ jFK (R := R) F) z J := by
  obtain ⟨s, hs, s₁, s₂⟩ := exists_sq D hB hE F m
  obtain ⟨t, ht, vt⟩ := exists_cubN D.cub 1 (cP D D.P.A χ) (𝟙 D.P.A) m
  obtain ⟨t', ht', vt'⟩ := exists_cubN D.cub 1 (𝟙 D.P.A) (cP D D.P.A χ) m
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := mulφB D m χ) (ε' := mulεB 1 (m ^ 2)) (fun U _ h => by
      have p := prod_mulB D (𝟙 D.P.A) m χ 1 (m ^ 2) h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p, cPoint_nsmul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_eight,
        Matrix.cons_val, Over.id_left, _root_.one_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_comm (𝟙 D.P.A ^ m) (cP D D.P.A χ), mul_comm (𝟙 D.P.A) (cP D D.P.A χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s t) (LB.invGen D.P.L _ _ t'))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hs ht) (invGen_isGen _ _ _ _ ht'))
  have ev : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val u x.left z J = val s x.left z J * cubN (th D z J) m 1 (cP D T χ) x * (cubN (th D z J) m 1 x (cP D T χ))⁻¹ :=
    fun T x z J hJ => by
      rw [vu _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, vt _ _ z J hJ, vt' _ _ z J hJ, MonObj.comp_one, comp_cP,
        Category.comp_id]
  refine ⟨u, hu, fun T z J hJ => ?_, fun T σ mu z J hJ => ?_⟩
  · have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have c : cubN (th D z J) m 1 1 (cP D T χ) = 1 := Finset.prod_eq_one fun _ _ => C.face₂ _ _
    rw [ev _ _ z J hJ, C.N_one, c, inv_one, _root_.mul_one, _root_.mul_one, s₁ T z J hJ]
  · have f₁ := tau_nsmul σ hJ hB 0 χ mu m
    have f₂ := tau_nsmul σ hJ hB 0 mu χ m
    rw [zero_add, cPoint_zero', tau_zero σ hJ hB] at f₁ f₂
    rw [tau_symm σ hJ, tau_symm σ hJ χ] at f₁
    have f₄ := s₂ T σ mu z J hJ
    rw [ev _ _ z J hJ]
    apply Additive.ofMul.injective
    have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
    have g₁ := E f₁; have g₂ := E f₂; have g₄ := E f₄
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at g₁ g₂ g₄ ⊢
    linear_combination (norm := module) g₁ - g₂ + g₄

/- English proof (translation)
Establish `p` using `prod_fam D F (ρ ≫ DegPre.trF D F mu) α k h`. Establish `e : (ρ ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * cP D T mu` using `Over.OverMorphism.ext (comp_trF mu ρ)`. Rewrite `p` using `[e, Over.comp_left]`. Simplify using `only [Category.assoc] at p`. Conclude with `prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_fam D F ρ (α + k • mu) k h) (prod_neg _ _ p)`.
-/
theorem prod_delta {F : Type} [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (ρ : T ⟶ DegPre.BF D F) (k : ℕ) (α mu : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ DegPre.deltaφ D F k α mu i) ^ DegPre.deltaε k i =
      h (ρ ≫ DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (cP D T (α + k • mu) * (ρ ≫ DegPre.prB D F)).left *
        (h (cP D T (α + k • mu)).left)⁻¹ * h (1 : T ⟶ D.P.A).left *
      (h ((ρ ≫ DegPre.prB D F) * cP D T mu).left ^ ((k : ℤ) - 1) *
        h (cP D T α * ((ρ ≫ DegPre.prB D F) * cP D T mu)).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left)⁻¹ := by
  have p := prod_fam D F (ρ ≫ DegPre.trF D F mu) α k h
  have e : (ρ ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * cP D T mu :=
    Over.OverMorphism.ext (comp_trF mu ρ)
  rw [e, Over.comp_left] at p
  simp only [Category.assoc] at p
  exact prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_fam D F ρ (α + k • mu) k h) (prod_neg _ _ p)

/- English proof (translation)
Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Rewrite using `[feUnit, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul]`.
-/
theorem feUnit_one (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J)
    (ψ : D.X → (T.left.presheaf.stalk z)ˣ) (ρ : (T.left.presheaf.stalk z)ˣ) :
    feUnit D k mu α 1 z J ψ ρ = ψ (mu + α) * (ψ mu)⁻¹ * (ψ α)⁻¹ * ρ⁻¹ * (ψ mu ^ k * ρ ^ k) := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  rw [feUnit, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul]

/- English proof (translation)
Set `a : DegPre.BF D F ⟶ DegPre.BF D F` to `lift (fst _ _) (DegPre.prB D F ^ m)`. Establish `a₁ : a ≫ fst _ _ = fst _ _` using `lift_fst _ _`. Establish `a₂ : a ≫ DegPre.prB D F = DegPre.prB D F ^ m` using `lift_snd _ _`. Take `⟨⟨w₁, hw₁, c₁⟩, vw₁⟩` from `gen_fe (D := D) (F := F) hG 1 (m • mu) χ`. Take `⟨⟨w₂, hw₂, c₂⟩, vw₂⟩` from `gen_fe (D := D) (F := F) hG (m ^ 2) mu (m • χ)`.

Establish `ev : ∀ {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J}, Good D.P.L z J → val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ w₁ a.left) (LB.pullGen D.P.L _ _ u₁ (DegPre.prB D F).left)) ρ.left z J = feUnit D 1 (m • mu) χ ((ρ ≫ DegPre.prB D F) ^ m) z J …` using `R) F) z J) (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) * val u₁ (ρ ≫ DegPre.prB D F).left z J ∧ val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u₂ (DegPre.prB D F * cP D _ mu).left) w₂) ρ.left z J = val u₂ ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J * feUnit D (m ^ …`. Prove the components needed by the constructor for the conclusion. Rewrite using `[val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, vw₁ w₁ hw₁ c₁ _ _ z J hJ, val_feUnit _ _ _ _ hJ, Category.assoc, Category.assoc, a₁, a₂, MonObj.comp_pow]`. Rewrite using `[val_mul hJ, val_pull hJ, ← Over.comp_left, vw₂ w₂ hw₂ c₂ _ _ z J hJ, val_feUnit _ _ _ _ hJ, MonObj.comp_mul, comp_cP]`. Establish `z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _` using `lift_fst _ _`.

Establish `z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1` using `lift_snd _ _`. Use `(ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun U _ h => ?_) (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left (congrArg (fun q => q.left) z₁) (surj_appTop D F hG) (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw₁ _) (pullGen_isGen _ _ _ _ hu₁ _)) (mulGen_isG …` and prove the remaining obligations. Establish `p₁` using `prod_delta D a 1 χ (m • mu) h`. Establish `p₂` using `prod_mulB D (DegPre.prB D F) m (χ + 1 • m • mu) 1 (m ^ 2) h`. Establish `p₃` using `prod_mulB D (DegPre.prB D F * cP D _ mu) m χ 1 (m ^ 2) h`.

Establish `p₄` using `prod_delta D (𝟙 (DegPre.BF D F)) (m ^ 2) (m • χ) mu h`. Simplify using `only [Over.id_left, Category.id_comp] at p₄`. Establish `s : m • (χ + 1 • m • mu) = m • χ + m ^ 2 • mu` using `by rw [one_nsmul, nsmul_add, smul_smul, sq]`. Use `(prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _ p₃ p₄).trans (Eq.trans ?_ (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _ p₁ p₂).symm)` and prove the remaining obligations. Rewrite using `[s, a₂, mul_pow, ← cPoint_nsmul]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `module`. Rewrite using `[(ev (DegPre.zF D F) hI).1, (ev (DegPre.zF D F) hI).2, z₂, one_pow, _root_.one_mul, feUnit_one D _ _ _ hI, feUnit_one D _ _ _ hI, val_rigK _ hI]`. Establish `f₁` using `v₁ _ y I hI`.

Establish `f₂` using `v₂ _ (DegPre.zF D F ≫ fst _ _) y I hI`. Rewrite `f₂` using `[TauPull.val_tau _ hI, TauPull.val_tau _ hI, val_rigK _ hI]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `g₁` using `congrArg Additive.ofMul f₁`. Establish `g₂` using `congrArg Additive.ofMul f₂`.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow] at g₁ g₂ ⊢`. Take the linear combination `(norm := module) g₁ - g₂`.
-/
theorem fe_compat (hG : GlobalFnsSt) {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ) (χ mu : D.X)
    (u₁ : LB.Gen (LB.LinComb D.P.L (mulφB D m (χ + 1 • m • mu)) (mulεB 1 (m ^ 2)))) (hu₁ : u₁.IsGen)
    (u₂ : LB.Gen (LB.LinComb D.P.L (mulφB D m χ) (mulεB 1 (m ^ 2)))) (hu₂ : u₂.IsGen)
    (v₁ : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J), Good D.P.L z J →
        val u₁ (1 : T ⟶ D.P.A).left z J * rigV D z J = rigV D z J ^ (m ^ 2))
    (v₂ : ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
        val u₂ (cP D T mu).left z J * val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J ^ (m ^ 2) *
            val (D.tau mu (m • χ)) (σ.left ≫ jFK (R := R) F) z J =
          val (D.psi (m • mu)) (σ.left ≫ jFK (R := R) F) z J * val (D.tau (m • mu) χ) (σ.left ≫ jFK (R := R) F) z J)
    {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J} (hJ : Good D.P.L z J) :
    feUnit D 1 (m • mu) χ ((ρ ≫ DegPre.prB D F) ^ m) z J
        (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
        (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) * val u₁ (ρ ≫ DegPre.prB D F).left z J =
      val u₂ ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J * feUnit D (m ^ 2) mu (m • χ) (ρ ≫ DegPre.prB D F) z J
        (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
        (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) := by
  let a : DegPre.BF D F ⟶ DegPre.BF D F := lift (fst _ _) (DegPre.prB D F ^ m)
  have a₁ : a ≫ fst _ _ = fst _ _ := lift_fst _ _
  have a₂ : a ≫ DegPre.prB D F = DegPre.prB D F ^ m := lift_snd _ _
  obtain ⟨⟨w₁, hw₁, c₁⟩, vw₁⟩ := gen_fe (D := D) (F := F) hG 1 (m • mu) χ
  obtain ⟨⟨w₂, hw₂, c₂⟩, vw₂⟩ := gen_fe (D := D) (F := F) hG (m ^ 2) mu (m • χ)
  have ev : ∀ {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ w₁ a.left) (LB.pullGen D.P.L _ _ u₁ (DegPre.prB D F).left))
        ρ.left z J = feUnit D 1 (m • mu) χ ((ρ ≫ DegPre.prB D F) ^ m) z J
          (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
          (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) * val u₁ (ρ ≫ DegPre.prB D F).left z J ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u₂ (DegPre.prB D F * cP D _ mu).left) w₂) ρ.left z J =
        val u₂ ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J * feUnit D (m ^ 2) mu (m • χ) (ρ ≫ DegPre.prB D F) z J
          (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
          (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) := fun ρ z J hJ => by
    constructor
    · rw [val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, vw₁ w₁ hw₁ c₁ _ _ z J hJ,
        val_feUnit _ _ _ _ hJ, Category.assoc, Category.assoc, a₁, a₂, MonObj.comp_pow]
    · rw [val_mul hJ, val_pull hJ, ← Over.comp_left, vw₂ w₂ hw₂ c₂ _ _ z J hJ, val_feUnit _ _ _ _ hJ, MonObj.comp_mul,
        comp_cP]
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun U _ h => ?_) (fst (TF (R := R) F) D.P.A).left
    (DegPre.zF D F).left (congrArg (fun q => q.left) z₁) (surj_appTop D F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hw₁ _) (pullGen_isGen _ _ _ _ hu₁ _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₂ _) hw₂) (fun y I hI => ?_) _ _ z J hJ) (ev ρ hJ).2)
  · have p₁ := prod_delta D a 1 χ (m • mu) h
    have p₂ := prod_mulB D (DegPre.prB D F) m (χ + 1 • m • mu) 1 (m ^ 2) h
    have p₃ := prod_mulB D (DegPre.prB D F * cP D _ mu) m χ 1 (m ^ 2) h
    have p₄ := prod_delta D (𝟙 (DegPre.BF D F)) (m ^ 2) (m • χ) mu h
    simp only [Over.id_left, Category.id_comp] at p₄
    have s : m • (χ + 1 • m • mu) = m • χ + m ^ 2 • mu := by rw [one_nsmul, nsmul_add, smul_smul, sq]
    refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _ p₃ p₄).trans (Eq.trans ?_
      (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _ p₁ p₂).symm)
    rw [s, a₂, mul_pow, ← cPoint_nsmul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rw [(ev (DegPre.zF D F) hI).1, (ev (DegPre.zF D F) hI).2, z₂, one_pow, _root_.one_mul, feUnit_one D _ _ _ hI,
      feUnit_one D _ _ _ hI, val_rigK _ hI]
    have f₁ := v₁ _ y I hI
    have f₂ := v₂ _ (DegPre.zF D F ≫ fst _ _) y I hI
    rw [TauPull.val_tau _ hI, TauPull.val_tau _ hI, val_rigK _ hI] at f₂
    apply Additive.ofMul.injective
    have g₁ := congrArg Additive.ofMul f₁
    have g₂ := congrArg Additive.ofMul f₂
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at g₁ g₂ ⊢
    linear_combination (norm := module) g₁ - g₂

/- English proof (translation)
Take `⟨h, hh⟩ : ∃ h : pullback D.P.A.hom (thick R I e) ⟶ pullback D.P.A.hom (thick R I e), h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D.P.A.hom (thick R I e) ≫ g.left` from `⟨pullback.lift _ (pullback.snd D.P.A.hom (thick R I e)) (by`. Rewrite using `[Category.assoc, Over.w, pullback.condition]), pullback.lift_fst _ _ _⟩`. Introduce `q`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Use `choose J hJ₀ using fun ψ : pullback D.P.A.hom (thick R I e) ⟶ D.P.A.left => exists_chart D.P.isLB (ψ y)`.

Establish `hJ : Good D.P.L y J` using `hJ₀`. Take `⟨c, hc⟩` from `H _ (pullback.fst D.P.A.hom (thick R I e)) y J hJ`. Establish `z₁ : sval b (pullback.fst D.P.A.hom (thick R I e) ≫ g.left) y J = 0`. Rewrite using `[← hh]`. Establish `hm` using `hJ.mem (D.famφB χ) (h ≫ pullback.fst D.P.A.hom (thick R I e))`.

Conclude with `(gs_pull h _ y _ hm _).symm.trans ((congrArg (gs h y _) (hb _)).trans (gs_zero h y _ hm))`. Rewrite `hc` using `[z₁, zero_mul]`. Establish `t` using `sec_trans b' (pullback.fst D.P.A.hom (thick R I e)) y hy (hJ.mem (D.famφB β) _)`. Establish `e₂` using `t.trans ((congrArg (_ * ·) hc).trans (mul_zero _))`. Conclude with `((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans (gs_zero _ y _ hy).symm`.
-/
theorem vanMod_of_sval {I : Ideal R} {k k' : ℕ} {χ β : D.X} {b : D.SecB k χ} {b' : D.SecB k' β} (g : D.P.A ⟶ D.P.A)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      ∃ c, sval b' r z J = sval b (r ≫ g.left) z J * c) {e : ℕ} (hb : VanMod I b e) : VanMod I b' e := by
  obtain ⟨h, hh⟩ : ∃ h : pullback D.P.A.hom (thick R I e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D.P.A.hom (thick R I e) ≫ g.left :=
    ⟨pullback.lift _ (pullback.snd D.P.A.hom (thick R I e)) (by
      rw [Category.assoc, Over.w, pullback.condition]), pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose J hJ₀ using fun ψ : pullback D.P.A.hom (thick R I e) ⟶ D.P.A.left => exists_chart D.P.isLB (ψ y)
  have hJ : Good D.P.L y J := hJ₀
  obtain ⟨c, hc⟩ := H _ (pullback.fst D.P.A.hom (thick R I e)) y J hJ
  have z₁ : sval b (pullback.fst D.P.A.hom (thick R I e) ≫ g.left) y J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.famφB χ) (h ≫ pullback.fst D.P.A.hom (thick R I e))
    exact (gs_pull h _ y _ hm _).symm.trans ((congrArg (gs h y _) (hb _)).trans (gs_zero h y _ hm))
  rw [z₁, zero_mul] at hc
  have t := sec_trans b' (pullback.fst D.P.A.hom (thick R I e)) y hy (hJ.mem (D.famφB β) _)
  have e₂ := t.trans ((congrArg (_ * ·) hc).trans (mul_zero _))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (gs_zero _ y _ hy).symm

/- English proof (translation)
The claim follows from `(congrArg (gs r z _) (hb _)).trans (gs_zero r z _ (hJ.mem _ _))`.
-/
theorem sval_zero {k : ℕ} {β : D.X} {b : D.SecB k β} (hb : ∀ j, b.f j = 0) {Z : Scheme.{0}} (r : Z ⟶ D.P.A.left)
    {z : Z} {J} (hJ : Good D.P.L z J) : sval b r z J = 0 :=
  (congrArg (gs r z _) (hb _)).trans (gs_zero r z _ (hJ.mem _ _))

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_sec D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) (fun U _ h => by`. Establish `p` using `prod_fam D F (𝟙 _) α k h`. Simplify using `only [Over.id_left, Category.id_comp] at p`. Conclude with `(FamPull.prod_famB D _ α k h).trans p.symm)`. Use the proof step `(pullSec D.P.L _ _ f (DegPre.prB D F).left)`.

Conclude with `⟨s, secScal_of_sval D.P.isLB fun y J hJ => ((hs _ _ y J hJ).trans (sval_pullSec _ _ _ _ _ y hJ)).symm⟩`.
-/
theorem exists_secScal (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} {α : D.X} (f : D.SecB k α) :
    ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s (D.famφB α) (DegPre.famε k) f (DegPre.prB D F).left 1 := by
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k)
    (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      exact (FamPull.prod_famB D _ α k h).trans p.symm)
    (pullSec D.P.L _ _ f (DegPre.prB D F).left)
  exact ⟨s, secScal_of_sval D.P.isLB fun y J hJ => ((hs _ _ y J hJ).trans (sval_pullSec _ _ _ _ _ y hJ)).symm⟩

/- English proof (translation)
Use `choose u hu u₁ u₂ using exists_mulGen D hB hE (FractionRing R) m`. Establish `inj : ∀ χ χ' : D.X, m • χ = m • χ' → χ = χ'` using `fun χ χ' h => smul_right_injective D.X (Int.natCast_ne_zero.2 hm) (by simpa only [natCast_zsmul] using h)`. Establish `ex : ∀ β : D.X, ∃ g : D.SecB (m ^ 2) β, (∀ χ, m • χ = β → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval g r z J = sval (F₁.f χ) (r ≫ (mulA D.P.A m).left) z J * (val (u χ) r z J).val) ∧ ((∀ χ, β ≠ m • χ) → ∀ j, g.f j = 0)` using `fun β => by`. Distinguish the cases in `hβ : ∃ χ, m • χ = β`. Take `⟨χ, rfl⟩` from `hβ`.

Take `⟨g, hg⟩` from `exists_sec D.P.isLB (φ' := D.famφB (m • χ)) (ε' := DegPre.famε (m ^ 2)) (fun U _ h => by`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mulφB, mulεB, zpow_neg, Finset.prod_inv_distrib]`. Rewrite using `[mul_comm, inv_mul_cancel_right]) (pullMulSec (F₁.f χ) (mulA D.P.A m).left (u χ) (hu χ))`. Use `⟨g, fun χ' h Z r z J hJ => ?_, fun h => (h χ rfl).elim⟩` and prove the remaining obligations. Take `rfl` from `inj _ _ h`.

Rewrite using `[hg Z r z J hJ, sval_pullMulSec _ _ _ _ _ z hJ]`. Conclude with `⟨SecOps.secZero, fun χ h => (hβ ⟨χ, h⟩).elim, fun _ _ => rfl⟩`. Use `choose g hg hg₀ using ex`. Use `choose s hs using fun β => exists_secScal D (FractionRing R) (g β)`. Establish `s₁ : scal (DegPre.BF D (FractionRing R)).hom 1 = 1` using `by rw [scal, map_one, map_one]`.

Establish `sm : ∀ χ mu : D.X, m • (χ + 1 • m • mu) = m • χ + m ^ 2 • mu` using `fun χ mu => by`. Rewrite using `[one_nsmul, nsmul_add, smul_smul, sq]`. Establish `em : ∀ {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A), x.left ≫ (mulA D.P.A m).left = (x ^ m).left` using `fun x => by rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Establish `fe : DegPre.FamFE D (FractionRing R) (m ^ 2) s`. Use `(famFE_iff hG s g hs).2 fun mu α T ρ z J hJ => ?_` and prove the remaining obligations.

Distinguish the cases in `hα : ∃ χ, α = m • χ`. Take `⟨χ, rfl⟩` from `hα`. Establish `e` using `(famFE_iff hG F₁.F.s F₁.f (fun α => s₁ ▸ F₁.ext α)).1 F₁.F.fe (m • mu) χ T (lift (ρ ≫ fst _ _) ((ρ ≫ DegPre.prB D (FractionRing R)) ^ m)) z J hJ`. Rewrite `e` using `[lift_fst, lift_snd]`. Establish `c` using `fe_compat D hG m χ mu (u _) (hu _) (u χ) (hu χ) (u₁ _) (fun T σ => u₂ χ T σ mu) ρ hJ`.

Rewrite using `[hg _ _ (sm χ mu) _ _ z J hJ, hg _ χ rfl _ _ z J hJ, em, em, e, mul_pow, ← cPoint_nsmul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, c]`. Establish `z₁` using `hg₀ α fun χ h => hα ⟨χ, h⟩`. Establish `z₂` using `hg₀ (α + m ^ 2 • mu) fun χ h => hα ⟨χ - 1 • m • mu, by`. Use `sm (χ - 1 • m • mu) mu` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, ← h]`.

Conclude with `add_right_cancel this⟩`. Rewrite using `[sval_zero D z₁ _ hJ, sval_zero D z₂ _ hJ, zero_mul]`. Use `⟨{ F := ⟨s, fe⟩, f := g, ext := fun α => s₁.symm ▸ hs α, small := fun e => ?_ }, fun χ => ?_, hg₀⟩` and prove the remaining obligations. Use `((F₁.small e).image (m • ·)).subset fun β hβ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ χ, β = m • χ`.

Take `⟨χ, rfl⟩` from `h`. Conclude with `⟨χ, fun hv => hβ (vanMod_of_sval D (mulA D.P.A m) (fun Z r z J hJ => ⟨_, hg _ χ rfl Z r z J hJ⟩) hv), rfl⟩`. Use `(hβ fun j => ?_).elim` and prove the remaining obligations. Rewrite using `[hg₀ β (fun χ e => h ⟨χ, e⟩) j]`. Conclude with `map_zero _`.

Use `⟨u χ, hu χ, corr_of_val D.P.isLB fun y J hJ => ?_, (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => hg _ χ rfl _ _ y J hJ⟩` and prove the remaining obligations. Establish `e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A` using `Category.id_comp _`. Establish `e₂` using `u₁ χ (𝟙_ _) y J hJ`. Take `⟨n, hn⟩ : ∃ n, m ^ 2 = n + 1` from `Nat.exists_eq_succ_of_ne_zero (pow_ne_zero 2 hm)`. Establish `e₃ : rigV D (T` using `𝟙_ _) y J ^ (m ^ 2) = rigV D (T := 𝟙_ _) y J ^ (m ^ 2 - 1) * rigV D (T := 𝟙_ _) y J := by`.

Rewrite using `[hn, pow_succ]`. Both sides reduce to the same expression. Rewrite `e₂` using `[e₁, e₃]`. Rewrite using `[val_pull hJ, Category.id_comp]`. Conclude with `(mul_right_cancel e₂).trans (val_pow _ _ _ _ _).symm`.
-/
theorem exists_mulFam (hG : GlobalFnsSt) (hB : D.TauBimult) (hE : D.PsiEven) {I : Ideal R} {m : ℕ} (hm : m ≠ 0)
    (F₁ : IntFam I D 1) : ∃ G : IntFam I D (m ^ 2), MulFam m F₁ G := by
  choose u hu u₁ u₂ using exists_mulGen D hB hE (FractionRing R) m
  have inj : ∀ χ χ' : D.X, m • χ = m • χ' → χ = χ' := fun χ χ' h =>
    smul_right_injective D.X (Int.natCast_ne_zero.2 hm) (by simpa only [natCast_zsmul] using h)
  have ex : ∀ β : D.X, ∃ g : D.SecB (m ^ 2) β, (∀ χ, m • χ = β → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval g r z J = sval (F₁.f χ) (r ≫ (mulA D.P.A m).left) z J * (val (u χ) r z J).val) ∧
      ((∀ χ, β ≠ m • χ) → ∀ j, g.f j = 0) := fun β => by
    by_cases hβ : ∃ χ, m • χ = β
    · obtain ⟨χ, rfl⟩ := hβ
      obtain ⟨g, hg⟩ := exists_sec D.P.isLB (φ' := D.famφB (m • χ)) (ε' := DegPre.famε (m ^ 2)) (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mulφB, mulεB, zpow_neg, Finset.prod_inv_distrib]
        rw [mul_comm, inv_mul_cancel_right]) (pullMulSec (F₁.f χ) (mulA D.P.A m).left (u χ) (hu χ))
      refine ⟨g, fun χ' h Z r z J hJ => ?_, fun h => (h χ rfl).elim⟩
      obtain rfl := inj _ _ h
      rw [hg Z r z J hJ, sval_pullMulSec _ _ _ _ _ z hJ]
    · exact ⟨SecOps.secZero, fun χ h => (hβ ⟨χ, h⟩).elim, fun _ _ => rfl⟩
  choose g hg hg₀ using ex
  choose s hs using fun β => exists_secScal D (FractionRing R) (g β)
  have s₁ : scal (DegPre.BF D (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have sm : ∀ χ mu : D.X, m • (χ + 1 • m • mu) = m • χ + m ^ 2 • mu := fun χ mu => by
    rw [one_nsmul, nsmul_add, smul_smul, sq]
  have em : ∀ {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A), x.left ≫ (mulA D.P.A m).left = (x ^ m).left :=
    fun x => by rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have fe : DegPre.FamFE D (FractionRing R) (m ^ 2) s := by
    refine (famFE_iff hG s g hs).2 fun mu α T ρ z J hJ => ?_
    by_cases hα : ∃ χ, α = m • χ
    · obtain ⟨χ, rfl⟩ := hα
      have e := (famFE_iff hG F₁.F.s F₁.f (fun α => s₁ ▸ F₁.ext α)).1 F₁.F.fe (m • mu) χ T
        (lift (ρ ≫ fst _ _) ((ρ ≫ DegPre.prB D (FractionRing R)) ^ m)) z J hJ
      rw [lift_fst, lift_snd] at e
      have c := fe_compat D hG m χ mu (u _) (hu _) (u χ) (hu χ) (u₁ _) (fun T σ => u₂ χ T σ mu) ρ hJ
      rw [hg _ _ (sm χ mu) _ _ z J hJ, hg _ χ rfl _ _ z J hJ, em, em, e, mul_pow, ← cPoint_nsmul, _root_.mul_assoc,
        _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, c]
    · have z₁ := hg₀ α fun χ h => hα ⟨χ, h⟩
      have z₂ := hg₀ (α + m ^ 2 • mu) fun χ h => hα ⟨χ - 1 • m • mu, by
        have := sm (χ - 1 • m • mu) mu
        rw [sub_add_cancel, ← h] at this
        exact add_right_cancel this⟩
      rw [sval_zero D z₁ _ hJ, sval_zero D z₂ _ hJ, zero_mul]
  refine ⟨{ F := ⟨s, fe⟩, f := g, ext := fun α => s₁.symm ▸ hs α, small := fun e => ?_ }, fun χ => ?_, hg₀⟩
  · refine ((F₁.small e).image (m • ·)).subset fun β hβ => ?_
    by_cases h : ∃ χ, β = m • χ
    · obtain ⟨χ, rfl⟩ := h
      exact ⟨χ, fun hv => hβ (vanMod_of_sval D (mulA D.P.A m) (fun Z r z J hJ => ⟨_, hg _ χ rfl Z r z J hJ⟩) hv), rfl⟩
    · refine (hβ fun j => ?_).elim
      rw [hg₀ β (fun χ e => h ⟨χ, e⟩) j]
      exact map_zero _
  · refine ⟨u χ, hu χ, corr_of_val D.P.isLB fun y J hJ => ?_,
      (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => hg _ χ rfl _ _ y J hJ⟩
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    have e₂ := u₁ χ (𝟙_ _) y J hJ
    obtain ⟨n, hn⟩ : ∃ n, m ^ 2 = n + 1 := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero 2 hm)
    have e₃ : rigV D (T := 𝟙_ _) y J ^ (m ^ 2) = rigV D (T := 𝟙_ _) y J ^ (m ^ 2 - 1) * rigV D (T := 𝟙_ _) y J := by
      rw [hn, pow_succ]; rfl
    rw [e₁, e₃] at e₂
    rw [val_pull hJ, Category.id_comp]
    exact (mul_right_cancel e₂).trans (val_pow _ _ _ _ _).symm

end GlobalTheory.Mum.MulInt

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `_ _ _ _ _ D _ hm F₁` and use `MulInt.exists_mulFam D.toPre GlobalTheory.allSixLaws.1.globalFns D.tau_bimult D.psi_even hm.pos.ne' F₁`.
-/
theorem exists_intFam_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ G : IntFam (maximalIdeal R) D.toPre (m ^ 2), MulFam m F₁ G :=
  fun _ _ _ _ _ D _ hm F₁ =>
    MulInt.exists_mulFam D.toPre GlobalTheory.allSixLaws.1.globalFns D.tau_bimult D.psi_even hm.pos.ne' F₁

end GlobalTheory.Mum
