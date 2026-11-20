import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf.TwoVarSetup

/- English proof (translation)
Establish `hu : ∀ y : Submonoid.powers x, IsUnit (τ y)`. Introduce and unpack `⟨y, n, rfl⟩`. Use `show IsUnit (τ (x ^ n))`. Rewrite using `[map_pow]`. Conclude with `h.pow n`.

Conclude with `⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩`.
-/
theorem exists_liftAway {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by
  have hu : ∀ y : Submonoid.powers x, IsUnit (τ y) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (τ (x ^ n))
    rw [map_pow]; exact h.pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩

variable {k : Type} [Field k]

/- English proof (translation)
Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))` to reduce the goal to its premises. Conclude with `RingHom.ext h`.
-/
theorem laurent_ext {F : Type} [CommRing F] [Algebra k F] {a b : FractionRing (PowerSeries k) →ₐ[k] F}
    (h : ∀ x : PowerSeries k, a (algebraMap _ _ x) = b (algebraMap _ _ x)) : a = b := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))
  exact RingHom.ext h

/- English proof (translation)
Apply `MvPowerSeries.hasSubst_of_constantCoeff_zero` to reduce the goal to its premises. Introduce `s`. Apply the tactic sequence `fin_cases s <;> exact PowerSeries.constantCoeff_X`.
-/
theorem hasSubst_diag :
    MvPowerSeries.HasSubst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> exact PowerSeries.constantCoeff_X

/- English proof (translation)
The claim follows from `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`.
-/
theorem hasSubst_var (i : Fin 2) :
    PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_X hasSubst_diag]`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem diag_var (i : Fin 2) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) = PowerSeries.X := by
  rw [MvPowerSeries.subst_X hasSubst_diag]
  fin_cases i <;> rfl

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_var i).const hasSubst_diag]`. Simplify using `only [diag_var]`. Rewrite using `[← PowerSeries.subst_def]`. Simplify using the standard rewrite rules.
-/
theorem diag_subst (i : Fin 2) (x : PowerSeries k) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) = x := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_var i).const hasSubst_diag]
  simp only [diag_var]
  rw [← PowerSeries.subst_def]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨(IsScalarTower.toAlgHom k (PowerSeries k) _).comp (MvPowerSeries.substAlgHom hasSubst_diag), fun y => by rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]; rfl⟩`.
-/
theorem exists_diag : ∃ τ : MvPowerSeries (Fin 2) k →ₐ[k] FractionRing (PowerSeries k), ∀ y,
    τ y = algebraMap (PowerSeries k) _
      (MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) y) :=
  ⟨(IsScalarTower.toAlgHom k (PowerSeries k) _).comp (MvPowerSeries.substAlgHom hasSubst_diag), fun y => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]; rfl⟩

/- English proof (translation)
Establish `hu` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)`. Rewrite `hu` using `[map_mul]`. Take `⟨s, hs⟩` from `exists_lift ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))).comp (PowerSeries.substAlgHom (hasSubst_var i))) (by`. Rewrite using `[AlgHom.comp_apply, PowerSeries.substAlgHom_X]`. Use `fin_cases i`.

Conclude with `isUnit_of_mul_isUnit_left hu`. Conclude with `isUnit_of_mul_isUnit_right hu)`. Use `⟨s, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hs, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression.
-/
theorem exists_copy (i : Fin 2) : ∃ s : FractionRing (PowerSeries k) →ₐ[k]
      Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k),
    ∀ x : PowerSeries k, s (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)
  rw [map_mul] at hu
  obtain ⟨s, hs⟩ := exists_lift ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k)
    (Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (hasSubst_var i))) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    fin_cases i
    · exact isUnit_of_mul_isUnit_left hu
    · exact isUnit_of_mul_isUnit_right hu)
  refine ⟨s, fun x => ?_⟩
  rw [hs, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]; rfl

/- English proof (translation)
Rewrite using `[algOverHom_comp, Category.assoc, h, MonObj.comp_one]`.
-/
theorem point_one {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} (h : algOverHom ε ≫ j = 1) (F : Type) [CommRing F] [Algebra k F] :
    algOverHom ((Algebra.ofId k F).comp ε) ≫ j = 1 := by
  rw [algOverHom_comp, Category.assoc, h, MonObj.comp_one]

/- English proof (translation)
Introduce `k _ G _ A _ _ j ε r f hc a`. Take `⟨τ₀, hτ₀⟩` from `exists_diag (k := k)`. Take `⟨s₀, hs₀⟩` from `exists_copy (k := k) 0`. Take `⟨s₁, hs₁⟩` from `exists_copy (k := k) 1`. Establish `hinj` using `IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))`.

Establish `hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0` using `fun i => by`. Rewrite using `[hτ₀, diag_var]`. Conclude with `(map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero`. Establish `hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0`. Rewrite using `[map_mul]`.

Conclude with `mul_ne_zero (hX 0) (hX 1)`. Generalize the expression as in `(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx`. Take `⟨δ, hδ⟩` from `exists_liftAway x τ₀ hx.isUnit`. Establish `hδ₀ : δ.comp s₀ = AlgHom.id k _` using `laurent_ext fun y => by`. Rewrite using `[AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]`.

Both sides reduce to the same expression. Establish `hδ₁ : δ.comp s₁ = AlgHom.id k _` using `laurent_ext fun y => by`. Rewrite using `[AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]`. Both sides reduce to the same expression. Take `⟨e, he, hfac⟩` from `GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by`.

Rewrite using `[point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])`. Take `⟨n, e₀, he₀⟩` from `IsLocalization.Away.surj x e`. Establish `hτe : τ₀ e₀ ≠ 0`. Rewrite using `[← hδ, ← he₀, map_mul, map_pow, hδ]`. Conclude with `mul_ne_zero he (pow_ne_zero _ hx)`.

Establish `hu` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)`. Rewrite `hu` using `[map_mul]`. Take `⟨ρ, hρ⟩` from `exists_liftAway x (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀))) (isUnit_of_mul_isUnit_left hu)`. Simplify using `only [IsScalarTower.coe_toAlgHom'] at hρ`. Establish `hρe : IsUnit (ρ e)`.

Establish `h1` using `isUnit_of_mul_isUnit_right hu`. Rewrite `h1` using `[← hρ, ← he₀, map_mul]`. Conclude with `isUnit_of_mul_isUnit_left h1`. Take `⟨χ, hχ⟩` from `hfac _ ρ hρe`. Take `⟨⟨b, M, rfl⟩, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (x * e₀)) (fun i => χ (f i))`.

Use `choose h hh using hb`. Simplify using `only [Algebra.smul_def] at hh`. Establish `hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0`. Rewrite using `[← pow_succ', map_pow, map_mul]`. Conclude with `pow_ne_zero _ (mul_ne_zero hx hτe)`.

Establish `htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M)`. Introduce `F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁`. Establish `h0 : τ (x * e₀) ≠ 0`. Rewrite `hτ` using `[map_mul]`. Conclude with `left_ne_zero_of_mul hτ`.

Take `⟨τ', hτ'⟩` from `exists_liftAway (x * e₀) τ h0.isUnit`. Establish `e0 : τ'.comp (ρ.comp s₀) = σ₀` using `laurent_ext fun y => by`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]`. Establish `e1 : τ'.comp (ρ.comp s₁) = σ₁` using `laurent_ext fun y => by`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]`.

Use `⟨τ'.comp χ, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀), AlgHom.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]`. Simplify using `only [← Category.assoc, ← algOverHom_comp]`.

Rewrite using `[e0, e1, inv_mul_cancel_right]`. Use `⟨_, _, ?_, fun i => ?_, htv⟩` and prove the remaining obligations. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[hτ₀, h0, map_zero]`.

Take `⟨χ', h1, h2⟩` from `htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)`. Establish `h3 : χ' = (Algebra.ofId k _).comp ε`. Apply `eq_of_comp_eq hc.1` to reduce the goal to its premises. Rewrite using `[point_one hc.2.1]`. Conclude with `right_eq_mul.1 h2`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]`.
-/
theorem exists_twoVar : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  intro k _ G _ A _ _ j ε r f hc a
  obtain ⟨τ₀, hτ₀⟩ := exists_diag (k := k)
  obtain ⟨s₀, hs₀⟩ := exists_copy (k := k) 0
  obtain ⟨s₁, hs₁⟩ := exists_copy (k := k) 1
  have hinj := IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  have hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0 := fun i => by
    rw [hτ₀, diag_var]
    exact (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  have hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (hX 0) (hX 1)
  generalize (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx
  obtain ⟨δ, hδ⟩ := exists_liftAway x τ₀ hx.isUnit
  have hδ₀ : δ.comp s₀ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]; rfl
  have hδ₁ : δ.comp s₁ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]; rfl
  obtain ⟨e, he, hfac⟩ := GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j
    ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by
      rw [point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])
  obtain ⟨n, e₀, he₀⟩ := IsLocalization.Away.surj x e
  have hτe : τ₀ e₀ ≠ 0 := by
    rw [← hδ, ← he₀, map_mul, map_pow, hδ]
    exact mul_ne_zero he (pow_ne_zero _ hx)
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)
  rw [map_mul] at hu
  obtain ⟨ρ, hρ⟩ := exists_liftAway x
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀)))
    (isUnit_of_mul_isUnit_left hu)
  simp only [IsScalarTower.coe_toAlgHom'] at hρ
  have hρe : IsUnit (ρ e) := by
    have h1 := isUnit_of_mul_isUnit_right hu
    rw [← hρ, ← he₀, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨χ, hχ⟩ := hfac _ ρ hρe
  obtain ⟨⟨b, M, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (x * e₀)) (fun i => χ (f i))
  choose h hh using hb
  simp only [Algebra.smul_def] at hh
  have hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0 := by
    rw [← pow_succ', map_pow, map_mul]
    exact pow_ne_zero _ (mul_ne_zero hx hτe)
  have htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M) := by
    intro F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁
    have h0 : τ (x * e₀) ≠ 0 := by
      rw [map_mul] at hτ; exact left_ne_zero_of_mul hτ
    obtain ⟨τ', hτ'⟩ := exists_liftAway (x * e₀) τ h0.isUnit
    have e0 : τ'.comp (ρ.comp s₀) = σ₀ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]
    have e1 : τ'.comp (ρ.comp s₁) = σ₁ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]
    refine ⟨τ'.comp χ, fun i => ?_, ?_⟩
    · rw [map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀),
        AlgHom.comp_apply]
      ring
    · rw [algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
        GrpObj.comp_inv]
      simp only [← Category.assoc, ← algOverHom_comp]
      rw [e0, e1, inv_mul_cancel_right]
  refine ⟨_, _, ?_, fun i => ?_, htv⟩
  · intro h0
    apply hd
    rw [hτ₀, h0, map_zero]
  · obtain ⟨χ', h1, h2⟩ := htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd
      (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)
    have h3 : χ' = (Algebra.ofId k _).comp ε := by
      apply eq_of_comp_eq hc.1
      rw [point_one hc.2.1]
      exact right_eq_mul.1 h2
    apply hinj
    rw [← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]

end GlobalTheory.SS.ArcInf.TwoVarSetup
end
