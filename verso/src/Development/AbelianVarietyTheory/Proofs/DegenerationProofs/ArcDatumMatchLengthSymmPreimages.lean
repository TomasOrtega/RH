import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BeTransSymmOfWitData

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

/- English proof (translation)
Substitute `hχ` using the available equality. Take `⟨-, -, -, -, -, hG⟩` from `hW`. Establish `hG'` using `(genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)`. Take `⟨hp, hv⟩` from `hG'`. Set `g : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R _)`.

Set `x : Sp R ⟶ P.P.A.left` to `(P.c (e y)).left`. Establish `hx : Out.jFK (R` using `R) F ≫ Out.ptK (P.c (e y)) = spMap g ≫ x := by`. Establish `: spMap g = Out.jFK (R` using `R) F ≫ Out.jK R := by`. Simplify using `only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Rewrite using `[this, Category.assoc]`.

Both sides reduce to the same expression. Take `⟨j₀, hj₀⟩` from `exists_chart a.D₀.P.isLB (φ (x (cpt R)))`. Establish `ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j)` using `(top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩`. Establish `hz : (Out.jFK (R` using `R) F ≫ Out.ptK (P.c (e y))) z ∈ (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by`. Rewrite using `[hx]`.

Conclude with `ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)`. Establish `hz₀` using `mem_pull.1 hz.1`. Establish `H1` using `hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)`. Rewrite `H1` using `[gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one, Units.val_mul, Units.inv_mul_eq_iff_eq_mul]`. Take `⟨u₁, hu₁⟩` from `GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z`.

Establish `hz₁ : (Out.jFK (R` using `O') F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by`. Rewrite using `[← hp PUnit.unit]`. Conclude with `hz₀`. Establish `ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing O'))) ⁻¹ᵁ (LB.wchart a.D₀.P.L (K` using `PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) := (top_le_iff_mem _ _ (Out.jFK (R := O') F z)).2 (Set.mem_iInter.2 fun _ => hz₁)`. Take `⟨u₀, hu₀⟩` from `GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap (algebraMap (FractionRing O') F) (𝟙 _) _ ht₀ ((a.D₀.psi y).s (fun _ => j₀)) z`.

Take `⟨r, s, hs, hr⟩` from `IsFractionRing.div_surjective (A := O') u₀.val`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Establish `hr0 : r ≠ 0` using `fun h0 => u₀.ne_zero (by rw [← hr, h0, map_zero, zero_div])`. Take `⟨r', hr'⟩` from `hf r hr0`. Take `⟨s', hs'⟩` from `hf s hs0`.

Establish `hq : algebraMap (FractionRing O') F u₀.val = g (r' * s'⁻¹).val`. Rewrite using `[← hr, map_div₀, hF, hF, ← hr', ← hs', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]`. Both sides reduce to the same expression. Rewrite `hu₀` using `[hq, Category.comp_id]`. Rewrite `hu₁` using `[← hx]`.

Use `⟨u₁ * (r' * s'⁻¹), H1.trans ?_⟩` and prove the remaining obligations. Use `(congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_` and prove the remaining obligations. Simplify using `only [Units.val_mul, map_mul]`. Rewrite using `[mul_left_comm]`. Both sides reduce to the same expression.
-/
theorem psi_value_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.X) (hW : Match a f u P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.X) (hχ : e y = χ) (j : P.P.L.ι)
    (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c (e y)).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c (e y)) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := O') F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing O'))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := O') F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap (algebraMap (FractionRing O') F) (𝟙 _) _ ht₀
    ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, s, hs, hr⟩ := IsFractionRing.div_surjective (A := O') u₀.val
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr, h0, map_zero, zero_div])
  obtain ⟨r', hr'⟩ := hf r hr0
  obtain ⟨s', hs'⟩ := hf s hs0
  have hq : algebraMap (FractionRing O') F u₀.val = g (r' * s'⁻¹).val := by
    rw [← hr, map_div₀, hF, hF, ← hr', ← hs', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]
    rfl
  rw [hq, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * (r' * s'⁻¹), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

/- English proof (translation)
Distinguish the cases in `hz : u = 0`. Substitute `hz` using the available equality. Establish `h0'` using `h ▸ h0`. Establish `hm : m = 0`. Assume the negation of the conclusion as `hm; exact h0 (by rw [zero_pow hm, zero_mul])`.

Establish `hn : n = 0`. Assume the negation of the conclusion as `hn; exact h0' (by rw [zero_pow hn, zero_mul])`. Use linear arithmetic over natural numbers and integers. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨k, t, ht⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ`.

Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hu (by rw [ht, pow_zero, _root_.mul_one]; exact t.isUnit)`. Use `IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (t ^ m * v) (t ^ n * v') (k * m) (k * n) (by` as an intermediate fact. Rewrite `h` using `[ht]`.

Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, pow_mul]`. Take the linear combination `h)`. Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) this`.
-/
theorem pow_eq_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {u : R} (hu : ¬ IsUnit u)
    (v v' : Rˣ) (m n : ℕ) (h0 : u ^ m * v ≠ 0) (h : u ^ m * v = u ^ n * v') : m = n := by
  by_cases hz : u = 0
  · subst hz
    have h0' := h ▸ h0
    have hm : m = 0 := by
      by_contra hm; exact h0 (by rw [zero_pow hm, zero_mul])
    have hn : n = 0 := by
      by_contra hn; exact h0' (by rw [zero_pow hn, zero_mul])
    omega
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨k, t, ht⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    have hk : k ≠ 0 := by
      rintro rfl
      exact hu (by rw [ht, pow_zero, _root_.mul_one]; exact t.isUnit)
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (t ^ m * v) (t ^ n * v') (k * m) (k * n) (by
      rw [ht] at h
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_mul]
      linear_combination h)
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) this

/- English proof (translation)
Set `F` to `AlgebraicClosure (FractionRing R)`. Set `g : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R _)`. Establish `hg : Function.Injective g` using `(algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective _ _)`. Establish `hfi : Function.Injective f` using `(injective_iff_map_eq_zero f).2 fun x hx => by`. Assume the negation of the conclusion as `h0`.

Conclude with `(hf x h0).ne_zero hx`. Establish `hgf : Function.Injective (g.comp f)` using `hg.comp hfi`. Set `alg : Algebra (FractionRing O') F` to `(IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra`. Establish `hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))` using `fun x => IsFractionRing.lift_algebraMap hgf x`. Establish `z : Sp F` using `(default : PrimeSpectrum F)`.

Take `⟨j, hj⟩` from `exists_chart P.P.isLB ((P.c (e₁ y)).left (cpt R))`. Take `⟨v, hv⟩` from `@psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₁ he₁ w₁ e₁ h₁ F _ _ _ alg hF z y _ rfl j hj`. Take `⟨v', hv'⟩` from `@psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₂ he₂ w₂ e₂ h₂ F _ _ _ alg hF z y' _ hy.symm j hj`. Establish `e` using `(toStk z).injective (hv.symm.trans hv')`. Establish `e0` using `fun h => Units.ne_zero _ (hv.trans ((congrArg (toStk z) h).trans (map_zero _)))`.

Establish `nn : ∀ y, 0 ≤ a.be y y` using `fun y => by`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using the standard rewrite rules. Conclude with `(a.be_pos y hy).le`.

Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y) (by norm_num : (0 : ℤ) ≤ 2))`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y') (by norm_num : (0 : ℤ) ≤ 2))`. Rewrite `e` using `[hm, hn, zpow_natCast, zpow_natCast]`. Rewrite `e0` using `[hm, zpow_natCast]`. Establish `e' : u ^ m * v = u ^ n * v'`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_pow, map_pow]`. Conclude with `e`. Establish `e0' : u ^ m * v ≠ 0` using `fun h => e0 (by`. Use `congrArg g h` as an intermediate fact.

Rewrite `this` using `[map_mul, map_pow, map_zero]`. Conclude with `this)`. Establish `hmn : m = n` using `pow_eq_of_not_isUnit hu v v' m n e0' e'`. Establish `d : (2 : ℤ) ∣ a.be y y` using `(Dvd.intro _ rfl).trans (a.be_dvd y y)`. Establish `d' : (2 : ℤ) ∣ a.be y' y'` using `(Dvd.intro _ rfl).trans (a.be_dvd y' y')`.

Use linear arithmetic over natural numbers and integers.
-/
theorem be_self_eq_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu : ¬ IsUnit u) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X)
    (h₁ : Match a f u P oP φ₁ he₁ w₁ e₁) (h₂ : Match a f u P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing R)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective _ _)
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact (hf x h0).ne_zero hx
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.P.isLB ((P.c (e₁ y)).left (cpt R))
  obtain ⟨v, hv⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₁ he₁ w₁ e₁ h₁
    F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨v', hv'⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₂ he₂ w₂ e₂ h₂
    F _ _ _ alg hF z y' _ hy.symm j hj
  have e := (toStk z).injective (hv.symm.trans hv')
  have e0 := fun h => Units.ne_zero _ (hv.trans ((congrArg (toStk z) h).trans (map_zero _)))
  have nn : ∀ y, 0 ≤ a.be y y := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · exact (a.be_pos y hy).le
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  rw [hm, zpow_natCast] at e0
  have e' : u ^ m * v = u ^ n * v' := by
    apply hg
    rw [map_mul, map_mul, map_pow, map_pow]
    exact e
  have e0' : u ^ m * v ≠ 0 := fun h => e0 (by
    have := congrArg g h
    rw [map_mul, map_pow, map_zero] at this
    exact this)
  have hmn : m = n := pow_eq_of_not_isUnit hu v v' m n e0' e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ f u hf hu P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ y` and use `be_self_eq_of_match a f u hf hu P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ _ _ (by simp)`.
-/
theorem be_symm_eq_of_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ f u hf hu P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ y =>
    be_self_eq_of_match a f u hf hu P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ _ _ (by simp)

end GlobalTheory.LN

end
