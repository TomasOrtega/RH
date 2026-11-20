import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInv
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMLiePeriod

/- English proof (translation)
Take `⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩` from `SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA`. Take `⟨Q, i', r', -, hi', hr', hir'⟩` from `EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK`. Take `⟨rig, hrig⟩` from `Q.rigid`. Take `⟨v, Hm, χ, -, hAH, -, hv1, hv2, -, hsec, -⟩` from `thetaUnifAV_all Q rig hrig`. Establish `hu` using `TorusTransfer.tangent_bijective u hgA`.

Use `haveI := hi`. Use `haveI := hr`. Use `haveI := hi'`. Use `haveI := hr'`. Take `⟨J, hJ, hJΛ, -, -⟩` from `HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v hv1 hv2 (i ≫ i') inferInstance`.

Take `⟨R, hR, hRΛ, -, -⟩` from `HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u hu.1 hu.2 (r' ≫ r) inferInstance`. Establish `hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤))`. Use `(IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hsB` using `(abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2`.

Establish `: Surjective (r.left ≫ i.left)` using `by rw [← Over.comp_left, hri]; exact hsB`. Establish `: Surjective i.left` using `Surjective.of_comp r.left i.left`. Take `⟨n, hn, hkill⟩` from `HolUnifEnd.exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i`. Establish `hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m`. Introduce `x`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, Category.assoc]`. Establish `hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ`. Introduce `a b h`. Rewrite using `[← v.ker]`.

Establish `e` using `v.ex_add (a - b) b`. Rewrite `e` using `[sub_add_cancel, h]`. Establish `e2` using `congrArg (· * (v.ex b)⁻¹) e`. Simplify using `using e2.symm`. Establish `hRJ : ∀ z, R (J z) = m • z`.

Introduce `z`. Establish `hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ`. Introduce `t`. Establish `h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z))`. Rewrite using `[hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]`.

Simplify using `only [Category.assoc]`. Establish `h2` using `hsubv _ _ h1`. Establish `h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z)`. Rewrite using `[map_smul, map_smul, smul_sub, smul_comm t m z]`. Rewrite using `[h3, map_sub, map_nsmul]`.

Conclude with `h2`. Establish `hJy0 : J (R (J z) - m • z) = 0` using `LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t`. Establish `hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1`. Introduce `t`. Establish `h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1`.

Rewrite using `[← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hir', Category.comp_id]`. Use `_ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]`. Use `_ = 1 := by rw [h2, MonObj.one_comp]`.

Establish `hn0 : (n : ℂ) ≠ 0` using `by exact_mod_cast (show n ≠ 0 by omega)`. Establish `hy0 : R (J z) - m • z = 0` using `LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by`. Rewrite using `[← u.ker]`. Establish `e` using `hkill _ (hker ((n : ℂ)⁻¹ * t))`. Rewrite `e` using `[← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc, mul_inv_cancel₀ hn0, _root_.one_mul]`.

Conclude with `e`. Conclude with `sub_eq_zero.1 hy0`. Conclude with `⟨Q, v, Hm, χ, r' ≫ r, J, m, hAH, fun k s => ((hsec k).1 s).exists, inferInstance, hm, hJΛ, fun z => by rw [← hR, hRJ]⟩`.
-/
theorem exists_lifts_nsmul (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (v : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : v.Λ → ℂ)
      (q : Q.A ⟶ A) (J : (Fin g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (m : ℕ), v.IsAH Hm χ ∧
      (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ IsMonHom q ∧ 1 ≤ m ∧ (∀ l ∈ u.Λ, J l ∈ v.Λ) ∧
      ∀ z, v.ex (J z) ≫ q = u.ex (m • z) := by
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', -, hi', hr', hir'⟩ :=
    EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, Hm, χ, -, hAH, -, hv1, hv2, -, hsec, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance
  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := HolUnifEnd.exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i
  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0
  exact ⟨Q, v, Hm, χ, r' ≫ r, J, m, hAH, fun k s => ((hsec k).1 s).exists, inferInstance, hm, hJΛ,
    fun z => by rw [← hR, hRJ]⟩

/- English proof (translation)
Take `⟨hL, -⟩` from `abelianSchemeLaws_all`. Take `⟨Q, v, Hm', χ', q, J, m, hAH', hfn, hq, hm, hJΛ, hJ⟩` from `exists_lifts_nsmul A g hA hgA L u`. Use `⟨m, hm, fun P w Hm χ hAH hsec F hF => ?_⟩` and prove the remaining obligations. Establish `hΛ : ∀ l ∈ w.Λ, (J ∘ₗ F) l ∈ v.Λ` using `fun l hl => hJΛ _ (hF l hl)`. Take `⟨d, hd⟩` from `LatticeHom.exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero w v P.isLB Q.isLB hAH hAH' (J ∘ₗ F) hΛ 4`.

Take `⟨f, hf, hfe⟩` from `LatticeHom.exists_isMonHom_of_complementary hL.ample P Q w v hsec hfn (J ∘ₗ F) hΛ d hd`. Use `⟨f ≫ q, inferInstance, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← hfe, LinearMap.comp_apply, hJ, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]`.
-/
theorem exists_hom_nsmul (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (P : Out.PolAV (Sp ℂ)) (w : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : w.Λ → ℂ),
      w.IsAH Hm χ → (∀ (k : ℕ) θ, w.IsThetaFn Hm χ k θ → ∃ s, w.IsFnPow k s θ) →
      ∀ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ w.Λ, F l ∈ u.Λ) →
        ∃ f : P.A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (((m : ℂ) • F) z) = w.ex z ≫ f := by
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨Q, v, Hm', χ', q, J, m, hAH', hfn, hq, hm, hJΛ, hJ⟩ := exists_lifts_nsmul A g hA hgA L u
  refine ⟨m, hm, fun P w Hm χ hAH hsec F hF => ?_⟩
  have hΛ : ∀ l ∈ w.Λ, (J ∘ₗ F) l ∈ v.Λ := fun l hl => hJΛ _ (hF l hl)
  obtain ⟨d, hd⟩ := LatticeHom.exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero w v P.isLB Q.isLB hAH hAH'
    (J ∘ₗ F) hΛ 4
  obtain ⟨f, hf, hfe⟩ := LatticeHom.exists_isMonHom_of_complementary hL.ample P Q w v hsec hfn (J ∘ₗ F) hΛ d hd
  refine ⟨f ≫ q, inferInstance, fun z => ?_⟩
  rw [← Category.assoc, ← hfe, LinearMap.comp_apply, hJ, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Take `⟨-, h2⟩` from `TorusTransfer.tangent_bijective u hg`. Take `⟨h1', h2'⟩` from `TorusTransfer.tangent_bijective u' hg'`. Establish `key` using `GlobalTheory.HomLinear.exists_linear_of_isMonHom A A' hA hA' L L' g g' u u' h1' h2'`. Prove the components needed by the constructor for the conclusion. Use `choose F hF hΛ hd hu using key`.

Use `u.discrete` as an intermediate fact. Use `u'.discrete` as an intermediate fact. Establish `: Countable u'.Λ` using `Finsupp.Countable.of_moduleFinite (R := ℤ)`. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := u.Λ)`. Rewrite using `[← Set.countable_coe_iff]`.

Use `Function.Injective.countable (f := fun (f : {f : A ⟶ A' | IsMonHom f}) (i : Fin n) => (⟨F f.1 f.2 (s i), hΛ f.1 f.2 _ (s i).2⟩ : u'.Λ)) ?_` and prove the remaining obligations. Introduce `f f' h`. Establish `e1 : ∀ l : u.Λ, F f.1 f.2 l = F f'.1 f'.2 l`. Introduce `l`. Establish `hl : l ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`.

Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx`. Conclude with `congrArg Subtype.val (congrFun h i)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`.

Consider the case `smul a x _ hx => rw [Submodule.coe_smul, map_zsmul, map_zsmul, hx]`. Establish `e2 : ∀ z, F f.1 f.2 z = F f'.1 f'.2 z`. Introduce `z`. Establish `hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ))` using `u.full ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx => exact e1 ⟨x, hx⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul a x _ hx => simp [hx]`. Conclude with `Subtype.ext (hu f'.1 f'.2 f.1 fun z => by rw [← e2, hF])`.

Introduce `f f' hf hf' h`. Take `⟨F, hF, -, hd, -⟩` from `key f hf`. Take `⟨F', -, -, hd', hu'⟩` from `key f' hf'`. Use `hu' f fun z => ?_` and prove the remaining obligations. Take `⟨v, ⟨hv, hvz⟩, -⟩` from `h2 z`.

Establish `a` using `hd z v hv hvz`. Establish `b` using `hd' z v hv hvz`. Rewrite `b` using `[← h v hv]`. Rewrite using `[← hF, (h1' _ a.1).unique a.2 b.2]`.
-/
theorem countable_and_ext {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' A'.hom)
    {L : LB A.left} {L' : LB A'.left} (u : HolUnif A L g) (u' : HolUnif A' L' g') :
    {f : A ⟶ A' | IsMonHom f}.Countable ∧
      ∀ f f' : A ⟶ A', IsMonHom f → IsMonHom f' → (∀ v, IsTangent v → v ≫ f = v ≫ f') → f = f' := by
  obtain ⟨-, h2⟩ := TorusTransfer.tangent_bijective u hg
  obtain ⟨h1', h2'⟩ := TorusTransfer.tangent_bijective u' hg'
  have key := GlobalTheory.HomLinear.exists_linear_of_isMonHom A A' hA hA' L L' g g' u u' h1' h2'
  constructor
  · choose F hF hΛ hd hu using key
    have := u.discrete
    have := u'.discrete
    have : Countable u'.Λ := Finsupp.Countable.of_moduleFinite (R := ℤ)
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := u.Λ)
    rw [← Set.countable_coe_iff]
    refine Function.Injective.countable
      (f := fun (f : {f : A ⟶ A' | IsMonHom f}) (i : Fin n) =>
        (⟨F f.1 f.2 (s i), hΛ f.1 f.2 _ (s i).2⟩ : u'.Λ)) ?_
    intro f f' h
    have e1 : ∀ l : u.Λ, F f.1 f.2 l = F f'.1 f'.2 l := by
      intro l
      have hl : l ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hl using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact congrArg Subtype.val (congrFun h i)
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => rw [Submodule.coe_smul, map_zsmul, map_zsmul, hx]
    have e2 : ∀ z, F f.1 f.2 z = F f'.1 f'.2 z := by
      intro z
      have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := u.full ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem x hx => exact e1 ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    exact Subtype.ext (hu f'.1 f'.2 f.1 fun z => by rw [← e2, hF])
  · intro f f' hf hf' h
    obtain ⟨F, hF, -, hd, -⟩ := key f hf
    obtain ⟨F', -, -, hd', hu'⟩ := key f' hf'
    refine hu' f fun z => ?_
    obtain ⟨v, ⟨hv, hvz⟩, -⟩ := h2 z
    have a := hd z v hv hvz
    have b := hd' z v hv hvz
    rw [← h v hv] at b
    rw [← hF, (h1' _ a.1).unique a.2 b.2]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hc' : Transcendental k (c : ℂ)` using `fun h => hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)`. Establish `hcount : (S ∪ {x : ℂ | IsAlgebraic k x}).Countable` using `hS.union (Algebraic.countable k ℂ)`. Establish `hne : (S ∪ {x : ℂ | IsAlgebraic k x}) ≠ Set.univ` using `fun h => not_countable_complex (h ▸ hcount)`. Take `⟨t, ht⟩` from `(Set.ne_univ_iff_exists_notMem _).1 hne`.

Take `⟨ρ, hρt⟩` from `exists_algHom_apply_eq_of_transcendental R hR c hc' t (fun h => ht (Or.inr h))`. Conclude with `ht (Or.inl (hρt ▸ hρ ρ))`.
-/
theorem isAlgebraic_of_countable {k : Type} [Field k] [Countable k] [Algebra k ℂ] (R : Subalgebra k ℂ) (hR : R.FG) (c : R)
    (S : Set ℂ) (hS : S.Countable) (hρ : ∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) : IsAlgebraic k c := by
  by_contra hc
  have hc' : Transcendental k (c : ℂ) := fun h =>
    hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)
  have hcount : (S ∪ {x : ℂ | IsAlgebraic k x}).Countable := hS.union (Algebraic.countable k ℂ)
  have hne : (S ∪ {x : ℂ | IsAlgebraic k x}) ≠ Set.univ := fun h =>
    not_countable_complex (h ▸ hcount)
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  obtain ⟨ρ, hρt⟩ := exists_algHom_apply_eq_of_transcendental R hR c hc' t
    (fun h => ht (Or.inr h))
  exact ht (Or.inl (hρt ▸ hρ ρ))

open HomDescent in

/- English proof (translation)
Set `Φ'` to `IsOpenImmersion.lift hU.fromSpec Φ (by`. Rewrite using `[hU.range_fromSpec]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hΦ x)`. Establish `hΦ' : Φ' ≫ hU.fromSpec = Φ` using `IsOpenImmersion.lift_fac _ _ _`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective Φ'`. Set `G : (Γ(Z, U) ⟶ CommRingCat.of (ℂ ⊗[k] B)) → (Sp (ℂ ⊗[k] B) ⟶ Z)` to `fun a => Spec.map a ≫ hU.fromSpec`. Establish `hG : Function.Injective G` using `fun a a' h => Spec.map_injective ((cancel_mono _).1 h)`. Establish `e : ∀ ρ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ Φ = G (φ ≫ CommRingCat.ofHom (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom)` using `fun ρ => by`. Rewrite using `[← hΦ', ← hφ]`.

Simplify using `only [G, Spec.map_comp, Category.assoc]`. Rewrite using `[e, e]`. Use `congr 1`. Set `b` to `Module.Basis.ofVectorSpace k B`. Use extensionality with `y`.

Apply `(Algebra.TensorProduct.basis ℂ b).repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map ρ₁ (AlgHom.id k B) (φ.hom y)) i = (Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map R.val (AlgHom.id k B) (φ.hom y)) i`. Rewrite using `[basis_repr_map, basis_repr_map]`. Apply `hρ₁` to reduce the goal to its premises.

Use `isAlgebraic_of_countable R hR _ _ ((hc.preimage_of_injOn hG.injOn).image fun a => (Algebra.TensorProduct.basis ℂ b).repr (a.hom y) i) fun ρ => ⟨_, ⟨ρ, e ρ⟩, ?_⟩` and prove the remaining obligations. Conclude with `basis_repr_map b ρ _ i`.
-/
theorem specialise_eq {k : Type} [Field k] [Countable k] [Algebra k ℂ] (R : Subalgebra k ℂ)
    (hR : R.FG) {B : Type} [CommRing B] [Algebra k B] {Z : Scheme.{0}} (Φ : Sp (R ⊗[k] B) ⟶ Z) (U : Z.Opens)
    (hU : IsAffineOpen U) (hΦ : ∀ x, Φ x ∈ U)
    (hc : (Set.range fun ρ : R →ₐ[k] ℂ =>
      spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ Φ).Countable)
    (ρ₁ : R →ₐ[k] ℂ) (hρ₁ : ∀ c : R, IsAlgebraic k c → ρ₁ c = c) :
    spMap (Algebra.TensorProduct.map ρ₁ (AlgHom.id k B)).toRingHom ≫ Φ =
      spMap (Algebra.TensorProduct.map R.val (AlgHom.id k B)).toRingHom ≫ Φ := by
  let Φ' := IsOpenImmersion.lift hU.fromSpec Φ (by
    rw [hU.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact hΦ x)
  have hΦ' : Φ' ≫ hU.fromSpec = Φ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective Φ'
  let G : (Γ(Z, U) ⟶ CommRingCat.of (ℂ ⊗[k] B)) → (Sp (ℂ ⊗[k] B) ⟶ Z) := fun a => Spec.map a ≫ hU.fromSpec
  have hG : Function.Injective G := fun a a' h => Spec.map_injective ((cancel_mono _).1 h)
  have e : ∀ ρ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ Φ =
      G (φ ≫ CommRingCat.ofHom (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom) := fun ρ => by
    rw [← hΦ', ← hφ]
    simp only [G, Spec.map_comp, Category.assoc]
  rw [e, e]
  congr 1
  let b := Module.Basis.ofVectorSpace k B
  ext y
  apply (Algebra.TensorProduct.basis ℂ b).repr.injective
  ext i
  change (Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map ρ₁ (AlgHom.id k B) (φ.hom y)) i =
    (Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map R.val (AlgHom.id k B) (φ.hom y)) i
  rw [basis_repr_map, basis_repr_map]
  apply hρ₁
  refine isAlgebraic_of_countable R hR _ _
    ((hc.preimage_of_injOn hG.injOn).image fun a => (Algebra.TensorProduct.basis ℂ b).repr (a.hom y) i)
    fun ρ => ⟨_, ⟨ρ, e ρ⟩, ?_⟩
  exact basis_repr_map b ρ _ i

open HomDescent Spread in

/- English proof (translation)
Use `hA.proper` as an intermediate fact. Use `hA'.proper` as an intermediate fact. Use `hA.smooth` as an intermediate fact. Use `hA'.smooth` as an intermediate fact. Take `⟨R, fR, hR, hm, hfR⟩` from `exists_fg_isMonHom f`.

Use `haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR`. Take `⟨ρ, -⟩` from `exists_algHom_isAlgebraic_of_finiteType k R k`. Establish `hρ : ∀ c : R, IsAlgebraic k c → ((Algebra.ofId k ℂ).comp ρ) c = c`. Introduce `c hc`. Choose the witnesses or unpack the hypotheses as in `⟨a, rfl⟩ : c ∈ (algebraMap k R).range := by`.

Conclude with `minpoly.mem_range_of_degree_eq_one k c (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hc.isIntegral))`. Simplify using `[Algebra.ofId_apply]`. Take `⟨f₁, hf₁, e₁⟩` from `exists_specialise fR ρ`. Use `choose g hg eg using fun σ : R →ₐ[k] ℂ => exists_specialise fR σ`. Establish `main : g ((Algebra.ofId k ℂ).comp ρ) = f`.

Use `hext _ _ (hg _) hf fun v hv => ?_` and prove the remaining obligations. Take `⟨U, hU, h0, -⟩` from `exists_isAffineOpen_mem_and_subset (X := A'.left) (x := eSec A' (default : Sp k)) (U := ⊤) trivial`. Establish `e : ∀ σ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map σ (AlgHom.id k (DualNumber ℂ))).toRingHom ≫ ptBC A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _ = ptBC A.hom _ (tangent_over v) ℂ ≫ (g σ).left ≫ pullback.fst _ _` using `fun σ => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (spMap_map_ptBC A.hom (tangent_over v) σ)).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (eg σ).symm)))`. Establish `h` using `specialise_eq R hR (ptBC A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _) U hU (fun x => by`. Take `⟨y, hy⟩` from `tangent_range fR v hv x`.

Rewrite using `[← hy, Subsingleton.elim (α := Sp k) y default]`. Conclude with `h0)`. Use the proof step `((hc.image fun a => ptBC A.hom _ (tangent_over v) ℂ ≫ a.left ≫ pullback.fst _ _).mono (by`. Introduce and unpack `_ ⟨σ, rfl⟩`. Conclude with `⟨g σ, hg σ, (e σ).symm⟩))`.

Use the proof step `((Algebra.ofId k ℂ).comp ρ) hρ`. Establish `a : (g R.val).left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _` using `(eg R.val).trans hfR`. Use `replace h := (e _).symm.trans (h.trans ((e _).trans (congrArg (_ ≫ ·) a)))`. Take `⟨m, hm⟩` from `tangent_factor v`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `b : ∀ c : pullback A.hom (spMap (algebraMap k ℂ)) ⟶ A'.left, m ≫ ptBC A.hom _ (tangent_over v) ℂ ≫ c = v.left ≫ c` using `fun c => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hm)`. Conclude with `(Category.assoc _ _ _).trans ((b _).symm.trans ((congrArg (m ≫ ·) h).trans ((b _).trans (Category.assoc _ _ _).symm)))`. Conclude with `(Over.w _).trans (Over.w _).symm`. Establish `hj : bcMap A.hom (Algebra.ofId k ℂ) ≫ f₁.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _`.

Rewrite using `[← main]`. Conclude with `(congrArg (_ ≫ ·) e₁).trans ((bcMap_comp_assoc A.hom ρ (Algebra.ofId k ℂ) _).trans (eg _).symm)`. Establish `hid : ∀ (G : Over (Sp k)) [GrpObj G], IsGrpPullback G G (spMap (algebraMap k k)) (𝟙 G.left)`. Introduce `G _`. Use `haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 _))`.

Conclude with `(isGrpPullback_of_iso (Iso.refl G)).congr (Spec.map_id (CommRingCat.of k)).symm rfl`. Take `⟨a, ha, ha'⟩` from `grpPullback_iso (hid A) (isGrpPullback_pullback A (spMap (algebraMap k k)))`. Take `⟨b, hb, hb'⟩` from `grpPullback_iso (isGrpPullback_pullback A' (spMap (algebraMap k k))) (hid A')`. Use `⟨a.hom ≫ f₁ ≫ b.hom, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite `hb'` using `[Category.comp_id]`.

Establish `h3 : pullback.fst A.hom (spMap (algebraMap k ℂ)) ≫ a.hom.left = bcMap A.hom (Algebra.ofId k ℂ)`. Apply `eq_bcMap` to reduce the goal to its premises. Rewrite using `[Category.assoc] erw [ha']`. Conclude with `Category.comp_id _`. Establish `: a.hom.left ≫ pullback.snd _ _ = A.hom` using `Over.w a.hom`.

Rewrite using `[Category.assoc]`. Use `erw [this]`. Conclude with `pullback.condition`. Rewrite using `[← hj, ← h3, Over.comp_left, Over.comp_left, hb']`. Conclude with `Category.assoc _ _ _`.
-/
theorem descend_pullback {k : Type} [Field k] [Countable k] [IsAlgClosed k] [Algebra k ℂ]
    (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (hc : {f : (Over.pullback (spMap (algebraMap k ℂ))).obj A ⟶ (Over.pullback (spMap (algebraMap k ℂ))).obj A' |
      IsMonHom f}.Countable)
    (hext : ∀ f f' : (Over.pullback (spMap (algebraMap k ℂ))).obj A ⟶ (Over.pullback (spMap (algebraMap k ℂ))).obj A',
      IsMonHom f → IsMonHom f' → (∀ v, IsTangent v → v ≫ f = v ≫ f') → f = f')
    (f : (Over.pullback (spMap (algebraMap k ℂ))).obj A ⟶ (Over.pullback (spMap (algebraMap k ℂ))).obj A') (hf : IsMonHom f) :
    ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ f.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f₀.left := by
  have := hA.proper
  have := hA'.proper
  have := hA.smooth
  have := hA'.smooth
  obtain ⟨R, fR, hR, hm, hfR⟩ := exists_fg_isMonHom f
  haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨ρ, -⟩ := exists_algHom_isAlgebraic_of_finiteType k R k
  have hρ : ∀ c : R, IsAlgebraic k c → ((Algebra.ofId k ℂ).comp ρ) c = c := by
    intro c hc
    obtain ⟨a, rfl⟩ : c ∈ (algebraMap k R).range := by
      exact minpoly.mem_range_of_degree_eq_one k c
        (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hc.isIntegral))
    simp [Algebra.ofId_apply]
  obtain ⟨f₁, hf₁, e₁⟩ := exists_specialise fR ρ
  choose g hg eg using fun σ : R →ₐ[k] ℂ => exists_specialise fR σ
  have main : g ((Algebra.ofId k ℂ).comp ρ) = f := by
    refine hext _ _ (hg _) hf fun v hv => ?_
    obtain ⟨U, hU, h0, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := A'.left) (x := eSec A' (default : Sp k)) (U := ⊤) trivial
    have e : ∀ σ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map σ (AlgHom.id k (DualNumber ℂ))).toRingHom ≫
        ptBC A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _ =
        ptBC A.hom _ (tangent_over v) ℂ ≫ (g σ).left ≫ pullback.fst _ _ := fun σ =>
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (spMap_map_ptBC A.hom (tangent_over v) σ)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (eg σ).symm)))
    have h := specialise_eq R hR
      (ptBC A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _) U hU
      (fun x => by
        obtain ⟨y, hy⟩ := tangent_range fR v hv x
        rw [← hy, Subsingleton.elim (α := Sp k) y default]
        exact h0)
      ((hc.image fun a => ptBC A.hom _ (tangent_over v) ℂ ≫ a.left ≫ pullback.fst _ _).mono (by
        rintro _ ⟨σ, rfl⟩
        exact ⟨g σ, hg σ, (e σ).symm⟩))
      ((Algebra.ofId k ℂ).comp ρ) hρ
    have a : (g R.val).left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ :=
      (eg R.val).trans hfR
    replace h := (e _).symm.trans (h.trans ((e _).trans (congrArg (_ ≫ ·) a)))
    obtain ⟨m, hm⟩ := tangent_factor v
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have b : ∀ c : pullback A.hom (spMap (algebraMap k ℂ)) ⟶ A'.left,
          m ≫ ptBC A.hom _ (tangent_over v) ℂ ≫ c = v.left ≫ c := fun c =>
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hm)
      exact (Category.assoc _ _ _).trans ((b _).symm.trans ((congrArg (m ≫ ·) h).trans
        ((b _).trans (Category.assoc _ _ _).symm)))
    · exact (Over.w _).trans (Over.w _).symm
  have hj : bcMap A.hom (Algebra.ofId k ℂ) ≫ f₁.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
    rw [← main]
    exact (congrArg (_ ≫ ·) e₁).trans ((bcMap_comp_assoc A.hom ρ (Algebra.ofId k ℂ) _).trans (eg _).symm)
  have hid : ∀ (G : Over (Sp k)) [GrpObj G], IsGrpPullback G G (spMap (algebraMap k k)) (𝟙 G.left) := by
    intro G _
    haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact (isGrpPullback_of_iso (Iso.refl G)).congr (Spec.map_id (CommRingCat.of k)).symm rfl
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (hid A) (isGrpPullback_pullback A (spMap (algebraMap k k)))
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback A' (spMap (algebraMap k k))) (hid A')
  refine ⟨a.hom ≫ f₁ ≫ b.hom, inferInstance, ?_⟩
  rw [Category.comp_id] at hb'
  have h3 : pullback.fst A.hom (spMap (algebraMap k ℂ)) ≫ a.hom.left = bcMap A.hom (Algebra.ofId k ℂ) := by
    apply eq_bcMap
    · rw [Category.assoc]
      erw [ha']
      exact Category.comp_id _
    · have : a.hom.left ≫ pullback.snd _ _ = A.hom := Over.w a.hom
      rw [Category.assoc]
      erw [this]
      exact pullback.condition
  rw [← hj, ← h3, Over.comp_left, Over.comp_left, hb']
  exact Category.assoc _ _ _

/- English proof (translation)
Take `⟨e, he, he1⟩` from `grpPullback_iso hp (isGrpPullback_pullback A₀ (spMap (algebraMap k ℂ)))`. Take `⟨e', he', he1'⟩` from `grpPullback_iso hp' (isGrpPullback_pullback A₀' (spMap (algebraMap k ℂ)))`. Take `⟨h1, h2⟩` from `countable_and_ext hA hA' hg hg' u u'`. Take `⟨f₀, hf₀, hf⟩` from `descend_pullback A₀ A₀' hA₀ hA₀' ((h1.image fun g => e.inv ≫ g ≫ e'.hom).mono fun f hf => by`. Establish `: IsMonHom f` using `hf`.

Conclude with `⟨e.hom ≫ f ≫ e'.inv, show IsMonHom _ from inferInstance, by simp⟩)`. Use the proof step `(fun f f' hf hf' h => by`. Use `h2 (e.hom ≫ f ≫ e'.inv) (e.hom ≫ f' ≫ e'.inv) inferInstance inferInstance fun v hv => by` as an intermediate fact. Use `h _ (HomDescent.isTangent_comp e.hom hv)` as an intermediate fact. Simplify using `only [← Category.assoc] at this ⊢`.

Rewrite using `[this]`. Simplify using `using this) (e.inv ≫ f ≫ e'.hom) inferInstance`. Use `⟨f₀, hf₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← he1, ← he1', Category.assoc]`. Use `erw [← hf]`.

Rewrite using `[← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]`. Simplify using the standard rewrite rules.
-/
theorem descend {k : Type} [Field k] [Countable k] [IsAlgClosed k] [Algebra k ℂ]
    {A₀ A₀' : Over (Sp k)} [GrpObj A₀] [GrpObj A₀'] (hA₀ : IsAbelianScheme A₀) (hA₀' : IsAbelianScheme A₀')
    {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' A'.hom)
    {L : LB A.left} {L' : LB A'.left} (u : HolUnif A L g) (u' : HolUnif A' L' g')
    {p : A.left ⟶ A₀.left} {p' : A'.left ⟶ A₀'.left} (hp : IsGrpPullback A A₀ (spMap (algebraMap k ℂ)) p)
    (hp' : IsGrpPullback A' A₀' (spMap (algebraMap k ℂ)) p') (f : A ⟶ A') [IsMonHom f] :
    ∃ f₀ : A₀ ⟶ A₀', IsMonHom f₀ ∧ f.left ≫ p' = p ≫ f₀.left := by
  obtain ⟨e, he, he1⟩ := grpPullback_iso hp (isGrpPullback_pullback A₀ (spMap (algebraMap k ℂ)))
  obtain ⟨e', he', he1'⟩ := grpPullback_iso hp' (isGrpPullback_pullback A₀' (spMap (algebraMap k ℂ)))
  obtain ⟨h1, h2⟩ := countable_and_ext hA hA' hg hg' u u'
  obtain ⟨f₀, hf₀, hf⟩ := descend_pullback A₀ A₀' hA₀ hA₀'
    ((h1.image fun g => e.inv ≫ g ≫ e'.hom).mono fun f hf => by
      have : IsMonHom f := hf
      exact ⟨e.hom ≫ f ≫ e'.inv, show IsMonHom _ from inferInstance, by simp⟩)
    (fun f f' hf hf' h => by
      have := h2 (e.hom ≫ f ≫ e'.inv) (e.hom ≫ f' ≫ e'.inv) inferInstance inferInstance fun v hv => by
        have := h _ (HomDescent.isTangent_comp e.hom hv)
        simp only [← Category.assoc] at this ⊢
        rw [this]
      simpa using this) (e.inv ≫ f ≫ e'.hom) inferInstance
  refine ⟨f₀, hf₀, ?_⟩
  rw [← he1, ← he1', Category.assoc]
  erw [← hf]
  rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  simp

/- English proof (translation)
Take `⟨M, hM, -, hW⟩` from `CMData.exists_field h2 io hio`. Take `⟨W, hΔ, hW⟩` from `hW 1`. Establish `hle : M ≤ algebraicClosure ℚ ℂ` using `fun x hx => mem_algebraicClosure_iff.2 (((IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).1 (Algebra.IsAlgebraic.isAlgebraic _)))`. Set `j : 𝓞 M →+* Qb` to `(IntermediateField.inclusion hle).toRingHom.comp (algebraMap (𝓞 M) M)`. Take `⟨P₀, t₀, hg, hb, -, hfib⟩` from `WeierstrassCurve.exists_polAV_invariants Qb (W.map j) (by`.

Rewrite using `[WeierstrassCurve.map_Δ]`. Conclude with `hΔ.map j)`. Take `⟨P, ψ, hP⟩` from `exists_isPolFibre polBaseChange_holds (algebraMap Qb ℂ) P₀`. Take `⟨t, ht, -⟩` from `existsUnique_isVecOver hP.2.1.1 t₀`. Establish `ht₀ : IsTangent t₀` using `hb.1 0`.

Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨w, Hm, χ, -, hAH, -, hd, -, -, hsec, -⟩` from `thetaUnifAV_all P rig hrig`. Take `⟨x, hx, -⟩` from `hd t (ht.isTangent hP.2.1 ht₀)`. Take `⟨hx0, L, hL, h4, -, hD⟩` from `hfib _ P ψ t w x hP ht hx`. Rewrite `h4` using `[WeierstrassCurve.map_c₄]`.

Rewrite `hD` using `[WeierstrassCurve.map_Δ]`. Take `⟨c, hc, hLc⟩` from `hW L h4 hD`. Take `⟨ev, hev, hev1⟩` from `EllipticHom.exists_coord (hP.1.trans hg) hx0`. Use `⟨P₀, t₀, P, ψ, t, w, Hm, χ, ev, x, c, ht₀, hP.2.1, ht, hAH, fun k θ h => ((hsec k).2 θ h).exists, hx, hev1, fun l hl => ?_, hc, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, e⟩` from `(hLc (ev l)).1 ((hL _).2 (by rwa [hev]))`.

Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Conclude with `⟨b, e⟩`. Establish `h12` using `DiscClass.latDisc_eq_of_mul Λ₀ L c hc fun z => by`. Rewrite using `[hLc, ← SetLike.mem_coe, hΛ₀]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, e⟩`. Conclude with `⟨a, ha, (mul_left_cancel₀ hc e).symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨a, ha, rfl⟩`. Use `IsAlgebraic.of_pow (n := 12) (by norm_num) ?_` and prove the remaining obligations.

Establish `e : (Ω₀ / c) ^ 12 = algebraMap Qb ℂ (j W.Δ)`. Rewrite using `[hD, div_pow, hΩ, h12, mul_div_cancel_left₀ _ (pow_ne_zero _ hc)]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mem_algebraicClosure_iff.1 (j W.Δ).2`.
-/
theorem exists_curve (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hio : ¬ ComplexEmbedding.IsReal io) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ₀ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    ∃ (P₀ : Out.PolAV (Sp Qb)) (t₀ : epsR Qb ⟶ P₀.A) (P : Out.PolAV (Sp ℂ)) (ψ : P.A.left ⟶ P₀.A.left) (t : epsR ℂ ⟶ P.A)
      (w : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : w.Λ → ℂ) (ev : (Fin P.g → ℂ) →ₗ[ℂ] ℂ)
      (x : Fin P.g → ℂ) (c : ℂ), IsTangent t₀ ∧ IsGrpPullback P.A P₀.A (spMap (algebraMap Qb ℂ)) ψ ∧
      IsVecOver (algebraMap Qb ℂ) ψ t₀ t ∧ w.IsAH Hm χ ∧ (∀ (k : ℕ) θ, w.IsThetaFn Hm χ k θ → ∃ s, w.IsFnPow k s θ) ∧
      w.IsDiff x t ∧ ev x = 1 ∧ (∀ l ∈ w.Λ, ∃ a : 𝓞 K, ev l = c * io a) ∧ c ≠ 0 ∧ IsAlgebraic ℚ (Ω₀ / c) := by
  obtain ⟨M, hM, -, hW⟩ := CMData.exists_field h2 io hio
  obtain ⟨W, hΔ, hW⟩ := hW 1
  have hle : M ≤ algebraicClosure ℚ ℂ := fun x hx =>
    mem_algebraicClosure_iff.2 (((IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).1 (Algebra.IsAlgebraic.isAlgebraic _)))
  let j : 𝓞 M →+* Qb := (IntermediateField.inclusion hle).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, t₀, hg, hb, -, hfib⟩ := WeierstrassCurve.exists_polAV_invariants Qb (W.map j) (by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map j)
  obtain ⟨P, ψ, hP⟩ := exists_isPolFibre polBaseChange_holds (algebraMap Qb ℂ) P₀
  obtain ⟨t, ht, -⟩ := existsUnique_isVecOver hP.2.1.1 t₀
  have ht₀ : IsTangent t₀ := hb.1 0
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨w, Hm, χ, -, hAH, -, hd, -, -, hsec, -⟩ := thetaUnifAV_all P rig hrig
  obtain ⟨x, hx, -⟩ := hd t (ht.isTangent hP.2.1 ht₀)
  obtain ⟨hx0, L, hL, h4, -, hD⟩ := hfib _ P ψ t w x hP ht hx
  rw [WeierstrassCurve.map_c₄] at h4
  rw [WeierstrassCurve.map_Δ] at hD
  obtain ⟨c, hc, hLc⟩ := hW L h4 hD
  obtain ⟨ev, hev, hev1⟩ := EllipticHom.exists_coord (hP.1.trans hg) hx0
  refine ⟨P₀, t₀, P, ψ, t, w, Hm, χ, ev, x, c, ht₀, hP.2.1, ht, hAH, fun k θ h => ((hsec k).2 θ h).exists, hx, hev1,
    fun l hl => ?_, hc, ?_⟩
  · obtain ⟨a, ha, e⟩ := (hLc (ev l)).1 ((hL _).2 (by rwa [hev]))
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    exact ⟨b, e⟩
  · have h12 := DiscClass.latDisc_eq_of_mul Λ₀ L c hc fun z => by
      rw [hLc, ← SetLike.mem_coe, hΛ₀]
      constructor
      · rintro ⟨a, ha, e⟩
        exact ⟨a, ha, (mul_left_cancel₀ hc e).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
    have e : (Ω₀ / c) ^ 12 = algebraMap Qb ℂ (j W.Δ) := by
      rw [hD, div_pow, hΩ, h12, mul_div_cancel_left₀ _ (pow_ne_zero _ hc)]
      rfl
    rw [e]
    exact mem_algebraicClosure_iff.1 (j W.Δ).2

section Span

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {σ : R →+* ℂ}
  {X₀ : RealMult.Obj F 𝔠 (Sp R)} {X : RealMult.Obj F 𝔠 (Sp ℂ)} {p : X.A.left ⟶ X₀.A.left}

/- English proof (translation)
Set `j : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR R` to `Over.homMk (spMap (Chart.dualMapR σ)) (PolFibre.spMap_dual_hom σ)`. Establish `h` using `hp.2 (epsR ℂ) v.hom w.hom (j ≫ v₀.hom) (j ≫ w₀.hom) hv.symm hw.symm`. Rewrite `h` using `[← MonObj.comp_mul]`. Conclude with `h.symm`.
-/
theorem lieCorr_add (hp : IsGrpPullback X.A X₀.A (spMap σ) p) {v₀ w₀ : X₀.Lie} {v w : X.Lie}
    (hv : Obj.LieCorr σ p v₀ v) (hw : Obj.LieCorr σ p w₀ w) : Obj.LieCorr σ p (v₀ + w₀) (v + w) := by
  let j : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR R :=
    Over.homMk (spMap (Chart.dualMapR σ)) (PolFibre.spMap_dual_hom σ)
  have h := hp.2 (epsR ℂ) v.hom w.hom (j ≫ v₀.hom) (j ≫ w₀.hom) hv.symm hw.symm
  rw [← MonObj.comp_mul] at h
  exact h.symm

/- English proof (translation)
Unfold `Obj.LieCorr at hv ⊢`. Rewrite using `[Serre.Lie.hom_smul_left, Serre.Lie.hom_smul_left, Category.assoc, hv, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, HomDerivDescent.epsScaleR_comp_dualMapR]`.
-/
theorem lieCorr_smul {v₀ : X₀.Lie} {v : X.Lie} (hv : Obj.LieCorr σ p v₀ v) (a : R) :
    Obj.LieCorr σ p (a • v₀) (σ a • v) := by
  unfold Obj.LieCorr at hv ⊢
  rw [Serre.Lie.hom_smul_left, Serre.Lie.hom_smul_left, Category.assoc, hv, ← Category.assoc, ← Category.assoc,
    spMap_comp_spMap, spMap_comp_spMap, HomDerivDescent.epsScaleR_comp_dualMapR]

variable {L : LB X.A.left} {g : ℕ} (u : HolUnif X.A L g)

/- English proof (translation)
Apply the tactic sequence `have h := isDiff_sum_smul_of_isLieComb X.A X.ab L g 2 u (fun i => (![v, w] i).hom) ![x, y] ![a, b] _ (fun i => Serre.Lie.isTangent _) (fun i => by fin_cases i <;> assumption) ((Serre.Lie.isLieComb_iff ![a, b] ![v, w] _).2 rfl)`. Simplify `h` using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]`.
-/
theorem isDiff_comb {v w : X.Lie} {x y : Fin g → ℂ} (hv : u.IsDiff x v.hom) (hw : u.IsDiff y w.hom) (a b : ℂ) :
    u.IsDiff (a • x + b • y) (a • v + b • w).hom := by
  have h := isDiff_sum_smul_of_isLieComb X.A X.ab L g 2 u (fun i => (![v, w] i).hom) ![x, y] ![a, b] _
    (fun i => Serre.Lie.isTangent _) (fun i => by fin_cases i <;> assumption)
    ((Serre.Lie.isLieComb_iff ![a, b] ![v, w] _).2 rfl)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/- English proof (translation)
Establish `hsm : ∀ (a : R) (x : Fin g → R), (∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ (x j)) v.hom) → ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ ((a • x) j)) v.hom`. Introduce and unpack `a x ⟨v₀, v, h1, h2⟩`. Use `⟨a • v₀, σ a • v, lieCorr_smul h1 a, ?_⟩` and prove the remaining obligations. Establish `h` using `isDiff_comb u h2 h2 (σ a) 0`. Rewrite `h` using `[zero_smul, zero_smul, add_zero, add_zero]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hs x hx`. Consider the case `zero`. Take `⟨y, hy⟩` from `h0`. Simplify `hsm 0 y (hs y hy)` using `only [zero_smul]`. Consider the case `add x y _ _ hx hy`.

Take `⟨v₀, v, h1, h2⟩` from `hx`. Take `⟨w₀, w, h3, h4⟩` from `hy`. Use `⟨v₀ + w₀, v + w, lieCorr_add hp h1 h3, ?_⟩` and prove the remaining obligations. Establish `h` using `isDiff_comb u h2 h4 1 1`. Simplify using `only [one_smul] at h`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `only [Pi.add_apply, map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a x _ hx => exact hsm a x hx`.
-/
theorem descends_of_mem_span (hp : IsGrpPullback X.A X₀.A (spMap σ) p) (κ : ℂ) (s : Set (Fin g → R))
    (hs : ∀ x ∈ s, ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ (x j)) v.hom)
    (h0 : s.Nonempty) (x : Fin g → R) (hx : x ∈ Submodule.span R s) :
    ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ (x j)) v.hom := by
  have hsm : ∀ (a : R) (x : Fin g → R),
      (∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ (x j)) v.hom) →
      ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr σ p v₀ v ∧ u.IsDiff (fun j => κ * σ ((a • x) j)) v.hom := by
    rintro a x ⟨v₀, v, h1, h2⟩
    refine ⟨a • v₀, σ a • v, lieCorr_smul h1 a, ?_⟩
    have h := isDiff_comb u h2 h2 (σ a) 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at h
    convert h using 1
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    obtain ⟨y, hy⟩ := h0
    simpa only [zero_smul] using hsm 0 y (hs y hy)
  | add x y _ _ hx hy =>
    obtain ⟨v₀, v, h1, h2⟩ := hx
    obtain ⟨w₀, w, h3, h4⟩ := hy
    refine ⟨v₀ + w₀, v + w, lieCorr_add hp h1 h3, ?_⟩
    have h := isDiff_comb u h2 h4 1 1
    simp only [one_smul] at h
    convert h using 1
    ext j
    simp only [Pi.add_apply, map_add]
    ring
  | smul a x _ hx => exact hsm a x hx

end Span

/- English proof (translation)
Introduce `_ _ _ K _ _ d δ io h2 hd hδ Λ₀ Ω₀ hΛ₀ hΩ E _ _ _ _ I _ φ hφ hK c y hc 𝔠 X U X₀ p hp`. Establish `hio : ¬ ComplexEmbedding.IsReal io` using `fun h => by`. Establish `h1 : (h.embedding δ) ^ 2 = -(d : ℝ)` using `by rw [← map_pow, hδ, map_neg, map_natCast]`. Establish `h3 : (0 : ℝ) < d` using `by exact_mod_cast hd`. Use polynomial arithmetic with `[sq_nonneg (h.embedding δ)]`.

Take `⟨P₀, t₀, P, ψ, t, w, Hm, χ, ev, x, ϖ, ht₀, hψ, ht, hAH, hsec, hx, hev, hΛ, hϖ, halg⟩` from `exists_curve K io h2 hio Λ₀ Ω₀ hΛ₀ hΩ`. Take `⟨N, hN, hNL, -⟩` from `LatBound.lattice_between E c hc y`. Take `⟨m, hm, hhom⟩` from `exists_hom_nsmul X.A _ X.ab X.dim _ U.u`. Use `haveI : Countable Qb := (Algebraic.countable ℚ ℂ).mono (fun z hz => mem_algebraicClosure_iff.1 hz) |>.to_subtype`. Use `haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed`.

Set `φ₀ : I → E →+* Qb` to `fun i => (φ i).codRestrict (algebraicClosure ℚ ℂ) fun b => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) b).algHom (φ i).toRatAlgHom)`. Establish `hinj : Function.Injective fun j => ((φ₀ (U.e j)).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom : 𝓞 E →* Qb)`. Introduce `j j' h`. Establish `e : φ (U.e j) = φ (U.e j')` using `IsFractionRing.ringHom_ext (A := 𝓞 E) fun b => congrArg Subtype.val (DFunLike.congr_fun h b)`. Conclude with `U.e.injective ((hφ (φ (U.e j))).unique (Or.inl rfl) (Or.inl e))`.

Establish `hsp` using `span_flip_eq_top_iff_linearIndependent.2 ((linearIndependent_monoidHom (𝓞 E) Qb).comp _ hinj)`. Establish `key : ∀ i, ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr (algebraMap Qb ℂ) p v₀ v ∧ U.u.IsDiff (Pi.single (U.e.symm i) ((m : ℂ) * N / ϖ)) v.hom` using `fun i => by`. Establish `e₁ : (Pi.single (U.e.symm i) ((m : ℂ) * N / ϖ) : Fin (Module.finrank ℚ (FR E)) → ℂ) = fun j => (m : ℂ) * N / ϖ * algebraMap Qb ℂ ((Pi.single (U.e.symm i) 1 : Fin (Module.finrank ℚ (FR E)) → Qb) j)`. Use extensionality with `j`. Apply the tactic sequence `by_cases hj : j = U.e.symm i <;> simp [hj]`.

Rewrite using `[e₁]`. Use `descends_of_mem_span U.u hp.grp ((m : ℂ) * N / ϖ) _ ?_ (Set.range_nonempty _) (Pi.single (U.e.symm i) 1) (hsp ▸ Submodule.mem_top)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Set `F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)` to `ev.smulRight fun j => N / ϖ * φ (U.e j) (algebraMap (𝓞 E) E b)`. Take `⟨f, hf, hfe⟩` from `hhom P w Hm χ hAH hsec F fun l hl => by`.

Take `⟨a, ha⟩` from `hΛ l hl`. Use `(U.lat _).2 ⟨_, hNL (algebraMap (𝓞 K) (𝓞 E) a * b), ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Establish `e : φ (U.e j) (algebraMap (𝓞 E) E (algebraMap (𝓞 K) (𝓞 E) a)) = io a`. Rewrite using `[← hK (U.e j)]`.

Both sides reduce to the same expression. Simplify using `only [F, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul, ha, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero, map_mul, map_natCast, e]`. Clear the denominators using the available nonvanishing facts. Take `⟨f₀, hf₀, hff⟩` from `descend P₀.isAb X₀.ab P.isAb X.ab P.smoothDim X.dim w U.u hψ hp.grp f`. Establish `htt` using `ht.isTangent hψ ht₀`.

Use `⟨Serre.Lie.mk _ (t₀ ≫ f₀) (HomLinear.isTangent_comp f₀ ht₀), Serre.Lie.mk _ (t ≫ f) (HomLinear.isTangent_comp f htt), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(t ≫ f).left ≫ p = _ ≫ (t₀ ≫ f₀).left`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, hff, ← Category.assoc, ht, Category.assoc]`. Establish `h` using `HomLinear.isDiff_comp w U.u f _ hfe htt hx`. Rewrite using `[Serre.Lie.hom_mk]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `only [F, LinearMap.smul_apply, LinearMap.smulRight_apply, hev, Pi.smul_apply, smul_eq_mul, _root_.one_mul]`. Express the relevant statement in the definitionally equal form `_ * φ (U.e j) (algebraMap (𝓞 E) E b) = _`. Expand and normalize the polynomial expressions, which then agree.

Use `choose v₀ v h1 h3 using key`. Establish `hm0 : (m : ℂ) ≠ 0` using `by exact_mod_cast (show m ≠ 0 by omega)`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `⟨v₀, v, fun _ => (m : ℂ) * N / ϖ, fun i => ⟨?_, ?_, div_ne_zero (mul_ne_zero hm0 hN0) hϖ, ?_⟩⟩` and prove the remaining obligations. Conclude with `h1 i`.

Use `h3 i` and compare the differences between its conclusion and the goal. Establish `e : (m : ℂ) * N / ϖ * Ω₀ = ((m * N : ℕ) : ℂ) * (Ω₀ / ϖ)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `(isAlgebraic_nat _).mul halg`.
-/
theorem exists_lie_frame : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X) (X₀ : Obj (FR E) 𝔠 (Sp Qb))
        (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∃ (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        ∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀) := by
  intro _ _ _ K _ _ d δ io h2 hd hδ Λ₀ Ω₀ hΛ₀ hΩ E _ _ _ _ I _ φ hφ hK c y hc 𝔠 X U X₀ p hp
  classical
  have hio : ¬ ComplexEmbedding.IsReal io := fun h => by
    have h1 : (h.embedding δ) ^ 2 = -(d : ℝ) := by rw [← map_pow, hδ, map_neg, map_natCast]
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (h.embedding δ)]
  obtain ⟨P₀, t₀, P, ψ, t, w, Hm, χ, ev, x, ϖ, ht₀, hψ, ht, hAH, hsec, hx, hev, hΛ, hϖ, halg⟩ :=
    exists_curve K io h2 hio Λ₀ Ω₀ hΛ₀ hΩ
  obtain ⟨N, hN, hNL, -⟩ := LatBound.lattice_between E c hc y
  obtain ⟨m, hm, hhom⟩ := exists_hom_nsmul X.A _ X.ab X.dim _ U.u
  haveI : Countable Qb := (Algebraic.countable ℚ ℂ).mono (fun z hz => mem_algebraicClosure_iff.1 hz) |>.to_subtype
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let φ₀ : I → E →+* Qb := fun i => (φ i).codRestrict (algebraicClosure ℚ ℂ) fun b =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) b).algHom (φ i).toRatAlgHom)
  have hinj : Function.Injective fun j => ((φ₀ (U.e j)).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom : 𝓞 E →* Qb) := by
    intro j j' h
    have e : φ (U.e j) = φ (U.e j') := IsFractionRing.ringHom_ext (A := 𝓞 E) fun b =>
      congrArg Subtype.val (DFunLike.congr_fun h b)
    exact U.e.injective ((hφ (φ (U.e j))).unique (Or.inl rfl) (Or.inl e))
  have hsp := span_flip_eq_top_iff_linearIndependent.2 ((linearIndependent_monoidHom (𝓞 E) Qb).comp _ hinj)
  have key : ∀ i, ∃ (v₀ : X₀.Lie) (v : X.Lie), Obj.LieCorr (algebraMap Qb ℂ) p v₀ v ∧
      U.u.IsDiff (Pi.single (U.e.symm i) ((m : ℂ) * N / ϖ)) v.hom := fun i => by
    have e₁ : (Pi.single (U.e.symm i) ((m : ℂ) * N / ϖ) : Fin (Module.finrank ℚ (FR E)) → ℂ) = fun j => (m : ℂ) * N / ϖ *
        algebraMap Qb ℂ ((Pi.single (U.e.symm i) 1 : Fin (Module.finrank ℚ (FR E)) → Qb) j) := by
      ext j
      by_cases hj : j = U.e.symm i <;> simp [hj]
    rw [e₁]
    refine descends_of_mem_span U.u hp.grp ((m : ℂ) * N / ϖ) _ ?_ (Set.range_nonempty _)
      (Pi.single (U.e.symm i) 1) (hsp ▸ Submodule.mem_top)
    rintro _ ⟨b, rfl⟩
    let F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      ev.smulRight fun j => N / ϖ * φ (U.e j) (algebraMap (𝓞 E) E b)
    obtain ⟨f, hf, hfe⟩ := hhom P w Hm χ hAH hsec F fun l hl => by
      obtain ⟨a, ha⟩ := hΛ l hl
      refine (U.lat _).2 ⟨_, hNL (algebraMap (𝓞 K) (𝓞 E) a * b), ?_⟩
      ext j
      have e : φ (U.e j) (algebraMap (𝓞 E) E (algebraMap (𝓞 K) (𝓞 E) a)) = io a := by
        rw [← hK (U.e j)]; rfl
      simp only [F, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul, ha, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply,
        zero_mul, add_zero, map_mul, map_natCast, e]
      field_simp
    obtain ⟨f₀, hf₀, hff⟩ := descend P₀.isAb X₀.ab P.isAb X.ab P.smoothDim X.dim w U.u hψ hp.grp f
    have htt := ht.isTangent hψ ht₀
    refine ⟨Serre.Lie.mk _ (t₀ ≫ f₀) (HomLinear.isTangent_comp f₀ ht₀), Serre.Lie.mk _ (t ≫ f) (HomLinear.isTangent_comp f htt),
      ?_, ?_⟩
    · change (t ≫ f).left ≫ p = _ ≫ (t₀ ≫ f₀).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hff, ← Category.assoc, ht, Category.assoc]
    · have h := HomLinear.isDiff_comp w U.u f _ hfe htt hx
      rw [Serre.Lie.hom_mk]
      convert h using 1
      ext j
      simp only [F, LinearMap.smul_apply, LinearMap.smulRight_apply, hev, Pi.smul_apply, smul_eq_mul, _root_.one_mul]
      change _ * φ (U.e j) (algebraMap (𝓞 E) E b) = _
      ring
  choose v₀ v h1 h3 using key
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨v₀, v, fun _ => (m : ℂ) * N / ϖ, fun i => ⟨?_, ?_, div_ne_zero (mul_ne_zero hm0 hN0) hϖ, ?_⟩⟩
  · exact h1 i
  · convert h3 i
  · have e : (m : ℂ) * N / ϖ * Ω₀ = ((m * N : ℕ) : ℂ) * (Ω₀ / ϖ) := by push_cast; ring
    rw [e]
    exact (isAlgebraic_nat _).mul halg

end GlobalTheory.CMLiePeriod
