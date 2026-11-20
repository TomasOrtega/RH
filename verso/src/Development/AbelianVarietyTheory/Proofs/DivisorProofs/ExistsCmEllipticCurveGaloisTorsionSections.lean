import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtDvrOfCardTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionModel

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := B)`. Establish `hi : ∀ b : B, IsIntegral ℤ b` using `fun b => IsIntegral.of_finite ℤ b`. Use `choose p hp hp' using hi`. Set `q : Polynomial ℚ` to `(∏ b ∈ s, p b).map (algebraMap ℤ ℚ)`. Establish `hq : q.Monic` using `(Polynomial.monic_prod_of_monic _ _ fun b _ => hp b).map _`.

Set `N : IntermediateField ℚ ℂ` to `IntermediateField.adjoin ℚ (q.rootSet ℂ)`. Establish `hN : Polynomial.IsSplittingField ℚ N q` using `IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Establish `: FiniteDimensional ℚ N` using `Polynomial.IsSplittingField.finiteDimensional N q`. Establish `: Normal ℚ N` using `Normal.of_isSplittingField q`. Establish `: NumberField N` using `⟨⟩`.

Use `⟨N, inferInstance, ⟨⟩, fun χ => ?_⟩` and prove the remaining obligations. Establish `hm : ∀ b, χ b ∈ N` using `fun b => by`. Establish `hb : b ∈ Submodule.span ℤ (s : Set B)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem c hc`.

Use `IntermediateField.subset_adjoin ℚ _ (Polynomial.mem_rootSet.2 ⟨hq.ne_zero, ?_⟩)` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_map_algebraMap, map_prod]`. Use `Finset.prod_eq_zero hc ?_` and prove the remaining obligations. Establish `h` using `congrArg χ (hp' c)`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`.

Rewrite using `[Polynomial.aeval_def, ← h]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add _ _ _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul r c _ hc => rw [map_zsmul]`. Conclude with `zsmul_mem hc r`. Set `χ₁ : B →+* N` to `χ.codRestrict N hm`.

Conclude with `⟨χ₁.codRestrict (integralClosure ℤ N) fun b => (IsIntegral.of_finite ℤ b).map χ₁.toIntAlgHom, rfl⟩`.
-/
theorem exists_galois (B : Type) [CommRing B] [Module.Finite ℤ B] :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N), ∀ χ : B →+* ℂ,
      ∃ χ' : B →+* 𝓞 N, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp χ' = χ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have hi : ∀ b : B, IsIntegral ℤ b := fun b => IsIntegral.of_finite ℤ b
  choose p hp hp' using hi
  let q : Polynomial ℚ := (∏ b ∈ s, p b).map (algebraMap ℤ ℚ)
  have hq : q.Monic := (Polynomial.monic_prod_of_monic _ _ fun b _ => hp b).map _
  let N : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (q.rootSet ℂ)
  have hN : Polynomial.IsSplittingField ℚ N q :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ N := Polynomial.IsSplittingField.finiteDimensional N q
  have : Normal ℚ N := Normal.of_isSplittingField q
  have : NumberField N := ⟨⟩
  refine ⟨N, inferInstance, ⟨⟩, fun χ => ?_⟩
  have hm : ∀ b, χ b ∈ N := fun b => by
    have hb : b ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc =>
      refine IntermediateField.subset_adjoin ℚ _ (Polynomial.mem_rootSet.2 ⟨hq.ne_zero, ?_⟩)
      rw [Polynomial.aeval_map_algebraMap, map_prod]
      refine Finset.prod_eq_zero hc ?_
      have h := congrArg χ (hp' c)
      rw [Polynomial.hom_eval₂, map_zero] at h
      rw [Polynomial.aeval_def, ← h]
      congr 1
      exact RingHom.ext_int _ _
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r c _ hc => rw [map_zsmul]; exact zsmul_mem hc r
  let χ₁ : B →+* N := χ.codRestrict N hm
  exact ⟨χ₁.codRestrict (integralClosure ℤ N) fun b => (IsIntegral.of_finite ℤ b).map χ₁.toIntAlgHom, rfl⟩

/- English proof (translation)
Establish `: IsAffine Z` using `isAffine_of_isAffineHom q`. Take `⟨g, hg⟩` from `Spec.map_surjective (Z.isoSpec.inv ≫ q)`. Use `⟨Γ(Z, ⊤), inferInstance, g.hom, Z.isoSpec.symm, ?_, hg.symm⟩` and prove the remaining obligations. Establish `: IsFinite (Spec.map g)` using `by rw [hg]; infer_instance`. Conclude with `(IsFinite.SpecMap_iff g).1 this`.
-/
theorem exists_finite_ring {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) [IsFinite q] :
    ∃ (B : Type) (_ : CommRing B) (g : R →+* B) (e : Sp B ≅ Z), g.Finite ∧ e.hom ≫ q = spMap g := by
  have : IsAffine Z := isAffine_of_isAffineHom q
  obtain ⟨g, hg⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ q)
  refine ⟨Γ(Z, ⊤), inferInstance, g.hom, Z.isoSpec.symm, ?_, hg.symm⟩
  have : IsFinite (Spec.map g) := by rw [hg]; infer_instance
  exact (IsFinite.SpecMap_iff g).1 this

/- English proof (translation)
Establish `: IsNoetherianRing R` using `IsNoetherianRing.of_finite ℤ R`. Use `(hM _ P n hn).1` as an intermediate fact. Set `η₀ : Sp R ⟶ P.A.left` to `(η[P.A]).left`. Establish `hη : η₀ ≫ P.A.hom = 𝟙 _` using `Over.w η[P.A]`. Establish `hw : (Out.mulA P.A n).left ≫ P.A.hom = P.A.hom` using `Over.w _`.

Establish `key : ∀ {T : Over (Sp R)} (x : T ⟶ P.A), x ^ n = 1 ↔ x.left ≫ (Out.mulA P.A n).left = T.hom ≫ η₀`. Introduce `T x`. Establish `e₁ : x ≫ Out.mulA P.A n = x ^ n` using `by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]`. Establish `e₂ : (1 : T ⟶ P.A).left = T.hom ≫ η₀` using `by rw [Hom.one_def]; simp [η₀]`. Rewrite using `[← Over.comp_left, e₁, ← e₂]`.

Conclude with `⟨fun h => by rw [h], Over.OverMorphism.ext⟩`. Take `⟨B, _, g, e, hg, he⟩` from `exists_finite_ring (pullback.snd (Out.mulA P.A n).left η₀)`. Establish `: Module.Finite ℤ B`. Establish `h` using `RingHom.Finite.comp hg (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℤ R))`. Rewrite `h` using `[RingHom.ext_int (g.comp _) (algebraMap ℤ B)]`.

Conclude with `RingHom.finite_algebraMap.1 h`. Take `⟨N, _, _, hN⟩` from `exists_galois B`. Establish `main : ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ χ' : B →+* 𝓞 N, (∀ r, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) (χ' (g r)) = σ r) ∧ spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' ≫ e.hom ≫ pullback.fst _ _ = x.left`. Introduce `x hx`. Take `⟨χ, hχ⟩` from `Spec.map_surjective (pullback.lift x.left (spMap σ) ((key x).1 hx) ≫ e.inv)`.

Take `⟨χ', h⟩` from `hN χ.hom`. Establish `e₁ : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' = Spec.map χ` using `Ex.UnifModel.spMap_comp fun r => congr($h r)`. Use `⟨χ', fun r => ?_, by rw [reassoc_of% e₁, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]⟩` and prove the remaining obligations. Establish `e₂ : Spec.map χ ≫ spMap g = spMap σ`. Rewrite using `[← he, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]`.

Rewrite `e₂` using `[← Spec.map_comp]`. Conclude with `(congr($h (g r))).trans (congrArg (fun f => f.hom r) (Spec.map_injective e₂))`. Take `⟨χ₀, h₀, -⟩` from `main 1 (one_pow n)`. Use `⟨N, inferInstance, inferInstance, χ₀.comp g, RingHom.ext h₀, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨χ', h₁, h₂⟩` from `main x hx`.

Establish `e₁ : spMap χ' ≫ spMap g = spMap (χ₀.comp g)` using `Ex.UnifModel.spMap_comp fun r => RingOfIntegers.coe_injective ((algebraMap N ℂ).injective ((h₁ r).trans (h₀ r).symm))`. Establish `e₂ : (spMap χ' ≫ e.hom ≫ pullback.fst _ _) ≫ (Out.mulA P.A n).left = spMap (χ₀.comp g) ≫ η₀`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% e₁]`. Conclude with `⟨Over.homMk (spMap χ' ≫ e.hom ≫ pullback.fst _ _) (by`. Rewrite using `[← hw, ← Category.assoc, e₂, Category.assoc, hη]`.

Conclude with `Category.comp_id _), (key _).2 e₂, h₂⟩`.
-/
theorem exists_integral_points (hM : Out.MulNSt) {R : Type} [CommRing R] [Module.Finite ℤ R] (P : Out.PolAV (Sp R))
    (σ : R →+* ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (f : R →+* 𝓞 N),
      ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp f = σ ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 →
        ∃ y : Over.mk (spMap f) ⟶ P.A, y ^ n = 1 ∧
          spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left = x.left := by
  have : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ R
  have := (hM _ P n hn).1
  let η₀ : Sp R ⟶ P.A.left := (η[P.A]).left
  have hη : η₀ ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hw : (Out.mulA P.A n).left ≫ P.A.hom = P.A.hom := Over.w _
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ P.A), x ^ n = 1 ↔ x.left ≫ (Out.mulA P.A n).left = T.hom ≫ η₀ := by
    intro T x
    have e₁ : x ≫ Out.mulA P.A n = x ^ n := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : (1 : T ⟶ P.A).left = T.hom ≫ η₀ := by rw [Hom.one_def]; simp [η₀]
    rw [← Over.comp_left, e₁, ← e₂]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  obtain ⟨B, _, g, e, hg, he⟩ := exists_finite_ring (pullback.snd (Out.mulA P.A n).left η₀)
  have : Module.Finite ℤ B := by
    have h := RingHom.Finite.comp hg (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℤ R))
    rw [RingHom.ext_int (g.comp _) (algebraMap ℤ B)] at h
    exact RingHom.finite_algebraMap.1 h
  obtain ⟨N, _, _, hN⟩ := exists_galois B
  have main : ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ χ' : B →+* 𝓞 N,
      (∀ r, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) (χ' (g r)) = σ r) ∧
      spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' ≫ e.hom ≫ pullback.fst _ _ = x.left := by
    intro x hx
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (pullback.lift x.left (spMap σ) ((key x).1 hx) ≫ e.inv)
    obtain ⟨χ', h⟩ := hN χ.hom
    have e₁ : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' = Spec.map χ :=
      Ex.UnifModel.spMap_comp fun r => congr($h r)
    refine ⟨χ', fun r => ?_, by rw [reassoc_of% e₁, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]⟩
    have e₂ : Spec.map χ ≫ spMap g = spMap σ := by
      rw [← he, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    rw [← Spec.map_comp] at e₂
    exact (congr($h (g r))).trans (congrArg (fun f => f.hom r) (Spec.map_injective e₂))
  obtain ⟨χ₀, h₀, -⟩ := main 1 (one_pow n)
  refine ⟨N, inferInstance, inferInstance, χ₀.comp g, RingHom.ext h₀, fun x hx => ?_⟩
  obtain ⟨χ', h₁, h₂⟩ := main x hx
  have e₁ : spMap χ' ≫ spMap g = spMap (χ₀.comp g) := Ex.UnifModel.spMap_comp fun r =>
    RingOfIntegers.coe_injective ((algebraMap N ℂ).injective ((h₁ r).trans (h₀ r).symm))
  have e₂ : (spMap χ' ≫ e.hom ≫ pullback.fst _ _) ≫ (Out.mulA P.A n).left = spMap (χ₀.comp g) ≫ η₀ := by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% e₁]
  exact ⟨Over.homMk (spMap χ' ≫ e.hom ≫ pullback.fst _ _) (by
    rw [← hw, ← Category.assoc, e₂, Category.assoc, hη]; exact Category.comp_id _), (key _).2 e₂, h₂⟩

/- English proof (translation)
Establish `: NeZero H.d` using `⟨H.d_prime.ne_zero⟩`. Take `⟨χ, hχ⟩` from `exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))`. Take `⟨M, _, ω, C, -, hω, hC, -⟩` from `CM.EllExists.exists_ell cmCurve_closed thetaUnifAV_all firstFiveLaws.1 (CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional) E H χ hχ H.rt0 H.sqrt_neg_disc_sq`. Take `⟨Q, ψ, hψ⟩` from `exists_isPolFibre firstFiveLaws.1.polBaseChange ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) C.P`. Take `⟨u, hu⟩` from `PureType.exists_isThetaUnif thetaUnifAV_all Q`.

Take `⟨c, hc, hΛ⟩` from `hC Q ψ hψ u`. Use `⟨M, inferInstance, ω, C, ⟨Q, hψ.1.trans C.dim, u, hu, c, hc, hΛ⟩, ψ, ?_, hψ.2.1⟩` and prove the remaining obligations. Use `RingOfIntegers.coe_injective ((algebraMap M ℂ).injective ?_)` and prove the remaining obligations. Rewrite using `[← RingHom.comp_apply, ← RingHom.comp_apply]`. Rewrite using `[map_pow, map_sub, map_mul, map_one, map_ofNat, map_neg, map_natCast, ← H.sqrt_neg_disc_sq, ← hω]`.

Both sides reduce to the same expression.
-/
theorem exists_ell_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : GlobalTheory.CM.Ell H (𝓞 M) ω) (C₀ : GlobalTheory.CompRat.Curve H)
      (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 M) ∧
      IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) ψ := by
  have : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨M, _, ω, C, -, hω, hC, -⟩ := CM.EllExists.exists_ell cmCurve_closed thetaUnifAV_all firstFiveLaws.1
    (CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional) E H χ hχ H.rt0 H.sqrt_neg_disc_sq
  obtain ⟨Q, ψ, hψ⟩ := exists_isPolFibre firstFiveLaws.1.polBaseChange
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) C.P
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif thetaUnifAV_all Q
  obtain ⟨c, hc, hΛ⟩ := hC Q ψ hψ u
  refine ⟨M, inferInstance, ω, C, ⟨Q, hψ.1.trans C.dim, u, hu, c, hc, hΛ⟩, ψ, ?_, hψ.2.1⟩
  refine RingOfIntegers.coe_injective ((algebraMap M ℂ).injective ?_)
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_neg, map_natCast, ← H.sqrt_neg_disc_sq, ← hω]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H n hn`. Take `⟨M, _, ω, C, C₀, ψ, hω, hψ⟩` from `exists_ell_fibre H`. Take `⟨N, _, _, f, hf, hN⟩` from `exists_integral_points firstFiveLaws.1.mulN C.P ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) hn`. Take `⟨C', φ, -, ⟨-, hφ, -⟩, -⟩` from `CM.exists_ellMap firstFiveLaws.1.polBaseChange E H _ ω C _ f`. Establish `e : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap f = spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))` using `Ex.UnifModel.spMap_comp fun r => congr($hf r)`.

Establish `w : ψ ≫ C.P.A.hom = (C₀.P.A.hom ≫ spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ≫ spMap f`. Rewrite using `[Category.assoc, e, hψ.1.w]`. Use `⟨N, inferInstance, inferInstance, f ω, C', C₀, hφ.1.lift _ _ w, by simpa [map_ofNat] using congrArg f hω, hφ.cancel (hψ.congr e.symm (hφ.1.lift_fst _ _ w).symm) (hφ.1.lift_snd _ _ w), fun a => ?_⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) _ (Category.id_comp _).symm`. Take `⟨ε', hε'⟩` from `exists_mulEquiv_of_isGrpPullback hφ (𝟙 (Sp (𝓞 N))) _ (Category.id_comp _).symm`.

Take `⟨y, hy, hy'⟩` from `hN (ε (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))) (by`. Rewrite using `[← map_pow]`. Conclude with `(congrArg ε (CurveField.ex_pow_eq_one C₀ hn a)).trans (map_one ε))`. Take `⟨z, rfl⟩` from `ε'.surjective y`. Rewrite `hy'` using `[hε, hε']`.

Use `⟨z, ε'.injective (by rw [map_pow, hy, map_one]), ?_⟩` and prove the remaining obligations. Establish `ho : C₀.pt (CompRat.wC H a / n) ≫ C₀.P.A.hom = 𝟙 _` using `Over.w (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))`. Establish `hz : z.left ≫ C'.P.A.hom = 𝟙 (Sp (𝓞 N))` using `Over.w z`. Use `hφ.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hφ.1.lift_fst, Category.assoc]`.

Conclude with `hy'.symm`. Rewrite using `[Category.assoc, hφ.1.lift_snd, Category.assoc, hz, reassoc_of% ho]`. Conclude with `(Category.comp_id _).symm`.
-/
theorem exists_ell_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  intro E _ _ _ H n hn
  obtain ⟨M, _, ω, C, C₀, ψ, hω, hψ⟩ := exists_ell_fibre H
  obtain ⟨N, _, _, f, hf, hN⟩ := exists_integral_points firstFiveLaws.1.mulN C.P
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) hn
  obtain ⟨C', φ, -, ⟨-, hφ, -⟩, -⟩ := CM.exists_ellMap firstFiveLaws.1.polBaseChange E H _ ω C _ f
  have e : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap f =
      spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) := Ex.UnifModel.spMap_comp fun r => congr($hf r)
  have w : ψ ≫ C.P.A.hom = (C₀.P.A.hom ≫ spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ≫ spMap f := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨N, inferInstance, inferInstance, f ω, C', C₀, hφ.1.lift _ _ w, by simpa [map_ofNat] using congrArg f hω,
    hφ.cancel (hψ.congr e.symm (hφ.1.lift_fst _ _ w).symm) (hφ.1.lift_snd _ _ w), fun a => ?_⟩
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) _ (Category.id_comp _).symm
  obtain ⟨ε', hε'⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 (Sp (𝓞 N))) _ (Category.id_comp _).symm
  obtain ⟨y, hy, hy'⟩ := hN (ε (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (CurveField.ex_pow_eq_one C₀ hn a)).trans (map_one ε))
  obtain ⟨z, rfl⟩ := ε'.surjective y
  rw [hε, hε'] at hy'
  refine ⟨z, ε'.injective (by rw [map_pow, hy, map_one]), ?_⟩
  have ho : C₀.pt (CompRat.wC H a / n) ≫ C₀.P.A.hom = 𝟙 _ := Over.w (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))
  have hz : z.left ≫ C'.P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w z
  refine hφ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hφ.1.lift_fst, Category.assoc]
    exact hy'.symm
  · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, hz, reassoc_of% ho]
    exact (Category.comp_id _).symm

end GlobalTheory.TorsionModel
