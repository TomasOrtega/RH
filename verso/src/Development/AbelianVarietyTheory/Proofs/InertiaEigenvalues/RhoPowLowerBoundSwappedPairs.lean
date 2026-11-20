import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ha hϖ`. Use `haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›`. Use `haveI : Finite (O ⧸ Ideal.span {a}) := by`. Rewrite using `[Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]`.

Conclude with `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k`. Use `haveI : Module.Finite O R := Module.Finite.iff_fg.2 hR`. Use `set J : Submodule O R := Ideal.span {a} • (⊤ : Submodule O R) with hJ`. Use `haveI hQ : Finite (R ⧸ J) := Submodule.finite_quotient_smul (Ideal.span {a}) (N := ⊤) Module.Finite.fg_top`. Establish `hJle : ∀ N : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N}, J ≤ N.1.comap R.subtype`.

Introduce `N x hx`. Rewrite `hx` using `[hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨y, -, rfl⟩` from `hx`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul]`. Conclude with `N.2.2 _ y.2`.

Set `φ : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} → Set (R ⧸ J)` to `fun N => ((N.1.comap R.subtype).map J.mkQ : Set (R ⧸ J))`. Use `Finite.of_injective φ ?_` and prove the remaining obligations. Introduce `N N' h`. Establish `h1 : (N.1.comap R.subtype).map J.mkQ = (N'.1.comap R.subtype).map J.mkQ` using `SetLike.coe_injective h`. Establish `h2` using `congrArg (Submodule.comap J.mkQ) h1`.

Rewrite `h2` using `[Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hJle N), sup_eq_right.2 (hJle N')]`. Establish `h3` using `congrArg (Submodule.map R.subtype) h2`. Rewrite `h3` using `[Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 N.2.1, inf_eq_right.2 N'.2.1]`. Conclude with `Subtype.ext h3`.
-/
theorem finite_between (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (R : Submodule O A) (hR : R.FG)
    (a : O) (ha : a ≠ 0) : Finite {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {a}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  haveI : Module.Finite O R := Module.Finite.iff_fg.2 hR
  set J : Submodule O R := Ideal.span {a} • (⊤ : Submodule O R) with hJ
  haveI hQ : Finite (R ⧸ J) := Submodule.finite_quotient_smul (Ideal.span {a}) (N := ⊤) Module.Finite.fg_top
  have hJle : ∀ N : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N}, J ≤ N.1.comap R.subtype := by
    intro N x hx
    rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul]
    exact N.2.2 _ y.2
  let φ : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} → Set (R ⧸ J) := fun N =>
    ((N.1.comap R.subtype).map J.mkQ : Set (R ⧸ J))
  refine Finite.of_injective φ ?_
  intro N N' h
  have h1 : (N.1.comap R.subtype).map J.mkQ = (N'.1.comap R.subtype).map J.mkQ := SetLike.coe_injective h
  have h2 := congrArg (Submodule.comap J.mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hJle N),
    sup_eq_right.2 (hJle N')] at h2
  have h3 := congrArg (Submodule.map R.subtype) h2
  rw [Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype,
    inf_eq_right.2 N.2.1, inf_eq_right.2 N'.2.1] at h3
  exact Subtype.ext h3

/- English proof (translation)
Take `⟨p, hpm, hp⟩` from `hy`. Use `choose cO hcO using K.c_int`. Establish `hinj : Function.Injective (algebraMap K.O K.E)` using `IsFractionRing.injective K.O K.E`. Set `ψ : K.O →+* K.O` to `{ toFun := cO map_one' := hinj (by rw [← hcO, map_one, map_one]) map_mul' := fun x y => hinj (by rw [← hcO, map_mul, map_mul, map_mul, hcO, hcO]) map_zero' := hinj (by rw [← hcO, map_zero, map_zero]) map_add' := fun x y => hinj (by rw [← hcO, map_add, map_add, map_add, hcO, hcO]) …`. Establish `hcomp : (algebraMap K.O B.A).comp ψ = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A)`.

Use extensionality with `x`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]`. Use `show _ = algebraMap K.E B.A (K.c (algebraMap K.O K.E x))`. Rewrite using `[hcO]`.

Both sides reduce to the same expression. Use `⟨p.map ψ, hpm.map ψ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hcomp]`. Use `Polynomial.hom_eval₂ p (algebraMap K.O B.A) (B.σ : B.A →+* B.A) y` as an intermediate fact. Conclude with `this.symm.trans (by rw [hp, map_zero])`.
-/
theorem isIntegral_sigma (K : UQ) (B : InvAlg K) (y : B.A) (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hpm, hp⟩ := hy
  choose cO hcO using K.c_int
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  let ψ : K.O →+* K.O :=
    { toFun := cO
      map_one' := hinj (by rw [← hcO, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [← hcO, map_mul, map_mul, map_mul, hcO, hcO])
      map_zero' := hinj (by rw [← hcO, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [← hcO, map_add, map_add, map_add, hcO, hcO]) }
  have hcomp : (algebraMap K.O B.A).comp ψ = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]
    show _ = algebraMap K.E B.A (K.c (algebraMap K.O K.E x))
    rw [hcO]; rfl
  refine ⟨p.map ψ, hpm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  have := Polynomial.hom_eval₂ p (algebraMap K.O B.A) (B.σ : B.A →+* B.A) y
  exact this.symm.trans (by rw [hp, map_zero])

/- English proof (translation)
Use `set R : Submodule K.O B.A := (integralClosure K.O B.A).toSubmodule with hR`. Establish `hRfg : R.FG`. Use `GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra K B hsep` as an intermediate fact. Establish `h2` using `Module.Finite.fg_top (R := K.O) (M := integralClosure K.O B.A)`. Establish `h3` using `h2.map (integralClosure K.O B.A).val.toLinearMap`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[hR]`. Establish `ha0 : a ^ (2 * k) ≠ 0` using `pow_ne_zero _ ha.1`. Establish `hfin` using `finite_between K.O B.A R hRfg (a ^ (2 * k)) ha0`.

Establish `hσα : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]`. Establish `hαu : IsUnit (algebraMap K.O B.A a)`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A]`. Use `IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)` and prove the remaining obligations.

Introduce `h0`. Conclude with `ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h0)`. Use `set αu : B.Aˣ := hαu.unit with hαudef`. Establish `hαeq : (αu : B.A) = algebraMap K.O B.A a` using `hαu.unit_spec`. Establish `hmem : ∀ (u : B.A) (y : B.A), y ∈ mulLat K.O u R ↔ ∃ r ∈ R, u * r = y`.

Introduce `u y`. Simplify using `only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]`. Establish `hσinv : ∀ t : B.T, B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) = ((t : B.Aˣ) : B.A)`. Introduce `t`. Establish `ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1` using `t.2`.

Establish `h1 : B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation. Set `φ : {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T // IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} → {N : Submodule K.O B.A // N ≤ R ∧ ∀ x ∈ R, a ^ (2 * k) • x ∈ N}` to `fun c => ⟨mulLat K.O ((((Quotient.out c.1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) R, by`. Introduce `y hy`.

Take `⟨r, hr, rfl⟩` from `(hmem _ _).1 hy`. Conclude with `c.2.mul hr, by`. Introduce `x hx`. Use `set t : B.T := Quotient.out c.1`. Establish `h2 : IsIntegral K.O (((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k)`.

Use `isIntegral_sigma K B _ c.2` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, hσα, hσinv]`. Then use the resulting hypothesis. Use `(hmem _ _).2 ⟨((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k * x, h2.mul hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_pow, pow_mul]`. Establish `: (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((t : B.Aˣ) : B.A) = 1` using `Units.inv_mul _`.

Take the linear combination `(algebraMap K.O B.A a ^ k * algebraMap K.O B.A a ^ k * x) * this⟩`. Use `Finite.of_injective φ ?_` and prove the remaining obligations. Introduce and unpack `⟨c, hc⟩ ⟨c', hc'⟩ h`. Establish `hN` using `congrArg Subtype.val h`. Simplify using `only [φ] at hN`.

Use `set t : B.T := Quotient.out c with htdef`. Use `set t' : B.T := Quotient.out c' with ht'def`. Establish `h1R : (1 : B.A) ∈ R` using `(integralClosure K.O B.A).one_mem`. Establish `key : ∀ (s s' : B.T), mulLat K.O ((((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R = mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R → IsIntegral K.O ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A)`. Introduce `s s' hss`.

Establish `: (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k ∈ mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R`. Rewrite using `[← hss]`. Conclude with `(hmem _ _).2 ⟨1, h1R, mul_one _⟩`. Take `⟨r, hr, hr'⟩` from `(hmem _ _).1 this`. Establish `h1 : ((s' : B.Aˣ) : B.A) * (((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = 1` using `Units.mul_inv _`.

Establish `h2 : algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) = 1`. Rewrite using `[← hαeq, ← Units.val_pow_eq_pow_val, Units.mul_inv]`. Establish `: ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) = r`. Rewrite using `[Units.val_mul]`. Take the linear combination `-(((s' : B.Aˣ) : B.A) * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * hr' - r * algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * h1 - r * h2 + (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((s' : B.Aˣ) : B.A) * h2)`.

Rewrite using `[this]`. Conclude with `hr`. Establish `hA` using `key t t' hN`. Establish `hB` using `key t' t hN.symm`. Establish `hmemU : (t : B.Aˣ)⁻¹ * (t' : B.Aˣ) ∈ intUnits K.O B.A`.

Use `⟨hA, ?_⟩` and prove the remaining obligations. Establish `: ((t : B.Aˣ)⁻¹ * (t' : B.Aˣ))⁻¹ = ((t' : B.Aˣ)⁻¹ * (t : B.Aˣ))`. Rewrite using `[mul_inv_rev, inv_inv]`. Rewrite using `[this]`. Conclude with `hB`.

Establish `: c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using hmemU`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem finite_rhoSet (K : UQ) (B : InvAlg K) (hsep : B.P.Separable) (a : K.O) (ha : K.Small a) (k : ℕ) :
    Finite {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} := by
  classical
  set R : Submodule K.O B.A := (integralClosure K.O B.A).toSubmodule with hR
  have hRfg : R.FG := by
    have := GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra K B hsep
    have h2 := Module.Finite.fg_top (R := K.O) (M := integralClosure K.O B.A)
    have h3 := h2.map (integralClosure K.O B.A).val.toLinearMap
    convert h3 using 1
    ext x; simp [hR]
  have ha0 : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha.1
  have hfin := finite_between K.O B.A R hRfg (a ^ (2 * k)) ha0
  have hσα : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  have hαu : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    exact ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h0)
  set αu : B.Aˣ := hαu.unit with hαudef
  have hαeq : (αu : B.A) = algebraMap K.O B.A a := hαu.unit_spec
  have hmem : ∀ (u : B.A) (y : B.A), y ∈ mulLat K.O u R ↔ ∃ r ∈ R, u * r = y := by
    intro u y
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]

  have hσinv : ∀ t : B.T, B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) = ((t : B.Aˣ) : B.A) := by
    intro t
    have ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := t.2
    have h1 : B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A)
        = B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * (((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by rw [ht, mul_one]
      _ = ((t : B.Aˣ) : B.A) * (B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by ring
      _ = ((t : B.Aˣ) : B.A) := by rw [h1, mul_one]
  let φ : {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} →
      {N : Submodule K.O B.A // N ≤ R ∧ ∀ x ∈ R, a ^ (2 * k) • x ∈ N} := fun c =>
    ⟨mulLat K.O ((((Quotient.out c.1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) R, by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := (hmem _ _).1 hy
      exact c.2.mul hr, by
      intro x hx
      set t : B.T := Quotient.out c.1
      have h2 : IsIntegral K.O (((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) := by
        have := isIntegral_sigma K B _ c.2
        rwa [map_mul, map_pow, hσα, hσinv] at this
      refine (hmem _ _).2 ⟨((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k * x, h2.mul hx, ?_⟩
      rw [Algebra.smul_def, map_pow, pow_mul]
      have : (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((t : B.Aˣ) : B.A) = 1 := Units.inv_mul _
      linear_combination (algebraMap K.O B.A a ^ k * algebraMap K.O B.A a ^ k * x) * this⟩
  refine Finite.of_injective φ ?_
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  have hN := congrArg Subtype.val h
  simp only [φ] at hN
  set t : B.T := Quotient.out c with htdef
  set t' : B.T := Quotient.out c' with ht'def
  have h1R : (1 : B.A) ∈ R := (integralClosure K.O B.A).one_mem

  have key : ∀ (s s' : B.T), mulLat K.O ((((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R =
      mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R →
      IsIntegral K.O ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) := by
    intro s s' hss
    have : (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k ∈
        mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R := by
      rw [← hss]; exact (hmem _ _).2 ⟨1, h1R, mul_one _⟩
    obtain ⟨r, hr, hr'⟩ := (hmem _ _).1 this
    have h1 : ((s' : B.Aˣ) : B.A) * (((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv _
    have h2 : algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) = 1 := by
      rw [← hαeq, ← Units.val_pow_eq_pow_val, Units.mul_inv]
    have : ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) = r := by
      rw [Units.val_mul]
      linear_combination -(((s' : B.Aˣ) : B.A) * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * hr' - r * algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * h1 - r * h2 + (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((s' : B.Aˣ) : B.A) * h2)
    rw [this]; exact hr
  have hA := key t t' hN
  have hB := key t' t hN.symm
  have hmemU : (t : B.Aˣ)⁻¹ * (t' : B.Aˣ) ∈ intUnits K.O B.A := by
    refine ⟨hA, ?_⟩
    have : ((t : B.Aˣ)⁻¹ * (t' : B.Aˣ))⁻¹ = ((t' : B.Aˣ)⁻¹ * (t : B.Aˣ)) := by
      rw [mul_inv_rev, inv_inv]
    rw [this]; exact hB
  have : c = c' := by
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmemU
  subst this
  rfl

/- English proof (translation)
Introduce `K B ι _ e π S a hsep ha hF k`. Establish `hfin` using `finite_rhoSet K B hsep a ha k`. Take `⟨f, hf, hint⟩` from `GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition K B ι e S a ha hF.1 k`. Set `g : ({i // i ∉ S} → Fin (k + 1)) → {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T // IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)}` to `fun n => ⟨f n, hint n⟩`. Establish `hg : Function.Injective g` using `fun n n' h => hf (congrArg Subtype.val h)`.

Establish `h` using `Nat.card_le_card_of_injective g hg`. Unfold `InvAlg.rho`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Rewrite using `[Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]`.
-/
theorem rho_lower : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ k : ℕ, (k + 1) ^ (Fintype.card ι - S.card) ≤ B.rho (algebraMap K.O B.A a ^ k) := by
  intro K B ι _ e π S a hsep ha hF k
  classical
  have hfin := finite_rhoSet K B hsep a ha k
  obtain ⟨f, hf, hint⟩ := GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition K B ι e S a ha hF.1 k
  let g : ({i // i ∉ S} → Fin (k + 1)) → {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} :=
    fun n => ⟨f n, hint n⟩
  have hg : Function.Injective g := fun n n' h => hf (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective g hg
  unfold InvAlg.rho
  refine le_trans (le_of_eq ?_) h
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_coe]

end GlobalTheory.UnitLemma.Desc
