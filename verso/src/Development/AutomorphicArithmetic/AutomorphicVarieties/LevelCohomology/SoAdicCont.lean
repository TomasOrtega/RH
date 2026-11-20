import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Establish `h1 : IsDiscreteValuationRing.addVal c.O y ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Establish `h2 : IsDiscreteValuationRing.addVal c.O y ≠ 0`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]` and apply the resulting hypothesis. Rewrite using `[Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]`.

The claim follows by propositional logic.
-/
private theorem one_le_addVal_toNat_of_ne_zero_of_not_isUnit {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) (h0 : y ≠ 0)
    (hu : ¬ IsUnit y) : 1 ≤ (IsDiscreteValuationRing.addVal c.O y).toNat := by
  have h1 : IsDiscreteValuationRing.addVal c.O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have h2 : IsDiscreteValuationRing.addVal c.O y ≠ 0 := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
  rw [Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]
  tauto

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Conclude with `pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) (by omega)`.
-/
private theorem prime_inv_pow_lt_one_of_one_le {l : ℕ} [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) :
    ((l : ℝ)⁻¹) ^ k < 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) (by omega)

/- English proof (translation)
Introduce `he`. Take `⟨w, hw⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `h` using `Base.normO l c.O w hw.ne_zero`. Rewrite `h` using `[he, pow_zero]`. Establish `hk` using `prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c w hw.ne_zero hw.not_isUnit)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem base_eO_toNat_ne_zero {l : ℕ} [Fact l.Prime] (c : HV.Coef l) :
    (Base.eO l c.O).toNat ≠ 0 := by
  intro he
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h := Base.normO l c.O w hw.ne_zero
  rw [he, pow_zero] at h
  have hk := prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c w hw.ne_zero hw.not_isUnit)
  linarith

/- English proof (translation)
Distinguish the cases in `h0 : y = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Establish `he` using `base_eO_toNat_ne_zero c`. Establish `h` using `Base.normO l c.O y h0`.

Establish `hk` using `prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c y h0 hy)`. Rewrite `hk` using `[← h]`. Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) he).mp hk`.
-/
private theorem norm_lt_one_of_not_isUnit {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) (hy : ¬ IsUnit y) :
    ‖(y : PadicAlgCl l)‖ < 1 := by
  by_cases h0 : y = 0
  · subst h0
    simp
  · have he := base_eO_toNat_ne_zero c
    have h := Base.normO l c.O y h0
    have hk := prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c y h0 hy)
    rw [← h] at hk
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).mp hk

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Conclude with `dvd_zero a`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Simplify using `only [ZeroMemClass.coe_zero, norm_zero] at h`. Combine the linear relations using `[norm_nonneg (x : PadicAlgCl l)]`. Establish `he` using `base_eO_toNat_ne_zero c`. Establish `hxa` using `pow_lt_pow_left₀ h (norm_nonneg _) he`. Rewrite `hxa` using `[Base.normO l c.O x hx, Base.normO l c.O a ha]`.

Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hlt` using `(pow_lt_pow_iff_right_of_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl)).mp hxa`. Establish `hta : IsDiscreteValuationRing.addVal c.O a ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Establish `htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤`.

Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, ← ENat.coe_toNat hta, ← ENat.coe_toNat htx]`. Conclude with `hlt.le` after adjusting the coercions.
-/
private theorem dvd_of_norm_lt {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (a x : c.O)
    (h : ‖(x : PadicAlgCl l)‖ < ‖(a : PadicAlgCl l)‖) : a ∣ x := by
  by_cases hx : x = 0
  · subst hx
    exact dvd_zero a
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ZeroMemClass.coe_zero, norm_zero] at h
    linarith [norm_nonneg (x : PadicAlgCl l)]
  have he := base_eO_toNat_ne_zero c
  have hxa := pow_lt_pow_left₀ h (norm_nonneg _) he
  rw [Base.normO l c.O x hx, Base.normO l c.O a ha] at hxa
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlt := (pow_lt_pow_iff_right_of_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl)).mp hxa
  have hta : IsDiscreteValuationRing.addVal c.O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← ENat.coe_toNat hta, ← ENat.coe_toNat htx]
  exact_mod_cast hlt.le

/- English proof (translation)
Establish `ha' : 0 < ‖(a : PadicAlgCl l)‖` using `norm_pos_iff.mpr (by exact_mod_cast ha)`. Establish `hc : Continuous (fun y : c.O => ‖(y : PadicAlgCl l) - x‖)` using `(continuous_subtype_val.sub continuous_const).norm`. Establish `h0 : ‖((x : c.O) : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖`. Rewrite using `[sub_self, norm_zero]`. Conclude with `ha'`.

Establish `hev : ∀ᶠ y : c.O in nhds x, ‖(y : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖` using `hc.continuousAt.eventually_lt (continuous_const (y := ‖(a : PadicAlgCl l)‖)).continuousAt h0`. Use `filter_upwards [hev] with y hy`. Apply `dvd_of_norm_lt c` to reduce the goal to its premises. Use `push_cast`. Conclude with `hy`.
-/
private theorem ev_dvd {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (a : c.O) (ha : a ≠ 0) (x : c.O) :
    ∀ᶠ y in nhds x, a ∣ y - x := by
  have ha' : 0 < ‖(a : PadicAlgCl l)‖ := norm_pos_iff.mpr (by exact_mod_cast ha)
  have hc : Continuous (fun y : c.O => ‖(y : PadicAlgCl l) - x‖) :=
    (continuous_subtype_val.sub continuous_const).norm
  have h0 : ‖((x : c.O) : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖ := by
    rw [sub_self, norm_zero]
    exact ha'
  have hev : ∀ᶠ y : c.O in nhds x, ‖(y : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖ :=
    hc.continuousAt.eventually_lt (continuous_const (y := ‖(a : PadicAlgCl l)‖)).continuousAt h0
  filter_upwards [hev] with y hy
  apply dvd_of_norm_lt c
  push_cast
  exact hy

/- English proof (translation)
Distinguish the cases in `hu : IsUnit y`. Establish `h` using `Base.normO l c.O y hu.ne_zero`. Rewrite `h` using `[IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, ENat.toNat_zero, pow_zero]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) (base_eO_toNat_ne_zero c)).mp h).le`. Conclude with `(norm_lt_one_of_not_isUnit c y hu).le`.
-/
private theorem norm_coef_O_coe_padicAlgCl_le_one {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) :
    ‖(y : PadicAlgCl l)‖ ≤ 1 := by
  by_cases hu : IsUnit y
  · have h := Base.normO l c.O y hu.ne_zero
    rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, ENat.toNat_zero, pow_zero] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (base_eO_toNat_ne_zero c)).mp h).le
  · exact (norm_lt_one_of_not_isUnit c y hu).le

/- English proof (translation)
Introduce `l _ c`. Use `⟨fun a ha => ?_, fun X _ z => ?_⟩` and prove the remaining obligations. Apply `IsLocallyConstant.continuous` to reduce the goal to its premises. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Use `filter_upwards [ev_dvd c a ha x] with y hy`. Rewrite using `[← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]`. Conclude with `hy`. Take `⟨w, hw⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `hm : ∀ N : ℕ, maximalIdeal c.O ^ N = Ideal.span {w ^ N}` using `fun N => by`.

Rewrite using `[hw.maximalIdeal_eq, Ideal.span_singleton_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Apply `continuous_induced_rng.mpr` to reduce the goal to its premises. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g0`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hw1 : ‖(w : PadicAlgCl l)‖ < 1` using `norm_lt_one_of_not_isUnit c w hw.not_isUnit`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one hε hw1`.

Establish `hl` using `(IsLocallyConstant.iff_eventually_eq _).mp (hz N) g0`. Use `filter_upwards [hl] with g hg`. Rewrite `hg` using `[Ideal.Quotient.eq, hm, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hg`. Rewrite using `[dist_eq_norm]`.

Simplify using `only [Function.comp_apply]`. Establish `he : ((z g : c.O) : PadicAlgCl l) - z g0 = (w : PadicAlgCl l) ^ N * t`. Conclude with `congrArg (fun u : c.O => (u : PadicAlgCl l)) ht` after adjusting the coercions. Rewrite using `[he, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_one]`. Conclude with `hN`. Introduce `hz N`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g0`.

Establish `hne : w ^ N ≠ 0` using `pow_ne_zero _ hw.ne_zero`. Establish `h1` using `(hz.tendsto g0).eventually (ev_dvd c (w ^ N) hne (z g0))`. Use `filter_upwards [h1] with g hg`. Rewrite using `[Ideal.Quotient.eq, hm, Ideal.mem_span_singleton]`. Conclude with `hg`.
-/
theorem UpperTheory.V.X.So.adicCont :
    ∀ (l : ℕ) [Fact l.Prime] (c : HV.Coef l), (∀ a : c.O, a ≠ 0 → Continuous (Lev.mk a)) ∧ ∀ (X : Type) [TopologicalSpace X] (z : X → c.O), Alg.AdicCont (maximalIdeal c.O) z ↔ Continuous z := by
  intro l _ c
  refine ⟨fun a ha => ?_, fun X _ z => ?_⟩
  · apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [ev_dvd c a ha x] with y hy
    rw [← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]
    exact hy
  · obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible c.O
    have hm : ∀ N : ℕ, maximalIdeal c.O ^ N = Ideal.span {w ^ N} := fun N => by
      rw [hw.maximalIdeal_eq, Ideal.span_singleton_pow]
    constructor
    · intro hz
      apply continuous_induced_rng.mpr
      rw [continuous_iff_continuousAt]
      intro g0
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      have hw1 : ‖(w : PadicAlgCl l)‖ < 1 := norm_lt_one_of_not_isUnit c w hw.not_isUnit
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hw1
      have hl := (IsLocallyConstant.iff_eventually_eq _).mp (hz N) g0
      filter_upwards [hl] with g hg
      rw [Ideal.Quotient.eq, hm, Ideal.mem_span_singleton] at hg
      obtain ⟨t, ht⟩ := hg
      rw [dist_eq_norm]
      simp only [Function.comp_apply]
      have he : ((z g : c.O) : PadicAlgCl l) - z g0 = (w : PadicAlgCl l) ^ N * t := by
        exact_mod_cast congrArg (fun u : c.O => (u : PadicAlgCl l)) ht
      rw [he, norm_mul, norm_pow]
      calc ‖(w : PadicAlgCl l)‖ ^ N * ‖(t : PadicAlgCl l)‖ ≤ ‖(w : PadicAlgCl l)‖ ^ N * 1 :=
            mul_le_mul_of_nonneg_left (norm_coef_O_coe_padicAlgCl_le_one c t) (by positivity)
        _ < ε := by
          rw [mul_one]
          exact hN
    · intro hz N
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g0
      have hne : w ^ N ≠ 0 := pow_ne_zero _ hw.ne_zero
      have h1 := (hz.tendsto g0).eventually (ev_dvd c (w ^ N) hne (z g0))
      filter_upwards [h1] with g hg
      rw [Ideal.Quotient.eq, hm, Ideal.mem_span_singleton]
      exact hg
