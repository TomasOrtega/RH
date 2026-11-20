import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagConst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Distinguish the cases in `h0 : P = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨r, hr, hd⟩` from `h.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)`. Establish `hu : IsUnit P` using `isUnit_of_dvd_unit hd ((IsUnit.mk0 r hr).map (algebraMap k _))`. Take `⟨p, -, hp⟩` from `MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu`.

Conclude with `⟨p, hp.symm⟩`.
-/
theorem exists_C_eq_of_isAlgebraic {k I : Type} [Field k] (P : MvPolynomial I k) (h : IsAlgebraic k P) :
    ∃ p : k, MvPolynomial.C p = P := by
  by_cases h0 : P = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨r, hr, hd⟩ := h.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hu : IsUnit P := isUnit_of_dvd_unit hd ((IsUnit.mk0 r hr).map (algebraMap k _))
  obtain ⟨p, -, hp⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  exact ⟨p, hp.symm⟩

/- English proof (translation)
Set `g : MvPolynomial I k →ₐ[k] L` to `MvPolynomial.aeval x`. Establish `hg : Function.Injective g` using `hx`. Use `letI : Algebra (MvPolynomial I k) L := g.toRingHom.toAlgebra`. Establish `hmap : ∀ P : MvPolynomial I k, algebraMap (MvPolynomial I k) L P = g P` using `fun _ => rfl`. Use `haveI : IsScalarTower k (MvPolynomial I k) L := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm`.

Use `haveI : FaithfulSMul (MvPolynomial I k) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hg`. Use `haveI : IsFractionRing (MvPolynomial I k) L := by`. Use `IsFractionRing.of_field _ _ fun z => ?_` and prove the remaining obligations. Establish `hz : z ∈ IntermediateField.adjoin k (Set.range x)` using `ht ▸ IntermediateField.mem_top`. Take `⟨r, s, e⟩` from `(IntermediateField.mem_adjoin_range_iff k x z).1 hz`.

Conclude with `⟨r, s, e⟩`. Establish `hi : IsIntegral (MvPolynomial I k) a` using `(ha.isIntegral).tower_top`. Take `⟨P, hP⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Establish `hPa : IsAlgebraic k P`. Rewrite using `[← isAlgebraic_algHom_iff g hg, ← hmap, hP]`.

Conclude with `ha`. Take `⟨p, rfl⟩` from `exists_C_eq_of_isAlgebraic P hPa`. Use `⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[← hP, hmap]`. Conclude with `(g.commutes p).symm`.
-/
theorem mem_range_of_isAlgebraic {k L I : Type} [Field k] [Field L] [Algebra k L] (x : I → L)
    (hx : AlgebraicIndependent k x) (ht : IntermediateField.adjoin k (Set.range x) = ⊤) (a : L)
    (ha : IsAlgebraic k a) : a ∈ (algebraMap k L).range := by
  let g : MvPolynomial I k →ₐ[k] L := MvPolynomial.aeval x
  have hg : Function.Injective g := hx
  letI : Algebra (MvPolynomial I k) L := g.toRingHom.toAlgebra
  have hmap : ∀ P : MvPolynomial I k, algebraMap (MvPolynomial I k) L P = g P := fun _ => rfl
  haveI : IsScalarTower k (MvPolynomial I k) L := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : FaithfulSMul (MvPolynomial I k) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsFractionRing (MvPolynomial I k) L := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (Set.range x) := ht ▸ IntermediateField.mem_top
    obtain ⟨r, s, e⟩ := (IntermediateField.mem_adjoin_range_iff k x z).1 hz
    exact ⟨r, s, e⟩
  have hi : IsIntegral (MvPolynomial I k) a := (ha.isIntegral).tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hPa : IsAlgebraic k P := by
    rw [← isAlgebraic_algHom_iff g hg, ← hmap, hP]
    exact ha
  obtain ⟨p, rfl⟩ := exists_C_eq_of_isAlgebraic P hPa
  refine ⟨p, ?_⟩
  rw [← hP, hmap]
  exact (g.commutes p).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ c.F := c.fin`. Use `haveI : NumberField c.F := {}`. Set `b₀ : 𝓞 c.F →+* 𝔐.Ω₀` to `(Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom`. Establish `hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀` using `(Spec.map_preimage _).symm`. Establish `hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)`.

Establish `hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))`. Establish `hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀` using `𝔐.fn_over`. Establish `hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]`. Use `CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)` as an intermediate fact. Simplify using `using this`. Establish `hinj : Function.Injective b₀`. Introduce `u v huv`.

Establish `h` using `congrArg 𝔐.fn huv`. Establish `hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w)` using `fun w => RingHom.congr_fun hc w`. Rewrite `h` using `[hu, hu]`. Conclude with `IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)`. Set `cst₀ : c.F →+* 𝔐.Ω₀` to `IsFractionRing.lift hinj`.

Establish `hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀`. Use extensionality with `w`. Conclude with `IsFractionRing.lift_algebraMap hinj w`. Use `⟨cst₀, ?_, by rw [hl, hb]⟩` and prove the remaining obligations. Use `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_assoc, hl, hc]`.
-/
theorem exists_cst₀ {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) :
    ∃ cst₀ : c.F →+* 𝔐.Ω₀, 𝔐.fn.comp cst₀ = 𝔐.cst ∧
      𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  refine ⟨cst₀, ?_, by rw [hl, hb]⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
  rw [RingHom.comp_assoc, hl, hc]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl hS hdeg a ha`. Take `⟨cst₀, h1, h2⟩` from `exists_cst₀ 𝔐`. Use `haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective`. Use `letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra`. Take `⟨-, u, -, -, -, -, hdiag, hup, -, hind, -, hfin⟩` from `Fl.generic`.

Rewrite `hfin` using `[hdeg]`. Set `x : (Σ q : CMType H ⊕ CMType H, {lk : Fin (labelRk D q) × Fin (labelRk D q) // lk.2 < lk.1}) → Ω` to `fun q => u q.1 q.2.1.1 q.2.1.2`. Set `A` to `IntermediateField.adjoin 𝔐.Ω₀ (Set.range fun q : Σ σ, Fin (labelRk D σ) × Fin (labelRk D σ) => u q.1 q.2.1 q.2.2)`. Establish `hA : A = ⊤`. Establish `hb` using `Subalgebra.bot_eq_top_of_finrank_eq_one hfin`.

Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Establish `hz : z ∈ (⊥ : Subalgebra A Ω)` using `hb ▸ Algebra.mem_top`. Take `⟨w, rfl⟩` from `Algebra.mem_bot.1 hz`. Conclude with `w.2`. Establish `ht : IntermediateField.adjoin 𝔐.Ω₀ (Set.range x) = ⊤`.

Use `eq_top_iff.2 (hA ▸ ?_)` and prove the remaining obligations. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨σ, l', k⟩, rfl⟩`. Break down `lt_trichotomy l' k with h | h | h` into its components or cases. Use `show u σ l' k ∈ _`.

Rewrite using `[hup σ l' k h]`. Conclude with `zero_mem _`. Substitute `h show u σ l' l' ∈ _` using the available equality. Rewrite using `[hdiag σ l']`. Conclude with `one_mem _`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l', k), h⟩⟩, rfl⟩`. Establish `hal : IsAlgebraic 𝔐.Ω₀ a` using `by haveI : CharZero 𝔐.Ω₀ := charZero_of_injective_ringHom cst₀.injective`. Conclude with `ha.extendScalars (RingHom.injective_int _)`. Take `⟨a₀, rfl⟩` from `mem_range_of_isAlgebraic x hind ht a hal`. Establish `ha₀ : IsAlgebraic ℤ a₀` using `(isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ 𝔐.Ω₀ Ω) (algebraMap 𝔐.Ω₀ Ω).injective).1 ha`.

Take `⟨k, rfl⟩` from `hS 𝔐.Ω₀ 𝔐.ξ₀ cst₀ 𝔐.gen₀ h2 a₀ ha₀`. Conclude with `⟨k, (RingHom.congr_fun h1 k).symm⟩`.
-/
theorem isAlgebraic_mem_cst_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl hS hdeg a ha
  obtain ⟨cst₀, h1, h2⟩ := exists_cst₀ 𝔐
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  obtain ⟨-, u, -, -, -, -, hdiag, hup, -, hind, -, hfin⟩ := Fl.generic
  rw [hdeg] at hfin
  let x : (Σ q : CMType H ⊕ CMType H, {lk : Fin (labelRk D q) × Fin (labelRk D q) // lk.2 < lk.1}) → Ω :=
    fun q => u q.1 q.2.1.1 q.2.1.2
  let A := IntermediateField.adjoin 𝔐.Ω₀
    (Set.range fun q : Σ σ, Fin (labelRk D σ) × Fin (labelRk D σ) => u q.1 q.2.1 q.2.2)
  have hA : A = ⊤ := by
    have hb := Subalgebra.bot_eq_top_of_finrank_eq_one hfin
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⊥ : Subalgebra A Ω) := hb ▸ Algebra.mem_top
    obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hz
    exact w.2
  have ht : IntermediateField.adjoin 𝔐.Ω₀ (Set.range x) = ⊤ := by
    refine eq_top_iff.2 (hA ▸ ?_)
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨σ, l', k⟩, rfl⟩
    rcases lt_trichotomy l' k with h | h | h
    · show u σ l' k ∈ _
      rw [hup σ l' k h]
      exact zero_mem _
    · subst h
      show u σ l' l' ∈ _
      rw [hdiag σ l']
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l', k), h⟩⟩, rfl⟩
  have hal : IsAlgebraic 𝔐.Ω₀ a := by
    haveI : CharZero 𝔐.Ω₀ := charZero_of_injective_ringHom cst₀.injective
    exact ha.extendScalars (RingHom.injective_int _)
  obtain ⟨a₀, rfl⟩ := mem_range_of_isAlgebraic x hind ht a hal
  have ha₀ : IsAlgebraic ℤ a₀ :=
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ 𝔐.Ω₀ Ω) (algebraMap 𝔐.Ω₀ Ω).injective).1 ha
  obtain ⟨k, rfl⟩ := hS 𝔐.Ω₀ 𝔐.ξ₀ cst₀ 𝔐.gen₀ h2 a₀ ha₀
  exact ⟨k, (RingHom.congr_fun h1 k).symm⟩

end GlobalTheory.CompanionTheory.Ar.FlagConst
