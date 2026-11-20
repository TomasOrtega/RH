import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.WeilBound.CoreStatements.VolumeEquality.PrimeIdealOfFromSpec
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Pt

/- English proof (translation)
Use `haveI : CharZero L := charZero_of_injective_ringHom f.injective`. Establish `e : f = algebraMap ℚ L` using `Subsingleton.elim _ _`. Use `haveI : Algebra.FiniteType ℚ L := RingHom.finiteType_algebraMap.1 (e ▸ hf)`. Conclude with `{ to_finiteDimensional := finite_of_finite_type_of_isJacobsonRing ℚ L }`.
-/
theorem numberField_of (L : Type) [Field L] (f : ℚ →+* L) (hf : f.FiniteType) : NumberField L := by
  haveI : CharZero L := charZero_of_injective_ringHom f.injective
  have e : f = algebraMap ℚ L := Subsingleton.elim _ _
  haveI : Algebra.FiniteType ℚ L := RingHom.finiteType_algebraMap.1 (e ▸ hf)
  exact { to_finiteDimensional := finite_of_finite_type_of_isJacobsonRing ℚ L }

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Use `letI : Field (B ⧸ m) := Ideal.Quotient.field m`. Establish `h1 : (algebraMap ℚ B).FiniteType` using `RingHom.finiteType_algebraMap.2 inferInstance`. Use `haveI : NumberField (B ⧸ m) := numberField_of _ ((Ideal.Quotient.mk m).comp (algebraMap ℚ B)) (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) h1)`. Conclude with `⟨B ⧸ m, inferInstance, inferInstance, ⟨Ideal.Quotient.mk m⟩⟩`.
-/
theorem exists_quot (B : Type) [CommRing B] [Nontrivial B] [Algebra ℚ B] [Algebra.FiniteType ℚ B] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L), Nonempty (B →+* L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have h1 : (algebraMap ℚ B).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  haveI : NumberField (B ⧸ m) := numberField_of _ ((Ideal.Quotient.mk m).comp (algebraMap ℚ B))
    (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) h1)
  exact ⟨B ⧸ m, inferInstance, inferInstance, ⟨Ideal.Quotient.mk m⟩⟩

/- English proof (translation)
Set `B : Subalgebra ℚ Ω` to `Algebra.adjoin ℚ (insert (e s)⁻¹ (Set.range t))`. Establish `hB : ∀ x ∈ Algebra.adjoin ℤ (Set.range t), x ∈ B`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)`.

Consider the case `algebraMap r => simpa using intCast_mem B r`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`. Use `haveI : Algebra.FiniteType ℚ B := by`. Use `(Subalgebra.fg_iff_finiteType _).1 ⟨((Set.finite_range t).insert (e s)⁻¹).toFinset, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.Finite.coe_toFinset]`. Take `⟨L, _, _, ⟨g⟩⟩` from `exists_quot B`. Set `e' : A →+* B` to `e.codRestrict B fun a => hB _ (he a)`. Use `⟨L, inferInstance, inferInstance, g.comp e', ?_⟩` and prove the remaining obligations. Establish `h1 : e' s * ⟨(e s)⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ = 1` using `Subtype.ext (mul_inv_cancel₀ hs)`.

Conclude with `((IsUnit.of_mul_eq_one _ h1).map g).ne_zero`.
-/
theorem exists_numberField {A Ω κ : Type} [CommRing A] [Field Ω] [CharZero Ω] [Finite κ] (e : A →+* Ω) (t : κ → Ω)
    (he : ∀ a, e a ∈ Algebra.adjoin ℤ (Set.range t)) (s : A) (hs : e s ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ε : A →+* L), ε s ≠ 0 := by
  classical
  let B : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (e s)⁻¹ (Set.range t))
  have hB : ∀ x ∈ Algebra.adjoin ℤ (Set.range t), x ∈ B := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
    | algebraMap r => simpa using intCast_mem B r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  haveI : Algebra.FiniteType ℚ B := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨((Set.finite_range t).insert (e s)⁻¹).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  obtain ⟨L, _, _, ⟨g⟩⟩ := exists_quot B
  let e' : A →+* B := e.codRestrict B fun a => hB _ (he a)
  refine ⟨L, inferInstance, inferInstance, g.comp e', ?_⟩
  have h1 : e' s * ⟨(e s)⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hs)
  exact ((IsUnit.of_mul_eq_one _ h1).map g).ne_zero

/- English proof (translation)
Take `⟨c, hc⟩` from `hT.cover ⟨genPt ξ, specializes_rfl⟩`. Take `⟨U, hU, hg, -, -, hr⟩` from `SheetDecomposition.BBase.chart hT c hc.1`. Take `⟨s, hsW, hsη⟩` from `hU.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hg`. Establish `h0 : SheetDecomposition.BBase.ev ξ U hg s ≠ 0` using `(((Scheme.mem_basicOpen X s _ hg).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero`. Take `⟨L, _, _, ε, hε⟩` from `exists_numberField (SheetDecomposition.BBase.ev ξ U hg) _ (fun a => (hr _).1 ⟨a, rfl⟩) s h0`.

Set `φ : Γ(X, U) ⟶ CommRingCat.of L` to `CommRingCat.ofHom ε`. Establish `hz : centre (Spec.map φ ≫ hU.fromSpec) ∈ U`. Express the relevant statement in the definitionally equal form `_ ∈ (U : Set X)`. Rewrite using `[← hU.range_fromSpec]`. Conclude with `⟨_, rfl⟩`.

Use `⟨L, inferInstance, inferInstance, Spec.map φ ≫ hU.fromSpec, hsW ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun g => g.hom s) (SheetDecomposition.ChartForm.germ_point hU φ hz)`. Use `(Scheme.mem_basicOpen X s _ hz).2 (isUnit_of_map_unit (Scheme.stalkClosedPointTo (Spec.map φ ≫ hU.fromSpec)).hom _ (IsUnit.mk0 _ ?_))` and prove the remaining obligations. Introduce `h`. Conclude with `hε (h1.symm.trans h)`.
-/
theorem exists_point {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    [Finite κ] {x : κ → Ω} (hT : CoordTie ℤ ξ x) (W : X.Opens) (hW : genPt ξ ∈ W) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : Spec (CommRingCat.of L) ⟶ X), centre z ∈ W := by
  obtain ⟨c, hc⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨U, hU, hg, -, -, hr⟩ := SheetDecomposition.BBase.chart hT c hc.1
  obtain ⟨s, hsW, hsη⟩ := hU.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hg
  have h0 : SheetDecomposition.BBase.ev ξ U hg s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hg).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨L, _, _, ε, hε⟩ := exists_numberField (SheetDecomposition.BBase.ev ξ U hg) _ (fun a => (hr _).1 ⟨a, rfl⟩) s h0
  let φ : Γ(X, U) ⟶ CommRingCat.of L := CommRingCat.ofHom ε
  have hz : centre (Spec.map φ ≫ hU.fromSpec) ∈ U := by
    change _ ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨L, inferInstance, inferInstance, Spec.map φ ≫ hU.fromSpec, hsW ?_⟩
  have h1 := congrArg (fun g => g.hom s) (SheetDecomposition.ChartForm.germ_point hU φ hz)
  refine (Scheme.mem_basicOpen X s _ hz).2
    (isUnit_of_map_unit (Scheme.stalkClosedPointTo (Spec.map φ ≫ hU.fromSpec)).hom _ (IsUnit.mk0 _ ?_))
  intro h
  exact hε (h1.symm.trans h)

def primeOf {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : Ideal (𝓞 F) :=
  { carrier := {b | ‖κ (b : F)‖ < 1}
    add_mem' := fun {a b} ha hb => by
      have := IsUltrametricDist.norm_add_le_max (κ (a : F)) (κ (b : F))
      show ‖κ ((a + b : 𝓞 F) : F)‖ < 1
      push_cast
      rw [map_add]
      exact this.trans_lt (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := fun a b hb => by
      show ‖κ ((a * b : 𝓞 F) : F)‖ < 1
      have h1 : ‖κ (a : F)‖ ≤ 1 := by
        have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
        exact_mod_cast this
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans_lt hb }

/- English proof (translation)
Use `HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem norm_int_le {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) (a : 𝓞 F) :
    ‖κ (a : F)‖ ≤ 1 := by
  have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
  exact_mod_cast this

/- English proof (translation)
The claim follows from `le_antisymm (norm_int_le κ a) (not_lt.1 h)`.
-/
theorem norm_eq_one {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : 𝓞 F}
    (h : a ∉ primeOf κ) : ‖κ (a : F)‖ = 1 := le_antisymm (norm_int_le κ a) (not_lt.1 h)

instance primeOf_isPrime {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : (primeOf κ).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ ‖κ ((1 : 𝓞 F) : F)‖ < 1
    simp
  mem_or_mem' := fun {a b} h => by
    by_contra hn
    rw [not_or] at hn
    have h' : ‖κ ((a * b : 𝓞 F) : F)‖ < 1 := h
    push_cast at h'
    rw [map_mul, norm_mul, norm_eq_one κ hn.1, norm_eq_one κ hn.2] at h'
    simp at h'

/- English proof (translation)
Introduce `h`. Establish `h1 : ((p : ℕ) : 𝓞 F) ∈ primeOf κ` using `by show ‖κ (((p : ℕ) : 𝓞 F) : F)‖ < 1`. Establish `: κ (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ_[p] ℂ_[p] ((p : ℕ) : ℚ_[p])` using `by simp`. Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `p.2.ne_zero (by exact_mod_cast h1)`.
-/
theorem primeOf_ne_bot {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : primeOf κ ≠ ⊥ := by
  intro h
  have h1 : ((p : ℕ) : 𝓞 F) ∈ primeOf κ := by
    show ‖κ (((p : ℕ) : 𝓞 F) : F)‖ < 1
    have : κ (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ_[p] ℂ_[p] ((p : ℕ) : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rw [h, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Set `V` to `Localization.subalgebra.ofField F (primeOf κ).primeCompl (primeOf κ).primeCompl_le_nonZeroDivisors`. Use `haveI : IsDiscreteValuationRing V := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) (primeOf_ne_bot κ) V`. Break down `ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩` into its components or cases. Take `⟨u, s, hs, e⟩` from `x.2`. Conclude with `⟨u, s, hs, hx.symm.trans e⟩`.

Take `⟨u, s, hs, e⟩` from `x.2`. Establish `e' : a⁻¹ = (u : F) * (s : F)⁻¹` using `hx.symm.trans e`. Distinguish the cases in `h0 : a = 0`. Conclude with `⟨0, 1, (primeOf κ).primeCompl.one_mem, by simp [h0]⟩`. Use `⟨s, u, fun hu => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : ‖κ (u : F)‖ < 1` using `hu`. Establish `h2` using `congrArg (fun t => ‖κ t‖) e'`. Simplify using `only [map_inv₀, map_mul, norm_mul, norm_inv, norm_eq_one κ hs, inv_one, mul_one] at h2`. Establish `h3 : 0 < ‖κ a‖` using `norm_pos_iff.2 ((map_ne_zero κ).2 h0)`. Use `one_le_inv₀ h3 |>.2 ha` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← inv_inv a, e', mul_inv, inv_inv, mul_comm]`.
-/
theorem exists_frac {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : F} (ha : ‖κ a‖ ≤ 1) :
    ∃ u s : 𝓞 F, s ∉ primeOf κ ∧ a = (u : F) * (s : F)⁻¹ := by
  let V := Localization.subalgebra.ofField F (primeOf κ).primeCompl (primeOf κ).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) (primeOf_ne_bot κ) V
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    exact ⟨u, s, hs, hx.symm.trans e⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    have e' : a⁻¹ = (u : F) * (s : F)⁻¹ := hx.symm.trans e
    by_cases h0 : a = 0
    · exact ⟨0, 1, (primeOf κ).primeCompl.one_mem, by simp [h0]⟩
    refine ⟨s, u, fun hu => ?_, ?_⟩
    · have h1 : ‖κ (u : F)‖ < 1 := hu
      have h2 := congrArg (fun t => ‖κ t‖) e'
      simp only [map_inv₀, map_mul, norm_mul, norm_inv, norm_eq_one κ hs, inv_one, mul_one] at h2
      have h3 : 0 < ‖κ a‖ := norm_pos_iff.2 ((map_ne_zero κ).2 h0)
      have := one_le_inv₀ h3 |>.2 ha
      linarith
    · rw [← inv_inv a, e', mul_inv, inv_inv, mul_comm]

/- English proof (translation)
Set `V` to `Localization.subalgebra.ofField L (primeOf j).primeCompl (primeOf j).primeCompl_le_nonZeroDivisors`. Use `haveI : IsDiscreteValuationRing V := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (primeOf_ne_bot j) V`. Use `⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun a => ⟨fun ha => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨u, s, hs, e⟩` from `exists_frac j ha`. Conclude with `⟨⟨a, u, s, hs, e⟩, rfl⟩`.

Introduce and unpack `⟨x, rfl⟩`. Take `⟨u, s, hs, e⟩` from `x.2`. Establish `e' : algebraMap V L x = (u : L) * (s : L)⁻¹` using `e`. Rewrite using `[e', map_mul, map_inv₀, norm_mul, norm_inv, norm_eq_one j hs, inv_one, mul_one]`. Conclude with `norm_int_le j u`.
-/
theorem exists_dvr {L : Type} [Field L] [NumberField L] {p : Nat.Primes} (j : L →+* ℂ_[p]) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra V L)
      (_ : IsFractionRing V L), ∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range := by
  let V := Localization.subalgebra.ofField L (primeOf j).primeCompl (primeOf j).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (primeOf_ne_bot j) V
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨u, s, hs, e⟩ := exists_frac j ha
    exact ⟨⟨a, u, s, hs, e⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨u, s, hs, e⟩ := x.2
    have e' : algebraMap V L x = (u : L) * (s : L)⁻¹ := e
    rw [e', map_mul, map_inv₀, norm_mul, norm_inv, norm_eq_one j hs, inv_one, mul_one]
    exact norm_int_le j u

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Introduce `p a ha`. Establish `hξ` using `hT.gen`. Take `⟨hd, hc⟩` from `hX p.1`. Use `letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra`. Establish `hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω)` using `hξ.inj p`.

Use `haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Use `haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by`. Take `⟨c, hc⟩` from `hT.cover p`. Take `⟨U, hU, hg, hm, -, -⟩` from `SheetDecomposition.BBase.chart hT c hc.1`. Establish `hp : p.1 ∈ U` using `(hm _).2 ⟨p.2, hc⟩`.

Take `⟨s, t, ht, e⟩` from `SheetDecomposition.BBase.exists_frac hU ⟨genPt ξ, specializes_rfl⟩ hg hg (SheetDecomposition.BBase.mem_regAt_gen hξ z)`. Establish `h0` using `((SheetDecomposition.BBase.unitAt_ev_iff hξ hU ⟨genPt ξ, specializes_rfl⟩ hg hg t).2 ht).1`. Use `⟨X.presheaf.germ U p.1 hp s, X.presheaf.germ U p.1 hp t, ?_⟩` and prove the remaining obligations. Use `show z = genMap ξ p _ / genMap ξ p _`. Rewrite using `[SheetDecomposition.BBase.genMap_germ p U hp hg, SheetDecomposition.BBase.genMap_germ p U hp hg, ← e, mul_div_cancel_left₀ _ h0]`.

Use `letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra`. Use `haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) := Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1) (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective`. Take `⟨b, hb⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1 (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)`. Conclude with `⟨b, hb⟩`.
-/
theorem normalCpt_of_tie {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    (hX : ∀ q : X, IsDomain (X.presheaf.stalk q) ∧ IsIntegrallyClosed (X.presheaf.stalk q)) : NormalCpt ξ := by
  intro p a ha
  have hξ := hT.gen
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨c, hc⟩ := hT.cover p
    obtain ⟨U, hU, hg, hm, -, -⟩ := SheetDecomposition.BBase.chart hT c hc.1
    have hp : p.1 ∈ U := (hm _).2 ⟨p.2, hc⟩
    obtain ⟨s, t, ht, e⟩ := SheetDecomposition.BBase.exists_frac hU ⟨genPt ξ, specializes_rfl⟩ hg hg (SheetDecomposition.BBase.mem_regAt_gen hξ z)
    have h0 := ((SheetDecomposition.BBase.unitAt_ev_iff hξ hU ⟨genPt ξ, specializes_rfl⟩ hg hg t).2 ht).1
    refine ⟨X.presheaf.germ U p.1 hp s, X.presheaf.germ U p.1 hp t, ?_⟩
    show z = genMap ξ p _ / genMap ξ p _
    rw [SheetDecomposition.BBase.genMap_germ p U hp hg, SheetDecomposition.BBase.genMap_germ p U hp hg, ← e, mul_div_cancel_left₀ _ h0]
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

/- English proof (translation)
The claim follows from `hN q _ ((map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe b)).tower_top)`.
-/
theorem int_reg (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω) (q : Cpt ξ) (b : 𝓞 F) :
    ψ (b : F) ∈ regAt ξ q := hN q _ ((map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe b)).tower_top)

/- English proof (translation)
Take `⟨h', g, rfl, rfl⟩` from `hv`. Take `⟨u, rfl⟩ : IsUnit g` from `(Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit g hr`. Conclude with `⟨u⁻¹.val, map_units_inv _ u⟩`.
-/
theorem inv_reg {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z)
    {a : Ω} {r : R} (hv : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨h', g, rfl, rfl⟩ := hv
  obtain ⟨u, rfl⟩ : IsUnit g :=
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit g hr
  exact ⟨u⁻¹.val, map_units_inv _ u⟩

/- English proof (translation)
Establish `hreg : ∀ a, ψ a ∈ regAt ξ ⟨centre z, h⟩`. Introduce `a`. Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨n, hn, hi⟩` from `halg.exists_integral_multiple`. Use `haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective`.

Establish `h1` using `int_reg hN ψ ⟨centre z, h⟩ ⟨n • a, hi⟩`. Establish `h2 : ValAt ξ z (n : Ω) (n : L)` using `⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩`. Establish `h3` using `inv_reg h h2 (IsUnit.mk0 _ (by exact_mod_cast hn))`. Establish `e : ψ a = (n : Ω)⁻¹ * ψ (n • a)`. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ (by exact_mod_cast hn)]`.

Rewrite using `[e]`. Conclude with `mul_mem h3 h1`. Set `e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩` to `RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), (genMap ξ ⟨centre z, h⟩).rangeRestrict_surjective⟩`. Use `⟨(Scheme.stalkClosedPointTo z).hom.comp (e.symm.toRingHom.comp (ψ.codRestrict _ hreg)), fun a => ⟨h, e.symm ⟨ψ a, hreg a⟩, congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hreg a⟩), rfl⟩⟩` and prove the remaining obligations.
-/
theorem exists_const (hξ : IsCptGen ξ) (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω)
    {L : Type} [Field L] [CharZero L] (z : Spec (CommRingCat.of L) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ψL : F →+* L, ∀ a, ValAt ξ z (ψ a) (ψL a) := by
  have hreg : ∀ a, ψ a ∈ regAt ξ ⟨centre z, h⟩ := by
    intro a
    have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
    haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
    have h1 := int_reg hN ψ ⟨centre z, h⟩ ⟨n • a, hi⟩
    have h2 : ValAt ξ z (n : Ω) (n : L) := ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩
    have h3 := inv_reg h h2 (IsUnit.mk0 _ (by exact_mod_cast hn))
    have e : ψ a = (n : Ω)⁻¹ * ψ (n • a) := by
      rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ (by exact_mod_cast hn)]
    rw [e]
    exact mul_mem h3 h1
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), (genMap ξ ⟨centre z, h⟩).rangeRestrict_surjective⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp (e.symm.toRingHom.comp (ψ.codRestrict _ hreg)), fun a =>
    ⟨h, e.symm ⟨ψ a, hreg a⟩, congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hreg a⟩), rfl⟩⟩

/- English proof (translation)
Take `⟨h1, s, hs, rfl⟩` from `h`. Take `⟨_, s', hs', rfl⟩` from `h'`. Rewrite using `[hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]`.
-/
theorem val_unique (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨_, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

end Val

/- English proof (translation)
Set `r : 𝓞 F →+* L` to `(Spec.preimage (z ≫ s)).hom`. Establish `hr : z ≫ s = spMap r`. Simplify using `[r, spMap]`. Establish `hinj : Function.Injective r`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`.

Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `n hn`. Establish `h0 : r (algebraMap ℤ (𝓞 F) n) = 0` using `hn`. Establish `: (n : L) = 0` using `by simpa using h0`.

Simplify using `using this`. Establish `hr' : (IsFractionRing.lift (K` using `F) hinj : F →+* L).comp (algebraMap (𝓞 F) F) = r := RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hinj a`. Use `⟨pullback.lift z (spMap (IsFractionRing.lift (K := F) hinj)) ?_, pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Rewrite using `[hr]`. Use `conv_lhs => rw [← hr']`.

Simplify using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem exists_lift_genFibre {F L : Type} [Field F] [NumberField F] [Field L] [CharZero L] {W : Scheme.{0}}
    (s : W ⟶ Spec (CommRingCat.of (𝓞 F))) (z : Spec (CommRingCat.of L) ⟶ W) :
    ∃ u : Spec (CommRingCat.of L) ⟶ pullback s (spMap (algebraMap (𝓞 F) F)), u ≫ pullback.fst _ _ = z := by
  let r : 𝓞 F →+* L := (Spec.preimage (z ≫ s)).hom
  have hr : z ≫ s = spMap r := by
    simp [r, spMap]
  have hinj : Function.Injective r := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
    have : (n : L) = 0 := by simpa using h0
    simpa using this
  have hr' : (IsFractionRing.lift (K := F) hinj : F →+* L).comp (algebraMap (𝓞 F) F) = r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hinj a
  refine ⟨pullback.lift z (spMap (IsFractionRing.lift (K := F) hinj)) ?_, pullback.lift_fst _ _ _⟩
  rw [hr]
  conv_lhs => rw [← hr']
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Pt

open Pt in
/- English proof (translation)
Introduce `E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 F' _ _ ψ p κ' hgen`. Use `haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective`. Establish `hN : NormalCpt 𝔐.ξ` using `normalCpt_of_tie 𝔐.tie 𝔐.normal`. Use `haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))`. Establish `hind : Topology.IsInducing (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `(pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing`.

Establish `hopen : IsOpen (Set.range Y.jQ)` using `by haveI := Y.jQ_open`. Conclude with `Y.jQ.isOpenEmbedding.isOpen_range`. Take `⟨C, hC, hCe⟩` from `hind.isClosed_iff.1 hopen.isClosed_compl`. Set `W : 𝔐.X.Opens` to `⟨(𝔐.f ⁻¹' C)ᶜ, (hC.preimage 𝔐.f.continuous).isOpen_compl⟩`. Establish `hW : genPt 𝔐.ξ ∈ W`.

Express the relevant statement in the definitionally equal form `𝔐.f (genPt 𝔐.ξ) ∉ C`. Rewrite using `[CptIn.Intr.genPt_dominates 𝔐.fn_over, hgen]`. Establish `h1 : genPt (Z.ξ₀ ≫ Y.j) = pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (Y.jQ (genPt Z.ξ₀))`. Simplify using `[genPt, Model.j, Scheme.Hom.comp_apply]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Introduce `hin`. Establish `: Y.jQ (genPt Z.ξ₀) ∈ (Set.range Y.jQ)ᶜ`. Rewrite using `[← hCe]`. Conclude with `hin`.

Conclude with `this ⟨_, rfl⟩`. Take `⟨L, _, _, zL, hzW⟩` from `exists_point 𝔐.tie W hW`. Establish `hint : 𝔐.Interior zL`. Use `(abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre zL)).1 ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `exists_lift_genFibre Y.s (zL ≫ 𝔐.f)`.

Set `u₀` to `u (IsLocalRing.closedPoint (CommRingCat.of L))`. Establish `hfu : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) u₀ = 𝔐.f (centre zL)`. Use `congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of L))) hu` as an intermediate fact. Conclude with `this`. Establish `hr : u₀ ∈ Set.range Y.jQ`.

Assume the negation of the conclusion as `hn`. Establish `: u₀ ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' C`. Rewrite using `[hCe]`. Conclude with `hn`. Apply `hzW` to reduce the goal to its premises.

Rewrite `this` using `[Set.mem_preimage, hfu]`. Conclude with `this`. Rewrite `hr` using `[← Y.ab_gen]`. Rewrite using `[← hfu]`. Conclude with `hr`.

Take `⟨ψL, hψL⟩` from `exists_const 𝔐.tie.gen hN ψ zL (𝔐.all _)`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j : L →+* ℂ_[p], j.comp ψL = κ' := by`. Use `letI := ψL.toAlgebra`. Use `letI := κ'.toAlgebra`. Use `haveI : Algebra.IsAlgebraic F' L := Algebra.IsAlgebraic.tower_top (K := ℚ) F'`.

Set `φ : L →ₐ[F'] ℂ_[p]` to `IsAlgClosed.lift`. Conclude with `⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩`. Take `⟨V, _, _, _, _, _, hV⟩` from `exists_dvr j`. Take `⟨s₀, hft, hqc, -⟩` from `ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie`. Use `haveI : IsProper s₀ := LocModel.isProper_of_coordTie 𝔐.all 𝔐.tie s₀`.

Take `⟨z, ⟨hz, -⟩, -⟩` from `existsUnique_valuationRing_lift ℤ V L (Int.castRingHom V) 𝔐.X s₀ zL (specZIsTerminal.hom_ext _ _)`. Substitute `hz` using the available equality. Use `⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, j, ψL, z, hV, hj, hint, hψL, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨u, s, hs, rfl⟩` from `exists_frac κ' ha`. Rewrite using `[map_mul, map_inv₀]`.

Use `mul_mem (int_reg hN ψ _ u) ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `int_reg hN ψ ⟨centre z, 𝔐.all _⟩ s`. Establish `hv : ValAt 𝔐.ξ z (ψ (s : F')) ((Scheme.stalkClosedPointTo z).hom g)` using `⟨𝔐.all _, g, hg, rfl⟩`. Use `inv_reg _ hv ?_` and prove the remaining obligations. Establish `h1` using `val_unique 𝔐.tie.gen (ChangeRing.valAt_change _ _ _ V L (algebraMap V L) z _ _ hv (𝔐.all _)) (hψL s)`.

Establish `h2 : ‖j (ψL s)‖ = 1`. Establish `: j (ψL s) = κ' s` using `by rw [← hj]; rfl`. Rewrite using `[this]`. Conclude with `norm_eq_one κ' hs`. Establish `h0 : ψL s ≠ 0`.

Introduce `h`. Rewrite `h2` using `[h, map_zero, norm_zero]`. Conclude with `zero_ne_one h2`. Take `⟨w, hw⟩` from `(hV (ψL s)⁻¹).1 (by rw [map_inv₀, norm_inv, h2, inv_one])`. Use `IsUnit.of_mul_eq_one w (IsFractionRing.injective V L ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, map_one, hw]`. Conclude with `(congrArg (· * _) h1).trans (mul_inv_cancel₀ h0)`.
-/
theorem pointEx : PointEx := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 F' _ _ ψ p κ' hgen
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hN : NormalCpt 𝔐.ξ := normalCpt_of_tie 𝔐.tie 𝔐.normal
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  have hind : Topology.IsInducing (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing
  have hopen : IsOpen (Set.range Y.jQ) := by
    haveI := Y.jQ_open
    exact Y.jQ.isOpenEmbedding.isOpen_range
  obtain ⟨C, hC, hCe⟩ := hind.isClosed_iff.1 hopen.isClosed_compl
  let W : 𝔐.X.Opens := ⟨(𝔐.f ⁻¹' C)ᶜ, (hC.preimage 𝔐.f.continuous).isOpen_compl⟩
  have hW : genPt 𝔐.ξ ∈ W := by
    change 𝔐.f (genPt 𝔐.ξ) ∉ C
    rw [CptIn.Intr.genPt_dominates 𝔐.fn_over, hgen]
    have h1 : genPt (Z.ξ₀ ≫ Y.j) = pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (Y.jQ (genPt Z.ξ₀)) := by
      simp [genPt, Model.j, Scheme.Hom.comp_apply]
      rfl
    rw [h1]
    intro hin
    have : Y.jQ (genPt Z.ξ₀) ∈ (Set.range Y.jQ)ᶜ := by
      rw [← hCe]
      exact hin
    exact this ⟨_, rfl⟩
  obtain ⟨L, _, _, zL, hzW⟩ := exists_point 𝔐.tie W hW
  have hint : 𝔐.Interior zL := by
    refine (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre zL)).1 ?_
    obtain ⟨u, hu⟩ := exists_lift_genFibre Y.s (zL ≫ 𝔐.f)
    let u₀ := u (IsLocalRing.closedPoint (CommRingCat.of L))
    have hfu : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) u₀ = 𝔐.f (centre zL) := by
      have := congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of L))) hu
      exact this
    have hr : u₀ ∈ Set.range Y.jQ := by
      by_contra hn
      have : u₀ ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' C := by
        rw [hCe]
        exact hn
      apply hzW
      rw [Set.mem_preimage, hfu] at this
      exact this
    rw [← Y.ab_gen] at hr
    rw [← hfu]
    exact hr
  obtain ⟨ψL, hψL⟩ := exists_const 𝔐.tie.gen hN ψ zL (𝔐.all _)
  obtain ⟨j, hj⟩ : ∃ j : L →+* ℂ_[p], j.comp ψL = κ' := by
    letI := ψL.toAlgebra
    letI := κ'.toAlgebra
    haveI : Algebra.IsAlgebraic F' L := Algebra.IsAlgebraic.tower_top (K := ℚ) F'
    let φ : L →ₐ[F'] ℂ_[p] := IsAlgClosed.lift
    exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
  obtain ⟨V, _, _, _, _, _, hV⟩ := exists_dvr j
  obtain ⟨s₀, hft, hqc, -⟩ := ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie
  haveI : IsProper s₀ := LocModel.isProper_of_coordTie 𝔐.all 𝔐.tie s₀
  obtain ⟨z, ⟨hz, -⟩, -⟩ := existsUnique_valuationRing_lift ℤ V L (Int.castRingHom V) 𝔐.X s₀ zL
    (specZIsTerminal.hom_ext _ _)
  subst hz
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    j, ψL, z, hV, hj, hint, hψL, fun a ha => ?_⟩
  obtain ⟨u, s, hs, rfl⟩ := exists_frac κ' ha
  rw [map_mul, map_inv₀]
  refine mul_mem (int_reg hN ψ _ u) ?_
  obtain ⟨g, hg⟩ := int_reg hN ψ ⟨centre z, 𝔐.all _⟩ s
  have hv : ValAt 𝔐.ξ z (ψ (s : F')) ((Scheme.stalkClosedPointTo z).hom g) := ⟨𝔐.all _, g, hg, rfl⟩
  refine inv_reg _ hv ?_
  have h1 := val_unique 𝔐.tie.gen
    (ChangeRing.valAt_change _ _ _ V L (algebraMap V L) z _ _ hv (𝔐.all _)) (hψL s)
  have h2 : ‖j (ψL s)‖ = 1 := by
    have : j (ψL s) = κ' s := by rw [← hj]; rfl
    rw [this]
    exact norm_eq_one κ' hs
  have h0 : ψL s ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  obtain ⟨w, hw⟩ := (hV (ψL s)⁻¹).1 (by rw [map_inv₀, norm_inv, h2, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V L ?_)
  rw [map_mul, map_one, hw]
  exact (congrArg (· * _) h1).trans (mul_inv_cancel₀ h0)

end RootFieldNumerics.RF
