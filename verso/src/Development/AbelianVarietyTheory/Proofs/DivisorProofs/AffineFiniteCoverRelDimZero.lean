import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfFiniteTypeOfComapEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeHeightComapFiniteTypeStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

open TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.FiniteNear

/- English proof (translation)
Establish `: T1Space X` using `t1Space_iff_specializes_imp_eq.2 h`. Establish `hfin` using `NoetherianSpace.finite_irreducibleComponents (α := X)`. Establish `hZ : ∀ Z ∈ irreducibleComponents X, Z.Finite` using `fun Z hZ => by`. Take `⟨x, hx⟩` from `QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)`. Rewrite using `[← hx.def, closure_singleton]`.

Conclude with `Set.finite_singleton x`. Establish `hu : (Set.univ : Set X) ⊆ ⋃ Z ∈ irreducibleComponents X, Z` using `fun x _ => Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents x) (mem_irreducibleComponent)`. Conclude with `Set.finite_univ_iff.1 ((hfin.biUnion hZ).subset hu)`.
-/
theorem finite_of_specializes_imp_eq {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (h : ∀ x y : X, x ⤳ y → x = y) : Finite X := by
  have : T1Space X := t1Space_iff_specializes_imp_eq.2 h
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have hZ : ∀ Z ∈ irreducibleComponents X, Z.Finite := fun Z hZ => by
    obtain ⟨x, hx⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    rw [← hx.def, closure_singleton]
    exact Set.finite_singleton x
  have hu : (Set.univ : Set X) ⊆ ⋃ Z ∈ irreducibleComponents X, Z := fun x _ =>
    Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents x) (mem_irreducibleComponent)
  exact Set.finite_univ_iff.1 ((hfin.biUnion hZ).subset hu)

/- English proof (translation)
Establish `hη : genericPoint X ∈ U` using `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩`. Use `(Specializes.antisymm ?_ (genericPoint_specializes (α := X) _)).eq` and prove the remaining obligations. Establish `h1 : hU.fromSpec (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(X, U)) ⤳ hU.fromSpec (hU.primeIdealOf ⟨_, hη⟩)` using `Specializes.map ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le) hU.fromSpec.continuous`. Rewrite `h1` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.
-/
theorem fromSpec_bot {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    [IsDomain Γ(X, U)] :
    hU.fromSpec (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(X, U)) = genericPoint X := by
  have hη : genericPoint X ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  refine (Specializes.antisymm ?_ (genericPoint_specializes (α := X) _)).eq
  have h1 : hU.fromSpec (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(X, U)) ⤳ hU.fromSpec (hU.primeIdealOf ⟨_, hη⟩) :=
    Specializes.map ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le) hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf] at h1

end GlobalTheory.Vert.FiniteNear

namespace GlobalTheory.Vert.FiniteNear
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Model O}

attribute [local instance low] specializationOrder in

/- English proof (translation)
Establish `hη : f.f (genericPoint B'.X) = genericPoint B.X` using `apply_genericPoint_of_isDominant f.f`. Choose the witnesses or unpack the hypotheses as in `⟨w, rfl⟩ : z ∈ Set.range (f.f.fiberι (genericPoint B.X)) := by`. Rewrite using `[Scheme.Hom.range_fiberι]`. Conclude with `hz`. Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : genericPoint B'.X ∈ Set.range (f.f.fiberι (genericPoint B.X)) := by`.

Rewrite using `[Scheme.Hom.range_fiberι]`. Conclude with `hη`. Establish `hsp : w₀ ⤳ w` using `(f.f.fiberι _).isEmbedding.isInducing.specializes_iff.1 (hw₀ ▸ genericPoint_specializes (α := B'.X) _)`. Establish `hd : topologicalKrullDim (f.f.fiber (genericPoint B.X)) ≤ 0`. Use `f.dim_genFibre_le` as an intermediate fact.

Rewrite `this` using `[hf]`. Conclude with `this` after adjusting the coercions. Rewrite `hd` using `[show topologicalKrullDim (f.f.fiber (genericPoint B.X)) = Order.krullDim (f.f.fiber (genericPoint B.X)) from Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := f.f.fiber (genericPoint B.X)))]`. Establish `hle : w ≤ w₀` using `hsp`. Rewrite using `[← hw₀, (Order.krullDim_nonpos_iff_forall_isMin.1 hd w₀).eq_of_le hle]`.
-/
theorem eq_genericPoint (f : Model.Hom B' B) (hf : f.relDim = 0) (z : B'.X)
    (hz : f.f z = genericPoint B.X) : z = genericPoint B'.X := by
  have hη : f.f (genericPoint B'.X) = genericPoint B.X := apply_genericPoint_of_isDominant f.f
  obtain ⟨w, rfl⟩ : z ∈ Set.range (f.f.fiberι (genericPoint B.X)) := by
    rw [Scheme.Hom.range_fiberι]; exact hz
  obtain ⟨w₀, hw₀⟩ : genericPoint B'.X ∈ Set.range (f.f.fiberι (genericPoint B.X)) := by
    rw [Scheme.Hom.range_fiberι]; exact hη
  have hsp : w₀ ⤳ w := (f.f.fiberι _).isEmbedding.isInducing.specializes_iff.1
    (hw₀ ▸ genericPoint_specializes (α := B'.X) _)
  have hd : topologicalKrullDim (f.f.fiber (genericPoint B.X)) ≤ 0 := by
    have := f.dim_genFibre_le
    rw [hf] at this
    exact_mod_cast this
  rw [show topologicalKrullDim (f.f.fiber (genericPoint B.X)) = Order.krullDim (f.f.fiber (genericPoint B.X)) from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := f.f.fiber (genericPoint B.X)))] at hd
  have hle : w ≤ w₀ := hsp
  rw [← hw₀, (Order.krullDim_nonpos_iff_forall_isMin.1 hd w₀).eq_of_le hle]

end GlobalTheory.Vert.FiniteNear

namespace GlobalTheory.Vert.FiniteNear
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Model O}

/- English proof (translation)
Take `⟨V, hV, hyV, -⟩` from `Opens.isBasis_iff_nbhd.1 B.X.isBasis_affineOpens (Opens.mem_top y)`. Take `⟨U, hU, hxU', hUV⟩` from `Opens.isBasis_iff_nbhd.1 B'.X.isBasis_affineOpens (show x' ∈ f.f ⁻¹ᵁ V from show f.f x' ∈ V from hx' ▸ hyV)`. Use `replace hV : IsAffineOpen V := hV`. Use `replace hU : IsAffineOpen U := hU`. Establish `hxU : x ∈ U` using `hs.mem_open U.isOpen hxU'`.

Establish `: Nonempty U` using `⟨⟨x, hxU⟩⟩`. Establish `: Nonempty V` using `⟨⟨y, hyV⟩⟩`. Establish `: IsNoetherianRing Γ(B.X, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Use `letI := (f.f.appLE V U hUV).hom.toAlgebra`. Establish `: Algebra.FiniteType Γ(B.X, V) Γ(B'.X, U)` using `f.f.finiteType_appLE hV hU hUV`.

Establish `key (P : PrimeSpectrum Γ(B'.X, U)) : hV.fromSpec (PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) P) = f.f (hU.fromSpec P)`. Use `congrArg (fun g => g.base P) (IsAffineOpen.SpecMap_appLE_fromSpec f.f hV hU hUV)` as an intermediate fact. Conclude with `this`. Establish `hfη : f.f (genericPoint B'.X) = genericPoint B.X` using `apply_genericPoint_of_isDominant f.f`. Establish `hη'` using `fromSpec_bot hU hxU`.

Establish `hη` using `fromSpec_bot hV hyV`. Establish `hcb : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨⊥, Ideal.isPrime_bot⟩ = ⟨⊥, Ideal.isPrime_bot⟩` using `hV.fromSpec.isOpenEmbedding.injective (by rw [key, hη', hfη, hη])`. Establish `hinj : Function.Injective (algebraMap Γ(B.X, V) Γ(B'.X, U))`. Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Establish `h : a ∈ (PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨⊥, Ideal.isPrime_bot⟩).asIdeal`.

Express the relevant statement in the definitionally equal form `algebraMap Γ(B.X, V) Γ(B'.X, U) a ∈ (⊥ : Ideal Γ(B'.X, U))`. Rewrite using `[ha]`. Conclude with `Ideal.zero_mem _`. Rewrite `h` using `[hcb]`. Conclude with `h`.

Establish `: FaithfulSMul Γ(B.X, V) Γ(B'.X, U)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `hgen : ∀ Q : Ideal Γ(B'.X, U), Q.IsPrime → Q.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = ⊥ → Q = ⊥`. Introduce `Q hQ hc`. Establish `hP : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨Q, hQ⟩ = ⟨⊥, Ideal.isPrime_bot⟩` using `PrimeSpectrum.ext hc`. Establish `h1 : f.f (hU.fromSpec ⟨Q, hQ⟩) = genericPoint B.X` using `by rw [← key, hP, hη]`.

Establish `h2 : (⟨Q, hQ⟩ : PrimeSpectrum Γ(B'.X, U)) = ⟨⊥, Ideal.isPrime_bot⟩` using `hU.fromSpec.isOpenEmbedding.injective ((eq_genericPoint f hf _ h1).trans hη'.symm)`. Conclude with `congrArg PrimeSpectrum.asIdeal h2`. Establish `: Algebra.IsAlgebraic Γ(B.X, V) Γ(B'.X, U)` using `GlobalTheory.isAlgebraic_of_finiteType_of_comap_eq_bot _ _ hgen`. Use `set Px := hU.primeIdealOf ⟨x, hxU⟩ with hPx`. Use `set Px' := hU.primeIdealOf ⟨x', hxU'⟩ with hPx'`.

Use `set Py := hV.primeIdealOf ⟨y, hyV⟩ with hPy`. Establish `ex : hU.fromSpec Px = x` using `hU.fromSpec_primeIdealOf _`. Establish `ex' : hU.fromSpec Px' = x'` using `hU.fromSpec_primeIdealOf _`. Establish `ey : hV.fromSpec Py = y` using `hV.fromSpec_primeIdealOf _`. Establish `hc : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) Px = Py` using `hV.fromSpec.isOpenEmbedding.injective (by rw [key, ex, ey, hx])`.

Establish `hc' : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) Px' = Py` using `hV.fromSpec.isOpenEmbedding.injective (by rw [key, ex', ey, hx'])`. Establish `hle : Px ≤ Px'` using `(PrimeSpectrum.le_iff_specializes _ _).2 (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 (by rw [ex, ex']; exact hs))`. Use `letI := B.X.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)`. Use `haveI : IsLocalization.AtPrime (B.X.presheaf.stalk y) Py.asIdeal := hV.isLocalization_stalk ⟨y, hyV⟩`. Establish `hPy1 : (Py.asIdeal.height : WithBot ℕ∞) ≤ 1`.

Rewrite using `[← IsLocalization.AtPrime.ringKrullDim_eq_height Py.asIdeal (B.X.presheaf.stalk y)]`. Conclude with `hy`. Assume the negation of the conclusion as `hne`. Establish `hne' : Px ≠ Px'` using `fun h => hne (by rw [← ex, ← ex', h])`. Distinguish the cases in `h0 : Px.asIdeal = ⊥`.

Apply `hne'` to reduce the goal to its premises. Establish `h1 : Px'.asIdeal.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = ⊥`. Use `congrArg PrimeSpectrum.asIdeal (hc'.trans hc.symm)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Px.asIdeal.comap _ = ⊥`.

Rewrite using `[h0]`. Conclude with `Ideal.comap_bot_of_injective _ hinj`. Conclude with `PrimeSpectrum.ext (h0.trans (hgen _ inferInstance h1).symm)`. Establish `hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(B'.X, U)) < Px` using `lt_of_le_of_ne (fun _ h => by rw [Ideal.mem_bot.1 h]; exact Px.asIdeal.zero_mem) (fun h => h0 (congrArg PrimeSpectrum.asIdeal h).symm)`. Establish `h2 : (2 : ℕ∞) ≤ Order.height Px'`.

Establish `a1` using `Order.height_add_one_le hb`. Establish `a2` using `Order.height_add_one_le (lt_of_le_of_ne hle hne')`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `GlobalTheory.T.height_le_height_comap_finite_type Γ(B.X, V) Γ(B'.X, U) Px'.asIdeal`. Rewrite `h3` using `[show Px'.asIdeal.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = Py.asIdeal from congrArg PrimeSpectrum.asIdeal hc', PrimeSpectrum.height_eq_orderHeight Px']`.

Establish `h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1` using `(WithBot.coe_le_coe.2 (h2.trans h3)).trans hPy1`. Conclude with `absurd h4 (by decide)`.
-/
theorem eq_of_specializes (f : Model.Hom B' B) (hf : f.relDim = 0) {y : B.X}
    (hy : ringKrullDim (B.X.presheaf.stalk y) ≤ 1) {x x' : B'.X} (hx : f.f x = y) (hx' : f.f x' = y)
    (hs : x ⤳ x') : x = x' := by
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.1 B.X.isBasis_affineOpens (Opens.mem_top y)
  obtain ⟨U, hU, hxU', hUV⟩ := Opens.isBasis_iff_nbhd.1 B'.X.isBasis_affineOpens
    (show x' ∈ f.f ⁻¹ᵁ V from show f.f x' ∈ V from hx' ▸ hyV)
  replace hV : IsAffineOpen V := hV
  replace hU : IsAffineOpen U := hU
  have hxU : x ∈ U := hs.mem_open U.isOpen hxU'
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have : IsNoetherianRing Γ(B.X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := (f.f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(B.X, V) Γ(B'.X, U) := f.f.finiteType_appLE hV hU hUV

  have key (P : PrimeSpectrum Γ(B'.X, U)) :
      hV.fromSpec (PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) P) = f.f (hU.fromSpec P) := by
    have := congrArg (fun g => g.base P) (IsAffineOpen.SpecMap_appLE_fromSpec f.f hV hU hUV)
    exact this
  have hfη : f.f (genericPoint B'.X) = genericPoint B.X := apply_genericPoint_of_isDominant f.f
  have hη' := fromSpec_bot hU hxU
  have hη := fromSpec_bot hV hyV
  have hcb : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨⊥, Ideal.isPrime_bot⟩ =
      ⟨⊥, Ideal.isPrime_bot⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (by rw [key, hη', hfη, hη])
  have hinj : Function.Injective (algebraMap Γ(B.X, V) Γ(B'.X, U)) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h : a ∈ (PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨⊥, Ideal.isPrime_bot⟩).asIdeal := by
      change algebraMap Γ(B.X, V) Γ(B'.X, U) a ∈ (⊥ : Ideal Γ(B'.X, U))
      rw [ha]; exact Ideal.zero_mem _
    rw [hcb] at h
    exact h
  have : FaithfulSMul Γ(B.X, V) Γ(B'.X, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hgen : ∀ Q : Ideal Γ(B'.X, U), Q.IsPrime → Q.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = ⊥ → Q = ⊥ := by
    intro Q hQ hc
    have hP : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) ⟨Q, hQ⟩ = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext hc
    have h1 : f.f (hU.fromSpec ⟨Q, hQ⟩) = genericPoint B.X := by rw [← key, hP, hη]
    have h2 : (⟨Q, hQ⟩ : PrimeSpectrum Γ(B'.X, U)) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      hU.fromSpec.isOpenEmbedding.injective ((eq_genericPoint f hf _ h1).trans hη'.symm)
    exact congrArg PrimeSpectrum.asIdeal h2
  have : Algebra.IsAlgebraic Γ(B.X, V) Γ(B'.X, U) := GlobalTheory.isAlgebraic_of_finiteType_of_comap_eq_bot _ _ hgen
  set Px := hU.primeIdealOf ⟨x, hxU⟩ with hPx
  set Px' := hU.primeIdealOf ⟨x', hxU'⟩ with hPx'
  set Py := hV.primeIdealOf ⟨y, hyV⟩ with hPy
  have ex : hU.fromSpec Px = x := hU.fromSpec_primeIdealOf _
  have ex' : hU.fromSpec Px' = x' := hU.fromSpec_primeIdealOf _
  have ey : hV.fromSpec Py = y := hV.fromSpec_primeIdealOf _
  have hc : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) Px = Py :=
    hV.fromSpec.isOpenEmbedding.injective (by rw [key, ex, ey, hx])
  have hc' : PrimeSpectrum.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) Px' = Py :=
    hV.fromSpec.isOpenEmbedding.injective (by rw [key, ex', ey, hx'])
  have hle : Px ≤ Px' := (PrimeSpectrum.le_iff_specializes _ _).2
    (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 (by rw [ex, ex']; exact hs))
  letI := B.X.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
  haveI : IsLocalization.AtPrime (B.X.presheaf.stalk y) Py.asIdeal := hV.isLocalization_stalk ⟨y, hyV⟩
  have hPy1 : (Py.asIdeal.height : WithBot ℕ∞) ≤ 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Py.asIdeal (B.X.presheaf.stalk y)]
    exact hy
  by_contra hne
  have hne' : Px ≠ Px' := fun h => hne (by rw [← ex, ← ex', h])
  by_cases h0 : Px.asIdeal = ⊥
  · apply hne'
    have h1 : Px'.asIdeal.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = ⊥ := by
      have := congrArg PrimeSpectrum.asIdeal (hc'.trans hc.symm)
      refine this.trans ?_
      change Px.asIdeal.comap _ = ⊥
      rw [h0]; exact Ideal.comap_bot_of_injective _ hinj
    exact PrimeSpectrum.ext (h0.trans (hgen _ inferInstance h1).symm)
  · have hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(B'.X, U)) < Px :=
      lt_of_le_of_ne (fun _ h => by rw [Ideal.mem_bot.1 h]; exact Px.asIdeal.zero_mem)
        (fun h => h0 (congrArg PrimeSpectrum.asIdeal h).symm)
    have h2 : (2 : ℕ∞) ≤ Order.height Px' := by
      have a1 := Order.height_add_one_le hb
      have a2 := Order.height_add_one_le (lt_of_le_of_ne hle hne')
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.height (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(B'.X, U)) + 1 + 1 := by gcongr; exact bot_le
        _ ≤ Order.height Px + 1 := by gcongr
        _ ≤ Order.height Px' := a2
    have h3 := GlobalTheory.T.height_le_height_comap_finite_type Γ(B.X, V) Γ(B'.X, U) Px'.asIdeal
    rw [show Px'.asIdeal.comap (algebraMap Γ(B.X, V) Γ(B'.X, U)) = Py.asIdeal from congrArg PrimeSpectrum.asIdeal hc',
      PrimeSpectrum.height_eq_orderHeight Px'] at h3
    have h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := (WithBot.coe_le_coe.2 (h2.trans h3)).trans hPy1
    exact absurd h4 (by decide)

/- English proof (translation)
Take `⟨U', rfl⟩ : ∃ U' : V.toScheme.Opens, V.ι ''ᵁ U' = U` from `⟨V.ι ⁻¹ᵁ U, by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using e⟩`. Establish `hU' : IsAffineOpen U'` using `(V.ι.isAffineOpen_iff_of_isOpenImmersion).1 hU`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← image_morphismRestrict_preimage]`. Conclude with `(hU'.preimage (π ∣_ V)).image_of_isOpenImmersion _`.

Use `IsFinite.finite_app (π ∣_ V) U' hU'` as an intermediate fact. Rewrite `this` using `[morphismRestrict_app]`. Conclude with `(RingHom.finite_respectsIso.cancel_right_isIso _ _).1 this`.
-/
theorem finite_app_of_le {X Y : Scheme.{0}} (π : Y ⟶ X) {V U : X.Opens} [IsFinite (π ∣_ V)]
    (hU : IsAffineOpen U) (e : U ≤ V) :
    IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite := by
  obtain ⟨U', rfl⟩ : ∃ U' : V.toScheme.Opens, V.ι ''ᵁ U' = U :=
    ⟨V.ι ⁻¹ᵁ U, by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using e⟩
  have hU' : IsAffineOpen U' := (V.ι.isAffineOpen_iff_of_isOpenImmersion).1 hU
  refine ⟨?_, ?_⟩
  · rw [← image_morphismRestrict_preimage]
    exact (hU'.preimage (π ∣_ V)).image_of_isOpenImmersion _
  · have := IsFinite.finite_app (π ∣_ V) U' hU'
    rw [morphismRestrict_app] at this
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).1 this

/- English proof (translation)
Establish `hemb` using `(f.f.fiberι y).isEmbedding`. Establish `: NoetherianSpace (f.f.fiber y)` using `hemb.isInducing.noetherianSpace`. Establish `hmem (w : f.f.fiber y) : f.f (f.f.fiberι y w) = y`. Establish `: f.f.fiberι y w ∈ Set.range (f.f.fiberι y)` using `⟨w, rfl⟩`. Rewrite `this` using `[Scheme.Hom.range_fiberι]`.

Conclude with `this`. Establish `: Finite (f.f.fiber y)` using `finite_of_specializes_imp_eq fun w w' h => hemb.injective (eq_of_specializes f hf hy (hmem w) (hmem w') (h.map hemb.continuous))`. Rewrite using `[← Scheme.Hom.range_fiberι]`. Conclude with `Set.finite_range _`.
-/
theorem finite_preimage (f : Model.Hom B' B) (hf : f.relDim = 0) {y : B.X}
    (hy : ringKrullDim (B.X.presheaf.stalk y) ≤ 1) : (f.f ⁻¹' {y}).Finite := by
  have hemb := (f.f.fiberι y).isEmbedding
  have : NoetherianSpace (f.f.fiber y) := hemb.isInducing.noetherianSpace
  have hmem (w : f.f.fiber y) : f.f (f.f.fiberι y w) = y := by
    have : f.f.fiberι y w ∈ Set.range (f.f.fiberι y) := ⟨w, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have : Finite (f.f.fiber y) := finite_of_specializes_imp_eq fun w w' h =>
    hemb.injective (eq_of_specializes f hf hy (hmem w) (hmem w') (h.map hemb.continuous))
  rw [← Scheme.Hom.range_fiberι]
  exact Set.finite_range _

/- English proof (translation)
Take `⟨V₀, hV₀, hfin⟩` from `exists_isFinite_morphismRestrict_of_finite_preimage_singleton f.f y (finite_preimage f hf hy)`. Take `⟨V, hV, hyV, hle⟩` from `Opens.isBasis_iff_nbhd.1 B.X.isBasis_affineOpens hV₀`. Use `replace hV : IsAffineOpen V := hV`. Take `⟨hW, hF⟩` from `finite_app_of_le f.f hV hle`. Conclude with `⟨V, hyV, hV, hW, hF⟩`.
-/
theorem exists_affine_finite (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (hf : f.relDim = 0) (y : B.X)
    (hy : ringKrullDim (B.X.presheaf.stalk y) ≤ 1) :
    ∃ V : B.X.Opens, y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
      (letI := (f.f.app V).hom.toAlgebra; Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V)) := by
  obtain ⟨V₀, hV₀, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f.f y
    (finite_preimage f hf hy)
  obtain ⟨V, hV, hyV, hle⟩ := Opens.isBasis_iff_nbhd.1 B.X.isBasis_affineOpens hV₀
  replace hV : IsAffineOpen V := hV
  obtain ⟨hW, hF⟩ := finite_app_of_le f.f hV hle
  exact ⟨V, hyV, hV, hW, hF⟩

end GlobalTheory.Vert.FiniteNear
