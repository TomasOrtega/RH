import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

def PrimeDivisor (X : Scheme.{u}) : Type u :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

abbrev WeilDivisor (X : Scheme.{u}) : Type u := PrimeDivisor X →₀ ℤ

variable {X : Scheme.{u}}

namespace PrimeDivisor

def point (x : PrimeDivisor X) : X := x.1

/- English proof (translation)
The claim follows from `x.2`.
-/
lemma ringKrullDim_stalk (x : PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk x.point) = 1 := x.2

/- English proof (translation)
Establish `h` using `x.ringKrullDim_stalk`. Rewrite `h` using `[ringKrullDim_stalk_eq_coheight]`. Conclude with `h` after adjusting the coercions.
-/
lemma coheight_point (x : PrimeDivisor X) : Order.coheight x.point = 1 := by
  have h := x.ringKrullDim_stalk
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext h`.
-/
lemma point_injective : Function.Injective (point (X := X)) := fun _ _ h => Subtype.ext h

/- English proof (translation)
Introduce `h`. Establish `hf : IsField (X.presheaf.stalk x.point)` using `(IsLocalRing.isField_iff_maximalIdeal_eq).mpr h`. Use `x.ringKrullDim_stalk` as an intermediate fact. Rewrite `this` using `[ringKrullDim_eq_zero_of_isField hf]`. Conclude with `zero_ne_one this`.
-/
lemma maximalIdeal_ne_bot (x : PrimeDivisor X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) ≠ ⊥ := by
  intro h
  have hf : IsField (X.presheaf.stalk x.point) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  have := x.ringKrullDim_stalk
  rw [ringKrullDim_eq_zero_of_isField hf] at this
  exact zero_ne_one this

variable [IsIntegral X]

/- English proof (translation)
Establish `hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point)`. Rewrite using `[Ring.krullDimLE_iff, x.ringKrullDim_stalk]`. Evaluate the numerical expressions. Use `⟨fun {p} hp hprime => ?_⟩` and prove the remaining obligations. Break down `Ring.krullDimLE_one_iff.mp hle p hprime with h | h` into its components or cases.

Rewrite `h` using `[IsDomain.minimalPrimes_eq_singleton_bot]`. Conclude with `absurd h hp`. Conclude with `h`.
-/
lemma dimensionLEOne_stalk (x : PrimeDivisor X) :
    Ring.DimensionLEOne (X.presheaf.stalk x.point) := by
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point) := by
    rw [Ring.krullDimLE_iff, x.ringKrullDim_stalk]
    norm_num
  refine ⟨fun {p} hp hprime => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
  · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
    exact absurd h hp
  · exact h

variable [IsLocallyNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Use `x.dimensionLEOne_stalk` as an intermediate fact. Use `IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point` as an intermediate fact. Conclude with `(isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr ⟨inferInstance, inferInstance, inferInstance, fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩`.
-/
lemma isDedekindDomain_stalk (x : PrimeDivisor X) :
    IsDedekindDomain (X.presheaf.stalk x.point) := by
  have := x.dimensionLEOne_stalk
  have := IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point
  exact (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩

noncomputable def heightOneSpectrum (x : PrimeDivisor X) :
    HeightOneSpectrum (X.presheaf.stalk x.point) :=
  ⟨IsLocalRing.maximalIdeal _, (IsLocalRing.maximalIdeal.isMaximal _).isPrime,
    x.maximalIdeal_ne_bot⟩

noncomputable def valuation (x : PrimeDivisor X) : Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
  @HeightOneSpectrum.valuation _ _ x.isDedekindDomain_stalk _ _ _ _ x.heightOneSpectrum

noncomputable def ord (x : PrimeDivisor X) (f : X.functionField) : ℤ :=
  - WithZero.log (x.valuation f)

/- English proof (translation)
Simplify using `only [ord, map_mul]`. Rewrite using `[WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ord_mul (x : PrimeDivisor X) {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    x.ord (f * g) = x.ord f + x.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]
  ring

/- English proof (translation)
Simplify using `[ord]`.
-/
lemma ord_one (x : PrimeDivisor X) : x.ord 1 = 0 := by
  simp [ord]

end PrimeDivisor

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Use `x.isDedekindDomain_stalk` as an intermediate fact. Establish `h1 : x.valuation (algebraMap _ X.functionField a) = 1`. Simplify using `only [valuation]`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha`.

Simplify using `[ord, h1]`.
-/
lemma ord_algebraMap_of_isUnit (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsUnit a) : x.ord (algebraMap _ X.functionField a) = 0 := by
  have := x.isDedekindDomain_stalk
  have h1 : x.valuation (algebraMap _ X.functionField a) = 1 := by
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha
  simp [ord, h1]

/- English proof (translation)
Rewrite using `[← Scheme.algebraMap_germ_eq_germToFunctionField X hx]`. Conclude with `x.ord_algebraMap_of_isUnit (hg.map _)`.
-/
lemma ord_germToFunctionField_of_isUnit (x : PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (hx : x.point ∈ U) {g : Γ(X, U)} (hg : IsUnit g) :
    x.ord (X.germToFunctionField U g) = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact x.ord_algebraMap_of_isUnit (hg.map _)

end PrimeDivisor

/- English proof (translation)
Use `set c := hT.genericPoint`. Establish `hc : IsGenericPoint c T`. Use `hT.isGenericPoint_genericPoint_closure` as an intermediate fact. Rewrite `this` using `[hTc.closure_eq]`. Then use the resulting hypothesis. Establish `hcx : c ⤳ x.point` using `hc.specializes hx`.

Establish `hcT : c ∈ T` using `hc.mem`. Establish `hηc : genericPoint X ⤳ c` using `(genericPoint_spec X).specializes (Set.mem_univ _)`. Establish `hηne : genericPoint X ≠ c` using `fun h => hgen (h ▸ hcT)`. Establish `hlt1 : c < genericPoint X`. Use `⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hlt2 : x.point < c` using `⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩`. Establish `h1` using `Order.coheight_add_one_le hlt1`. Establish `h2` using `Order.coheight_add_one_le hlt2`. Rewrite `h2` using `[x.coheight_point]`.

Establish `h4 : (1 : ℕ∞) ≤ Order.coheight c` using `le_trans le_add_self h1`. Establish `h5 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (add_le_add_left h4 1) h2`. Evaluate the numerical expressions using `at h5`.
-/
lemma PrimeDivisor.eq_genericPoint_of_mem [IsIntegral X] (x : PrimeDivisor X) {T : Set X}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hgen : genericPoint X ∉ T) (hx : x.point ∈ T) :
    x.point = hT.genericPoint := by
  set c := hT.genericPoint
  have hc : IsGenericPoint c T := by
    have := hT.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  have hcx : c ⤳ x.point := hc.specializes hx
  have hcT : c ∈ T := hc.mem
  have hηc : genericPoint X ⤳ c := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hηne : genericPoint X ≠ c := fun h => hgen (h ▸ hcT)
  have hlt1 : c < genericPoint X := by
    refine ⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩
  by_contra hne
  have hlt2 : x.point < c := ⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h2 := Order.coheight_add_one_le hlt2
  rw [x.coheight_point] at h2
  have h4 : (1 : ℕ∞) ≤ Order.coheight c := le_trans le_add_self h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h4 1) h2
  norm_num at h5

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Take `⟨U, -, g, hne, hgf, hgu⟩` from `exists_isUnit_germ_eq X f hf`. Use `set Z : Set X := (U : Set X)ᶜ with hZ`. Establish `hZc : IsClosed Z` using `U.isOpen.isClosed_compl`. Establish `hgenU : genericPoint X ∈ U`. Take `⟨⟨y, hy⟩⟩` from `hne`.

Conclude with `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩`. Establish `hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z}`. Introduce `x hx`. Assume the negation of the conclusion as `hxU`. Simplify using `only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU`.

Conclude with `hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)`. Use `Set.Finite.subset ?_ hsub` and prove the remaining obligations. Establish `key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z), C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C → ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint`. Introduce `x hx C hC hxC`. Establish `hT : IsIrreducible (closure (Subtype.val '' C))` using `(hC.1.image _ continuous_subtype_val.continuousOn).closure`.

Use `⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩` and prove the remaining obligations. Introduce `hg`. Establish `: closure (Subtype.val '' C) ⊆ Z` using `closure_minimal (Subtype.coe_image_subset _ _) hZc`. Conclude with `this hg hgenU`. Conclude with `subset_closure ⟨_, hxC, rfl⟩`.

Establish `hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z, {(⟨x.1.point, x.2⟩ : Z)} ⊆ C` using `fun x => exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton`. Set `φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z` to `fun x => ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩`. Establish `: Finite (irreducibleComponents Z)` using `(NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype`. Establish `hφ : Function.Injective φ`. Introduce `x y hxy`.

Establish `hx` using `(hcomp x).choose_spec`. Establish `hy` using `(hcomp y).choose_spec`. Establish `hC : (hcomp x).choose = (hcomp y).choose` using `congrArg Subtype.val hxy`. Take `⟨hT, hxT⟩` from `key x.1 x.2 _ hx.1 (hx.2 rfl)`. Take `⟨hT', hyT⟩` from `key y.1 y.2 _ hy.1 (hy.2 rfl)`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `PrimeDivisor.point_injective` to reduce the goal to its premises. Rewrite using `[hxT, hyT]`. Simplify using `only [hC]`. Establish `: Finite {x : PrimeDivisor X | x.point ∈ Z}` using `Finite.of_injective φ hφ`.

Conclude with `Set.toFinite _`.
-/
theorem PrimeDivisor.finite_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : PrimeDivisor X | x.ord f ≠ 0}.Finite := by
  obtain ⟨U, -, g, hne, hgf, hgu⟩ := exists_isUnit_germ_eq X f hf
  set Z : Set X := (U : Set X)ᶜ with hZ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have hgenU : genericPoint X ∈ U := by
    obtain ⟨⟨y, hy⟩⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z} := by
    intro x hx
    by_contra hxU
    simp only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU
    exact hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)
  refine Set.Finite.subset ?_ hsub
  have key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z),
      C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C →
      ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint := by
    intro x hx C hC hxC
    have hT : IsIrreducible (closure (Subtype.val '' C)) :=
      (hC.1.image _ continuous_subtype_val.continuousOn).closure
    refine ⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩
    · intro hg
      have : closure (Subtype.val '' C) ⊆ Z :=
        closure_minimal (Subtype.coe_image_subset _ _) hZc
      exact this hg hgenU
    · exact subset_closure ⟨_, hxC, rfl⟩
  have hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z,
      {(⟨x.1.point, x.2⟩ : Z)} ⊆ C := fun x =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton
  let φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z := fun x =>
    ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := (hcomp x).choose_spec
    have hy := (hcomp y).choose_spec
    have hC : (hcomp x).choose = (hcomp y).choose := congrArg Subtype.val hxy
    obtain ⟨hT, hxT⟩ := key x.1 x.2 _ hx.1 (hx.2 rfl)
    obtain ⟨hT', hyT⟩ := key y.1 y.2 _ hy.1 (hy.2 rfl)
    apply Subtype.ext
    apply PrimeDivisor.point_injective
    rw [hxT, hyT]
    simp only [hC]
  have : Finite {x : PrimeDivisor X | x.point ∈ Z} := Finite.of_injective φ hφ
  exact Set.toFinite _

end Finite

section Divisor

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

noncomputable def divisorOf (f : (X.functionField)ˣ) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x => x.ord (f : X.functionField))
    (PrimeDivisor.finite_ord_ne_zero f.ne_zero)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma divisorOf_apply (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    divisorOf f x = x.ord (f : X.functionField) := rfl

noncomputable def principalDivisor : Additive (X.functionField)ˣ →+ WeilDivisor X where
  toFun f := divisorOf f.toMul
  map_zero' := by
    ext x
    simp [divisorOf_apply, PrimeDivisor.ord_one]
  map_add' f g := by
    ext x
    simp only [divisorOf_apply, toMul_add, Units.val_mul, Finsupp.coe_add, Pi.add_apply]
    exact x.ord_mul f.toMul.ne_zero g.toMul.ne_zero

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma principalDivisor_apply (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    principalDivisor (Additive.ofMul f) x = x.ord (f : X.functionField) := rfl

variable (X) in

noncomputable def principalDivisors : AddSubgroup (WeilDivisor X) :=
  (principalDivisor (X := X)).range

variable (X) in

abbrev ClassGroup : Type u := WeilDivisor X ⧸ principalDivisors X

end Divisor

end GroundTheory.Arith.SchemeCoh
