import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.HasExponentMulOfIsUnram
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PowFamIsDeligneMeas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactors
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

/- English proof (translation)
Establish `hint : IsIntegral ℤ (algebraMap F Ω (x : F))` using `(RingOfIntegers.isIntegral_coe x).map (algebraMap F Ω).toIntAlgHom`. Establish `hA : IsIntegral A (algebraMap F Ω (x : F))` using `hint.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hA`. Rewrite using `[← hy]`. Conclude with `A.valuation_le_one y`.
-/
theorem valuation_algebraMap_le_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F]
    [Algebra F Ω] (x : 𝓞 F) : A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hint : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
    (RingOfIntegers.isIntegral_coe x).map (algebraMap F Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap F Ω (x : F)) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  rw [← hy]
  exact A.valuation_le_one y

/- English proof (translation)
Establish `hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q`. Establish `h1 : (Polynomial.X : Polynomial R).degree < (Polynomial.X ^ q : Polynomial R).degree`. Rewrite using `[Polynomial.degree_X_pow, Polynomial.degree_X]`. Conclude with `hq` after adjusting the coercions. Rewrite using `[Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_sub_eq_left_of_degree_lt h1), Polynomial.natDegree_X_pow]`.

Establish `hp : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0`. Introduce `h0`. Rewrite `hdeg` using `[h0, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hsub : (Finset.univ : Finset R).val ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial R).roots`.

Introduce `z _`. Rewrite using `[Polynomial.mem_roots hp, Polynomial.IsRoot.def]`. Simplify using `[H z]`. Use `Polynomial.card_le_degree_of_subset_roots hsub` as an intermediate fact. Rewrite `this` using `[hdeg, Finset.card_univ]`. Then use the resulting hypothesis.
-/
theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Fintype R] {q : ℕ} (hq : 1 < q)
    (H : ∀ z : R, z ^ q = z) : Fintype.card R ≤ q := by
  classical
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    have h1 : (Polynomial.X : Polynomial R).degree < (Polynomial.X ^ q : Polynomial R).degree := by
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq
    rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_sub_eq_left_of_degree_lt h1),
      Polynomial.natDegree_X_pow]
  have hp : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; omega
  have hsub : (Finset.univ : Finset R).val ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial R).roots := by
    intro z _
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simp [H z]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rwa [hdeg, Finset.card_univ] at this

section Transport

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}

omit [IsAlgClosure F Ω] in

/- English proof (translation)
Take `⟨f, hf⟩` from `GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver h h'`. Take `⟨φ, hφ⟩` from `exists_isFrob h`. Establish `hq : 1 < normV v` using `one_lt_normV v`. Establish `hφW : φ ∈ Weil h` using `mem_Weil_of_isFrob h hφ`. Establish `key : ∀ x : 𝓞 F, x ^ normV v - x ∈ w.asIdeal`.

Introduce `x`. Rewrite using `[← h' (x ^ normV v - x)]`. Establish `h1` using `hφ.2 _ (valuation_algebraMap_le_one A x)`. Establish `h2 : φ (algebraMap F Ω (x : F)) = algebraMap F Ω (x : F)` using `hloc ⟨φ, hφW⟩ (x : F)`. Rewrite `h1` using `[h2, Valuation.map_sub_swap]`.

Establish `e : algebraMap F Ω ((x ^ normV v - x : 𝓞 F) : F) = algebraMap F Ω (x : F) ^ normV v - algebraMap F Ω (x : F)`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h1`.

Establish `: w.asIdeal.IsPrime` using `w.isPrime`. Establish `: Finite (𝓞 F ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Set `_ : Fintype (𝓞 F ⧸ w.asIdeal)` to `Fintype.ofFinite _`. Establish `hle : normV w ≤ normV v`. Rewrite using `[normV, Nat.card_eq_fintype_card]`.

Use `card_le_of_pow_eq_self hq fun z => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `key x`. Establish `h1w : 1 < normV w` using `one_lt_normV w`.

Rewrite `hle`, `h1w`, the goal using `[hf]`. Establish `hf1 : f ≤ 1`. Conclude with `(pow_le_pow_iff_right₀ hq).mp (show normV v ^ f ≤ normV v ^ 1 by rwa [pow_one])`. Establish `hf0 : f ≠ 0` using `by rintro rfl; simp at h1w`. Establish `: f = 1` using `by omega`.

Rewrite using `[this, pow_one]`.
-/
theorem normV_eq_of_localDegreeOne (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    normV w = normV v := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver h h'
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hq : 1 < normV v := one_lt_normV v
  have hφW : φ ∈ Weil h := mem_Weil_of_isFrob h hφ
  have key : ∀ x : 𝓞 F, x ^ normV v - x ∈ w.asIdeal := by
    intro x
    rw [← h' (x ^ normV v - x)]
    have h1 := hφ.2 _ (valuation_algebraMap_le_one A x)
    have h2 : φ (algebraMap F Ω (x : F)) = algebraMap F Ω (x : F) := hloc ⟨φ, hφW⟩ (x : F)
    rw [h2, Valuation.map_sub_swap] at h1
    have e : algebraMap F Ω ((x ^ normV v - x : 𝓞 F) : F) =
        algebraMap F Ω (x : F) ^ normV v - algebraMap F Ω (x : F) := by
      push_cast
      rfl
    rw [e]
    exact h1
  have : w.asIdeal.IsPrime := w.isPrime
  have : Finite (𝓞 F ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let _ : Fintype (𝓞 F ⧸ w.asIdeal) := Fintype.ofFinite _
  have hle : normV w ≤ normV v := by
    rw [normV, Nat.card_eq_fintype_card]
    refine card_le_of_pow_eq_self hq fun z => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact key x
  have h1w : 1 < normV w := one_lt_normV w
  rw [hf] at hle h1w ⊢
  have hf1 : f ≤ 1 := by
    exact (pow_le_pow_iff_right₀ hq).mp (show normV v ^ f ≤ normV v ^ 1 by rwa [pow_one])
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1w
  have : f = 1 := by omega
  rw [this, pow_one]

/- English proof (translation)
Establish `hn` using `normV_eq_of_localDegreeOne h h' hloc`. Establish `inj : Function.Injective (GlobalTheory.WeilRestrict.resWeil h h')`. Introduce `σ τ e`. Use `Subtype.ext (AlgEquiv.ext fun z => ?_)` and prove the remaining obligations. Use `congrArg (fun ρ : Weil h => (ρ : G K Ω) z) e` as an intermediate fact.

Simplify `this` using `[GlobalTheory.WeilRestrict.resWeil_apply]`. Establish `surj : Function.Surjective (GlobalTheory.WeilRestrict.resWeil h h')`. Introduce `σ`. Set `τ : G F Ω` to `AlgEquiv.ofRingEquiv (f := (σ : G K Ω).toRingEquiv) (fun x => hloc σ x)`. Establish `hτ : τ ∈ Weil h'`.

Take `⟨a, b, hab⟩` from `(mem_Weil h).1 σ.2`. Use `(mem_Weil h').2 ⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`. Conclude with `⟨hab.1, hab.2⟩`. Conclude with `⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun z => rfl)⟩`.

Conclude with `⟨MulEquiv.ofBijective (GlobalTheory.WeilRestrict.resWeil h h') ⟨inj, surj⟩, fun σ z => rfl⟩`.
-/
theorem weil_equiv_of_localDegreeOne (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    ∃ r : Weil h' ≃* Weil h, ∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G F Ω) z := by
  have hn := normV_eq_of_localDegreeOne h h' hloc
  have inj : Function.Injective (GlobalTheory.WeilRestrict.resWeil h h') := by
    intro σ τ e
    refine Subtype.ext (AlgEquiv.ext fun z => ?_)
    have := congrArg (fun ρ : Weil h => (ρ : G K Ω) z) e
    simpa [GlobalTheory.WeilRestrict.resWeil_apply] using this
  have surj : Function.Surjective (GlobalTheory.WeilRestrict.resWeil h h') := by
    intro σ
    let τ : G F Ω := AlgEquiv.ofRingEquiv (f := (σ : G K Ω).toRingEquiv) (fun x => hloc σ x)
    have hτ : τ ∈ Weil h' := by
      obtain ⟨a, b, hab⟩ := (mem_Weil h).1 σ.2
      refine (mem_Weil h').2 ⟨a, b, ?_⟩
      rw [hn]
      exact ⟨hab.1, hab.2⟩
    exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun z => rfl)⟩
  exact ⟨MulEquiv.ofBijective (GlobalTheory.WeilRestrict.resWeil h h') ⟨inj, surj⟩, fun σ z => rfl⟩

end Transport

section GlobalModel

/- English proof (translation)
Establish `: Finite (𝓞 K ⧸ v.asIdeal)` using `v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Set `_ : Fintype (𝓞 K ⧸ v.asIdeal)` to `Fintype.ofFinite _`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, normV, Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`.
-/
theorem natCast_normV_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ((normV v : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, normV, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

/- English proof (translation)
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Establish `hD : (σ : G K Ω) ∈ Dec (F` using `K) A := Weil_le_Dec h σ.2`. Establish `hnA : A.valuation ((normV v : ℕ) : Ω) < 1`. Use `(h ((normV v : ℕ) : 𝓞 K)).mpr (natCast_normV_mem v)` as an intermediate fact. Simplify using `using this`.

Establish `hs' : s ^ 2 = 1 - 4 * ((normV v : ℕ) : Ω)`. Rewrite using `[hs, map_sub, map_one, map_mul, map_ofNat, map_natCast]`. Use `set y : Ω := (s - 1) * 2⁻¹ with hydef`. Establish `hy : y * (y + 1) = -((normV v : ℕ) : Ω)`. Rewrite using `[hydef]`.

Take the linear combination `(2⁻¹ * 2⁻¹ : Ω) * hs'`. Establish `hσs : ((σ : G K Ω) s) ^ 2 = s ^ 2`. Rewrite using `[← map_pow, hs, AlgEquiv.commutes]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hσs with h1 | h1` into its components or cases. Conclude with `h1`.

It suffices to derive a contradiction. Establish `hσy : (σ : G K Ω) y = -1 - y`. Rewrite using `[hydef, map_mul, map_sub, map_one, map_inv₀, map_ofNat, h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hprod : A.valuation y * A.valuation (y + 1) < 1`.

Rewrite using `[← map_mul, hy, Valuation.map_neg]`. Conclude with `hnA`. Distinguish the cases in `hyl : A.valuation y < 1`. Establish `h2 : A.valuation ((σ : G K Ω) y) < 1` using `(valuation_apply_lt_one_iff hD y).mpr hyl`. Rewrite `h2` using `[hσy]`.

Establish `h3 : A.valuation ((-1 - y) + y) < 1` using `Valuation.map_add_lt _ h2 hyl`. Rewrite `h3` using `[show (-1 - y) + y = -1 by ring, Valuation.map_neg, map_one]`. Conclude with `lt_irrefl _ h3`. Establish `hyl' : 1 ≤ A.valuation y` using `not_lt.mp hyl`. Establish `hy1 : A.valuation (y + 1) < 1`.

Assume the negation of the conclusion as `hc`. Use `mul_le_mul' hyl' (not_lt.mp hc)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `absurd hprod (not_lt.mpr this)`. Establish `h2 : A.valuation ((σ : G K Ω) (y + 1)) < 1` using `(valuation_apply_lt_one_iff hD _).mpr hy1`.

Rewrite `h2` using `[map_add, map_one, hσy, show -1 - y + 1 = -y by ring, Valuation.map_neg]`. Conclude with `absurd h2 (not_lt.mpr hyl')`.
-/
theorem weil_fix_sqrt {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) {s : Ω}
    (hs : s ^ 2 = algebraMap K Ω (1 - 4 * (normV v : K))) (σ : Weil h) : (σ : G K Ω) s = s := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hD : (σ : G K Ω) ∈ Dec (F := K) A := Weil_le_Dec h σ.2
  have hnA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 K)).mpr (natCast_normV_mem v)
    simpa using this
  have hs' : s ^ 2 = 1 - 4 * ((normV v : ℕ) : Ω) := by
    rw [hs, map_sub, map_one, map_mul, map_ofNat, map_natCast]
  set y : Ω := (s - 1) * 2⁻¹ with hydef
  have hy : y * (y + 1) = -((normV v : ℕ) : Ω) := by
    rw [hydef]
    linear_combination (2⁻¹ * 2⁻¹ : Ω) * hs'
  have hσs : ((σ : G K Ω) s) ^ 2 = s ^ 2 := by
    rw [← map_pow, hs, AlgEquiv.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hσs with h1 | h1
  · exact h1
  exfalso
  have hσy : (σ : G K Ω) y = -1 - y := by
    rw [hydef, map_mul, map_sub, map_one, map_inv₀, map_ofNat, h1]
    ring
  have hprod : A.valuation y * A.valuation (y + 1) < 1 := by
    rw [← map_mul, hy, Valuation.map_neg]
    exact hnA
  by_cases hyl : A.valuation y < 1
  · have h2 : A.valuation ((σ : G K Ω) y) < 1 := (valuation_apply_lt_one_iff hD y).mpr hyl
    rw [hσy] at h2
    have h3 : A.valuation ((-1 - y) + y) < 1 := Valuation.map_add_lt _ h2 hyl
    rw [show (-1 - y) + y = -1 by ring, Valuation.map_neg, map_one] at h3
    exact lt_irrefl _ h3
  · have hyl' : 1 ≤ A.valuation y := not_lt.mp hyl
    have hy1 : A.valuation (y + 1) < 1 := by
      by_contra hc
      have := mul_le_mul' hyl' (not_lt.mp hc)
      rw [one_mul] at this
      exact absurd hprod (not_lt.mpr this)
    have h2 : A.valuation ((σ : G K Ω) (y + 1)) < 1 := (valuation_apply_lt_one_iff hD _).mpr hy1
    rw [map_add, map_one, hσy, show -1 - y + 1 = -y by ring, Valuation.map_neg] at h2
    exact absurd h2 (not_lt.mpr hyl')

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed K`. Establish `: Algebra.IsIntegral K Ω` using `(IsAlgClosure.isAlgebraic (R := K) (K := Ω)).isIntegral`. Take `⟨M, hMfin, -, hMN⟩` from `GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup K Ω A v h N hN hopen`. Take `⟨s, hs⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (1 - 4 * (normV v : K))) (n := 2) two_pos`. Establish `: FiniteDimensional K M` using `hMfin`.

Establish `: ∀ i, FiniteDimensional K (E i)` using `hE`. Establish `: FiniteDimensional K (IntermediateField.adjoin K {s})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)`. Set `M₂ : IntermediateField K Ω` to `(M ⊔ ⨆ i, E i) ⊔ IntermediateField.adjoin K {s}`. Set `F' : IntermediateField K Ω` to `IntermediateField.normalClosure K M₂ Ω`. Establish `hM₂ : M₂ ≤ F'` using `IntermediateField.le_normalClosure M₂`.

Establish `hMF' : M ≤ F'` using `le_trans (le_trans le_sup_left le_sup_left) hM₂`. Establish `hF'norm : Normal K F'` using `normalClosure.normal K M₂ Ω`. Set `F : IntermediateField K Ω` to `F' ⊓ IntermediateField.fixedField (Weil h)`. Establish `hfixF : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (x : Ω) = x`. Introduce `σ x`.

Conclude with `((IntermediateField.mem_fixedField_iff _ _).mp (IntermediateField.mem_inf.mp x.2).2) σ σ.2`. Establish `hsF : s ∈ F`. Use `IntermediateField.mem_inf.mpr ⟨hM₂ (le_sup_right (a := M ⊔ ⨆ i, E i) (IntermediateField.mem_adjoin_simple_self K s)), ?_⟩` and prove the remaining obligations. Conclude with `(IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ => weil_fix_sqrt h hs ⟨σ, hσ⟩`. Establish `htc : IsTotallyComplex F`.

Prove the components needed by the constructor for the conclusion. Introduce `w`. Rewrite using `[NumberField.InfinitePlace.isComplex_iff]`. Introduce `hreal`. Set `t : F` to `⟨s, hsF⟩`.

Establish `ht : t ^ 2 = algebraMap K F (1 - 4 * (normV v : K))` using `Subtype.ext hs`. Establish `hφ : (w.embedding t) ^ 2 = 1 - 4 * ((normV v : ℕ) : ℂ)`. Rewrite using `[← map_pow, ht]`. Simplify using `only [map_sub, map_one, map_mul, map_ofNat, map_natCast]`. Rewrite `hφ` using `[← hreal.coe_embedding_apply t]`.

Establish `hR : (hreal.embedding t) ^ 2 = 1 - 4 * ((normV v : ℕ) : ℝ)` using `by exact_mod_cast hφ`. Establish `hn : (1 : ℝ) ≤ ((normV v : ℕ) : ℝ)` using `by exact_mod_cast (one_lt_normV v).le`. Use polynomial arithmetic with `[sq_nonneg (hreal.embedding t)]`. Use `⟨F, F', normalClosure.is_finiteDimensional K M₂ Ω, inf_le_left, htc, hfixF, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`.

Conclude with `(hMN σ).mpr fun x => hσ ⟨x, hMF' x.2⟩`. Introduce `τ hτ`. Establish `: IsGalois K F'` using `isGalois_iff.mpr ⟨inferInstance, hF'norm⟩`. Establish `: FiniteDimensional K F'` using `normalClosure.is_finiteDimensional K M₂ Ω`. Set `res : G K Ω →* (F' ≃ₐ[K] F')` to `AlgEquiv.restrictNormalHom F'`.

Set `H : Subgroup (F' ≃ₐ[K] F')` to `(Weil h).map res`. Establish `hmem : res τ ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField H)`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[AlgEquiv.restrictNormalHom_apply]`. Use `hτ ⟨(x : Ω), IntermediateField.mem_inf.mpr ⟨x.2, ?_⟩⟩` and prove the remaining obligations. Use `(IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ => ?_` and prove the remaining obligations. Establish `h1` using `(IntermediateField.mem_fixedField_iff _ _).mp hx (res σ) ⟨σ, hσ, rfl⟩`. Establish `h2` using `congrArg Subtype.val h1`.

Rewrite `h2` using `[AlgEquiv.restrictNormalHom_apply]`. Then use the resulting hypothesis. Rewrite `hmem` using `[IntermediateField.fixingSubgroup_fixedField]`. Take `⟨σ, hσ, hστ⟩` from `Subgroup.mem_map.mp hmem`. Use `⟨⟨σ, hσ⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun g : F' ≃ₐ[K] F' => ((g x : F') : Ω)) hστ`.

Simplify using `only [res, AlgEquiv.restrictNormalHom_apply] at h1`. Conclude with `h1`. Introduce `τ _ x hx`. Conclude with `IntermediateField.normal_iff_forall_map_le'.mp hF'norm τ ⟨x, hx, rfl⟩`. Introduce `i`.

Conclude with `le_trans (le_trans (le_iSup E i) le_sup_right) (le_trans le_sup_left hM₂)`.
-/
theorem exists_globalModel_fields {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (N : Subgroup (Weil h))
    (hN : N.FiniteIndex) (hopen : IsOpen {σ : Ine (F := K) A | ineIncl h σ ∈ N})
    {r : ℕ} (E : Fin r → IntermediateField K Ω) (hE : ∀ i, FiniteDimensional K (E i)) :
    ∃ F F' : IntermediateField K Ω, FiniteDimensional K F' ∧ F ≤ F' ∧ IsTotallyComplex F ∧
      (∀ (σ : Weil h) (x : F), (σ : G K Ω) (x : Ω) = x) ∧
      (∀ σ : Weil h, (∀ x : F', (σ : G K Ω) (x : Ω) = x) → σ ∈ N) ∧
      (∀ τ : G K Ω, (∀ x : F, τ (x : Ω) = x) → ∃ σ : Weil h, ∀ x : F', (σ : G K Ω) (x : Ω) = τ x) ∧
      (∀ τ : G K Ω, (∀ x : F, τ (x : Ω) = x) → ∀ x ∈ F', τ x ∈ F') ∧
      (∀ i, E i ≤ F') := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Algebra.IsIntegral K Ω := (IsAlgClosure.isAlgebraic (R := K) (K := Ω)).isIntegral
  obtain ⟨M, hMfin, -, hMN⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup K Ω A v h N hN hopen
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (1 - 4 * (normV v : K))) (n := 2) two_pos
  have : FiniteDimensional K M := hMfin
  have : ∀ i, FiniteDimensional K (E i) := hE
  have : FiniteDimensional K (IntermediateField.adjoin K {s}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  let M₂ : IntermediateField K Ω := (M ⊔ ⨆ i, E i) ⊔ IntermediateField.adjoin K {s}
  let F' : IntermediateField K Ω := IntermediateField.normalClosure K M₂ Ω
  have hM₂ : M₂ ≤ F' := IntermediateField.le_normalClosure M₂
  have hMF' : M ≤ F' := le_trans (le_trans le_sup_left le_sup_left) hM₂
  have hF'norm : Normal K F' := normalClosure.normal K M₂ Ω
  let F : IntermediateField K Ω := F' ⊓ IntermediateField.fixedField (Weil h)
  have hfixF : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (x : Ω) = x := by
    intro σ x
    exact ((IntermediateField.mem_fixedField_iff _ _).mp (IntermediateField.mem_inf.mp x.2).2) σ σ.2
  have hsF : s ∈ F := by
    refine IntermediateField.mem_inf.mpr ⟨hM₂ (le_sup_right (a := M ⊔ ⨆ i, E i)
      (IntermediateField.mem_adjoin_simple_self K s)), ?_⟩
    exact (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ => weil_fix_sqrt h hs ⟨σ, hσ⟩
  have htc : IsTotallyComplex F := by
    constructor
    intro w
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hreal
    let t : F := ⟨s, hsF⟩
    have ht : t ^ 2 = algebraMap K F (1 - 4 * (normV v : K)) := Subtype.ext hs
    have hφ : (w.embedding t) ^ 2 = 1 - 4 * ((normV v : ℕ) : ℂ) := by
      rw [← map_pow, ht]
      simp only [map_sub, map_one, map_mul, map_ofNat, map_natCast]
    rw [← hreal.coe_embedding_apply t] at hφ
    have hR : (hreal.embedding t) ^ 2 = 1 - 4 * ((normV v : ℕ) : ℝ) := by exact_mod_cast hφ
    have hn : (1 : ℝ) ≤ ((normV v : ℕ) : ℝ) := by exact_mod_cast (one_lt_normV v).le
    nlinarith [sq_nonneg (hreal.embedding t)]
  refine ⟨F, F', normalClosure.is_finiteDimensional K M₂ Ω, inf_le_left, htc, hfixF, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    exact (hMN σ).mpr fun x => hσ ⟨x, hMF' x.2⟩
  · intro τ hτ
    have : IsGalois K F' := isGalois_iff.mpr ⟨inferInstance, hF'norm⟩
    have : FiniteDimensional K F' := normalClosure.is_finiteDimensional K M₂ Ω
    let res : G K Ω →* (F' ≃ₐ[K] F') := AlgEquiv.restrictNormalHom F'
    let H : Subgroup (F' ≃ₐ[K] F') := (Weil h).map res
    have hmem : res τ ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField H) := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      refine hτ ⟨(x : Ω), IntermediateField.mem_inf.mpr ⟨x.2, ?_⟩⟩
      refine (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ => ?_
      have h1 := (IntermediateField.mem_fixedField_iff _ _).mp hx (res σ) ⟨σ, hσ, rfl⟩
      have h2 := congrArg Subtype.val h1
      rwa [AlgEquiv.restrictNormalHom_apply] at h2
    rw [IntermediateField.fixingSubgroup_fixedField] at hmem
    obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hmem
    refine ⟨⟨σ, hσ⟩, fun x => ?_⟩
    have h1 := congrArg (fun g : F' ≃ₐ[K] F' => ((g x : F') : Ω)) hστ
    simp only [res, AlgEquiv.restrictNormalHom_apply] at h1
    exact h1
  · intro τ _ x hx
    exact IntermediateField.normal_iff_forall_map_le'.mp hF'norm τ ⟨x, hx, rfl⟩
  · intro i
    exact le_trans (le_trans (le_iSup E i) le_sup_right) (le_trans le_sup_left hM₂)

/- English proof (translation)
Take `⟨F, F', h1, h2, h3, h4, h5, h6, h7, -⟩` from `exists_globalModel_fields A h N hN hopen (r := 0) Fin.elim0 (fun i => Fin.elim0 i)`. Conclude with `⟨F, F', h1, h2, h3, h4, h5, h6, h7⟩`.
-/
theorem exists_globalModel {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (N : Subgroup (Weil h))
    (hN : N.FiniteIndex) (hopen : IsOpen {σ : Ine (F := K) A | ineIncl h σ ∈ N}) :
    ∃ F F' : IntermediateField K Ω, FiniteDimensional K F' ∧ F ≤ F' ∧ IsTotallyComplex F ∧
      (∀ (σ : Weil h) (x : F), (σ : G K Ω) (x : Ω) = x) ∧
      (∀ σ : Weil h, (∀ x : F', (σ : G K Ω) (x : Ω) = x) → σ ∈ N) ∧
      (∀ τ : G K Ω, (∀ x : F, τ (x : Ω) = x) → ∃ σ : Weil h, ∀ x : F', (σ : G K Ω) (x : Ω) = τ x) ∧
      (∀ τ : G K Ω, (∀ x : F, τ (x : Ω) = x) → ∀ x ∈ F', τ x ∈ F') := by
  obtain ⟨F, F', h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    exists_globalModel_fields A h N hN hopen (r := 0) Fin.elim0 (fun i => Fin.elim0 i)
  exact ⟨F, F', h1, h2, h3, h4, h5, h6, h7⟩

end GlobalModel

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
