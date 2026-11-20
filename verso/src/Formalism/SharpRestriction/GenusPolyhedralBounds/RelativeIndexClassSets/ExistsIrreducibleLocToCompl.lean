import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section Compl

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/- English proof (translation)
Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K), ← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Use `first`. Consider the case `rfl`. Consider the case `congr 1`. Consider the case `simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]`.
-/
theorem valued_algebraMap_int (a : R) :
    Valued.v ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) : v.adicCompletion K) =
      v.intValuation a := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K),
    ← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  first
  | rfl
  | congr 1
  | simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]

/- English proof (translation)
Rewrite using `[ValuationSubring.valuation_eq_one_iff]`. Establish `h1` using `valued_algebraMap_int K v a`. Establish `h2 : (v.adicCompletionIntegers K).valuation ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 ↔ Valued.v ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1`. Conclude with `(Valuation.isEquiv_valuation_valuationSubring Valued.v).symm.eq_one_iff_eq_one`. Rewrite using `[h2, h1, Ideal.mem_primeCompl_iff, ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]`.

Prove the components needed by the constructor for the conclusion. Introduce `h hlt`. Rewrite `hlt` using `[h]`. Conclude with `lt_irrefl _ hlt`. Introduce `h`.

Conclude with `le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v a) (not_lt.mp h)`.
-/
theorem isUnit_algebraMap_int_iff (a : R) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) a) ↔ a ∈ v.asIdeal.primeCompl := by
  rw [ValuationSubring.valuation_eq_one_iff]
  have h1 := valued_algebraMap_int K v a
  have h2 : (v.adicCompletionIntegers K).valuation
      ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 ↔
      Valued.v ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    exact (Valuation.isEquiv_valuation_valuationSubring Valued.v).symm.eq_one_iff_eq_one
  rw [h2, h1, Ideal.mem_primeCompl_iff, ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  constructor
  · intro h hlt
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    exact le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v a) (not_lt.mp h)

def locToCompl : Localization.AtPrime v.asIdeal →+* v.adicCompletionIntegers K :=
  IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap R (v.adicCompletionIntegers K))
    fun y => (isUnit_algebraMap_int_iff K v y).2 y.2

/- English proof (translation)
Conclude with `IsLocalization.lift_eq (M := v.asIdeal.primeCompl) _ a`.
-/
theorem locToCompl_algebraMap (a : R) :
    locToCompl K v (algebraMap R (Localization.AtPrime v.asIdeal) a) = algebraMap R (v.adicCompletionIntegers K) a := by
  exact IsLocalization.lift_eq (M := v.asIdeal.primeCompl) _ a

/- English proof (translation)
Rewrite using `[ValuationSubring.valuation_eq_one_iff]`. Conclude with `(Valuation.isEquiv_valuation_valuationSubring Valued.v).symm.eq_one_iff_eq_one`.
-/
private lemma irreducible_algebraMap_int_lemma (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring Valued.v).symm.eq_one_iff_eq_one

/- English proof (translation)
Establish `hv : Valued.v ((algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletionIntegers K) : v.adicCompletion K) = WithZero.exp (-1)`. Rewrite using `[valued_algebraMap_int]`. Conclude with `h`. Use `⟨fun hu => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[irreducible_algebraMap_int_lemma, hv]`.

Establish `h1 : (-1 : ℤ) = 0` using `WithZero.exp_inj.mp (hu.trans WithZero.exp_zero.symm)`. Use linear arithmetic over natural numbers and integers. Introduce `y z hyz`. Establish `hy : Valued.v (y : v.adicCompletion K) ≤ 1` using `(IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp y.2`. Establish `hz : Valued.v (z : v.adicCompletion K) ≤ 1` using `(IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp z.2`.

Rewrite `hv` using `[hyz]`. Establish `hyz' : Valued.v (y : v.adicCompletion K) * Valued.v (z : v.adicCompletion K) = WithZero.exp (-1)`. Rewrite using `[← map_mul]`. Conclude with `hv`. Establish `hy0 : Valued.v (y : v.adicCompletion K) ≠ 0`.

Introduce `h0`. Rewrite `hyz'` using `[h0, zero_mul]`. Conclude with `WithZero.exp_ne_zero hyz'.symm`. Establish `hz0 : Valued.v (z : v.adicCompletion K) ≠ 0`. Introduce `h0`.

Rewrite `hyz'` using `[h0, mul_zero]`. Conclude with `WithZero.exp_ne_zero hyz'.symm`. Establish `hm : (Valued.v (y : v.adicCompletion K)).log ≤ 0`. Rewrite using `[← WithZero.exp_le_exp, WithZero.exp_log hy0, WithZero.exp_zero]`. Conclude with `hy`.

Establish `hn : (Valued.v (z : v.adicCompletion K)).log ≤ 0`. Rewrite using `[← WithZero.exp_le_exp, WithZero.exp_log hz0, WithZero.exp_zero]`. Conclude with `hz`. Rewrite `hyz'` using `[← WithZero.exp_log hy0, ← WithZero.exp_log hz0, ← WithZero.exp_add, WithZero.exp_inj]`. Distinguish the cases in `hm0 : (Valued.v (y : v.adicCompletion K)).log = 0`.

Use `left`. Rewrite using `[irreducible_algebraMap_int_lemma, ← WithZero.exp_log hy0, hm0, WithZero.exp_zero]`. Use `right`. Establish `hn0 : (Valued.v (z : v.adicCompletion K)).log = 0` using `by omega`. Rewrite using `[irreducible_algebraMap_int_lemma, ← WithZero.exp_log hz0, hn0, WithZero.exp_zero]`.
-/
theorem irreducible_algebraMap_int {π : R} (h : v.intValuation π = WithZero.exp (-1)) :
    Irreducible (algebraMap R (v.adicCompletionIntegers K) π) := by
  have hv : Valued.v ((algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletionIntegers K) :
      v.adicCompletion K) = WithZero.exp (-1) := by
    rw [valued_algebraMap_int]
    exact h
  refine ⟨fun hu => ?_, ?_⟩
  · rw [irreducible_algebraMap_int_lemma, hv] at hu
    have h1 : (-1 : ℤ) = 0 := WithZero.exp_inj.mp (hu.trans WithZero.exp_zero.symm)
    omega
  · intro y z hyz
    have hy : Valued.v (y : v.adicCompletion K) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp y.2
    have hz : Valued.v (z : v.adicCompletion K) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp z.2
    rw [hyz] at hv
    have hyz' : Valued.v (y : v.adicCompletion K) * Valued.v (z : v.adicCompletion K) = WithZero.exp (-1) := by
      rw [← map_mul]
      exact hv
    have hy0 : Valued.v (y : v.adicCompletion K) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hyz'
      exact WithZero.exp_ne_zero hyz'.symm
    have hz0 : Valued.v (z : v.adicCompletion K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hyz'
      exact WithZero.exp_ne_zero hyz'.symm
    have hm : (Valued.v (y : v.adicCompletion K)).log ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log hy0, WithZero.exp_zero]
      exact hy
    have hn : (Valued.v (z : v.adicCompletion K)).log ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log hz0, WithZero.exp_zero]
      exact hz
    rw [← WithZero.exp_log hy0, ← WithZero.exp_log hz0, ← WithZero.exp_add, WithZero.exp_inj] at hyz'
    by_cases hm0 : (Valued.v (y : v.adicCompletion K)).log = 0
    · left
      rw [irreducible_algebraMap_int_lemma, ← WithZero.exp_log hy0, hm0, WithZero.exp_zero]
    · right
      have hn0 : (Valued.v (z : v.adicCompletion K)).log = 0 := by omega
      rw [irreducible_algebraMap_int_lemma, ← WithZero.exp_log hz0, hn0, WithZero.exp_zero]

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v`. Establish `hirr` using `irreducible_algebraMap_int K v hπ`. Establish `hloc : ∀ x : Localization.AtPrime v.asIdeal, IsUnit (locToCompl K v x) → IsUnit x`. Introduce `x hx`. Break down `IsLocalization.mk'_surjective v.asIdeal.primeCompl x with ⟨⟨r, t⟩, hrt⟩` into its components or cases.

Substitute `hrt` using the available equality. Establish `hspec` using `IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r t`. Establish `hsu : IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) (t : R))` using `IsLocalization.map_units _ t`. Establish `hfr : IsUnit (locToCompl K v (algebraMap R (Localization.AtPrime v.asIdeal) r))`. Rewrite using `[← hspec, map_mul]`.

Conclude with `hx.mul (hsu.map _)`. Rewrite `hfr` using `[locToCompl_algebraMap, isUnit_algebraMap_int_iff]`. Establish `hru : IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) r)` using `IsLocalization.map_units _ ⟨r, hfr⟩`. Rewrite `hru` using `[← hspec]`. Conclude with `isUnit_of_mul_isUnit_left hru`.

Use `⟨algebraMap R (Localization.AtPrime v.asIdeal) π, ⟨fun hu => hirr.not_isUnit ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← locToCompl_algebraMap]`. Conclude with `hu.map _`. Introduce `y z hyz`. Establish `h1 : algebraMap R (v.adicCompletionIntegers K) π = locToCompl K v y * locToCompl K v z`.

Rewrite using `[← locToCompl_algebraMap, hyz, map_mul]`. Break down `hirr.isUnit_or_isUnit h1 with h | h` into its components or cases. Conclude with `Or.inl (hloc y h)`. Conclude with `Or.inr (hloc z h)`. Rewrite using `[locToCompl_algebraMap]`.

Conclude with `hirr`.
-/
theorem exists_irreducible_locToCompl :
    ∃ ϖ : Localization.AtPrime v.asIdeal, Irreducible ϖ ∧ Irreducible (locToCompl K v ϖ) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  have hirr := irreducible_algebraMap_int K v hπ
  have hloc : ∀ x : Localization.AtPrime v.asIdeal, IsUnit (locToCompl K v x) → IsUnit x := by
    intro x hx
    rcases IsLocalization.mk'_surjective v.asIdeal.primeCompl x with ⟨⟨r, t⟩, hrt⟩
    subst hrt
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r t
    have hsu : IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) (t : R)) := IsLocalization.map_units _ t
    have hfr : IsUnit (locToCompl K v (algebraMap R (Localization.AtPrime v.asIdeal) r)) := by
      rw [← hspec, map_mul]
      exact hx.mul (hsu.map _)
    rw [locToCompl_algebraMap, isUnit_algebraMap_int_iff] at hfr
    have hru : IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) r) := IsLocalization.map_units _ ⟨r, hfr⟩
    rw [← hspec] at hru
    exact isUnit_of_mul_isUnit_left hru
  refine ⟨algebraMap R (Localization.AtPrime v.asIdeal) π, ⟨fun hu => hirr.not_isUnit ?_, ?_⟩, ?_⟩
  · rw [← locToCompl_algebraMap]
    exact hu.map _
  · intro y z hyz
    have h1 : algebraMap R (v.adicCompletionIntegers K) π = locToCompl K v y * locToCompl K v z := by
      rw [← locToCompl_algebraMap, hyz, map_mul]
    rcases hirr.isUnit_or_isUnit h1 with h | h
    · exact Or.inl (hloc y h)
    · exact Or.inr (hloc z h)
  · rw [locToCompl_algebraMap]
    exact hirr

/- English proof (translation)
Establish `: IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _`. Set `: Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)` to `(locToCompl K v).toAlgebra`. Take `⟨ϖ, hϖ, hϖ'⟩` from `exists_irreducible_locToCompl K v`. Set `mR : Module R Q'` to `Module.compHom Q' (algebraMap R (v.adicCompletionIntegers K))`. Set `mL : Module (Localization.AtPrime v.asIdeal) Q'` to `Module.compHom Q' (locToCompl K v)`.

Establish `: IsScalarTower R (Localization.AtPrime v.asIdeal) Q'` using `⟨fun a b x => by show locToCompl K v (a • b) • x = algebraMap R (v.adicCompletionIntegers K) a • (locToCompl K v b • x)`. Rewrite using `[Algebra.smul_def, map_mul, locToCompl_algebraMap, mul_smul]⟩`. Set `gR : Q →ₗ[R] Q'` to `{ toFun := g, map_add' := g.map_add, map_smul' := fun a x => g.map_smulₛₗ a x }`. Establish `hu : ∀ s : v.asIdeal.primeCompl, IsUnit (algebraMap R (Module.End R Q') s)`. Introduce `s`.

Rewrite using `[Module.End.isUnit_iff]`. Take `⟨u, hu⟩` from `(isUnit_algebraMap_int_iff K v s).2 s.2`. Establish `: ⇑(algebraMap R (Module.End R Q') s) = fun x => u • x`. Use function extensionality and compare the values at `x`. Use `show algebraMap R (v.adicCompletionIntegers K) (s : R) • x = u • x`.

Rewrite using `[← hu]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `MulAction.bijective u`. Set `l` to `LinearMap.extendScalarsOfIsLocalization v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (LocalizedModule.lift v.asIdeal.primeCompl gR hu)`.

Set `g' : LocalizedModule v.asIdeal.primeCompl Q →ₛₗ[algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)] Q'` to `{ toFun := l, map_add' := l.map_add, map_smul' := fun a x => l.map_smul a x }`. Use `T0.length_le_of_semilinear ϖ hϖ hϖ' g' ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hg]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `⟨LocalizedModule.mkLinearMap _ _ x, LinearMap.congr_fun (LocalizedModule.lift_comp _ gR hu) x⟩`.
-/
theorem length_le_length_localized {Q Q' : Type} [AddCommGroup Q] [Module R Q] [AddCommGroup Q']
    [Module (v.adicCompletionIntegers K) Q'] (g : Q →ₛₗ[algebraMap R (v.adicCompletionIntegers K)] Q')
    (hg : Submodule.span (v.adicCompletionIntegers K) (Set.range g) = ⊤) :
    Module.length (v.adicCompletionIntegers K) Q' ≤
      Module.length (Localization.AtPrime v.asIdeal) (LocalizedModule v.asIdeal.primeCompl Q) := by
  have : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _
  let : Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) := (locToCompl K v).toAlgebra
  obtain ⟨ϖ, hϖ, hϖ'⟩ := exists_irreducible_locToCompl K v
  let mR : Module R Q' := Module.compHom Q' (algebraMap R (v.adicCompletionIntegers K))
  let mL : Module (Localization.AtPrime v.asIdeal) Q' := Module.compHom Q' (locToCompl K v)
  have : IsScalarTower R (Localization.AtPrime v.asIdeal) Q' := ⟨fun a b x => by
    show locToCompl K v (a • b) • x = algebraMap R (v.adicCompletionIntegers K) a • (locToCompl K v b • x)
    rw [Algebra.smul_def, map_mul, locToCompl_algebraMap, mul_smul]⟩
  let gR : Q →ₗ[R] Q' := { toFun := g, map_add' := g.map_add, map_smul' := fun a x => g.map_smulₛₗ a x }
  have hu : ∀ s : v.asIdeal.primeCompl, IsUnit (algebraMap R (Module.End R Q') s) := by
    intro s
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := (isUnit_algebraMap_int_iff K v s).2 s.2
    have : ⇑(algebraMap R (Module.End R Q') s) = fun x => u • x := by
      funext x
      show algebraMap R (v.adicCompletionIntegers K) (s : R) • x = u • x
      rw [← hu]; rfl
    rw [this]
    exact MulAction.bijective u
  let l := LinearMap.extendScalarsOfIsLocalization v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal)
    (LocalizedModule.lift v.asIdeal.primeCompl gR hu)
  let g' : LocalizedModule v.asIdeal.primeCompl Q →ₛₗ[algebraMap (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K)] Q' :=
    { toFun := l, map_add' := l.map_add, map_smul' := fun a x => l.map_smul a x }
  refine T0.length_le_of_semilinear ϖ hϖ hϖ' g' ?_
  rw [eq_top_iff, ← hg]
  refine Submodule.span_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨LocalizedModule.mkLinearMap _ _ x, LinearMap.congr_fun (LocalizedModule.lift_comp _ gR hu) x⟩

/- English proof (translation)
Establish `: IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _`. Establish `h1` using `Formalism.LatticeIndexTer.LatticeIndexLength.length_quot_ne_top (O := Localization.AtPrime v.asIdeal) (M := LocalizedModule v.asIdeal.primeCompl Q) (algebraMap R _ d) (by rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]; exact hd) ⊥ (fun m => by`. Proceed by induction on `m using LocalizedModule.induction_on with`. Consider the case `_ m s`. Rewrite using `[algebraMap_smul, LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk]`.

Conclude with `Submodule.zero_mem _)`. Rewrite `h1` using `[(Submodule.quotEquivOfEqBot ⊥ rfl).length_eq]`. Then use the resulting hypothesis.
-/
theorem length_localized_ne_top {Q : Type} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] (d : R) (hd : d ≠ 0)
    (h : ∀ x : Q, d • x = 0) :
    Module.length (Localization.AtPrime v.asIdeal) (LocalizedModule v.asIdeal.primeCompl Q) ≠ ⊤ := by
  have : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _
  have h1 := Formalism.LatticeIndexTer.LatticeIndexLength.length_quot_ne_top (O := Localization.AtPrime v.asIdeal)
    (M := LocalizedModule v.asIdeal.primeCompl Q) (algebraMap R _ d)
    (by rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]; exact hd) ⊥ (fun m => by
      induction m using LocalizedModule.induction_on with
      | _ m s =>
        rw [algebraMap_smul, LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk]
        exact Submodule.zero_mem _)
  rwa [(Submodule.quotEquivOfEqBot ⊥ rfl).length_eq] at h1

end Compl

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Lat

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (ka : WeightFamilies.Wt D j)

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.WeightAlgebra.PJ.bc, TensorProduct.mk_apply]`. Rewrite using `[← algebraMap_smul B.KO a F, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]`. Rewrite using `[show (algebraMap (𝓞 B.KO) (X.Ol la) a) • ((1 : X.Kl la) ⊗ₜ[B.KO] F) = ((algebraMap (𝓞 B.KO) (X.Ol la) a : X.Ol la) : X.Kl la) • ((1 : X.Kl la) ⊗ₜ[B.KO] F) from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `congr 1`.
-/
theorem bc_smul_int (a : 𝓞 B.KO) (F : X.Forms) :
    X.bc la (a • F) = algebraMap (𝓞 B.KO) (X.Ol la) a • X.bc la F := by
  simp only [Formalism.MainNotions.WeightAlgebra.PJ.bc, TensorProduct.mk_apply]
  rw [← algebraMap_smul B.KO a F, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    ← Algebra.algebraMap_eq_smul_one]
  rw [show (algebraMap (𝓞 B.KO) (X.Ol la) a) • ((1 : X.Kl la) ⊗ₜ[B.KO] F) =
      ((algebraMap (𝓞 B.KO) (X.Ol la) a : X.Ol la) : X.Kl la) • ((1 : X.Kl la) ⊗ₜ[B.KO] F) from rfl,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  congr 1

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Formalism.MainNotions.WeightAlgebra.PJ.loc, Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `Submodule.span_induction (p := fun F _ => X.bc la F ∈ Submodule.span (X.Ol la) (X.bc la '' s)) ?_ ?_ ?_ ?_ hF` and prove the remaining obligations. Introduce `x hx`.

Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Introduce `a x _ hx`. Rewrite using `[bc_smul_int]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[Formalism.MainNotions.WeightAlgebra.PJ.loc]`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem loc_span (s : Set X.Forms) :
    X.loc la (Submodule.span (𝓞 B.KO) s) = Submodule.span (X.Ol la) (X.bc la '' s) := by
  apply le_antisymm
  · rw [Formalism.MainNotions.WeightAlgebra.PJ.loc, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    refine Submodule.span_induction (p := fun F _ => X.bc la F ∈ Submodule.span (X.Ol la) (X.bc la '' s))
      ?_ ?_ ?_ ?_ hF
    · intro x hx
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [bc_smul_int]
      exact Submodule.smul_mem _ _ hx
  · rw [Formalism.MainNotions.WeightAlgebra.PJ.loc]
    exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Establish `hle : X.loc la N ≤ (T0.WL X ka la).restrictScalars (X.Ol la)`. Unfold `Formalism.MainNotions.WeightAlgebra.PJ.loc`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Conclude with `Submodule.subset_span ⟨n, hN hn, rfl⟩`.

Apply `Submodule.fg_of_fg_map_injective ((T0.WL X ka la).subtype.restrictScalars (X.Ol la)) Subtype.val_injective` to reduce the goal to its premises. Use `show (Submodule.map _ (Submodule.comap _ (X.loc la N))).FG`. Rewrite using `[Submodule.map_comap_eq, inf_eq_right.mpr (fun x hx => ⟨⟨x, hle hx⟩, rfl⟩)]`. Take `⟨S, hS⟩` from `hfg`. Rewrite using `[← hS, loc_span]`.

Conclude with `Submodule.fg_span (S.finite_toSet.image _)`.
-/
theorem inW_loc_fg (N : Submodule (𝓞 B.KO) X.Forms) (hN : N ≤ X.Msup ka) (hfg : N.FG) :
    (T0.inW X ka la (X.loc la N)).FG := by
  have hle : X.loc la N ≤ (T0.WL X ka la).restrictScalars (X.Ol la) := by
    unfold Formalism.MainNotions.WeightAlgebra.PJ.loc
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    exact Submodule.subset_span ⟨n, hN hn, rfl⟩
  apply Submodule.fg_of_fg_map_injective ((T0.WL X ka la).subtype.restrictScalars (X.Ol la)) Subtype.val_injective
  show (Submodule.map _ (Submodule.comap _ (X.loc la N))).FG
  rw [Submodule.map_comap_eq, inf_eq_right.mpr (fun x hx => ⟨⟨x, hle hx⟩, rfl⟩)]
  obtain ⟨S, hS⟩ := hfg
  rw [← hS, loc_span]
  exact Submodule.fg_span (S.finite_toSet.image _)

/- English proof (translation)
Establish `hWN : ∀ y ∈ Submodule.span (X.Kl la) (X.bc la '' (N : Set X.Forms)), y ∈ T0.WL X ka la`. Introduce `y hy`. Use `Submodule.span_mono ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Conclude with `⟨n, hN hn, rfl⟩`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨w, hw⟩ -`. Establish `hw' : w ∈ Submodule.span (X.Kl la) (X.bc la '' (N : Set X.Forms))` using `hW hw`. Use `Submodule.span_induction (p := fun y _ => ∀ h : y ∈ T0.WL X ka la, (⟨y, h⟩ : T0.WL X ka la) ∈ Submodule.span (X.Kl la) (T0.inW X ka la (X.loc la N) : Set (T0.WL X ka la))) ?_ ?_ ?_ ?_ hw' hw` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩ h`.

Conclude with `Submodule.subset_span (show X.bc la n ∈ X.loc la N from Submodule.subset_span ⟨n, hn, rfl⟩)`. Introduce `h`. Conclude with `Submodule.zero_mem _`. Introduce `x y hx' hy' hx hy h`. Establish `h1` using `Submodule.add_mem _ (hx (hWN x hx')) (hy (hWN y hy'))`.

Conclude with `h1`. Introduce `a x hx' hx h`. Establish `h1` using `Submodule.smul_mem _ a (hx (hWN x hx'))`. Conclude with `h1`.
-/
theorem span_inW_loc (N : Submodule (𝓞 B.KO) X.Forms) (hN : N ≤ X.Msup ka)
    (hW : X.locK la (X.Msup ka) ≤ X.locK la N) :
    Submodule.span (X.Kl la) (T0.inW X ka la (X.loc la N) : Set ↥(T0.WL X ka la)) = ⊤ := by
  have hWN : ∀ y ∈ Submodule.span (X.Kl la) (X.bc la '' (N : Set X.Forms)), y ∈ T0.WL X ka la := by
    intro y hy
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, hN hn, rfl⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  have hw' : w ∈ Submodule.span (X.Kl la) (X.bc la '' (N : Set X.Forms)) := hW hw
  refine Submodule.span_induction (p := fun y _ => ∀ h : y ∈ T0.WL X ka la,
      (⟨y, h⟩ : T0.WL X ka la) ∈ Submodule.span (X.Kl la) (T0.inW X ka la (X.loc la N) : Set (T0.WL X ka la)))
    ?_ ?_ ?_ ?_ hw' hw
  · rintro _ ⟨n, hn, rfl⟩ h
    exact Submodule.subset_span (show X.bc la n ∈ X.loc la N from Submodule.subset_span ⟨n, hn, rfl⟩)
  · intro h
    exact Submodule.zero_mem _
  · intro x y hx' hy' hx hy h
    have h1 := Submodule.add_mem _ (hx (hWN x hx')) (hy (hWN y hy'))
    exact h1
  · intro a x hx' hx h
    have h1 := Submodule.smul_mem _ a (hx (hWN x hx'))
    exact h1

/- English proof (translation)
Conclude with `⟨inW_loc_fg X la ka N hN hfg, span_inW_loc X la ka N hN hW⟩`.
-/
theorem isLat_inW_loc (N : Submodule (𝓞 B.KO) X.Forms) (hN : N ≤ X.Msup ka) (hfg : N.FG)
    (hW : X.locK la (X.Msup ka) ≤ X.locK la N) :
    Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(T0.WL X ka la) (T0.inW X ka la (X.loc la N)) := by
  exact ⟨inW_loc_fg X la ka N hN hfg, span_inW_loc X la ka N hN hW⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.WeightAlgebra.PJ.Msup Formalism.MainNotions.WeightAlgebra.PJ.emb`. Conclude with `hM.fg.map _`.
-/
theorem Msup_fg (hM : Submodule.IsLattice B.KO (B.Mlat j ka)) : (X.Msup ka).FG := by
  unfold Formalism.MainNotions.WeightAlgebra.PJ.Msup Formalism.MainNotions.WeightAlgebra.PJ.emb
  exact hM.fg.map _

/- English proof (translation)
Unfold `Formalism.MainNotions.WeightAlgebra.PJ.locK`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨G, ⟨F, -, rfl⟩, rfl⟩`. Establish `hF : F ∈ Submodule.span B.KO (N : Set (B.Cusp j ka))`. Rewrite using `[hsp]`.

Discharge the goal by the elementary cases of `trivial`. Establish `h1 : X.bc la (X.inc ka F) ∈ Submodule.span B.KO ((X.bc la ∘ₗ X.inc ka) '' (N : Set (B.Cusp j ka)))`. Rewrite using `[← Submodule.map_span]`. Conclude with `⟨F, hF, rfl⟩`. Establish `h2` using `Submodule.span_le_restrictScalars B.KO (X.Kl la) ((X.bc la ∘ₗ X.inc ka) '' (N : Set (B.Cusp j ka))) h1`.

Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Conclude with `⟨X.inc ka n, ⟨n, hn, rfl⟩, rfl⟩`.
-/
theorem locK_le_of_span (N : Submodule (𝓞 B.KO) (B.Cusp j ka))
    (hsp : Submodule.span B.KO (N : Set (B.Cusp j ka)) = ⊤) :
    X.locK la (X.Msup ka) ≤ X.locK la (X.emb ka N) := by
  unfold Formalism.MainNotions.WeightAlgebra.PJ.locK
  rw [Submodule.span_le]
  rintro _ ⟨G, ⟨F, -, rfl⟩, rfl⟩
  have hF : F ∈ Submodule.span B.KO (N : Set (B.Cusp j ka)) := by
    rw [hsp]
    trivial
  have h1 : X.bc la (X.inc ka F) ∈ Submodule.span B.KO ((X.bc la ∘ₗ X.inc ka) '' (N : Set (B.Cusp j ka))) := by
    rw [← Submodule.map_span]
    exact ⟨F, hF, rfl⟩
  have h2 := Submodule.span_le_restrictScalars B.KO (X.Kl la)
    ((X.bc la ∘ₗ X.inc ka) '' (N : Set (B.Cusp j ka))) h1
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨X.inc ka n, ⟨n, hn, rfl⟩, rfl⟩

end Lat

/- English proof (translation)
Use `⟨isLat_inW_loc X la ka (X.Msup ka) le_rfl (Msup_fg X ka hM) le_rfl, isLat_inW_loc X la ka _ hΘM ((Msup_fg X ka hM).of_le hΘM) ?_⟩` and prove the remaining obligations. Conclude with `(locK_le_of_span X la ka _ hsp).trans (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr (by`. Unfold `Formalism.MainNotions.WeightAlgebra.PJ.Theta`. Conclude with `le_sup_right))))`.
-/
theorem inLat_of (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hM : Submodule.IsLattice B.KO (B.Mlat j ka)) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka)
    (hsp : Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤) : T0.InLat X ka la S wL wF T := by
  refine ⟨isLat_inW_loc X la ka (X.Msup ka) le_rfl (Msup_fg X ka hM) le_rfl,
    isLat_inW_loc X la ka _ hΘM ((Msup_fg X ka hM).of_le hΘM) ?_⟩
  exact (locK_le_of_span X la ka _ hsp).trans (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr (by
    unfold Formalism.MainNotions.WeightAlgebra.PJ.Theta
    exact le_sup_right))))

section Quot

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (ka : WeightFamilies.Wt D j)

/- English proof (translation)
Use `show X.bc la (X.inc ka F) ∈ X.loc la (X.Msup ka)`. Conclude with `Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩`.
-/
theorem toW_mem_MW (F : B.Mlat j ka) : toW X la ka F ∈ T0.MW X ka la := by
  show X.bc la (X.inc ka F) ∈ X.loc la (X.Msup ka)
  exact Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩

/- English proof (translation)
Establish `hle : X.loc la (X.Msup ka) ≤ (T0.WL X ka la).restrictScalars (X.Ol la)`. Unfold `Formalism.MainNotions.WeightAlgebra.PJ.loc`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `Submodule.subset_span hx`.

Apply `Submodule.map_injective_of_injective (f := (T0.WL X ka la).subtype.restrictScalars (X.Ol la)) Subtype.val_injective` to reduce the goal to its premises. Use `show Submodule.map _ (Submodule.comap _ (X.loc la (X.Msup ka))) = _`. Rewrite using `[Submodule.map_comap_eq, inf_eq_right.mpr (fun x hx => ⟨⟨x, hle hx⟩, rfl⟩), Submodule.map_span]`. Unfold `Formalism.MainNotions.WeightAlgebra.PJ.loc`. Use `congr 1`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨G, ⟨F, hF, rfl⟩, rfl⟩`. Conclude with `⟨toW X la ka ⟨F, hF⟩, ⟨⟨F, hF⟩, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨F, rfl⟩, rfl⟩`.

Conclude with `⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩`.
-/
theorem MW_eq_span : T0.MW X ka la = Submodule.span (X.Ol la) (Set.range (toW X la ka)) := by
  have hle : X.loc la (X.Msup ka) ≤ (T0.WL X ka la).restrictScalars (X.Ol la) := by
    unfold Formalism.MainNotions.WeightAlgebra.PJ.loc
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span hx
  apply Submodule.map_injective_of_injective (f := (T0.WL X ka la).subtype.restrictScalars (X.Ol la))
    Subtype.val_injective
  show Submodule.map _ (Submodule.comap _ (X.loc la (X.Msup ka))) = _
  rw [Submodule.map_comap_eq, inf_eq_right.mpr (fun x hx => ⟨⟨x, hle hx⟩, rfl⟩), Submodule.map_span]
  unfold Formalism.MainNotions.WeightAlgebra.PJ.loc
  congr 1
  ext y
  constructor
  · rintro ⟨G, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨toW X la ka ⟨F, hF⟩, ⟨⟨F, hF⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨F, rfl⟩, rfl⟩
    exact ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩

def toWl : B.Mlat j ka →ₛₗ[algebraMap (𝓞 B.KO) (X.Ol la)] ↥(T0.MW X ka la) where
  toFun F := ⟨toW X la ka F, toW_mem_MW X la ka F⟩
  map_add' F G := by
    apply Subtype.ext; apply Subtype.ext
    show X.bc la (X.inc ka ((F + G : B.Mlat j ka) : B.Cusp j ka)) = X.bc la (X.inc ka F) + X.bc la (X.inc ka G)
    rw [Submodule.coe_add, map_add, map_add]
  map_smul' a F := by
    apply Subtype.ext; apply Subtype.ext
    show X.bc la (X.inc ka ((a • F : B.Mlat j ka) : B.Cusp j ka)) =
      algebraMap (𝓞 B.KO) (X.Ol la) a • X.bc la (X.inc ka F)
    rw [Submodule.coe_smul, ← bc_smul_int, LinearMap.map_smul_of_tower]

/- English proof (translation)
Use `set S₁ : Submodule (X.Ol la) ↥(T0.MW X ka la) := (MggW X la ka CRm T c ⊔ Submodule.span (X.Ol la) (Set.range fun i => toW X la ka (th i))).comap (T0.MW X ka la).subtype with hS₁`. Set `g0 : B.Mlat j ka →ₛₗ[algebraMap (𝓞 B.KO) (X.Ol la)] (↥(T0.MW X ka la) ⧸ S₁)` to `S₁.mkQ.comp (toWl X la ka)`. Establish `hk : WeightFamilies.MggIn B CRm T c j ka ≤ LinearMap.ker g0`. Introduce `F hF`. Rewrite using `[LinearMap.mem_ker]`.

Use `show S₁.mkQ _ = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `Submodule.mem_sup_left ?_` and prove the remaining obligations. Use `show X.bc la (X.inc ka F) ∈ X.loc la (X.emb ka (MggO B CRm T c j ka))`. Conclude with `Submodule.subset_span ⟨X.inc ka F, ⟨F, ⟨F.2, hF⟩, rfl⟩, rfl⟩`.

Set `g1 : WeightFamilies.Qm B CRm T c j ka →ₛₗ[algebraMap (𝓞 B.KO) (X.Ol la)] (↥(T0.MW X ka la) ⧸ S₁)` to `(WeightFamilies.MggIn B CRm T c j ka).liftQ g0 hk`. Establish `hk1 : Submodule.span (𝓞 B.KO) (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)) ≤ LinearMap.ker g1`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show g1 _ = 0`.

Use `show S₁.mkQ _ = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)`. Unfold `WeightFamilies.lenAt`. Use `length_le_length_localized B.KO la (Submodule.liftQ _ g1 hk1) ?_` and prove the remaining obligations.

Establish `key : ∀ y (_ : y ∈ Submodule.span (X.Ol la) (Set.range (toW X la ka))) (hy : y ∈ T0.MW X ka la), (Submodule.Quotient.mk ⟨y, hy⟩ : ↥(T0.MW X ka la) ⧸ S₁) ∈ Submodule.span (X.Ol la) (Set.range (Submodule.liftQ _ g1 hk1))`. Introduce `y hy'`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem y h`. Take `⟨F, rfl⟩` from `h`.

Introduce `hy`. Conclude with `Submodule.subset_span ⟨Submodule.Quotient.mk (Submodule.Quotient.mk F), rfl⟩`. Consider the case `zero => intro hy`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b ha hb iha ihb`.

Introduce `hy`. Conclude with `Submodule.add_mem _ (iha (MW_eq_span X la ka ▸ ha)) (ihb (MW_eq_span X la ka ▸ hb))`. Consider the case `smul r a ha ih`. Introduce `hy`. Conclude with `Submodule.smul_mem _ r (ih (MW_eq_span X la ka ▸ ha))`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨⟨y, hy⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `key y (MW_eq_span X la ka ▸ hy) hy`.
-/
theorem quot_len_le (CRm T c : ℝ) {n : ℕ} (th : Fin n → B.Mlat j ka) :
    Module.length (X.Ol la) (↥(T0.MW X ka la) ⧸ (MggW X la ka CRm T c ⊔
        Submodule.span (X.Ol la) (Set.range fun i => toW X la ka (th i))).comap (T0.MW X ka la).subtype) ≤
      WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
        (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) := by
  set S₁ : Submodule (X.Ol la) ↥(T0.MW X ka la) := (MggW X la ka CRm T c ⊔
    Submodule.span (X.Ol la) (Set.range fun i => toW X la ka (th i))).comap (T0.MW X ka la).subtype with hS₁
  let g0 : B.Mlat j ka →ₛₗ[algebraMap (𝓞 B.KO) (X.Ol la)] (↥(T0.MW X ka la) ⧸ S₁) := S₁.mkQ.comp (toWl X la ka)
  have hk : WeightFamilies.MggIn B CRm T c j ka ≤ LinearMap.ker g0 := by
    intro F hF
    rw [LinearMap.mem_ker]
    show S₁.mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_sup_left ?_
    show X.bc la (X.inc ka F) ∈ X.loc la (X.emb ka (MggO B CRm T c j ka))
    exact Submodule.subset_span ⟨X.inc ka F, ⟨F, ⟨F.2, hF⟩, rfl⟩, rfl⟩
  let g1 : WeightFamilies.Qm B CRm T c j ka →ₛₗ[algebraMap (𝓞 B.KO) (X.Ol la)] (↥(T0.MW X ka la) ⧸ S₁) :=
    (WeightFamilies.MggIn B CRm T c j ka).liftQ g0 hk
  have hk1 : Submodule.span (𝓞 B.KO)
      (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)) ≤ LinearMap.ker g1 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show g1 _ = 0
    show S₁.mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  unfold WeightFamilies.lenAt
  refine length_le_length_localized B.KO la (Submodule.liftQ _ g1 hk1) ?_
  have key : ∀ y (_ : y ∈ Submodule.span (X.Ol la) (Set.range (toW X la ka))) (hy : y ∈ T0.MW X ka la),
      (Submodule.Quotient.mk ⟨y, hy⟩ : ↥(T0.MW X ka la) ⧸ S₁) ∈
        Submodule.span (X.Ol la) (Set.range (Submodule.liftQ _ g1 hk1)) := by
    intro y hy'
    induction hy' using Submodule.span_induction with
    | mem y h =>
      obtain ⟨F, rfl⟩ := h
      intro hy
      exact Submodule.subset_span ⟨Submodule.Quotient.mk (Submodule.Quotient.mk F), rfl⟩
    | zero => intro hy; exact Submodule.zero_mem _
    | add a b ha hb iha ihb =>
      intro hy
      exact Submodule.add_mem _ (iha (MW_eq_span X la ka ▸ ha)) (ihb (MW_eq_span X la ka ▸ hb))
    | smul r a ha ih =>
      intro hy
      exact Submodule.smul_mem _ r (ih (MW_eq_span X la ka ▸ ha))
  rw [eq_top_iff]
  rintro z -
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact key y (MW_eq_span X la ka ▸ hy) hy

end Quot

/- English proof (translation)
Establish `: Module.Finite (𝓞 B.KO) (B.Mlat j ka)` using `Module.Finite.iff_fg.2 hM.1`. Take `⟨d, hd, h⟩` from `Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_le (K := B.KO) (B.Mlat j ka) (Submodule.span (𝓞 B.KO) (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔ (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)) hM.1 (by`. Rewrite using `[eq_top_iff, ← hsp]`. Use `sup_le (Submodule.span_le.2 ?_) fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))`. Unfold `WeightFamilies.lenAt`. Use `length_localized_ne_top la d hd ?_` and prove the remaining obligations. Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Take `⟨F, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht, G, hG, htG⟩` from `Submodule.mem_sup.1 (h F F.2)`. Establish `e1 : Submodule.span (𝓞 B.KO) (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) = (Submodule.span (𝓞 B.KO) (Set.range th)).map (B.Mlat j ka).subtype`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite `ht` using `[e1]`. Take `⟨t', ht', rfl⟩` from `ht`. Establish `hG' : d • F - t' ∈ WeightFamilies.MggIn B CRm T c j ka` using `by show ((d • F - t' : B.Mlat j ka) : B.Cusp j ka) ∈ WeightFamilies.MggK B CRm T c j ka`. Establish `: ((d • F - t' : B.Mlat j ka) : B.Cusp j ka) = G`.

Rewrite using `[Submodule.coe_sub, Submodule.coe_smul, ← htG]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hG`. Rewrite using `[(Submodule.Quotient.eq _).2 hG']`.

Establish `e2 : Submodule.span (𝓞 B.KO) (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)) = (Submodule.span (𝓞 B.KO) (Set.range th)).map (WeightFamilies.MggIn B CRm T c j ka).mkQ`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Conclude with `⟨t', ht', rfl⟩`.
-/
theorem quot_len_ne_top (la : HeightOneSpectrum (𝓞 B.KO)) (ka : WeightFamilies.Wt D j) (CRm T c : ℝ) {n : ℕ}
    (th : Fin n → B.Mlat j ka) (hM : Submodule.IsLattice B.KO (B.Mlat j ka))
    (hsp : Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤) :
    WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) ≠ ⊤ := by
  have : Module.Finite (𝓞 B.KO) (B.Mlat j ka) := Module.Finite.iff_fg.2 hM.1
  obtain ⟨d, hd, h⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_le (K := B.KO) (B.Mlat j ka)
    (Submodule.span (𝓞 B.KO) (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)) hM.1 (by
    rw [eq_top_iff, ← hsp]
    refine sup_le (Submodule.span_le.2 ?_) fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  unfold WeightFamilies.lenAt
  refine length_localized_ne_top la d hd ?_
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨t, ht, G, hG, htG⟩ := Submodule.mem_sup.1 (h F F.2)
  have e1 : Submodule.span (𝓞 B.KO) (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) =
      (Submodule.span (𝓞 B.KO) (Set.range th)).map (B.Mlat j ka).subtype := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [e1] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  have hG' : d • F - t' ∈ WeightFamilies.MggIn B CRm T c j ka := by
    show ((d • F - t' : B.Mlat j ka) : B.Cusp j ka) ∈ WeightFamilies.MggK B CRm T c j ka
    have : ((d • F - t' : B.Mlat j ka) : B.Cusp j ka) = G := by
      rw [Submodule.coe_sub, Submodule.coe_smul, ← htG]
      simp
    rw [this]; exact hG
  rw [(Submodule.Quotient.eq _).2 hG']
  have e2 : Submodule.span (𝓞 B.KO) (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)) =
      (Submodule.span (𝓞 B.KO) (Set.range th)).map (WeightFamilies.MggIn B CRm T c j ka).mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [e2]
  exact ⟨t', ht', rfl⟩

end Formalism.MainNotions.Gaps.EtaleWeightGaps
