import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevCong

/- English proof (translation)
Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at hij ⊢`. Rewrite using `[← map_mul, hij, map_mul]`. Apply the tactic sequence `by_cases hh : i = j <;> simp [Matrix.one_apply, hh]`.
-/
theorem map_smul_eq {R R' ι : Type} [CommRing R] [CommRing R'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') {e : R}
    {m : Matrix ι ι R} (h : e • m = e • (1 : Matrix ι ι R)) : φ e • m.map φ = φ e • (1 : Matrix ι ι R') := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at hij ⊢
  rw [← map_mul, hij, map_mul]
  by_cases hh : i = j <;> simp [Matrix.one_apply, hh]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem smul_inv_eq {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {e : R}
    {m m' : Matrix ι ι R} (h : e • m = e • (1 : Matrix ι ι R)) (hm : m * m' = 1) :
    e • m' = e • (1 : Matrix ι ι R) := by
  calc e • m' = (e • (1 : Matrix ι ι R)) * m' := by rw [Matrix.smul_mul, Matrix.one_mul]
    _ = (e • m) * m' := by rw [h]
    _ = e • (1 : Matrix ι ι R) := by rw [Matrix.smul_mul, hm]

/- English proof (translation)
Establish `e1 : (e • m) * x * (e • m') = (e * e) • (m * x * m')`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Establish `e2 : (e • (1 : Matrix ι ι R)) * x * (e • (1 : Matrix κ κ R)) = (e * e) • x`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]`. Rewrite `e1` using `[h, h', e2]`.

Use `congrFun (congrFun e1 a) k` as an intermediate fact. Simplify `this.symm` using `[Matrix.smul_apply]`.
-/
theorem smul_conj_eq {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {e : R}
    {m : Matrix ι ι R} {m' : Matrix κ κ R} (h : e • m = e • (1 : Matrix ι ι R))
    (h' : e • m' = e • (1 : Matrix κ κ R)) (x : Matrix ι κ R) (a : ι) (k : κ) :
    (e * e) * (m * x * m') a k = (e * e) * x a k := by
  have e1 : (e • m) * x * (e • m') = (e * e) • (m * x * m') := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e2 : (e • (1 : Matrix ι ι R)) * x * (e • (1 : Matrix κ κ R)) = (e * e) • x := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [h, h', e2] at e1
  have := congrFun (congrFun e1 a) k
  simpa [Matrix.smul_apply] using this.symm

/- English proof (translation)
Introduce `v`. Rewrite using `[AlgHom.commutes]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) s`.
-/
private theorem algebraMap_ringOfIntegers_mem_intAf {F : Type} [Field F] [NumberField F] (s : 𝓞 F) : algebraMap F (Af F) (s : F) ∈ intAf F := by
  intro v
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) s

/- English proof (translation)
Establish `hm : ∃ m : ℕ, Valued.v (evalV F v β) ≤ WithZero.exp (m : ℤ)`. Distinguish the cases in `h0 : Valued.v (evalV F v β) = 0`. Conclude with `⟨0, by rw [h0]; exact zero_le'⟩`. Use `⟨(WithZero.log (Valued.v (evalV F v β))).toNat, ?_⟩ conv_lhs => rw [← WithZero.exp_log h0]` and prove the remaining obligations. Conclude with `WithZero.exp_le_exp.mpr (Int.self_le_toNat _)`.

Take `⟨m, hm⟩` from `hm`. Use `⟨m, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hv1 : Valued.v (algebraMap F (Fv F v) (t : F)) = v.intValuation t`. Establish `e1` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (t : F)`. Establish `e2` using `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (K := F) t`.

Conclude with `e1.trans e2`. Establish `ht' : v.intValuation t ≤ WithZero.exp (-(m : ℤ))` using `(IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem (v := v) t m).mpr ht`. Rewrite using `[map_mul, AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv1]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_pow_evalV_mul_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F] (β : Af F) (v : HeightOneSpectrum (𝓞 F)) : ∃ n : ℕ, ∀ t : 𝓞 F, t ∈ v.asIdeal ^ n →
    evalV F v (algebraMap F (Af F) (t : F) * β) ∈ v.adicCompletionIntegers F := by
  have hm : ∃ m : ℕ, Valued.v (evalV F v β) ≤ WithZero.exp (m : ℤ) := by
    by_cases h0 : Valued.v (evalV F v β) = 0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v (evalV F v β))).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h0]
      exact WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, fun t ht => ?_⟩
  have hv1 : Valued.v (algebraMap F (Fv F v) (t : F)) = v.intValuation t := by
    have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (t : F)
    have e2 := IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (K := F) t
    exact e1.trans e2
  have ht' : v.intValuation t ≤ WithZero.exp (-(m : ℤ)) :=
    (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem (v := v) t m).mpr ht
  rw [map_mul, AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv1]
  calc v.intValuation t * Valued.v (evalV F v β) ≤ WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ) :=
        mul_le_mul' ht' hm
    _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ}

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | evalV F v β ∉ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.mp β.2`. Use `choose n hn using exists_pow_evalV_mul_mem_adicCompletionIntegers β`. Set `J : Ideal (𝓞 F)` to `∏ v ∈ hfin.toFinset, v.asIdeal ^ n v`. Establish `hJI : J ⊔ I = ⊤`. Rewrite using `[← Ideal.isCoprime_iff_sup_eq]`.

Use `IsCoprime.prod_left fun v hv => IsCoprime.pow_left ?_` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Establish `hnot : ¬ I ≤ v.asIdeal` using `fun h => (hfin.mem_toFinset.mp hv) (hβ v h)`. Conclude with `v.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left (fun h => hnot (le_sup_right.trans h.ge)))`. Establish `h1 : (1 : 𝓞 F) ∈ J ⊔ I` using `by rw [hJI]; exact Submodule.mem_top`.

Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.mp h1`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`. Conclude with `Submodule.mem_sup.mpr ⟨s, Ideal.mem_span_singleton_self s, t, ht, hst⟩`. Introduce `v`.

Distinguish the cases in `hv : v ∈ hfin.toFinset`. Conclude with `hn v s ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hs)`. Establish `hβv : evalV F v β ∈ v.adicCompletionIntegers F` using `not_not.mp fun h => hv (hfin.mem_toFinset.mpr h)`. Rewrite using `[map_mul]`. Conclude with `mul_mem (algebraMap_ringOfIntegers_mem_intAf s v) hβv`.
-/
theorem exists_clear (I : Ideal (𝓞 F)) (β : Af F)
    (hβ : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → evalV F v β ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Ideal.span {s} ⊔ I = ⊤ ∧ algebraMap F (Af F) s * β ∈ intAf F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | evalV F v β ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp β.2
  choose n hn using exists_pow_evalV_mul_mem_adicCompletionIntegers β
  let J : Ideal (𝓞 F) := ∏ v ∈ hfin.toFinset, v.asIdeal ^ n v
  have hJI : J ⊔ I = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq]
    refine IsCoprime.prod_left fun v hv => IsCoprime.pow_left ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    have hnot : ¬ I ≤ v.asIdeal := fun h => (hfin.mem_toFinset.mp hv) (hβ v h)
    exact v.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left (fun h => hnot (le_sup_right.trans h.ge)))
  have h1 : (1 : 𝓞 F) ∈ J ⊔ I := by rw [hJI]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp h1
  refine ⟨s, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    exact Submodule.mem_sup.mpr ⟨s, Ideal.mem_span_singleton_self s, t, ht, hst⟩
  · intro v
    by_cases hv : v ∈ hfin.toFinset
    · exact hn v s ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hs)
    · have hβv : evalV F v β ∈ v.adicCompletionIntegers F :=
        not_not.mp fun h => hv (hfin.mem_toFinset.mpr h)
      rw [map_mul]
      exact mul_mem (algebraMap_ringOfIntegers_mem_intAf s v) hβv

/- English proof (translation)
Introduce `v`. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha v) (hb v)`.
-/
private theorem mul_mem_intAf' {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v`. Rewrite using `[map_one]`. Conclude with `one_mem _`.
-/
private theorem one_mem_intAf_siegel_theta_transformation : (1 : Af F) ∈ intAf F := by
  intro v
  rw [map_one]
  exact one_mem _

omit [NumberField E] in
/- English proof (translation)
It suffices to establish `hsub : latHat F E N ≤ (latHat F E N').comap (DistribMulAction.toAddMonoidHom (Fin r → Af F ⊗[F] E) (a ⊗ₜ[F] c)) from hsub hu`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a', ha', x, hx, rfl⟩`. Use `show (a ⊗ₜ[F] c) • (fun i => a' ⊗ₜ[F] x i) ∈ latHat F E N'`. Use `AddSubgroup.subset_closure ⟨a * a', mul_mem_intAf' ha ha', c • x, hc x hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem tmul_smul_mem {N N' : Set (Fin r → E)} {a : Af F} (ha : a ∈ intAf F) {c : E} (hc : ∀ x ∈ N, c • x ∈ N')
    {u : Fin r → Af F ⊗[F] E} (hu : u ∈ latHat F E N) : (a ⊗ₜ[F] c) • u ∈ latHat F E N' := by
  suffices hsub : latHat F E N ≤ (latHat F E N').comap
      (DistribMulAction.toAddMonoidHom (Fin r → Af F ⊗[F] E) (a ⊗ₜ[F] c)) from hsub hu
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a', ha', x, hx, rfl⟩
  show (a ⊗ₜ[F] c) • (fun i => a' ⊗ₜ[F] x i) ∈ latHat F E N'
  refine AddSubgroup.subset_closure ⟨a * a', mul_mem_intAf' ha ha', c • x, hc x hx, ?_⟩
  funext i
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Establish `hle : stdL E n ≤ Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 E) E))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_pi]`. Introduce `i _`.

Rewrite using `[Submodule.mem_one]`. Distinguish the cases in `h : i = a`. Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [h]⟩`. Take `⟨c, hc⟩` from `Submodule.mem_one.mp (Submodule.mem_pi.mp (hle hx) k (Set.mem_univ _))`.

Conclude with `⟨c, hc.symm⟩`.
-/
theorem exists_int_of_std {n : ℕ} {x : Fin n → E} (hx : x ∈ stdL E n) (k : Fin n) : ∃ c : 𝓞 E, x k = c := by
  have hle : stdL E n ≤ Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 E) E)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    rw [Submodule.mem_one]
    by_cases h : i = a
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp (Submodule.mem_pi.mp (hle hx) k (Set.mem_univ _))
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Set `f : (Fin n → Af F ⊗[F] E) →+ (Fin r → Af F ⊗[F] E)` to `{ toFun := fun z => z k • u map_zero' := by simp map_add' := fun z z' => by simp [add_smul] }`. It suffices to establish `hsub : latHat F E (stdL E n : Set (Fin n → E)) ≤ (latHat F E (N : Set (Fin r → E))).comap f from hsub hz`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Take `⟨c, hc⟩` from `exists_int_of_std hx k`.

Use `show (a ⊗ₜ[F] x k) • u ∈ latHat F E (N : Set (Fin r → E))`. Rewrite using `[hc]`. Conclude with `tmul_smul_mem ha (fun y hy => N.smul_mem c hy) hu`.
-/
theorem std_smul_mem {n : ℕ} {N : Lt E r} {z : Fin n → Af F ⊗[F] E} (hz : z ∈ latHat F E (stdL E n : Set _))
    (k : Fin n) {u : Fin r → Af F ⊗[F] E} (hu : u ∈ latHat F E (N : Set _)) : z k • u ∈ latHat F E (N : Set _) := by
  let f : (Fin n → Af F ⊗[F] E) →+ (Fin r → Af F ⊗[F] E) :=
    { toFun := fun z => z k • u
      map_zero' := by simp
      map_add' := fun z z' => by simp [add_smul] }
  suffices hsub : latHat F E (stdL E n : Set (Fin n → E)) ≤ (latHat F E (N : Set (Fin r → E))).comap f from hsub hz
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, x, hx, rfl⟩
  obtain ⟨c, hc⟩ := exists_int_of_std hx k
  show (a ⊗ₜ[F] x k) • u ∈ latHat F E (N : Set (Fin r → E))
  rw [hc]
  exact tmul_smul_mem ha (fun y hy => N.smul_mem c hy) hu

/- English proof (translation)
Set `f : Matrix (Fin 1) (Fin r) E →+ (Fin r → E)` to `{ toFun := fun y => y 0, map_zero' := rfl, map_add' := fun _ _ => rfl }`. It suffices to establish `hsub : tens (stdL E 1) N ≤ N.toAddSubgroup.comap f from hsub hy`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, u, hu, rfl⟩`. Take `⟨c, hc⟩` from `exists_int_of_std hv 0`.

Use `show vecMulVec v u 0 ∈ N`. Establish `e : vecMulVec v u 0 = c • u`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.vecMulVec_apply, Pi.smul_apply, hc]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `N.smul_mem c hu`.
-/
private theorem row_zero_mem_of_mem_tens_stdL {N : Lt E r} {y : Matrix (Fin 1) (Fin r) E} (hy : y ∈ tens (stdL E 1) N) : y 0 ∈ N := by
  let f : Matrix (Fin 1) (Fin r) E →+ (Fin r → E) :=
    { toFun := fun y => y 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
  suffices hsub : tens (stdL E 1) N ≤ N.toAddSubgroup.comap f from hsub hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, u, hu, rfl⟩
  obtain ⟨c, hc⟩ := exists_int_of_std hv 0
  show vecMulVec v u 0 ∈ N
  have e : vecMulVec v u 0 = c • u := by
    funext j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, hc]
    rfl
  rw [e]
  exact N.smul_mem c hu

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x = ∑ i, x i • (Pi.single i 1 : Fin m → E)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[hx]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
private theorem span_stdL_eq_top (m : ℕ) : Submodule.span E (stdL E m : Set (Fin m → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin m → E) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range _)`.
-/
private theorem stdL_fg' (m : ℕ) : (stdL E m).FG :=
  Submodule.fg_span (Set.finite_range _)

/- English proof (translation)
Take `⟨d, hd, hdx⟩` from `HatLat.tens_den (stdL E 1) N (span_stdL_eq_top 1) hsp (Matrix.of fun _ j => x j)`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Conclude with `row_zero_mem_of_mem_tens_stdL hdx`.
-/
private theorem exists_pos_nat_smul_mem_of_span_eq_top' {N : Lt E r} (hsp : Submodule.span E (N : Set (Fin r → E)) = ⊤) (x : Fin r → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ N := by
  obtain ⟨d, hd, hdx⟩ := HatLat.tens_den (stdL E 1) N (span_stdL_eq_top 1) hsp (Matrix.of fun _ j => x j)
  refine ⟨d, hd, ?_⟩
  exact row_zero_mem_of_mem_tens_stdL hdx

/- English proof (translation)
Establish `hO : ∀ c : 𝓞 F, ∀ z ∈ tens (stdL E 1) N, (c : F) • z ∈ tens (stdL E 1) N`. Introduce `c z hz`. Establish `h` using `HatLat.smul_mem_tens (stdL E 1) N (algebraMap (𝓞 F) (𝓞 E) c) hz`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hfgT` using `HatLat.tens_fg (stdL E 1) N (stdL_fg' 1) hfg`. Establish `hden` using `HatLat.tens_den (stdL E 1) N (span_stdL_eq_top 1) hsp`. Set `g : (Fin r → Af F ⊗[F] E) →+ Matrix (Fin r) (Fin 1) (AF F ⊗[F] E)` to `{ toFun := fun u => Matrix.of fun a _ => TensorProduct.map (HatLat.finL F) LinearMap.id (u a) map_zero' := by ext a b; simp map_add' := fun u u' => by ext a b; simp }`.

Establish `hsub : latHat F E (N : Set (Fin r → E)) ≤ (HatLat.hatG F (tens (stdL E 1) N)).comap g`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, x, hx, rfl⟩`. Use `show g (fun i => α ⊗ₜ[F] x i) ∈ HatLat.hatG F (tens (stdL E 1) N)`. Establish `hmem : vecMulVec (Pi.single 0 1 : Fin 1 → E) x ∈ tens (stdL E 1) N` using `AddSubgroup.subset_closure ⟨Pi.single 0 1, Submodule.subset_span ⟨0, rfl⟩, x, hx, rfl⟩`.

Use `HatLat.fT_mem (F := F) (hα : α ∈ HatLat.intG F) hmem` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Take `rfl : b = 0` from `Subsingleton.elim _ _`. Simplify using `[g, HatLat.fT_apply, Matrix.vecMulVec_apply]`.

Both sides reduce to the same expression. Establish `hfT : HatLat.fT F 1 (Matrix.of fun (_ : Fin 1) j => v j) ∈ HatLat.hatG F (tens (stdL E 1) N)`. Use `hsub hv` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_comap]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a b`. Simplify using `[g, HatLat.fT_apply]`. Both sides reduce to the same expression. Use `HatLat.mem_of_fT_mem hO hfgT hden hfT` as an intermediate fact. Conclude with `row_zero_mem_of_mem_tens_stdL this`.
-/
theorem mem_of_hat {N : Lt E r} (hfg : N.FG) (hsp : Submodule.span E (N : Set (Fin r → E)) = ⊤) {v : Fin r → E}
    (hv : (fun i => (1 : Af F) ⊗ₜ[F] v i) ∈ latHat F E (N : Set _)) : v ∈ N := by
  classical
  have hO : ∀ c : 𝓞 F, ∀ z ∈ tens (stdL E 1) N, (c : F) • z ∈ tens (stdL E 1) N := by
    intro c z hz
    have h := HatLat.smul_mem_tens (stdL E 1) N (algebraMap (𝓞 F) (𝓞 E) c) hz
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]
    rfl
  have hfgT := HatLat.tens_fg (stdL E 1) N (stdL_fg' 1) hfg
  have hden := HatLat.tens_den (stdL E 1) N (span_stdL_eq_top 1) hsp
  let g : (Fin r → Af F ⊗[F] E) →+ Matrix (Fin r) (Fin 1) (AF F ⊗[F] E) :=
    { toFun := fun u => Matrix.of fun a _ => TensorProduct.map (HatLat.finL F) LinearMap.id (u a)
      map_zero' := by ext a b; simp
      map_add' := fun u u' => by ext a b; simp }
  have hsub : latHat F E (N : Set (Fin r → E)) ≤ (HatLat.hatG F (tens (stdL E 1) N)).comap g := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, x, hx, rfl⟩
    show g (fun i => α ⊗ₜ[F] x i) ∈ HatLat.hatG F (tens (stdL E 1) N)
    have hmem : vecMulVec (Pi.single 0 1 : Fin 1 → E) x ∈ tens (stdL E 1) N :=
      AddSubgroup.subset_closure ⟨Pi.single 0 1, Submodule.subset_span ⟨0, rfl⟩, x, hx, rfl⟩
    have := HatLat.fT_mem (F := F) (hα : α ∈ HatLat.intG F) hmem
    convert this using 1
    ext a b
    obtain rfl : b = 0 := Subsingleton.elim _ _
    simp [g, HatLat.fT_apply, Matrix.vecMulVec_apply]
    rfl
  have hfT : HatLat.fT F 1 (Matrix.of fun (_ : Fin 1) j => v j) ∈ HatLat.hatG F (tens (stdL E 1) N) := by
    have := hsub hv
    rw [AddSubgroup.mem_comap] at this
    convert this using 1
    ext a b
    simp [g, HatLat.fT_apply]
    rfl
  have := HatLat.mem_of_fT_mem hO hfgT hden hfT
  exact row_zero_mem_of_mem_tens_stdL this

/- English proof (translation)
Take `⟨m, hm, hm0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h𝔪`. Establish `hmE : (m : E) ≠ 0` using `by exact_mod_cast hm0`. Rewrite using `[eq_top_iff, ← hsp, Submodule.span_le]`. Introduce `x hx`. Establish `h1 : (m : E) • x ∈ (𝔪 • N : Lt E r)` using `Submodule.smul_mem_smul hm hx`.

Establish `e : x = (m : E)⁻¹ • ((m : E) • x)` using `by rw [smul_smul, inv_mul_cancel₀ hmE, one_smul]`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem span_ideal_smul {N : Lt E r} (hsp : Submodule.span E (N : Set (Fin r → E)) = ⊤) {𝔪 : Ideal (𝓞 E)}
    (h𝔪 : 𝔪 ≠ ⊥) : Submodule.span E ((𝔪 • N : Lt E r) : Set (Fin r → E)) = ⊤ := by
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm0
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  intro x hx
  have h1 : (m : E) • x ∈ (𝔪 • N : Lt E r) := Submodule.smul_mem_smul hm hx
  have e : x = (m : E)⁻¹ • ((m : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hmE, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

/- English proof (translation)
Take `⟨d, hd, hdx⟩` from `exists_pos_nat_smul_mem_of_span_eq_top' hsp x`. Establish `hd0 : (d : F) ≠ 0` using `Nat.cast_ne_zero.mpr hd.ne'`. Use `set β : Af F := (1 - α) * algebraMap F (Af F) ((d : F)⁻¹) with hβ`. Establish `hβI : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → evalV F v β ∈ v.adicCompletionIntegers F`. Introduce `v hv`.

Rewrite using `[hβ, map_mul, map_sub, map_one, hα v hv, sub_self, zero_mul]`. Conclude with `zero_mem _`. Take `⟨s, hs, hsβ⟩` from `exists_clear I β hβI`. Use `⟨s, hs, mem_of_hat (F := F) hfg hsp ?_⟩` and prove the remaining obligations. Establish `hA : (fun i => (algebraMap F (Af F) s * α) ⊗ₜ[F] x i) ∈ latHat F E (N : Set (Fin r → E))`.

Use `tmul_smul_mem (a := algebraMap F (Af F) s) (c := 1) (algebraMap_ringOfIntegers_mem_intAf s) (fun y hy => by rwa [one_smul]) hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Establish `hB : (fun i => (algebraMap F (Af F) s * β) ⊗ₜ[F] (d • x) i) ∈ latHat F E (N : Set (Fin r → E))` using `AddSubgroup.subset_closure ⟨_, hsβ, d • x, hdx, rfl⟩`.

Establish `h1 : algebraMap F (Af F) s * α + (d : F) • (algebraMap F (Af F) s * β) = algebraMap F (Af F) s`. Rewrite using `[hβ, Algebra.smul_def]`. Establish `e : algebraMap F (Af F) (d : F) * algebraMap F (Af F) ((d : F)⁻¹) = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hd0, map_one]`. Take the linear combination `(algebraMap F (Af F) s * (1 - α)) * e`.

Use `add_mem hA hB using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `show (1 : Af F) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) s • x) i) = (algebraMap F (Af F) s * α) ⊗ₜ[F] x i + (algebraMap F (Af F) s * β) ⊗ₜ[F] ((d • x) i)`. Establish `e2 : algebraMap (𝓞 F) (𝓞 E) s • x i = (s : F) • x i`. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[Pi.smul_apply, Pi.smul_apply, e2, ← Nat.cast_smul_eq_nsmul F d (x i), TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul, h1, Algebra.smul_def, mul_one]`.
-/
theorem exists_smul_mem (I : Ideal (𝓞 F)) {α : Af F}
    (hα : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → evalV F v α = 1)
    {N : Lt E r} (hfg : N.FG) (hsp : Submodule.span E (N : Set (Fin r → E)) = ⊤) {x : Fin r → E}
    (hx : (fun i => α ⊗ₜ[F] x i) ∈ latHat F E (N : Set _)) :
    ∃ s : 𝓞 F, Ideal.span {s} ⊔ I = ⊤ ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ N := by
  obtain ⟨d, hd, hdx⟩ := exists_pos_nat_smul_mem_of_span_eq_top' hsp x
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  set β : Af F := (1 - α) * algebraMap F (Af F) ((d : F)⁻¹) with hβ
  have hβI : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → evalV F v β ∈ v.adicCompletionIntegers F := by
    intro v hv
    rw [hβ, map_mul, map_sub, map_one, hα v hv, sub_self, zero_mul]
    exact zero_mem _
  obtain ⟨s, hs, hsβ⟩ := exists_clear I β hβI
  refine ⟨s, hs, mem_of_hat (F := F) hfg hsp ?_⟩
  have hA : (fun i => (algebraMap F (Af F) s * α) ⊗ₜ[F] x i) ∈ latHat F E (N : Set (Fin r → E)) := by
    have := tmul_smul_mem (a := algebraMap F (Af F) s) (c := 1) (algebraMap_ringOfIntegers_mem_intAf s)
      (fun y hy => by rwa [one_smul]) hx
    convert this using 1
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hB : (fun i => (algebraMap F (Af F) s * β) ⊗ₜ[F] (d • x) i) ∈ latHat F E (N : Set (Fin r → E)) :=
    AddSubgroup.subset_closure ⟨_, hsβ, d • x, hdx, rfl⟩
  have h1 : algebraMap F (Af F) s * α + (d : F) • (algebraMap F (Af F) s * β) = algebraMap F (Af F) s := by
    rw [hβ, Algebra.smul_def]
    have e : algebraMap F (Af F) (d : F) * algebraMap F (Af F) ((d : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hd0, map_one]
    linear_combination (algebraMap F (Af F) s * (1 - α)) * e
  convert add_mem hA hB using 1
  funext i
  show (1 : Af F) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) s • x) i) =
    (algebraMap F (Af F) s * α) ⊗ₜ[F] x i + (algebraMap F (Af F) s * β) ⊗ₜ[F] ((d • x) i)
  have e2 : algebraMap (𝓞 F) (𝓞 E) s • x i = (s : F) • x i := by
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  rw [Pi.smul_apply, Pi.smul_apply, e2, ← Nat.cast_smul_eq_nsmul F d (x i), TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul, h1,
    Algebra.smul_def, mul_one]

omit [NumberField E] in

/- English proof (translation)
Establish `h1v : (fun i => (1 : Af F) ⊗ₜ[F] v i) ∈ latHat F E L'` using `AddSubgroup.subset_closure ⟨1, one_mem_intAf_siegel_theta_transformation, v, hv, rfl⟩`. Take `⟨u₀, hu₀, he⟩` from `(hm _).mp h1v`. Establish `e : (fun i => α ⊗ₜ[F] v i) = (α ⊗ₜ[F] (1 : E)) • u₀`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `i`.

Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Use `_ = (α ⊗ₜ[F] (1 : E)) • (m *ᵥ u₀) := by rw [he]`. Use `_ = ((α ⊗ₜ[F] (1 : E)) • m) *ᵥ u₀ := by rw [Matrix.smul_mulVec]`. Use `_ = ((α ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin r) (Fin r) (Af F ⊗[F] E))) *ᵥ u₀ := by rw [h1]`. Use `_ = (α ⊗ₜ[F] (1 : E)) • u₀ := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]`.

Rewrite using `[e]`. Conclude with `tmul_smul_mem (c := 1) hα (fun x hx => by rwa [one_smul]) hu₀`.
-/
theorem tmul_mem_of_mov {m : Matrix (Fin r) (Fin r) (Af F ⊗[F] E)} {L L' : Set (Fin r → E)}
    (hm : ∀ u, u ∈ latHat F E L' ↔ ∃ u₀ ∈ latHat F E L, u = m *ᵥ u₀) {α : Af F} (hα : α ∈ intAf F)
    (h1 : (α ⊗ₜ[F] (1 : E)) • m = (α ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin r) (Fin r) (Af F ⊗[F] E)))
    {v : Fin r → E} (hv : v ∈ L') : (fun i => α ⊗ₜ[F] v i) ∈ latHat F E L := by
  have h1v : (fun i => (1 : Af F) ⊗ₜ[F] v i) ∈ latHat F E L' :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf_siegel_theta_transformation, v, hv, rfl⟩
  obtain ⟨u₀, hu₀, he⟩ := (hm _).mp h1v
  have e : (fun i => α ⊗ₜ[F] v i) = (α ⊗ₜ[F] (1 : E)) • u₀ := by
    calc (fun i => α ⊗ₜ[F] v i) = (α ⊗ₜ[F] (1 : E)) • (fun i => (1 : Af F) ⊗ₜ[F] v i) := by
          funext i; simp [Algebra.TensorProduct.tmul_mul_tmul]
      _ = (α ⊗ₜ[F] (1 : E)) • (m *ᵥ u₀) := by rw [he]
      _ = ((α ⊗ₜ[F] (1 : E)) • m) *ᵥ u₀ := by rw [Matrix.smul_mulVec]
      _ = ((α ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin r) (Fin r) (Af F ⊗[F] E))) *ᵥ u₀ := by rw [h1]
      _ = (α ⊗ₜ[F] (1 : E)) • u₀ := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [e]
  exact tmul_smul_mem (c := 1) hα (fun x hx => by rwa [one_smul]) hu₀

/- English proof (translation)
Use `show (Algebra.TensorProduct.map (sndA K) (AlgHom.id K L)) (pairA K 0 β ⊗ₜ[K] z) = β ⊗ₜ[K] z`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
private theorem finG_pairA_zero_tmul {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] (β : Af K) (z : L) :
    HatLat.finG K L (pairA K 0 β ⊗ₜ[K] z) = β ⊗ₜ[K] z := by
  show (Algebra.TensorProduct.map (sndA K) (AlgHom.id K L)) (pairA K 0 β ⊗ₜ[K] z) = β ⊗ₜ[K] z
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Establish `hmL : ∀ u ∈ (𝔪 • L : Lt E r), (fun i => α ⊗ₜ[F] u i) ∈ latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))`. Introduce `u hu`. Proceed by induction on `hu using Submodule.smul_induction_on' with`. Consider the case `smul b hb l hl`. Use `tmul_smul_mem (a := (1 : Af F)) (c := algebraMap (𝓞 E) E b) one_mem_intAf_siegel_theta_transformation (fun x hx => by rw [algebraMap_smul]; exact Submodule.smul_mem_smul hb hx) (hL l hl)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]`. Consider the case `add x _ y _ hx hy`. Use `add_mem hx hy` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[TensorProduct.tmul_add]`. Set `f : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) →+ (Fin r → Af F ⊗[F] E)` to `{ toFun := fun w a => ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E (w a k) map_zero' := by funext a; simp map_add' := fun w w' => by funext a; simp [mul_add] }`. It suffices to establish `hsub : HatLat.hatG F (tens Λ (𝔪 • L)) ≤ (latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))).comap f from hsub hw`.

Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨β, hβ, y, hy, rfl⟩`. Establish `key : tens Λ (𝔪 • L) ≤ (latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))).comap (f.comp (HatLat.fT F β).toAddMonoidHom)`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, u, hu, rfl⟩`.

Establish `h1` using `std_smul_mem (hΛ v hv) k (tmul_smul_mem (a := β) (c := 1) hβ (fun x hx => by rwa [one_smul]) (hmL u hu))`. Use `show (fun a => ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E (HatLat.fT F β (vecMulVec v u) a k)) ∈ latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, smul_eq_mul, HatLat.fT_apply, finG_pairA_zero_tmul, Algebra.TensorProduct.tmul_mul_tmul, Matrix.vecMulVec_apply]`.

Apply the tactic sequence `congr 1 <;> ring`. Conclude with `key hy`.
-/
theorem col_mem {n : ℕ} {Λ : Lt E n} {L L₀ : Lt E r} {𝔪 : Ideal (𝓞 E)}
    {α : Af F} (hΛ : ∀ v ∈ Λ, (fun i => α ⊗ₜ[F] v i) ∈ latHat F E (stdL E n : Set _))
    (hL : ∀ v ∈ L, (fun i => α ⊗ₜ[F] v i) ∈ latHat F E (L₀ : Set _)) {w : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}
    (hw : w ∈ HatLat.hatG F (tens Λ (𝔪 • L))) (k : Fin n) :
    (fun a => ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E (w a k)) ∈ latHat F E ((𝔪 • L₀ : Lt E r) : Set _) := by
  have hmL : ∀ u ∈ (𝔪 • L : Lt E r), (fun i => α ⊗ₜ[F] u i) ∈ latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E)) := by
    intro u hu
    induction hu using Submodule.smul_induction_on' with
    | smul b hb l hl =>
      have := tmul_smul_mem (a := (1 : Af F)) (c := algebraMap (𝓞 E) E b) one_mem_intAf_siegel_theta_transformation
        (fun x hx => by rw [algebraMap_smul]; exact Submodule.smul_mem_smul hb hx) (hL l hl)
      convert this using 1
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    | add x _ y _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext i
      simp [TensorProduct.tmul_add]
  let f : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) →+ (Fin r → Af F ⊗[F] E) :=
    { toFun := fun w a => ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E (w a k)
      map_zero' := by funext a; simp
      map_add' := fun w w' => by funext a; simp [mul_add] }
  suffices hsub : HatLat.hatG F (tens Λ (𝔪 • L)) ≤
      (latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))).comap f from hsub hw
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨β, hβ, y, hy, rfl⟩
  have key : tens Λ (𝔪 • L) ≤ (latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))).comap
      (f.comp (HatLat.fT F β).toAddMonoidHom) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    have h1 := std_smul_mem (hΛ v hv) k
      (tmul_smul_mem (a := β) (c := 1) hβ (fun x hx => by rwa [one_smul]) (hmL u hu))
    show (fun a => ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E (HatLat.fT F β (vecMulVec v u) a k)) ∈
      latHat F E ((𝔪 • L₀ : Lt E r) : Set (Fin r → E))
    convert h1 using 1
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, HatLat.fT_apply, finG_pairA_zero_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Matrix.vecMulVec_apply]
    congr 1 <;> ring
  exact key hy

omit [NumberField E] in
/- English proof (translation)
Establish `hf : HatLat.finG F E (pairA F 0 (α * α) ⊗ₜ[F] (1 : E)) = (α * α) ⊗ₜ[F] (1 : E)` using `finG_pairA_zero_tmul _ _`. Establish `ee : (pairA F 0 α ⊗ₜ[F] (1 : E)) * (pairA F 0 α ⊗ₜ[F] (1 : E)) = pairA F 0 (α * α) ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `congr 1`. Use `show ((0 : Ainf F), α) * ((0 : Ainf F), α) = ((0 : Ainf F), α * α)`.

Rewrite using `[Prod.mk_mul_mk, mul_zero]`. Establish `hc` using `smul_conj_eq h h' (HatLat.fT F 1 y) a k`. Rewrite `hc` using `[ee]`. Rewrite using `[← hf, ← map_mul, Matrix.sub_apply, mul_sub, hc, ← mul_sub, map_mul, hf, HatLat.fT_apply, HatLat.fT_apply, ← TensorProduct.tmul_sub]`. Simplify using `only [finG_pairA_zero_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.sub_apply]`.
-/
theorem sq_mul_finPart {n : ℕ} {α : Af F} {m : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    {m' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    (h : (pairA F 0 α ⊗ₜ[F] (1 : E)) • m = (pairA F 0 α ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)))
    (h' : (pairA F 0 α ⊗ₜ[F] (1 : E)) • m' = (pairA F 0 α ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))
    (y y' : Matrix (Fin n) (Fin r) E) (a : Fin r) (k : Fin n) :
    ((α * α) ⊗ₜ[F] (1 : E)) * HatLat.finG F E ((HatLat.fT F 1 y' - m * HatLat.fT F 1 y * m') a k) =
      (α * α) ⊗ₜ[F] (y' k - y k) a := by
  have hf : HatLat.finG F E (pairA F 0 (α * α) ⊗ₜ[F] (1 : E)) = (α * α) ⊗ₜ[F] (1 : E) := finG_pairA_zero_tmul _ _
  have ee : (pairA F 0 α ⊗ₜ[F] (1 : E)) * (pairA F 0 α ⊗ₜ[F] (1 : E)) = pairA F 0 (α * α) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    show ((0 : Ainf F), α) * ((0 : Ainf F), α) = ((0 : Ainf F), α * α)
    rw [Prod.mk_mul_mk, mul_zero]
  have hc := smul_conj_eq h h' (HatLat.fT F 1 y) a k
  rw [ee] at hc
  rw [← hf, ← map_mul, Matrix.sub_apply, mul_sub, hc, ← mul_sub, map_mul, hf, HatLat.fT_apply, HatLat.fT_apply,
    ← TensorProduct.tmul_sub]
  simp only [finG_pairA_zero_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.sub_apply]

end Gen

variable {D : D7}

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | I ≤ v.asIdeal}.Finite` using `(Ideal.finite_factors hI).subset fun v hv => Ideal.dvd_iff_le.mpr hv`. Establish `hev : ∀ w, evalV D.host.F w (∑ v ∈ hfin.toFinset, singleV D.host.F v 1) = if w ∈ hfin.toFinset then 1 else 0`. Introduce `w`. Rewrite using `[map_sum]`. Rewrite using `[Finset.sum_congr rfl (g := fun v => if w = v then (1 : Fv D.host.F w) else 0)]`.

Conclude with `Finset.sum_ite_eq _ _ _`. Introduce `v _`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[GlobalTheory.LatVac.evalV_singleV_same, if_pos rfl]`.

Rewrite using `[GlobalTheory.LatVac.evalV_singleV_ne _ _ _ h, if_neg h]`. Use `⟨∑ v ∈ hfin.toFinset, singleV D.host.F v 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[hev w]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Introduce `v hv`. Rewrite using `[hev v, if_pos (hfin.mem_toFinset.mpr hv)]`. Introduce `V J g hJ hg`.

Establish `he : (pairA D.host.F 0 (∑ v ∈ hfin.toFinset, singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = ∑ v ∈ hfin.toFinset, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))` using `by show _ = ∑ v ∈ hfin.toFinset, (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E)`. Rewrite using `[← TensorProduct.sum_tmul]`. Use `congr 1`. Conclude with `map_sum (HatLat.finL D.host.F) (fun v => singleV D.host.F v 1) hfin.toFinset`. Use extensionality with `i j`.

Rewrite using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub, ← Matrix.sub_apply, he, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Establish `hvI : I ≤ v.asIdeal` using `hfin.mem_toFinset.mp hv`. Conclude with `hg v (hJ.trans hvI) _ ⟨singleV D.host.F v 1, rfl, GlobalTheory.LatVac.evalV_singleV_same _ v, fun v' h => GlobalTheory.LatVac.evalV_singleV_ne _ v v' h⟩ i j`.
-/
theorem exists_idem (I : Ideal (𝓞 D.host.F)) (hI : I ≠ ⊥) : ∃ α ∈ intAf D.host.F,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), I ≤ v.asIdeal → evalV D.host.F v α = 1) ∧
    ∀ (V : HSp D) (J : Ideal (𝓞 D.host.F)) (g : GA D V), J ≤ I → TrivAt V J g →
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) : Formalism.L2.Theta.AE D) • mt V g =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) : Formalism.L2.Theta.AE D) • 1 := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | I ≤ v.asIdeal}.Finite :=
    (Ideal.finite_factors hI).subset fun v hv => Ideal.dvd_iff_le.mpr hv
  have hev : ∀ w, evalV D.host.F w (∑ v ∈ hfin.toFinset, singleV D.host.F v 1) =
      if w ∈ hfin.toFinset then 1 else 0 := by
    intro w
    rw [map_sum]
    rw [Finset.sum_congr rfl (g := fun v => if w = v then (1 : Fv D.host.F w) else 0)]
    · exact Finset.sum_ite_eq _ _ _
    · intro v _
      by_cases h : w = v
      · subst h; rw [GlobalTheory.LatVac.evalV_singleV_same, if_pos rfl]
      · rw [GlobalTheory.LatVac.evalV_singleV_ne _ _ _ h, if_neg h]
  refine ⟨∑ v ∈ hfin.toFinset, singleV D.host.F v 1, ?_, ?_, ?_⟩
  · intro w
    rw [hev w]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro v hv
    rw [hev v, if_pos (hfin.mem_toFinset.mpr hv)]
  · intro V J g hJ hg
    have he : (pairA D.host.F 0 (∑ v ∈ hfin.toFinset, singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) =
        ∑ v ∈ hfin.toFinset, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
      show _ = ∑ v ∈ hfin.toFinset, (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E)
      rw [← TensorProduct.sum_tmul]
      congr 1
      exact map_sum (HatLat.finL D.host.F) (fun v => singleV D.host.F v 1) hfin.toFinset
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub,
      ← Matrix.sub_apply, he, Finset.sum_mul]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hvI : I ≤ v.asIdeal := hfin.mem_toFinset.mp hv
    exact hg v (hJ.trans hvI) _ ⟨singleV D.host.F v 1, rfl, GlobalTheory.LatVac.evalV_singleV_same _ v,
      fun v' h => GlobalTheory.LatVac.evalV_singleV_ne _ v v' h⟩ i j

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`.
-/
theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

/- English proof (translation)
Introduce `D S T C Lv hn M hw hM hMm h Λ g L hh htriv hΛfg hΛmov hg gtriv hLfg hLmov y y' hy k`. Unfold `Formalism.IndefR.Datum.actO at hy`. Establish `hMu : (M : 𝓞 D.host.F) ∈ C.under Lv` using `by show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (M : 𝓞 D.host.F) ∈ Lv.𝔪`. Rewrite using `[map_natCast]`. Conclude with `hMm`.

Establish `hI : C.under Lv ≠ ⊥`. Introduce `h0`. Rewrite `hMu` using `[h0, Ideal.mem_bot]`. Conclude with `hM.ne' (by exact_mod_cast hMu)`. Take `⟨α, hαint, hα1, hαtriv⟩` from `exists_idem (D := D) (C.under Lv) hI`.

Establish `hgE` using `hαtriv T (C.under Lv) g le_rfl gtriv`. Establish `hhE` using `hαtriv S (Ideal.span {(M : 𝓞 D.host.F)}) h (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hMu)) htriv`. Establish `hhiE` using `smul_inv_eq hhE (mt_mul_inv S h)`. Establish `hfe : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = α ⊗ₜ[D.host.F] (1 : D.host.E)` using `finG_pairA_zero_tmul α 1`. Establish `hce : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)` using `by show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _`.

Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Establish `hgF : (α ⊗ₜ[D.host.F] (1 : D.host.E)) • fmt T g = (α ⊗ₜ[D.host.F] (1 : D.host.E)) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AfE D))`. Establish `h2` using `map_smul_eq (finPart D) hgE`. Rewrite `h2` using `[hfe]`.

Conclude with `h2`. Establish `hhF : (α ⊗ₜ[D.host.F] (1 : D.host.E)) • fmtC S h = (α ⊗ₜ[D.host.F] (1 : D.host.E)) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AfE D))`. Establish `h1` using `map_smul_eq (cA D) hhE`. Rewrite `h1` using `[hce]`. Establish `h2` using `map_smul_eq (finPart D) h1`.

Rewrite `h2` using `[hfe]`. Conclude with `h2`. Establish `hΛ : ∀ v ∈ Λ, (fun i => α ⊗ₜ[D.host.F] v i) ∈ latHat D.host.F D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))` using `fun v hv => tmul_mem_of_mov (L := (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))) (L' := (Λ : Set (Fin S.rank → D.host.E))) hΛmov hαint hhF hv`. Establish `hL : ∀ v ∈ L, (fun i => α ⊗ₜ[D.host.F] v i) ∈ latHat D.host.F D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E))` using `fun v hv => tmul_mem_of_mov (L := (C.X.Λ : Set (Fin T.rank → D.host.E))) (L' := (L : Set (Fin T.rank → D.host.E))) hLmov hαint hgF hv`. Establish `e1 : ∀ z : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T z = HatLat.fT D.host.F 1 z` using `fun z => by`.

Use extensionality with `a b`. Rewrite using `[HatLat.fT_apply]`. Both sides reduce to the same expression. Establish `e2 : hatA S T (tens Λ (Lv.𝔪 • L)) = HatLat.hatG D.host.F (tens Λ (Lv.𝔪 • L))`. Unfold `GlobalTheory.Ker.hatA HatLat.hatG`.

Use `congr 1`. Rewrite `hy` using `[e2, e1, e1]`. Establish `hcol` using `col_mem (L₀ := C.X.Λ) hΛ hL hy k`. Establish `hcol' : (fun a => (α * α) ⊗ₜ[D.host.F] (y' k - y k) a) ∈ latHat D.host.F D.host.E ((Lv.𝔪 • C.X.Λ : Lt D.host.E T.rank) : Set (Fin T.rank → D.host.E))`. Use `hcol using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `a`. Conclude with `(sq_mul_finPart hgE hhiE y y' a k).symm`. Establish `hsp` using `span_ideal_smul C.X.Λ_span Lv.ne_bot`. Establish `hfgm : (Lv.𝔪 • C.X.Λ).FG` using `Submodule.FG.smul (IsNoetherian.noetherian Lv.𝔪) C.X.Λ_fg`. Take `⟨s, hs, hsx⟩` from `exists_smul_mem (C.under Lv) (α := α * α) (fun v hv => by rw [map_mul, hα1 v hv, one_mul]) hfgm hsp hcol'`.

Use `(⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s, ?_, hsx⟩ : ∃ c : 𝓞 D.host.E, IsCoprime (Ideal.span {c}) Lv.𝔪 ∧ c • (y' k - y k) ∈ Lv.𝔪 • C.X.Λ)` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq, eq_top_iff]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs, Ideal.map_top]`. Use `_ = Ideal.span {algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s} ⊔ Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (C.under Lv) := by`.

Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Use `_ ≤ _ := sup_le_sup_left (Ideal.map_comap_le (K := Lv.𝔪)) _`.
-/
theorem cong_of_act : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y' - actO S T h g (finW S T y) ∈ hatA S T (tens Λ (Lv.𝔪 • L)) → ∀ k, Cong C.X Lv.𝔪 (y' k) (y k) := by
  intro D S T C Lv hn M hw hM hMm h Λ g L hh htriv hΛfg hΛmov hg gtriv hLfg hLmov y y' hy k
  unfold Formalism.IndefR.Datum.actO at hy
  have hMu : (M : 𝓞 D.host.F) ∈ C.under Lv := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (M : 𝓞 D.host.F) ∈ Lv.𝔪
    rw [map_natCast]
    exact hMm
  have hI : C.under Lv ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hMu
    exact hM.ne' (by exact_mod_cast hMu)
  obtain ⟨α, hαint, hα1, hαtriv⟩ := exists_idem (D := D) (C.under Lv) hI
  have hgE := hαtriv T (C.under Lv) g le_rfl gtriv
  have hhE := hαtriv S (Ideal.span {(M : 𝓞 D.host.F)}) h
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hMu)) htriv
  have hhiE := smul_inv_eq hhE (mt_mul_inv S h)
  have hfe : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = α ⊗ₜ[D.host.F] (1 : D.host.E) :=
    finG_pairA_zero_tmul α 1
  have hce : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hgF : (α ⊗ₜ[D.host.F] (1 : D.host.E)) • fmt T g =
      (α ⊗ₜ[D.host.F] (1 : D.host.E)) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AfE D)) := by
    have h2 := map_smul_eq (finPart D) hgE
    rw [hfe] at h2
    exact h2
  have hhF : (α ⊗ₜ[D.host.F] (1 : D.host.E)) • fmtC S h =
      (α ⊗ₜ[D.host.F] (1 : D.host.E)) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AfE D)) := by
    have h1 := map_smul_eq (cA D) hhE
    rw [hce] at h1
    have h2 := map_smul_eq (finPart D) h1
    rw [hfe] at h2
    exact h2
  have hΛ : ∀ v ∈ Λ, (fun i => α ⊗ₜ[D.host.F] v i) ∈
      latHat D.host.F D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) := fun v hv =>
    tmul_mem_of_mov (L := (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)))
      (L' := (Λ : Set (Fin S.rank → D.host.E))) hΛmov hαint hhF hv
  have hL : ∀ v ∈ L, (fun i => α ⊗ₜ[D.host.F] v i) ∈
      latHat D.host.F D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) := fun v hv =>
    tmul_mem_of_mov (L := (C.X.Λ : Set (Fin T.rank → D.host.E)))
      (L' := (L : Set (Fin T.rank → D.host.E))) hLmov hαint hgF hv
  have e1 : ∀ z : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T z = HatLat.fT D.host.F 1 z := fun z => by
    ext a b
    rw [HatLat.fT_apply]
    rfl
  have e2 : hatA S T (tens Λ (Lv.𝔪 • L)) = HatLat.hatG D.host.F (tens Λ (Lv.𝔪 • L)) := by
    unfold GlobalTheory.Ker.hatA HatLat.hatG
    congr 1
  rw [e2, e1, e1] at hy
  have hcol := col_mem (L₀ := C.X.Λ) hΛ hL hy k
  have hcol' : (fun a => (α * α) ⊗ₜ[D.host.F] (y' k - y k) a) ∈
      latHat D.host.F D.host.E ((Lv.𝔪 • C.X.Λ : Lt D.host.E T.rank) : Set (Fin T.rank → D.host.E)) := by
    convert hcol using 1
    funext a
    exact (sq_mul_finPart hgE hhiE y y' a k).symm
  have hsp := span_ideal_smul C.X.Λ_span Lv.ne_bot
  have hfgm : (Lv.𝔪 • C.X.Λ).FG := Submodule.FG.smul (IsNoetherian.noetherian Lv.𝔪) C.X.Λ_fg
  obtain ⟨s, hs, hsx⟩ := exists_smul_mem (C.under Lv) (α := α * α)
    (fun v hv => by rw [map_mul, hα1 v hv, one_mul]) hfgm hsp hcol'
  refine (⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s, ?_, hsx⟩ : ∃ c : 𝓞 D.host.E,
    IsCoprime (Ideal.span {c}) Lv.𝔪 ∧ c • (y' k - y k) ∈ Lv.𝔪 • C.X.Λ)
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff]
  calc (⊤ : Ideal (𝓞 D.host.E))
      = Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (Ideal.span {s} ⊔ C.under Lv) := by
        rw [hs, Ideal.map_top]
    _ = Ideal.span {algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s} ⊔
        Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (C.under Lv) := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    _ ≤ _ := sup_le_sup_left (Ideal.map_comap_le (K := Lv.𝔪)) _

end GlobalTheory.Ker.LevCong

end
