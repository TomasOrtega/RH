import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

section Series

variable {E σ : Type} [Field E]

/- English proof (translation)
Simplify using `only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]`.
-/
private theorem mem_max_iff (f : MvPowerSeries σ E) :
    f ∈ maximalIdeal (MvPowerSeries σ E) ↔ MvPowerSeries.constantCoeff f = 0 := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f h`. Use `⟨fun _ => 0, ?_⟩` and prove the remaining obligations. Use extensionality with `n`.

Simplify using `using h n (by simp)`. Consider the case `insert a s ha ih`. Introduce `f h`. Set `q : MvPowerSeries σ E` to `fun n => MvPowerSeries.coeff (Finsupp.single a 1 + n) f`. Establish `hqc : ∀ n, MvPowerSeries.coeff n q = MvPowerSeries.coeff (Finsupp.single a 1 + n) f` using `fun _ => rfl`.

Take `⟨g, e⟩` from `ih (f - MvPowerSeries.X a * q) (by`. Introduce `n hn`. Rewrite using `[map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]`. Use `split_ifs with hle`. Rewrite using `[hqc, add_tsub_cancel_of_le hle, one_mul, sub_self]`.

Rewrite using `[sub_zero]`. Use `h n fun i hi => ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Rewrite `hle` using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers.

Conclude with `hn i hi)`. Use `⟨Function.update g a q, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)], ← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_X_mul (s : Finset σ) :
    ∀ f : MvPowerSeries σ E, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ E, f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f h
    refine ⟨fun _ => 0, ?_⟩
    ext n
    simpa using h n (by simp)
  | insert a s ha ih =>
    intro f h
    let q : MvPowerSeries σ E := fun n => MvPowerSeries.coeff (Finsupp.single a 1 + n) f
    have hqc : ∀ n, MvPowerSeries.coeff n q = MvPowerSeries.coeff (Finsupp.single a 1 + n) f := fun _ => rfl
    obtain ⟨g, e⟩ := ih (f - MvPowerSeries.X a * q) (by
      intro n hn
      rw [map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      split_ifs with hle
      · rw [hqc, add_tsub_cancel_of_le hle, one_mul, sub_self]
      · rw [sub_zero]
        refine h n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [Finsupp.single_le_iff] at hle
          omega
        · exact hn i hi)
    refine ⟨Function.update g a q, ?_⟩
    rw [Finset.sum_insert ha, Function.update_self,
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)], ← e]
    ring

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]`. Simplify using the standard rewrite rules.
-/
private theorem coeff_lin_mul (i : σ) (a b : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (a * b) =
      MvPowerSeries.constantCoeff a * MvPowerSeries.coeff (Finsupp.single i 1) b +
        MvPowerSeries.coeff (Finsupp.single i 1) a * MvPowerSeries.constantCoeff b := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]
  simp

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_X]`. Simplify using `only [Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]`.
-/
private theorem coeff_lin_X [DecidableEq σ] (i j : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries σ E) = if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  simp only [Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

/- English proof (translation)
Rewrite `hf` using `[pow_two]`. Use `Submodule.mul_induction_on hf (fun a ha b hb => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[coeff_lin_mul, (mem_max_iff a).1 ha, (mem_max_iff b).1 hb, zero_mul, mul_zero, add_zero]`. Rewrite using `[map_add, ha, hb, add_zero]`.
-/
private theorem coeff_lin_of_mem_sq {f : MvPowerSeries σ E} (hf : f ∈ maximalIdeal (MvPowerSeries σ E) ^ 2)
    (i : σ) : MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) fun a b ha hb => ?_
  · rw [coeff_lin_mul, (mem_max_iff a).1 ha, (mem_max_iff b).1 hb, zero_mul, mul_zero, add_zero]
  · rw [map_add, ha, hb, add_zero]

/- English proof (translation)
Take `⟨g, e⟩` from `sum_X_mul Finset.univ f fun n hn => by`. Establish `: n = 0` using `Finsupp.ext fun j => hn j (Finset.mem_univ j)`. Substitute `this` using the available equality. Simplify using `using h0`. Establish `hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0` using `fun i => by`.

Use `h1 i` as an intermediate fact. Rewrite `this` using `[e, map_sum]`. Simplify `this` using `[coeff_lin_mul, coeff_lin_X]`. Rewrite using `[e, pow_two]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul ((mem_max_iff _).2 (MvPowerSeries.constantCoeff_X i)) ((mem_max_iff _).2 (hg i))`.
-/
private theorem mem_sq_of_coeff [Fintype σ] {f : MvPowerSeries σ E} (h0 : MvPowerSeries.constantCoeff f = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f = 0) : f ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  classical
  obtain ⟨g, e⟩ := sum_X_mul Finset.univ f fun n hn => by
    have : n = 0 := Finsupp.ext fun j => hn j (Finset.mem_univ j)
    subst this
    simpa using h0
  have hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := h1 i
    rw [e, map_sum] at this
    simpa [coeff_lin_mul, coeff_lin_X] using this
  rw [e, pow_two]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_mul ((mem_max_iff _).2 (MvPowerSeries.constantCoeff_X i)) ((mem_max_iff _).2 (hg i))

end Series

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Assume the negation of the conclusion as `h`. Establish `hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime` using `inferInstance`. Establish `hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal` using `hp.isMaximal h`. Establish `h2 : (⊥ : Ideal O).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm`.

Conclude with `IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm`.
-/
private theorem zl_inj (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
  have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm

/- English proof (translation)
Introduce `hP l _ O _ _ _ _ _ _ _ D U`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `R _ _ _ r r' h hh e ⟨f, hf, hI⟩`. Take `⟨f', hf', hI'⟩` from `rtConj hP D U R r.hom h hh ⟨f, congrArg GLift.hom hf, hI⟩`. Conclude with `⟨f', GLift.ext (hf'.trans e.symm), hI'⟩`.

Establish `hi` using `zl_inj l O haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi`. Establish `hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]`. Conclude with `(IsFractionRing.injective O _).comp hi`. Use `letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra`.

Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance`. Use `haveI : Module.Finite ℚ_[l] (FractionRing O) := Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])`. Take `⟨x, hx, -⟩` from `univEx D U`. Take `⟨w, φ, hc, hd, hg⟩` from `rtChart hP D U (FractionRing O) x hx`.

Use `⟨x, Fin 12, inferInstance, w, φ, hx, ⟨hc.ker, hg, hc.const, fun i => ?_, fun f hf h1 => ?_⟩, hd⟩` and prove the remaining obligations. Take `⟨a, c, hc0, ha⟩` from `hc.dense 2 (MvPowerSeries.X i)`. Establish `key : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (φ a) = if j = i then algebraMap O (FractionRing O) c else 0` using `fun j => by`. Use `coeff_lin_of_mem_sq ha j` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero, ← algebraMap_smul (FractionRing O) c, map_smul, coeff_lin_X]`.

Rewrite using `[← this]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨a, ?_, fun j hj => by rw [key, if_neg hj]⟩` and prove the remaining obligations. Rewrite using `[key, if_pos rfl]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective O _)).2 hc0`.

Conclude with `hc.inj 2 f (mem_sq_of_coeff (by rw [hc.const, hf, map_zero]) h1)`.
-/
theorem UpperTheory.V.Loc.locGood :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), LocGood U (D.It U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  refine ⟨?_, ?_⟩
  · rintro R _ _ _ r r' h hh e ⟨f, hf, hI⟩
    obtain ⟨f', hf', hI'⟩ := rtConj hP D U R r.hom h hh ⟨f, congrArg GLift.hom hf, hI⟩
    exact ⟨f', GLift.ext (hf'.trans e.symm), hI'⟩
  · have hi := zl_inj l O
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
    have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
      exact (IsFractionRing.injective O _).comp hi
    letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
    haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
      IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
    haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
    haveI : Module.Finite ℚ_[l] (FractionRing O) :=
      Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
    obtain ⟨x, hx, -⟩ := univEx D U
    obtain ⟨w, φ, hc, hd, hg⟩ := rtChart hP D U (FractionRing O) x hx
    refine ⟨x, Fin 12, inferInstance, w, φ, hx, ⟨hc.ker, hg, hc.const, fun i => ?_, fun f hf h1 => ?_⟩, hd⟩
    · obtain ⟨a, c, hc0, ha⟩ := hc.dense 2 (MvPowerSeries.X i)
      have key : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (φ a) =
          if j = i then algebraMap O (FractionRing O) c else 0 := fun j => by
        have := coeff_lin_of_mem_sq ha j
        rw [map_sub, sub_eq_zero, ← algebraMap_smul (FractionRing O) c, map_smul, coeff_lin_X] at this
        rw [← this]
        split_ifs <;> simp
      refine ⟨a, ?_, fun j hj => by rw [key, if_neg hj]⟩
      rw [key, if_pos rfl]
      exact (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 hc0
    · exact hc.inj 2 f (mem_sq_of_coeff (by rw [hc.const, hf, map_zero]) h1)
