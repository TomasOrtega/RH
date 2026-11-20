import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix

namespace DictRing

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩`.
-/
theorem nonempty_places : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

/- English proof (translation)
Take `⟨v⟩` from `nonempty_places (F := F)`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h2 : (0 : v.adicCompletion F) = 1` using `congrArg (fun a : Af F => a v) h`. Conclude with `zero_ne_one h2`.
-/
theorem nontrivial : Nontrivial (Af F) := by
  obtain ⟨v⟩ := nonempty_places (F := F)
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun a : Af F => a v) h
  exact zero_ne_one h2

/- English proof (translation)
Use `haveI := nontrivial (F := F)`. Conclude with `(algebraMap F (Af F)).injective`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap F (Af F)) := by
  haveI := nontrivial (F := F)
  exact (algebraMap F (Af F)).injective

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comp_algebraMap (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap (𝓞 F) (Af F) r) v = algebraMap (𝓞 F) (v.adicCompletion F) r := by
  rfl

/- English proof (translation)
Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Establish `h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) = v.valuation F (algebraMap (𝓞 F) F r)` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F r)`. Rewrite using `[h]`. Conclude with `v.valuation_le_one r`.
-/
theorem int_mem (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  have h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) =
      v.valuation F (algebraMap (𝓞 F) F r) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F r)
  rw [h]
  exact v.valuation_le_one r

/- English proof (translation)
Conclude with `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`.
-/
theorem val_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := by exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), val_alg]`.
-/
theorem val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.valuation F (algebraMap (𝓞 F) F r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), val_alg]

/- English proof (translation)
Establish `h1 : ν * x ≤ ν * 1` using `by rwa [mul_one]`. Conclude with `le_of_mul_le_mul_left h1 (zero_lt_iff.mpr hν)`.
-/
theorem cancel {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ν x : Γ} (hν : ν ≠ 0) (h : ν * x ≤ ν) : x ≤ 1 := by
  have h1 : ν * x ≤ ν * 1 := by rwa [mul_one]
  exact le_of_mul_le_mul_left h1 (zero_lt_iff.mpr hν)

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (a v ∈ v.adicCompletionIntegers F)}.Finite` using `Filter.eventually_cofinite.mp a.2`. Use `choose b hb0 hb using fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)`. Set `T` to `hfin.toFinset`. Set `mv : HeightOneSpectrum (𝓞 F) → ℕ` to `fun v => Ideal.absNorm (Ideal.span {b v})`. Establish `hmv : ∀ v, 0 < mv v` using `fun v => by`.

Use `Nat.pos_of_ne_zero ?_` and prove the remaining obligations. Simplify using `only [mv, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `nonZeroDivisors.ne_zero (hb0 v)`. Use `⟨∏ v ∈ T, mv v, Finset.prod_pos fun v _ => hmv v, ?_⟩` and prove the remaining obligations. Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), ((∏ w ∈ T, mv w : ℕ) : Af F) v * a v ∈ v.adicCompletionIntegers F`.

Introduce `v`. Establish `hcast : ((∏ w ∈ T, mv w : ℕ) : Af F) = algebraMap (𝓞 F) (Af F) ((∏ w ∈ T, mv w : ℕ) : 𝓞 F)` using `(map_natCast _ _).symm`. Rewrite using `[hcast, comp_algebraMap]`. Distinguish the cases in `hv : v ∈ T`. Establish `hdvd : (b v : 𝓞 F) ∣ ((∏ w ∈ T, mv w : ℕ) : 𝓞 F)`.

Establish `h1 : ((mv v : ℕ) : 𝓞 F) ∈ Ideal.span {b v}` using `Ideal.absNorm_mem _`. Rewrite `h1` using `[Ideal.mem_span_singleton]`. Conclude with `h1.trans (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem mv hv))`. Take `⟨d, hd⟩` from `hdvd`. Rewrite using `[hd, map_mul, mul_comm (algebraMap (𝓞 F) (v.adicCompletion F) (b v)), mul_assoc]`.

Conclude with `mul_mem (int_mem d v) (by rw [mul_comm]; exact hb v)`. Establish `: a v ∈ v.adicCompletionIntegers F` using `by simpa [T] using hv`. Conclude with `mul_mem (int_mem _ v) this`. Conclude with `key`.
-/
theorem af_denom (a : Af F) : ∃ m : ℕ, 0 < m ∧ (m : Af F) * a ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (a v ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb0 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  let T := hfin.toFinset
  let mv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => Ideal.absNorm (Ideal.span {b v})
  have hmv : ∀ v, 0 < mv v := fun v => by
    refine Nat.pos_of_ne_zero ?_
    simp only [mv, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero (hb0 v)
  refine ⟨∏ v ∈ T, mv v, Finset.prod_pos fun v _ => hmv v, ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((∏ w ∈ T, mv w : ℕ) : Af F) v * a v ∈ v.adicCompletionIntegers F := by
    intro v
    have hcast : ((∏ w ∈ T, mv w : ℕ) : Af F) = algebraMap (𝓞 F) (Af F) ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) :=
      (map_natCast _ _).symm
    rw [hcast, comp_algebraMap]
    by_cases hv : v ∈ T
    · have hdvd : (b v : 𝓞 F) ∣ ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) := by
        have h1 : ((mv v : ℕ) : 𝓞 F) ∈ Ideal.span {b v} := Ideal.absNorm_mem _
        rw [Ideal.mem_span_singleton] at h1
        exact h1.trans (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem mv hv))
      obtain ⟨d, hd⟩ := hdvd
      rw [hd, map_mul, mul_comm (algebraMap (𝓞 F) (v.adicCompletion F) (b v)), mul_assoc]
      exact mul_mem (int_mem d v) (by rw [mul_comm]; exact hb v)
    · have : a v ∈ v.adicCompletionIntegers F := by simpa [T] using hv
      exact mul_mem (int_mem _ v) this
  exact key

/- English proof (translation)
Establish `ha' : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (a v) ≤ 1` using `ha`. Use `set n : 𝓞 F := (N : 𝓞 F) with hn`. Establish `hn0 : n ≠ 0` using `by rw [hn]; exact_mod_cast hN.ne'`. Establish `hnF : algebraMap (𝓞 F) F n ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hn0`. Establish `hTfin : {v : HeightOneSpectrum (𝓞 F) | v.valuation F (algebraMap (𝓞 F) F n) < 1}.Finite`.

Repeatedly rewrite using `[HeightOneSpectrum.valuation_lt_one_iff_dvd]`. Apply `Ideal.finite_factors` to reduce the goal to its premises. Simplify using `only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]`. Set `T` to `hTfin.toFinset`. Establish `hν0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≠ 0`.

Introduce `v`. Rewrite using `[val_int]`. Conclude with `(Valuation.ne_zero_iff _).2 hnF`. Establish `hν1 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≤ 1`. Introduce `v`.

Rewrite using `[val_int]`. Conclude with `v.valuation_le_one n`. Establish `hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : F, Valued.v (algebraMap F (v.adicCompletion F) k - a v) < Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)`. Introduce `v`. Establish `hx0 : algebraMap (𝓞 F) (v.adicCompletion F) n ≠ 0` using `(Valuation.ne_zero_iff _).1 (hν0 v)`.

Establish `hs : {x : v.adicCompletion F | Valued.v (x - a v) < Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)} ∈ nhds (a v)` using `Valued.mem_nhds.mpr ⟨Units.mk0 (Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) n)) ((Valuation.ne_zero_iff _).2 hx0), fun y hy => by simpa [Valuation.restrict_lt_iff] using hy⟩`. Take `⟨_, hy, ⟨k, rfl⟩⟩` from `mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v) (a v)) _ hs`. Conclude with `⟨k, hy⟩`. Use `choose k hk using hloc`. Take `⟨t, ht1, ht2⟩` from `PI.StrongApproxE.DedekindLFunctions.sa (R := 𝓞 F) (K := F) T k (fun _ => algebraMap (𝓞 F) F n) (fun _ _ => hnF)`.

Establish `hclose : ∀ v ∈ T, Valued.v (a v - algebraMap F (v.adicCompletion F) t) ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)`. Introduce `v hv`. Establish `e : a v - algebraMap F (v.adicCompletion F) t = -(algebraMap F (v.adicCompletion F) (k v) - a v) + algebraMap F (v.adicCompletion F) (k v - t)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[Valuation.map_neg]`. Conclude with `(hk v).le`. Rewrite using `[val_alg, Valuation.map_sub_swap, val_int]`.

Conclude with `ht1 v hv`. Establish `htint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F t ≤ 1`. Introduce `v`. Distinguish the cases in `hv : v ∈ T`. Rewrite using `[← val_alg]`.

Establish `e : algebraMap F (v.adicCompletion F) t = a v - (a v - algebraMap F (v.adicCompletion F) t)` using `by ring`. Rewrite using `[e]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le (ha' v) ((hclose v hv).trans (hν1 v)))`. Conclude with `ht2 v hv`. Take `⟨β, rfl⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) t htint`.

Establish `hu : IsUnit (algebraMap (𝓞 F) (Af F) n)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]`. Conclude with `(Ne.isUnit hnF).map (algebraMap F (Af F))`. Use `set y : Af F := ↑hu.unit⁻¹ * (a - algebraMap (𝓞 F) (Af F) β) with hy`. Establish `hNy : algebraMap (𝓞 F) (Af F) n * y = a - algebraMap (𝓞 F) (Af F) β`.

Rewrite using `[hy, ← mul_assoc, IsUnit.mul_val_inv, one_mul]`. Establish `hNcast : (N : Af F) = algebraMap (𝓞 F) (Af F) n` using `by rw [hn, map_natCast]`. Use `⟨β, y, ?_, by rw [hNcast, hNy]; ring⟩` and prove the remaining obligations. Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F`. Introduce `v`.

Establish `hv' : algebraMap (𝓞 F) (v.adicCompletion F) n * y v = a v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β)`. Use `congrArg (fun z : Af F => z v) hNy` as an intermediate fact. Rewrite using `[← IsScalarTower.algebraMap_apply, ← comp_algebraMap, ← comp_algebraMap]`. Conclude with `this`. Establish `hle : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) * Valued.v (y v) ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)`.

Rewrite using `[← Valuation.map_mul, hv']`. Distinguish the cases in `hv : v ∈ T`. Conclude with `hclose v hv`. Establish `h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) = 1`. Use `le_antisymm (hν1 v) (not_lt.mp ?_)` and prove the remaining obligations.

Rewrite using `[val_int]`. Simplify `hv` using `[T]`. Rewrite using `[h1]`. Use `(Valuation.map_sub _ _ _).trans (max_le (ha' v) ?_)` and prove the remaining obligations. Rewrite using `[val_alg]`.

Conclude with `htint v`. Conclude with `cancel (hν0 v) hle`. Conclude with `key`.
-/
theorem af_approx (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (N : ℕ) (hN : 0 < N) :
    ∃ β : 𝓞 F, ∃ y ∈ Formalism.UG.intAd F, a = algebraMap (𝓞 F) (Af F) β + (N : Af F) * y := by
  classical
  have ha' : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (a v) ≤ 1 := ha
  set n : 𝓞 F := (N : 𝓞 F) with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hN.ne'
  have hnF : algebraMap (𝓞 F) F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hn0
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | v.valuation F (algebraMap (𝓞 F) F n) < 1}.Finite := by
    simp_rw [HeightOneSpectrum.valuation_lt_one_iff_dvd]
    apply Ideal.finite_factors
    simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  let T := hTfin.toFinset
  have hν0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≠ 0 := by
    intro v
    rw [val_int]
    exact (Valuation.ne_zero_iff _).2 hnF
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≤ 1 := by
    intro v
    rw [val_int]
    exact v.valuation_le_one n
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : F,
      Valued.v (algebraMap F (v.adicCompletion F) k - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v
    have hx0 : algebraMap (𝓞 F) (v.adicCompletion F) n ≠ 0 := (Valuation.ne_zero_iff _).1 (hν0 v)
    have hs : {x : v.adicCompletion F | Valued.v (x - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)} ∈ nhds (a v) :=
      Valued.mem_nhds.mpr ⟨Units.mk0 (Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) n))
        ((Valuation.ne_zero_iff _).2 hx0), fun y hy => by simpa [Valuation.restrict_lt_iff] using hy⟩
    obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
      mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v) (a v)) _ hs
    exact ⟨k, hy⟩
  choose k hk using hloc
  obtain ⟨t, ht1, ht2⟩ := PI.StrongApproxE.DedekindLFunctions.sa (R := 𝓞 F) (K := F) T k
    (fun _ => algebraMap (𝓞 F) F n) (fun _ _ => hnF)

  have hclose : ∀ v ∈ T, Valued.v (a v - algebraMap F (v.adicCompletion F) t) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v hv
    have e : a v - algebraMap F (v.adicCompletion F) t =
        -(algebraMap F (v.adicCompletion F) (k v) - a v) + algebraMap F (v.adicCompletion F) (k v - t) := by
      rw [map_sub]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact (hk v).le
    · rw [val_alg, Valuation.map_sub_swap, val_int]; exact ht1 v hv
  have htint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F t ≤ 1 := by
    intro v
    by_cases hv : v ∈ T
    · rw [← val_alg]
      have e : algebraMap F (v.adicCompletion F) t = a v - (a v - algebraMap F (v.adicCompletion F) t) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha' v) ((hclose v hv).trans (hν1 v)))
    · exact ht2 v hv
  obtain ⟨β, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) t htint
  have hu : IsUnit (algebraMap (𝓞 F) (Af F) n) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    exact (Ne.isUnit hnF).map (algebraMap F (Af F))
  set y : Af F := ↑hu.unit⁻¹ * (a - algebraMap (𝓞 F) (Af F) β) with hy
  have hNy : algebraMap (𝓞 F) (Af F) n * y = a - algebraMap (𝓞 F) (Af F) β := by
    rw [hy, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hNcast : (N : Af F) = algebraMap (𝓞 F) (Af F) n := by rw [hn, map_natCast]
  refine ⟨β, y, ?_, by rw [hNcast, hNy]; ring⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F := by
    intro v
    have hv' : algebraMap (𝓞 F) (v.adicCompletion F) n * y v =
        a v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β) := by
      have := congrArg (fun z : Af F => z v) hNy
      rw [← IsScalarTower.algebraMap_apply, ← comp_algebraMap, ← comp_algebraMap]
      exact this
    have hle : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) * Valued.v (y v) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
      rw [← Valuation.map_mul, hv']
      by_cases hv : v ∈ T
      · exact hclose v hv
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) = 1 := by
          refine le_antisymm (hν1 v) (not_lt.mp ?_)
          rw [val_int]
          simpa [T] using hv
        rw [h1]
        refine (Valuation.map_sub _ _ _).trans (max_le (ha' v) ?_)
        rw [val_alg]; exact htint v
    exact cancel (hν0 v) hle
  exact key

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : x ⊗ₜ[F] (1 : Af F) ∈ IntAf F E` using `Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)`. Establish `h2 : (1 : E) ⊗ₜ[F] y ∈ IntAf F E` using `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`. Establish `h3` using `mul_mem h1 h2`. Rewrite `h3` using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem tmul_mem {x : E} (hx : x ∈ Formalism.UG.intOE E) {y : Af F} (hy : y ∈ Formalism.UG.intAd F) :
    x ⊗ₜ[F] y ∈ IntAf F E := by
  have h1 : x ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ IntAf F E := Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨(a : E), a, rfl⟩, rfl⟩)`.
-/
theorem incl_mem (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (a : E) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨(a : E), a, rfl⟩, rfl⟩)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem incl_add (a b : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((a + b : 𝓞 E) : E) =
    Formalism.UG.inclE (F := F) (Af F) (a : E) + Formalism.UG.inclE (F := F) (Af F) (b : E) := by simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem incl_mul (a b : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((a * b : 𝓞 E) : E) =
    Formalism.UG.inclE (F := F) (Af F) (a : E) * Formalism.UG.inclE (F := F) (Af F) (b : E) := by simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem incl_neg (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((-a : 𝓞 E) : E) =
    -Formalism.UG.inclE (F := F) (Af F) (a : E) := by simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem incl_zero : Formalism.UG.inclE (F := F) (Af F) ((0 : 𝓞 E) : E) = 0 := by simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem incl_one : Formalism.UG.inclE (F := F) (Af F) ((1 : 𝓞 E) : E) = 1 := by simp

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {e}`. Establish `hi` using `hy e (Finset.mem_singleton_self e)`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩` and prove the remaining obligations. Establish `hi' : IsIntegral ℤ ((y.natAbs : E) * e)`. Break down `Int.natAbs_eq y with h | h` into its components or cases.

Rewrite `hi` using `[h, zsmul_eq_mul]`. Simplify using `using hi`. Rewrite `hi` using `[h, zsmul_eq_mul]`. Simplify using `using hi.neg`. Conclude with `⟨⟨_, hi'⟩, rfl⟩`.
-/
theorem e_denom (e : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * e ∈ Formalism.UG.intOE E := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have hi := hy e (Finset.mem_singleton_self e)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  have hi' : IsIntegral ℤ ((y.natAbs : E) * e) := by
    rcases Int.natAbs_eq y with h | h
    · rw [h, zsmul_eq_mul] at hi
      simpa using hi
    · rw [h, zsmul_eq_mul] at hi
      simpa using hi.neg
  exact ⟨⟨_, hi'⟩, rfl⟩

end DictRing

/- English proof (translation)
Introduce `F E _ _ _ _ _ r`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩`. Consider the case `tmul e a`. Take `⟨m₁, hm₁, he⟩` from `DictRing.e_denom e`.

Take `⟨m₂, hm₂, ha⟩` from `DictRing.af_denom a`. Use `⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩` and prove the remaining obligations. Establish `hc : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) = (m₁ : E) ⊗ₜ[F] (m₂ : Af F)`. Rewrite using `[Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hc, Algebra.TensorProduct.tmul_mul_tmul]`.

Conclude with `DictRing.tmul_mem he ha`. Consider the case `add x y hx hy`. Take `⟨m₁, hm₁, h₁⟩` from `hx`. Take `⟨m₂, hm₂, h₂⟩` from `hy`. Use `⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩` and prove the remaining obligations.

Establish `e : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) * (x + y) = (m₂ : E ⊗[F] Af F) * ((m₁ : E ⊗[F] Af F) * x) + (m₁ : E ⊗[F] Af F) * ((m₂ : E ⊗[F] Af F) * y)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `add_mem (mul_mem (natCast_mem _ _) h₁) (mul_mem (natCast_mem _ _) h₂)`.
-/
theorem dual_denominator : DDenom := by
  intro F E _ _ _ _ _ r
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨m₁, hm₁, he⟩ := DictRing.e_denom e
    obtain ⟨m₂, hm₂, ha⟩ := DictRing.af_denom a
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have hc : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) = (m₁ : E) ⊗ₜ[F] (m₂ : Af F) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul]
    exact DictRing.tmul_mem he ha
  | add x y hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have e : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) * (x + y) =
        (m₂ : E ⊗[F] Af F) * ((m₁ : E ⊗[F] Af F) * x) + (m₁ : E ⊗[F] Af F) * ((m₂ : E ⊗[F] Af F) * y) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) h₁) (mul_mem (natCast_mem _ _) h₂)

/- English proof (translation)
Introduce `F E _ _ _ _ _ N hN r hr`. Establish `hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪ Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F)))` using `hr`. Use `clear hr`. Proceed by induction on `hr' using Subring.closure_induction with`. Consider the case `mem x hx`.

Break down `hx with ⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩` into its components or cases. Conclude with `⟨a, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩`. Take `⟨β, y', hy', hyeq⟩` from `DictRing.af_approx y hy N hN`. Set `b : 𝓞 E` to `⟨algebraMap F E (algebraMap (𝓞 F) F β), (RingOfIntegers.isIntegral_coe β).algebraMap⟩`. Use `⟨b, (1 : E) ⊗ₜ[F] y', DictRing.tmul_mem (one_mem _) hy', ?_⟩` and prove the remaining obligations.

Use `show (1 : E) ⊗ₜ[F] y = algebraMap F E (algebraMap (𝓞 F) F β) ⊗ₜ[F] (1 : Af F) + (N : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] y')`. Rewrite using `[hyeq, TensorProduct.tmul_add, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), Algebra.algebraMap_eq_smul_one (R := F) (A := Af F), Algebra.algebraMap_eq_smul_one (R := F) (A := E), TensorProduct.smu …`. Consider the case `zero => exact ⟨0, 0, zero_mem _, by rw [DictRing.incl_zero, mul_zero, add_zero]⟩`. Consider the case `one => exact ⟨1, 0, zero_mem _, by rw [DictRing.incl_one, mul_zero, add_zero]⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a₁, r₁, hr₁, e₁⟩` from `hx`. Take `⟨a₂, r₂, hr₂, e₂⟩` from `hy`. Conclude with `⟨a₁ + a₂, r₁ + r₂, add_mem hr₁ hr₂, by rw [e₁, e₂, DictRing.incl_add]; ring⟩`. Consider the case `neg x _ hx`. Take `⟨a₁, r₁, hr₁, e₁⟩` from `hx`.

Conclude with `⟨-a₁, -r₁, neg_mem hr₁, by rw [e₁, DictRing.incl_neg]; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a₁, r₁, hr₁, e₁⟩` from `hx`. Take `⟨a₂, r₂, hr₂, e₂⟩` from `hy`. Use `⟨a₁ * a₂, r₁ * Formalism.UG.inclE (F := F) (Af F) (a₂ : E) + Formalism.UG.inclE (F := F) (Af F) (a₁ : E) * r₂ + (N : E ⊗[F] Af F) * r₁ * r₂, ?_, by rw [e₁, e₂, DictRing.incl_mul]; ring⟩` and prove the remaining obligations.

Conclude with `add_mem (add_mem (mul_mem hr₁ (DictRing.incl_mem a₂)) (mul_mem (DictRing.incl_mem a₁) hr₂)) (mul_mem (mul_mem (natCast_mem _ N) hr₁) hr₂)`.
-/
theorem dual_dense : DDense := by
  intro F E _ _ _ _ _ N hN r hr
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨a, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨β, y', hy', hyeq⟩ := DictRing.af_approx y hy N hN
      let b : 𝓞 E := ⟨algebraMap F E (algebraMap (𝓞 F) F β), (RingOfIntegers.isIntegral_coe β).algebraMap⟩
      refine ⟨b, (1 : E) ⊗ₜ[F] y', DictRing.tmul_mem (one_mem _) hy', ?_⟩
      show (1 : E) ⊗ₜ[F] y = algebraMap F E (algebraMap (𝓞 F) F β) ⊗ₜ[F] (1 : Af F) +
        (N : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] y')
      rw [hyeq, TensorProduct.tmul_add, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), Algebra.algebraMap_eq_smul_one (R := F) (A := Af F),
        Algebra.algebraMap_eq_smul_one (R := F) (A := E), TensorProduct.smul_tmul]
  | zero => exact ⟨0, 0, zero_mem _, by rw [DictRing.incl_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, 0, zero_mem _, by rw [DictRing.incl_one, mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    exact ⟨a₁ + a₂, r₁ + r₂, add_mem hr₁ hr₂, by rw [e₁, e₂, DictRing.incl_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    exact ⟨-a₁, -r₁, neg_mem hr₁, by rw [e₁, DictRing.incl_neg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    refine ⟨a₁ * a₂, r₁ * Formalism.UG.inclE (F := F) (Af F) (a₂ : E) + Formalism.UG.inclE (F := F) (Af F) (a₁ : E) * r₂ +
      (N : E ⊗[F] Af F) * r₁ * r₂, ?_, by rw [e₁, e₂, DictRing.incl_mul]; ring⟩
    exact add_mem (add_mem (mul_mem hr₁ (DictRing.incl_mem a₂)) (mul_mem (DictRing.incl_mem a₁) hr₂))
      (mul_mem (mul_mem (natCast_mem _ N) hr₁) hr₂)

end PIW.AdelClassFin
