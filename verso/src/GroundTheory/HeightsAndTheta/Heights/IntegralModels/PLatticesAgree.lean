import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulMemOfSpanEqTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v`.
-/
theorem exists_ne_zero_smul_mem_of_span_eq_top (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v

/- English proof (translation)
Take `⟨d, hd, hdv⟩` from `exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v`. Take `⟨c, hc⟩` from `Module.projective_def.mp (inferInstance : Module.Projective A M)`. Use `set x : M := ⟨d • v, hdv⟩ with hx`. Establish `hdK : algebraMap A K d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd`. Establish `hdiv : ∀ y : M, ∃ a : A, c x y = d * a`.

Introduce `y`. Establish `hq : algebraMap A K (c x y) / algebraMap A K d ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K)`. Rewrite using `[hHOI A K]`. Simplify using `only [Submodule.mem_iInf]`. Introduce `p hp`.

Take `⟨s, hs, hsv⟩` from `hv p hp`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `set x' : M := ⟨s • v, hsv⟩`. Establish `hxx : d • x' = s • x` using `by ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]`. Establish `hcc : d * c x' y = s * c x y`.

Use `congrArg (fun z => c z y) hxx` as an intermediate fact. Simplify `this` using `[map_smul]`. Use `Algebra.mem_bot.mpr ⟨c x' y, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul, mul_div_right_comm, div_self hdK, one_mul]`. Take `⟨a, ha⟩` from `Algebra.mem_bot.mp hq`.

Use `⟨a, IsFractionRing.injective A K ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ha, mul_div_cancel₀ _ hdK]`. Use `choose a ha using hdiv`. Establish `hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M` using `M.sum_mem fun y _ => M.smul_mem (a y) y.2`. Establish `hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V)`.

Establish `h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v` using `by rw [hc x]`. Rewrite using `[← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, id, ha y, mul_smul]`. Establish `hvw : v = ∑ y ∈ (c x).support, a y • (y : V)`.

Rewrite `hsum` using `[← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]`. Conclude with `smul_right_injective V hdK hsum`. Rewrite using `[hvw]`. Conclude with `hw`.
-/
theorem mem_of_forall_mem_localizedIn (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw

/- English proof (translation)
Introduce `A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN`. Establish `sub : ∀ (P Q : Submodule A V), Module.Projective A P → Submodule.span K (P : Set V) = ⊤ → (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P`. Introduce `P Q hP hPs hQP v hvQ`. Conclude with `mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp => hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩`. Conclude with `le_antisymm (sub N M hNp hN fun p hp => hMN p hp) (sub M N hMp hM fun p hp => (hMN p hp).symm)`.
-/
theorem LatticesAgree.proof (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by
  intro A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN
  have sub : ∀ (P Q : Submodule A V), Module.Projective A P →
      Submodule.span K (P : Set V) = ⊤ →
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P := by
    intro P Q hP hPs hQP v hvQ
    exact mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp =>
      hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩
  exact le_antisymm (sub N M hNp hN fun p hp => hMN p hp)
    (sub M N hMp hM fun p hp => (hMN p hp).symm)

end GroundTheory.Heights₂.Heights.Model
