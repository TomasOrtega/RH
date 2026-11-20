import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartHodgeMatrix

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x hc hred φ hφ b hb`. Use `set I : Ideal (rB ℂ K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hI`. Establish `hφI : ∀ a ∈ I, φ a = 0`. Introduce `a ha`. Rewrite `ha` using `[hI, Ideal.mem_span_range_iff_exists_fun]`.

Take `⟨g, rfl⟩` from `ha`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [map_mul, hφ j, mul_zero]`. Set `ψ : (rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ` to `Ideal.Quotient.liftₐ I φ hφI`. Establish `hψ : ∀ a, ψ (Ideal.Quotient.mk I a) = φ a` using `fun a => rfl`.

Set `ι : ↥(rA ℂ x {0}) →+* ↥(rB ℂ K x {0})` to `(algebraMap (↥(rA ℂ x {0})) K).codRestrict (rB ℂ K x {0}) (fun r => isIntegral_algebraMap)`. Establish `hι : ∀ r, (ι r : K) = algebraMap F K (r : F)` using `fun r => rfl`. Establish `hbot : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ, Ideal.Quotient.mk I (ι ⟨y, hy⟩) = algebraMap ℂ _ c`. Introduce `y hy`. Establish `hy' : y ∈ Algebra.adjoin ℂ {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i}` using `hy`.

Proceed by induction on `hy' using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Take `⟨i, hi, j, rfl⟩` from `hz`. Rewrite `hi` using `[Finset.mem_singleton]`. Substitute `hi` using the available equality.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Distinguish the cases in `h0 : x 0 = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: ι ⟨x 0 / x 0, hy⟩ = 0` using `Subtype.ext (by rw [hι]; simp [h0])`.

Rewrite using `[this, map_zero, map_zero]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: ι ⟨x 0 / x 0, hy⟩ = 1` using `Subtype.ext (by rw [hι]; simp [h0])`. Rewrite using `[this, map_one, map_one]`. Consider the case `succ j`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Establish `: ι ⟨x j.succ / x 0, hy⟩ = ⟨_, tco_mem ℂ K x j⟩` using `rfl`. Rewrite using `[this]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.

Consider the case `algebraMap c`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `: ι ⟨algebraMap ℂ F c, hy⟩ = algebraMap ℂ _ c`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hι]`.

Conclude with `(IsScalarTower.algebraMap_apply ℂ F K c).symm`. Rewrite using `[this]`. Conclude with `(Ideal.Quotient.mkₐ ℂ I).commutes c`. Consider the case `add y z hy1 hz1 ihy ihz`. Take `⟨c1, h1⟩` from `ihy hy1`.

Take `⟨c2, h2⟩` from `ihz hz1`. Use `⟨c1 + c2, ?_⟩` and prove the remaining obligations. Establish `: ι ⟨y + z, hy⟩ = ι ⟨y, hy1⟩ + ι ⟨z, hz1⟩`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.

Rewrite using `[this, map_add, h1, h2, map_add]`. Consider the case `mul y z hy1 hz1 ihy ihz`. Take `⟨c1, h1⟩` from `ihy hy1`. Take `⟨c2, h2⟩` from `ihz hz1`. Use `⟨c1 * c2, ?_⟩` and prove the remaining obligations.

Establish `: ι ⟨y * z, hy⟩ = ι ⟨y, hy1⟩ * ι ⟨z, hz1⟩`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression. Rewrite using `[this, map_mul, h1, h2, map_mul]`. Set `f : ↥(rA ℂ x {0}) →+* (rB ℂ K x {0} ⧸ I)` to `(Ideal.Quotient.mk I).comp ι`.

Set `g : ↥(rA ℂ x {0}) →+* ℂ` to `ψ.toRingHom.comp f`. Establish `hfg : (algebraMap ℂ (rB ℂ K x {0} ⧸ I)).comp g = f`. Use extensionality with `r`. Take `⟨c, hc'⟩` from `hbot r.1 r.2`. Establish `hr : f r = algebraMap ℂ _ c` using `hc'`.

Use `show algebraMap ℂ _ (ψ (f r)) = f r`. Rewrite using `[hr, ψ.commutes]`. Both sides reduce to the same expression. Establish `hint : Algebra.IsIntegral ℂ (rB ℂ K x {0} ⧸ I)`. Prove the components needed by the constructor for the conclusion.

Introduce `q`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨p, hpm, hp⟩` from `(a.2 : IsIntegral (↥(rA ℂ x {0})) (a : K))`. Use `⟨p.map g, hpm.map g, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hfg]`.

Establish `hzero : p.eval₂ ι a = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Polynomial.hom_eval₂ p ι (rB ℂ K x {0}).val.toRingHom a` as an intermediate fact. Simplify using `using this.trans hp`. Use `Polynomial.hom_eval₂ p ι (Ideal.Quotient.mk I) a` as an intermediate fact.

Rewrite `this` using `[hzero, map_zero]`. Conclude with `this.symm`. Establish `hft : Algebra.FiniteType ℂ (rB ℂ K x {0} ⧸ I)`. Use `hc.3 0` as an intermediate fact. Conclude with `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective ℂ I)`.

Establish `hfin : Module.Finite ℂ (rB ℂ K x {0} ⧸ I)` using `Algebra.IsIntegral.finite`. Establish `hart : IsArtinianRing (rB ℂ K x {0} ⧸ I)` using `IsArtinianRing.of_finite ℂ _`. Take `⟨n, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I b) (1 : rB ℂ K x {0} ⧸ I)`. Take `⟨y0, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `⟨1 - b * y0, ?_⟩` and prove the remaining obligations.

Establish `hc1 : φ (1 - b * y0) ≠ 0`. Simplify using `[map_sub, map_mul, hb]`. Establish `hkill : Ideal.Quotient.mk I ((1 - b * y0) * b) = 0`. Establish `hy2 : Ideal.Quotient.mk I b ^ (n + 1) * Ideal.Quotient.mk I y0 = Ideal.Quotient.mk I b ^ n`. Simplify `hy` using `[smul_eq_mul]`.

Establish `h0 : Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n = 0`. Rewrite using `[map_sub, map_one, map_mul]`. Take the linear combination `(-1 : rB ℂ K x {0} ⧸ I) * hy2`. Apply `IsReduced.eq_zero` to reduce the goal to its premises. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hkill` using `[Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun]`. Take `⟨gg, hgg⟩` from `hkill`. Conclude with `⟨gg, hc1, hgg.symm⟩`.
-/
theorem UpperTheory.exists_regular_parameters_of_reduced_quotient :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover ℂ K x → IsReduced ((rB ℂ K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})))) → ∀ φ : rB ℂ K x {0} →ₐ[ℂ] ℂ, (∀ j : Fin d, φ ⟨_, tco_mem ℂ K x j⟩ = 0) → ∀ b : rB ℂ K x {0}, φ b = 0 → ∃ (c : rB ℂ K x {0}) (g : Fin d → rB ℂ K x {0}), φ c ≠ 0 ∧ c * b = ∑ l, g l * ⟨_, tco_mem ℂ K x l⟩ := by
  intro F K _ _ _ _ _ _ d x hc hred φ hφ b hb
  set I : Ideal (rB ℂ K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hI
  have hφI : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    rw [hI, Ideal.mem_span_range_iff_exists_fun] at ha
    obtain ⟨g, rfl⟩ := ha
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hφ j, mul_zero]
  let ψ : (rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ I φ hφI
  have hψ : ∀ a, ψ (Ideal.Quotient.mk I a) = φ a := fun a => rfl
  let ι : ↥(rA ℂ x {0}) →+* ↥(rB ℂ K x {0}) :=
    (algebraMap (↥(rA ℂ x {0})) K).codRestrict (rB ℂ K x {0}) (fun r => isIntegral_algebraMap)
  have hι : ∀ r, (ι r : K) = algebraMap F K (r : F) := fun r => rfl
  have hbot : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
      Ideal.Quotient.mk I (ι ⟨y, hy⟩) = algebraMap ℂ _ c := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin ℂ {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i} := hy
    induction hy' using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, hi, j, rfl⟩ := hz
      rw [Finset.mem_singleton] at hi
      subst hi
      induction j using Fin.cases with
      | zero =>
        by_cases h0 : x 0 = 0
        · refine ⟨0, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 0 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_zero, map_zero]
        · refine ⟨1, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 1 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_one, map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
        have : ι ⟨x j.succ / x 0, hy⟩ = ⟨_, tco_mem ℂ K x j⟩ := rfl
        rw [this]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap c =>
      refine ⟨c, ?_⟩
      have : ι ⟨algebraMap ℂ F c, hy⟩ = algebraMap ℂ _ c := by
        apply Subtype.ext
        rw [hι]
        exact (IsScalarTower.algebraMap_apply ℂ F K c).symm
      rw [this]
      exact (Ideal.Quotient.mkₐ ℂ I).commutes c
    | add y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 + c2, ?_⟩
      have : ι ⟨y + z, hy⟩ = ι ⟨y, hy1⟩ + ι ⟨z, hz1⟩ := by
        rw [← map_add]
        rfl
      rw [this, map_add, h1, h2, map_add]
    | mul y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 * c2, ?_⟩
      have : ι ⟨y * z, hy⟩ = ι ⟨y, hy1⟩ * ι ⟨z, hz1⟩ := by
        rw [← map_mul]
        rfl
      rw [this, map_mul, h1, h2, map_mul]
  let f : ↥(rA ℂ x {0}) →+* (rB ℂ K x {0} ⧸ I) := (Ideal.Quotient.mk I).comp ι
  let g : ↥(rA ℂ x {0}) →+* ℂ := ψ.toRingHom.comp f
  have hfg : (algebraMap ℂ (rB ℂ K x {0} ⧸ I)).comp g = f := by
    ext r
    obtain ⟨c, hc'⟩ := hbot r.1 r.2
    have hr : f r = algebraMap ℂ _ c := hc'
    show algebraMap ℂ _ (ψ (f r)) = f r
    rw [hr, ψ.commutes]
    rfl
  have hint : Algebra.IsIntegral ℂ (rB ℂ K x {0} ⧸ I) := by
    constructor
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ := (a.2 : IsIntegral (↥(rA ℂ x {0})) (a : K))
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map, hfg]
    have hzero : p.eval₂ ι a = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ p ι (rB ℂ K x {0}).val.toRingHom a
      simpa using this.trans hp
    have := Polynomial.hom_eval₂ p ι (Ideal.Quotient.mk I) a
    rw [hzero, map_zero] at this
    exact this.symm
  have hft : Algebra.FiniteType ℂ (rB ℂ K x {0} ⧸ I) := by
    have := hc.3 0
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective ℂ I)
  have hfin : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := Algebra.IsIntegral.finite
  have hart : IsArtinianRing (rB ℂ K x {0} ⧸ I) := IsArtinianRing.of_finite ℂ _
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I b) (1 : rB ℂ K x {0} ⧸ I)
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨1 - b * y0, ?_⟩
  have hc1 : φ (1 - b * y0) ≠ 0 := by
    simp [map_sub, map_mul, hb]
  have hkill : Ideal.Quotient.mk I ((1 - b * y0) * b) = 0 := by
    have hy2 : Ideal.Quotient.mk I b ^ (n + 1) * Ideal.Quotient.mk I y0 = Ideal.Quotient.mk I b ^ n := by
      simpa [smul_eq_mul] using hy
    have h0 : Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n = 0 := by
      rw [map_sub, map_one, map_mul]
      linear_combination (-1 : rB ℂ K x {0} ⧸ I) * hy2
    apply IsReduced.eq_zero
    refine ⟨n + 1, ?_⟩
    rw [map_mul, mul_pow]
    calc Ideal.Quotient.mk I (1 - b * y0) ^ (n + 1) * Ideal.Quotient.mk I b ^ (n + 1)
        = Ideal.Quotient.mk I (1 - b * y0) ^ n * Ideal.Quotient.mk I b
          * (Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n) := by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun] at hkill
  obtain ⟨gg, hgg⟩ := hkill
  exact ⟨gg, hc1, hgg.symm⟩
