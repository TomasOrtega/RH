import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataFurther
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormOneMkIff

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section

namespace GlobalTheory.DiscAutLenOne

open Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.fibreCountingData

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

def gen (J : JD h L 𝔭 b a) (i : Fin m) : DiscMod h ⊤ L 𝔭 :=
  Submodule.Quotient.mk ⟨phi (K := K) b a (Pi.single i 1), J.u_mem i⟩

/- English proof (translation)
The claim follows from `J.max.isPrime; jK z / jK (ι (a k)) ∈ HU.SP K 𝔭 := by have := J.max.isPrime rw [div_mem_SP_iff J.max (J.ne k), hk, pow_zero, Ideal.one_eq_top] trivial`.
-/
theorem div_mem_of_zero (J : JD h L 𝔭 b a) {k : Fin m} (hk : vF 𝔭 (a k) = 0) (z : 𝓞 K) :
    haveI := J.max.isPrime; jK z / jK (ι (a k)) ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  rw [div_mem_SP_iff J.max (J.ne k), hk, pow_zero, Ideal.one_eq_top]
  trivial

/- English proof (translation)
The claim follows from `J.max.isPrime; jK z / jK (ι (a i)) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ 1 := by have := J.max.isPrime rw [div_mem_SP_iff J.max (J.ne i), hi]`.
-/
theorem div_mem_iff_one (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1) (z : 𝓞 K) :
    haveI := J.max.isPrime; jK z / jK (ι (a i)) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  rw [div_mem_SP_iff J.max (J.ne i), hi]

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Rewrite using `[gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, J.memB]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `H i` as an intermediate fact.

Rewrite `this` using `[crd_smul, J.crd_u, if_pos rfl, mul_one_div]`. Conclude with `(div_mem_iff_one J hi c).1 this`. Introduce `hc k`. Rewrite using `[crd_smul, J.crd_u]`. Use `split_ifs with hk`.

Substitute `hk` using the available equality. Rewrite using `[mul_one_div]`. Conclude with `(div_mem_iff_one J hi c).2 hc`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.
-/
theorem smul_gen_eq_zero_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1) (c : 𝓞 K) :
    c • gen J i = 0 ↔ c ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  rw [gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_smul, J.memB]
  constructor
  · intro H
    have := H i
    rw [crd_smul, J.crd_u, if_pos rfl, mul_one_div] at this
    exact (div_mem_iff_one J hi c).1 this
  · intro hc k
    rw [crd_smul, J.crd_u]
    split_ifs with hk
    · subst hk; rw [mul_one_div]; exact (div_mem_iff_one J hi c).2 hc
    · rw [mul_zero]; exact zero_mem _

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `hx` using `(J.memA x).1 x.2`. Take `⟨z, hz⟩` from `exists_sub_div_mem_SP J.max (J.ne i) (hx i)`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul, J.memB]`. Introduce `k`. Rewrite using `[crd_sub, crd_smul, J.crd_u]`. Use `split_ifs with hk`. Substitute `hk` using the available equality.

Establish `e : crd h b a (x : V) k - jK z * (1 / jK (ι (a k))) = (jK (ι (a k)) * crd h b a (x : V) k - jK z) / jK (ι (a k))`. Rewrite using `[sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne k))]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hz`.

Rewrite using `[mul_zero, sub_zero]`. Establish `e : crd h b a (x : V) k = (jK (ι (a k)) * crd h b a (x : V) k) * (jK 1 / jK (ι (a k)))`. Rewrite using `[map_one]`. Clear denominators, using `[jK_ι_ne_zero (J.ne k)]` for the nonvanishing conditions. Rewrite using `[e]`.

Conclude with `mul_mem (hx k) (div_mem_of_zero J (hj k hk) 1)`.
-/
theorem exists_smul_gen (J : JD h L 𝔭 b a) {i : Fin m} (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0)
    (q : DiscMod h ⊤ L 𝔭) : ∃ c : 𝓞 K, q = c • gen J i := by
  have := J.max.isPrime
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := (J.memA x).1 x.2
  obtain ⟨z, hz⟩ := exists_sub_div_mem_SP J.max (J.ne i) (hx i)
  refine ⟨z, ?_⟩
  rw [gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul, J.memB]
  intro k
  rw [crd_sub, crd_smul, J.crd_u]
  split_ifs with hk
  · subst hk
    have e : crd h b a (x : V) k - jK z * (1 / jK (ι (a k))) =
        (jK (ι (a k)) * crd h b a (x : V) k - jK z) / jK (ι (a k)) := by
      rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne k))]; ring
    rw [e]; exact hz
  · rw [mul_zero, sub_zero]
    have e : crd h b a (x : V) k = (jK (ι (a k)) * crd h b a (x : V) k) * (jK 1 / jK (ι (a k))) := by
      rw [map_one]; field_simp [jK_ι_ne_zero (J.ne k)]
    rw [e]
    exact mul_mem (hx k) (div_mem_of_zero J (hj k hk) 1)

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_smul_gen J hj (P (gen J i))`. Use `⟨c, LinearMap.ext fun q => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `exists_smul_gen J hj q`. Rewrite using `[Module.algebraMap_end_apply, map_smul, hc, smul_comm]`.
-/
theorem end_eq_algebraMap (J : JD h L 𝔭 b a) {i : Fin m} (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0)
    (P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) :
    ∃ c : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c = P := by
  obtain ⟨c, hc⟩ := exists_smul_gen J hj (P (gen J i))
  refine ⟨c, LinearMap.ext fun q => ?_⟩
  obtain ⟨d, rfl⟩ := exists_smul_gen J hj q
  rw [Module.algebraMap_end_apply, map_smul, hc, smul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `LinearMap.congr_fun H (gen J i)` as an intermediate fact. Rewrite `this` using `[Module.algebraMap_end_apply, LinearMap.zero_apply]`. Conclude with `(smul_gen_eq_zero_iff J hi c).1 this`.

Introduce `hc`. Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨d, rfl⟩` from `exists_smul_gen J hj q`. Rewrite using `[Module.algebraMap_end_apply, LinearMap.zero_apply, smul_comm, (smul_gen_eq_zero_iff J hi c).2 hc, smul_zero]`.
-/
theorem algebraMap_eq_zero_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) (c : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c = 0 ↔ c ∈ extP K 𝔭 ^ 1 := by
  constructor
  · intro H
    have := LinearMap.congr_fun H (gen J i)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at this
    exact (smul_gen_eq_zero_iff J hi c).1 this
  · intro hc
    refine LinearMap.ext fun q => ?_
    obtain ⟨d, rfl⟩ := exists_smul_gen J hj q
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, smul_comm,
      (smul_gen_eq_zero_iff J hi c).2 hc, smul_zero]

end GlobalTheory.DiscAutLenOne

namespace GlobalTheory.DiscAutLenOne

open Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.fibreCountingData

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Establish `hjc : jK (conjO K c * c - 1) = star (jK c) * jK c - 1`. Rewrite using `[map_sub, map_mul, map_one, jK_conjO]`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Set `u : ↥(locF 𝔭 (dualIn h ⊤ L))` to `⟨_, J.u_mem i⟩`. Establish `e1 : (Submodule.Quotient.mk (c • u) : DiscMod h ⊤ L 𝔭) = algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk u)`. Rewrite using `[Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]`. Establish `H1` using `H u u (c • u) (c • u) e1 e1`. Rewrite `H1` using `[← HU.mem_SP_iff_locF]`.

Establish `huu : h (u : V) (u : V) = 1 / jK (ι (a i))`. Rewrite using `[h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.sum_eq_single i]`. Simplify using `only [u]`. Rewrite using `[J.crd_u, if_pos rfl, star_div₀, star_one, star_jK_ι J.fix]`. Clear denominators, using `[jK_ι_ne_zero (J.ne i)]` for the nonvanishing conditions.

Introduce `k _ hk`. Simplify using `only [u]`. Rewrite using `[J.crd_u, if_neg hk, star_zero, zero_mul, zero_mul]`. Introduce `hi'`. Conclude with `absurd (Finset.mem_univ i) hi'`.

Establish `e2 : h ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) - h (u : V) (u : V) = jK (conjO K c * c - 1) / jK (ι (a i))`. Rewrite using `[Submodule.coe_smul, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, huu, hjc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `H1` using `[e2]`. Conclude with `(div_mem_iff_one J hi _).1 H1`.

Introduce `hc x y x' y' hx hy`. Rewrite `hx`, `hy` using `[Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul]`. Rewrite using `[← HU.mem_SP_iff_locF]`. Establish `e : h (x' : V) (y' : V) - h (x : V) (y : V) = (h (x' : V) (y' : V) - h (c • (x : V)) (c • (y : V))) + (h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V))` using `by ring`. Rewrite using `[e]`.

Use `add_mem (J.h_sub_mem _ _ _ _ (Submodule.smul_mem _ c x.2) (Submodule.smul_mem _ c y.2) hx hy) ?_` and prove the remaining obligations. Establish `e3 : h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V) = (star (jK c) * jK c - 1) * h (x : V) (y : V)`. Rewrite using `[smul_eq_jK c, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.mul_sum]`.

Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Establish `hxA` using `(J.memA x).1 x.2 k`. Establish `hyA` using `(J.memA y).1 y.2 k`. Establish `hW : jK (conjO K c * c - 1) / jK (ι (a k)) ∈ HU.SP K 𝔭`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Conclude with `(div_mem_iff_one J hi _).2 hc`. Conclude with `div_mem_of_zero J (hj k hk) _`. Establish `hne` using `jK_ι_ne_zero (K := K) (J.ne k)`. Establish `e4 : (star (jK c) * jK c - 1) * (star (crd h b a (x : V) k) * jK (ι (a k)) * crd h b a (y : V) k) = star (jK (ι (a k)) * crd h b a (x : V) k) * (jK (conjO K c * c - 1) / jK (ι (a k))) * (jK (ι (a k)) * crd h b a (y : V) k)`.

Rewrite using `[star_mul', star_jK_ι J.fix, hjc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e4]`. Conclude with `mul_mem (mul_mem (star_mem_SP J.fix hxA) hW) hyA`.
-/
theorem cond_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) (c : 𝓞 K) :
    (∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      (Submodule.Quotient.mk x' : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) ↔
      conjO K c * c - 1 ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  have hjc : jK (conjO K c * c - 1) = star (jK c) * jK c - 1 := by
    rw [map_sub, map_mul, map_one, jK_conjO]
  constructor
  · intro H
    let u : ↥(locF 𝔭 (dualIn h ⊤ L)) := ⟨_, J.u_mem i⟩
    have e1 : (Submodule.Quotient.mk (c • u) : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk u) := by
      rw [Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
    have H1 := H u u (c • u) (c • u) e1 e1
    rw [← HU.mem_SP_iff_locF] at H1
    have huu : h (u : V) (u : V) = 1 / jK (ι (a i)) := by
      rw [h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.sum_eq_single i]
      · simp only [u]
        rw [J.crd_u, if_pos rfl, star_div₀, star_one, star_jK_ι J.fix]
        field_simp [jK_ι_ne_zero (J.ne i)]
      · intro k _ hk
        simp only [u]
        rw [J.crd_u, if_neg hk, star_zero, zero_mul, zero_mul]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have e2 : h ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) -
        h (u : V) (u : V) = jK (conjO K c * c - 1) / jK (ι (a i)) := by
      rw [Submodule.coe_smul, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, starRingEnd_apply, huu, hjc]
      ring
    rw [e2] at H1
    exact (div_mem_iff_one J hi _).1 H1
  · intro hc x y x' y' hx hy
    rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul] at hx hy
    rw [← HU.mem_SP_iff_locF]
    have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (x' : V) (y' : V) - h (c • (x : V)) (c • (y : V))) +
          (h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V)) := by ring
    rw [e]
    refine add_mem (J.h_sub_mem _ _ _ _ (Submodule.smul_mem _ c x.2) (Submodule.smul_mem _ c y.2)
      hx hy) ?_
    have e3 : h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V) =
        (star (jK c) * jK c - 1) * h (x : V) (y : V) := by
      rw [smul_eq_jK c, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, starRingEnd_apply]
      ring
    rw [e3, h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    have hxA := (J.memA x).1 x.2 k
    have hyA := (J.memA y).1 y.2 k
    have hW : jK (conjO K c * c - 1) / jK (ι (a k)) ∈ HU.SP K 𝔭 := by
      by_cases hk : k = i
      · subst hk; exact (div_mem_iff_one J hi _).2 hc
      · exact div_mem_of_zero J (hj k hk) _
    have hne := jK_ι_ne_zero (K := K) (J.ne k)
    have e4 : (star (jK c) * jK c - 1) * (star (crd h b a (x : V) k) * jK (ι (a k)) * crd h b a (y : V) k) =
        star (jK (ι (a k)) * crd h b a (x : V) k) * (jK (conjO K c * c - 1) / jK (ι (a k))) *
          (jK (ι (a k)) * crd h b a (y : V) k) := by
      rw [star_mul', star_jK_ι J.fix, hjc]
      field_simp
    rw [e4]
    exact mul_mem (mul_mem (star_mem_SP J.fix hxA) hW) hyA

/- English proof (translation)
Set `Φ : (𝓞 K ⧸ extP K 𝔭 ^ 1) →+* Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)` to `Ideal.Quotient.lift _ (algebraMap _ _) fun c hc => (algebraMap_eq_zero_iff J hi hj c).2 hc`. Establish `hΦ : Function.Bijective Φ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 ((algebraMap_eq_zero_iff J hi hj c).1 hz)`. Introduce `P`. Take `⟨c, hc⟩` from `end_eq_algebraMap J hj P`. Conclude with `⟨Ideal.Quotient.mk _ c, hc⟩`.

Rewrite using `[discAut, ← NormOneGroup.card_normOne]`. Use `symm`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Φ hΦ) fun z => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[NormOneGroup.normOne_mk_iff J.fix 𝔭 1 c, Equiv.ofBijective_apply]`.

Conclude with `(cond_iff J hi hj c).symm`.
-/
theorem discAut_eq (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) :
    discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  let Φ : (𝓞 K ⧸ extP K 𝔭 ^ 1) →+* Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
    Ideal.Quotient.lift _ (algebraMap _ _) fun c hc => (algebraMap_eq_zero_iff J hi hj c).2 hc
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((algebraMap_eq_zero_iff J hi hj c).1 hz)
    · intro P
      obtain ⟨c, hc⟩ := end_eq_algebraMap J hj P
      exact ⟨Ideal.Quotient.mk _ c, hc⟩
  rw [discAut, ← NormOneGroup.card_normOne]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Φ hΦ) fun z => ?_)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [NormOneGroup.normOne_mk_iff J.fix 𝔭 1 c, Equiv.ofBijective_apply]
  exact (cond_iff J hi hj c).symm

end GlobalTheory.DiscAutLenOne

open GlobalTheory.DiscAutLenOne in

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ _ hF h _ L hL 𝔭 h𝔭 b a hJ i hi hj`. Take `⟨-, hloc, horth, hdiag, hne⟩` from `hJ`. Conclude with `discAut_eq ⟨horth, hdiag, hne, hloc, hF, h𝔭, hL.fg, hL.span_eq_top⟩ hi hj`.
-/
theorem GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ L 𝔭 b a → ∀ i, vF 𝔭 (a i) = 1 → (∀ j, j ≠ i → vF 𝔭 (a j) = 0) → discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hF h _ L hL 𝔭 h𝔭 b a hJ i hi hj
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hJ
  exact discAut_eq ⟨horth, hdiag, hne, hloc, hF, h𝔭, hL.fg, hL.span_eq_top⟩ hi hj
