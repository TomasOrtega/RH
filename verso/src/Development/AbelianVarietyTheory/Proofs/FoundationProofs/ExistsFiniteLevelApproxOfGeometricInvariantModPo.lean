import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantsFromFiniteLevel

open GlobalTheory.K5

namespace GlobalTheory.K5.GeoLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Use `⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1`. Simplify using `[(T.prim n).pow_eq_one]`.
-/
theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

def ggens (T : Tower p Ω) (N : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x} ∪ T.qq '' Set.Iic N

/- English proof (translation)
Unfold `ggens`. Use `gcongr`.
-/
theorem ggens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : ggens T m ⊆ ggens T n := by
  unfold ggens
  gcongr

/- English proof (translation)
Establish `hgeo : ∀ x : Ω, IsAlgZp p x → g x = x` using `(Subgroup.mem_inf.mp hg).1`. Establish `hq : g (T.qq N) = T.qq N` using `(Subgroup.mem_inf.mp hg).2`. Introduce and unpack `a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)`. Conclude with `g.commutes r`. Conclude with `hgeo a ha`.

Establish `hi' : i + (N - i) = N` using `Nat.add_sub_cancel' hi`. Rewrite using `[GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]`.
-/
theorem fixes_ggens (T : Tower p Ω) (N : ℕ) (g : Gal p Ω)
    (hg : g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N)) :
    ∀ a ∈ ggens T N, g a = a := by
  have hgeo : ∀ x : Ω, IsAlgZp p x → g x = x := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq N) = T.qq N := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · exact hgeo a ha
  · have hi' : i + (N - i) = N := Nat.add_sub_cancel' hi
    rw [GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]

/- English proof (translation)
Use `haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T`. Set `L : IntermediateField ℚ Ω` to `IntermediateField.adjoin ℚ (⋃ n, ggens T n)`. Establish `hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L` using `fun a ha => IntermediateField.subset_adjoin ℚ _ ha`. Establish `hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L` using `fun r => hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)`. Set `φ : O0 p →+* L` to `(algebraMap (O0 p) Ω).codRestrict L hO`.

Establish `hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r` using `fun r => rfl`. Establish `hφinj : Function.Injective φ`. Introduce `a b hab`. Apply `hClo.inj` to reduce the goal to its premises. Rewrite using `[← hφ a, ← hφ b, hab]`.

Use `haveI halg : Algebra.IsAlgebraic L Ω := by`. Prove the components needed by the constructor for the conclusion. Introduce `z`. Take `⟨P, hP0, hPz⟩` from `hClo.alg.isAlgebraic z`. Use `⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Rewrite `hPz` using `[Polynomial.aeval_def]`. Use `hPz using 2` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext hφ`. Use `haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩`.

Use `haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω`. Establish `hyL : y ∈ L`. Establish `: y ∈ Set.range (algebraMap L Ω)`. Rewrite using `[InfiniteGalois.mem_range_algebraMap_iff_fixed]`. Introduce `f`.

Set `g : Gal p Ω` to `AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))`. Establish `hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a` using `fun a ha => f.commutes ⟨a, hmemL a ha⟩`. Establish `hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n`. Use `Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩), Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)`.

Conclude with `hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)`. Conclude with `hy g hg`. Take `⟨l, rfl⟩` from `this`. Conclude with `l.2`. Take `⟨S, hS, hyS⟩` from `IntermediateField.exists_finset_of_mem_adjoin hyL`.

Establish `hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m` using `fun t ht => Set.mem_iUnion.mp (hS ht)`. Use `choose! m hm using hex`. Use `⟨S.sup m, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hSN : (S : Set Ω) ⊆ ggens T (S.sup m)` using `fun t ht => ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)`. Establish `hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m))` using `IntermediateField.adjoin.mono ℚ _ _ hSN hyS`.

Set `gq : Ω ≃ₐ[ℚ] Ω` to `AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)`. Establish `hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω)` using `Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha`. Take `⟨r, hr, s, hs, rfl⟩` from `IntermediateField.mem_adjoin_iff_div.mp hyN`. Establish `hr' : g r = r` using `hle hr`. Establish `hs' : g s = s` using `hle hs`.

Rewrite using `[map_div₀, hr', hs']`.
-/
theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h y = y) :
    ∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y := by
  haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, ggens T n)
  have hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a := fun a ha => f.commutes ⟨a, hmemL a ha⟩
      have hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
        refine Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩),
          Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
        · exact hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)
        · exact hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ ggens T (S.sup m) := fun t ht =>
    ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.GeoLevel

/- English proof (translation)
Introduce `p _ hp2 Ω _ _ hClo T k j hj x hx hfix`. Take `⟨y₀, E, hy₀, hEH, huniq, hsum⟩` from `GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj`. Establish `hgi : ∀ (g : Gal p Ω) (z : Ω), IsInt p z → IsInt p (g z)` using `fun g z hz => hz.map (g : Ω →ₐ[O0 p] Ω)`. Use `⟨∑ g ∈ E, g (y₀ * x), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsIntegral.sum _ fun g _ => hgi g _ (hy₀.mul hx)`.

Conclude with `GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _ (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)`. Establish `hz : ∀ g ∈ E, ∃ z : Ω, IsInt p z ∧ g x - x = (p : Ω) ^ k * z` using `fun g hg => hfix g (hEH g hg) choose! z hzi hzx using hz`. Use `⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg`. Rewrite using `[← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Take the linear combination `(-(g y₀)) * hzx g hg`.
-/
theorem GlobalTheory.K5.geo_invariants_from_finite_level :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt p x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (g x) x) →
  ∃ y : Ω, IsInt p y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong p k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi : ∀ (g : Gal p Ω) (z : Ω), IsInt p z → IsInt p (g z) := fun g z hz =>
    hz.map (g : Ω →ₐ[O0 p] Ω)
  refine ⟨∑ g ∈ E, g (y₀ * x), ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun g _ => hgi g _ (hy₀.mul hx)
  · exact GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
      (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  · have hz : ∀ g ∈ E, ∃ z : Ω, IsInt p z ∧ g x - x = (p : Ω) ^ k * z :=
      fun g hg => hfix g (hEH g hg)
    choose! z hzi hzx using hz
    refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
    · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
    · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_mul]
      linear_combination (-(g y₀)) * hzx g hg
