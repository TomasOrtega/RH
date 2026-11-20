import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzTame

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]`. Conclude with `ne_of_lt h`.
-/
private theorem resS_eq_resS_of_mul_sub_eq_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y₁ y₂ : 𝒪[k]) (h : valuation k ((y₁ : k) - y₂) < 1) :
    IsLocalRing.residue 𝒪[k] y₁ = IsLocalRing.residue 𝒪[k] y₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ne_of_lt h

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Conclude with `h`.
-/
private theorem residue_eq_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z₁ z₂ : A)
    (h : A.valuation ((z₁ : Ω) - z₂) < 1) :
    IsLocalRing.residue A z₁ = IsLocalRing.residue A z₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

/- English proof (translation)
Unfold `ArtRead`. Introduce `E Ω _ _ _ _ _ A v h g _ hg1 hg2 a ha e he t ϖ hϖ`. Unfold `ResEmb at he`. Establish `hp : Nat.Prime g` using `Fact.out`. Establish `hEq : (valuation (HeightOneSpectrum.adicCompletion E v)).IsEquiv Valued.v` using `ValuativeRel.isEquiv _ _`.

Establish `hα : Valued.v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) = 1` using `DiscreteGroups.sglob.DzType.val_artin_ine ha t`. Take `⟨u, hu⟩` from `valuation_eq_one_iff.1 (hEq.eq_one_iff_eq_one.2 hα)`. Establish `hg0 : (g : Ω) ≠ 0`. Rewrite using `[← map_natCast (algebraMap E Ω)]`. Conclude with `(_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)`.

Establish `hg1' : (g : Ω) ≠ 1`. Rewrite using `[← map_natCast (algebraMap E Ω), ← map_one (algebraMap E Ω)]`. Introduce `hc`. Use `(algebraMap E Ω).injective hc` as an intermediate fact. Conclude with `hp.one_lt.ne' (by exact_mod_cast this)`.

Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Break down `Nat.eq_zero_or_pos (normV v - 1) with hm | hm` into its components or cases. Rewrite `hϖ` using `[hm, pow_zero]`. Conclude with `hg1' hϖ.symm`.

Rewrite `hϖ` using `[zero_pow hm.ne']`. Conclude with `hg0 hϖ.symm`. Establish `hz : A.valuation ((t : G E Ω) ϖ / ϖ) = 1` using `DiscreteGroups.sglob.DzType.val_ratio (Ine_le_Dec A t.2) hϖ0`. Take `⟨z, hzdef⟩ : ∃ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ` from `⟨⟨_, (A.valuation_le_one_iff _).1 hz.le⟩, rfl⟩`. Take `⟨x, hx⟩` from `DiscreteGroups.sglob.DzType.exists_int_approx_compl v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) hα.le`.

Establish `hx2` using `UpperTheory.Zero.LLC.tameRecAll E Ω g A v h hg1 hg2 a ha ϖ hϖ t x hx`. Use `⟨z, u, hzdef, hu, ?_, ?_⟩` and prove the remaining obligations. Establish `hxA : algebraMap E Ω x ∈ A`. Establish `h1 : ((t : G E Ω) ϖ / ϖ - algebraMap E Ω x) ∈ A` using `(A.valuation_le_one_iff _).1 hx2.le`. Establish `h2` using `A.sub_mem z.2 h1`.

Rewrite `h2` using `[hzdef, sub_sub_cancel]`. Conclude with `h2`. Establish `hyK : valuation (HeightOneSpectrum.adicCompletion E v) (algebraMap E (HeightOneSpectrum.adicCompletion E v) x) ≤ 1` using `hEq.le_one_iff_le_one.2 (DiscreteGroups.sglob.DzType.val_alg_le_one x)`. Set `y : 𝒪[HeightOneSpectrum.adicCompletion E v]` to `⟨_, hyK⟩`. Set `zx : A` to `⟨_, hxA⟩`.

Establish `hu' : (((u : 𝒪[HeightOneSpectrum.adicCompletion E v])) : HeightOneSpectrum.adicCompletion E v) = (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v)` using `congrArg Units.val hu`. Establish `h1 : IsLocalRing.residue _ (u : 𝒪[HeightOneSpectrum.adicCompletion E v]) = IsLocalRing.residue _ y`. Apply `resS_eq_resS_of_mul_sub_eq_mul` to reduce the goal to its premises. Use `show valuation (HeightOneSpectrum.adicCompletion E v) (((u : 𝒪[HeightOneSpectrum.adicCompletion E v]) : HeightOneSpectrum.adicCompletion E v) - algebraMap E (HeightOneSpectrum.adicCompletion E v) x) < 1`. Rewrite using `[hu']`.

Conclude with `hEq.lt_one_iff_lt_one.2 hx`. Establish `h2 : IsLocalRing.residue A z = IsLocalRing.residue A zx`. Apply `residue_eq_of_valuation_sub_lt_one` to reduce the goal to its premises. Use `show A.valuation ((z : Ω) - algebraMap E Ω x) < 1`. Rewrite using `[hzdef]`.

Conclude with `hx2`. Rewrite using `[h2, ← he x y zx rfl rfl, ← h1]`. Both sides reduce to the same expression. Establish `hzm : z ^ (normV v - 1) = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[SubmonoidClass.coe_pow, hzdef, div_pow, ← map_pow, hϖ, map_natCast, div_self hg0]`. Both sides reduce to the same expression. Rewrite using `[← map_pow, hzm, map_one]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.artRead :
    ArtRead := by
  unfold ArtRead
  intro E Ω _ _ _ _ _ A v h g _ hg1 hg2 a ha e he t ϖ hϖ
  unfold ResEmb at he
  have hp : Nat.Prime g := Fact.out
  have hEq : (valuation (HeightOneSpectrum.adicCompletion E v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have hα : Valued.v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) = 1 :=
    DiscreteGroups.sglob.DzType.val_artin_ine ha t
  obtain ⟨u, hu⟩ := valuation_eq_one_iff.1 (hEq.eq_one_iff_eq_one.2 hα)
  have hg0 : (g : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hg1' : (g : Ω) ≠ 1 := by
    rw [← map_natCast (algebraMap E Ω), ← map_one (algebraMap E Ω)]
    intro hc
    have := (algebraMap E Ω).injective hc
    exact hp.one_lt.ne' (by exact_mod_cast this)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos (normV v - 1) with hm | hm
    · rw [hm, pow_zero] at hϖ
      exact hg1' hϖ.symm
    · rw [zero_pow hm.ne'] at hϖ
      exact hg0 hϖ.symm
  have hz : A.valuation ((t : G E Ω) ϖ / ϖ) = 1 := DiscreteGroups.sglob.DzType.val_ratio (Ine_le_Dec A t.2) hϖ0
  obtain ⟨z, hzdef⟩ : ∃ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ :=
    ⟨⟨_, (A.valuation_le_one_iff _).1 hz.le⟩, rfl⟩
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v
    (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) hα.le
  have hx2 := UpperTheory.Zero.LLC.tameRecAll E Ω g A v h hg1 hg2 a ha ϖ hϖ t x hx
  refine ⟨z, u, hzdef, hu, ?_, ?_⟩
  · have hxA : algebraMap E Ω x ∈ A := by
      have h1 : ((t : G E Ω) ϖ / ϖ - algebraMap E Ω x) ∈ A := (A.valuation_le_one_iff _).1 hx2.le
      have h2 := A.sub_mem z.2 h1
      rw [hzdef, sub_sub_cancel] at h2
      exact h2
    have hyK : valuation (HeightOneSpectrum.adicCompletion E v)
        (algebraMap E (HeightOneSpectrum.adicCompletion E v) x) ≤ 1 :=
      hEq.le_one_iff_le_one.2 (DiscreteGroups.sglob.DzType.val_alg_le_one x)
    let y : 𝒪[HeightOneSpectrum.adicCompletion E v] := ⟨_, hyK⟩
    let zx : A := ⟨_, hxA⟩
    have hu' : (((u : 𝒪[HeightOneSpectrum.adicCompletion E v])) : HeightOneSpectrum.adicCompletion E v) =
        (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) := congrArg Units.val hu
    have h1 : IsLocalRing.residue _ (u : 𝒪[HeightOneSpectrum.adicCompletion E v]) = IsLocalRing.residue _ y := by
      apply resS_eq_resS_of_mul_sub_eq_mul
      show valuation (HeightOneSpectrum.adicCompletion E v)
        (((u : 𝒪[HeightOneSpectrum.adicCompletion E v]) : HeightOneSpectrum.adicCompletion E v) -
          algebraMap E (HeightOneSpectrum.adicCompletion E v) x) < 1
      rw [hu']
      exact hEq.lt_one_iff_lt_one.2 hx
    have h2 : IsLocalRing.residue A z = IsLocalRing.residue A zx := by
      apply residue_eq_of_valuation_sub_lt_one
      show A.valuation ((z : Ω) - algebraMap E Ω x) < 1
      rw [hzdef]
      exact hx2
    rw [h2, ← he x y zx rfl rfl, ← h1]
    rfl
  · have hzm : z ^ (normV v - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hzdef, div_pow, ← map_pow, hϖ, map_natCast, div_self hg0]
      rfl
    rw [← map_pow, hzm, map_one]
