import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hT hC hN hB`. Introduce `E Ω _ _ _ _ _ A v h g _ i hi Θ hΘ e y c hy hdz hreg htr rc hrc f hf hdiv t ϖ hϖ z hz`. Take `⟨a, ha, hL⟩` from `hrc`. Establish `hty` using `(UpperTheory.Zero.LLC.typeIff E Ω A v h rc).mp hL.type y`. Establish `hn : 0 < y.fst` using `Nat.pos_of_dvd_of_pos hdiv hf`.

Take `⟨D⟩` from `UpperTheory.Zero.LLC.extEx E Ω A v h g i hi y.fst hn`. Take `⟨⟨R, hR⟩, hsys⟩` from `UpperTheory.Zero.LLC.resEx E Ω A v h g i hi y.fst hn D`. Establish `hrank` using `(hsys R hR).rank`. Take `⟨ι, hι⟩` from `hT E Ω A v h g y.fst hn D R hR`. Take `⟨_, hcard, ⟨r⟩⟩` from `hB E v g i hi`.

Use `haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion E v] := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : g.Prime).ne_zero)`. Take `⟨θ, hθ, hreg', hnames⟩` from `hN g y.fst hn 𝓀[HeightOneSpectrum.adicCompletion E v] D.K (IsLocalRing.ResidueField A) hrank r e ι Θ hΘ c hreg`. Establish `hcls : GlobalTheory.LocLanglands.cls y.snd.rep = y`. Unfold `GlobalTheory.LocLanglands.cls`. Conclude with `IrrGL.of_rep y`.

Establish `hy' : (GlobalTheory.LocLanglands.cls y.snd.rep).IsCusp` using `by rw [hcls]; exact hy`. Establish `hdz' : UpperTheory.Zero.LLC.DZ (GlobalTheory.LocLanglands.cls y.snd.rep)` using `by rw [hcls]; exact hdz`. Take `⟨τ, hcusp, hinfl⟩` from `(UpperTheory.Zero.LLC.typeEx E Ω A v h g i hi y.fst hn y.snd.rep).1 hy' hdz'`. Establish `hchar` using `hC E v g i hi r y τ hcusp hinfl`. Establish `hnm` using `hnames τ (fun γ => (hchar γ).trans (htr γ))`.

Take `⟨_, hin⟩` from `hty g i hi y.fst hn D R hR θ hreg' τ hcusp hnm y.snd.rep hcls hinfl`. Rewrite using `[hin t]`. Use `set N := (g ^ f - 1) / (g ^ y.fst - 1) with hN'`. Establish `hdvd : g ^ y.fst - 1 ∣ g ^ f - 1`. Take `⟨m, hm⟩` from `hdiv`.

Rewrite using `[hm, pow_mul]`. Simplify `Nat.sub_dvd_pow_sub_pow (g ^ y.fst) 1 m` using `only [one_pow]`. Establish `hϖ' : (ϖ ^ N) ^ (g ^ y.fst - 1) = (g : Ω)`. Rewrite using `[← pow_mul, hN', Nat.div_mul_cancel hdvd, hϖ]`. Establish `hz' : ((z ^ N : A) : Ω) = (t : G E Ω) (ϖ ^ N) / ϖ ^ N`.

Rewrite using `[map_pow, ← div_pow, ← hz]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hιR : ι ((R t : D.Kˣ) : D.K) = (IsLocalRing.residue A z) ^ N`. Rewrite using `[hι t (ϖ ^ N) hϖ' (z ^ N) hz', map_pow]`.

Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `congr 2`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, hθ, hιR, map_pow, ← pow_mul, ← pow_mul]`. Put the polynomial expressions in normal form.
-/
theorem UpperTheory.Gal.InertialTypesAlt.cuspIne :
    TameRead → TypeChar → NameOf → BaseQ → CuspIne := by
  intro hT hC hN hB
  intro E Ω _ _ _ _ _ A v h g _ i hi Θ hΘ e y c hy hdz hreg htr rc hrc f hf hdiv t ϖ hϖ z hz
  obtain ⟨a, ha, hL⟩ := hrc
  have hty := (UpperTheory.Zero.LLC.typeIff E Ω A v h rc).mp hL.type y
  have hn : 0 < y.fst := Nat.pos_of_dvd_of_pos hdiv hf
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A v h g i hi y.fst hn
  obtain ⟨⟨R, hR⟩, hsys⟩ := UpperTheory.Zero.LLC.resEx E Ω A v h g i hi y.fst hn D
  have hrank := (hsys R hR).rank
  obtain ⟨ι, hι⟩ := hT E Ω A v h g y.fst hn D R hR
  obtain ⟨_, hcard, ⟨r⟩⟩ := hB E v g i hi
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion E v] :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : g.Prime).ne_zero)
  obtain ⟨θ, hθ, hreg', hnames⟩ :=
    hN g y.fst hn 𝓀[HeightOneSpectrum.adicCompletion E v] D.K (IsLocalRing.ResidueField A) hrank r e ι Θ hΘ c hreg
  have hcls : GlobalTheory.LocLanglands.cls y.snd.rep = y := by
    unfold GlobalTheory.LocLanglands.cls
    exact IrrGL.of_rep y
  have hy' : (GlobalTheory.LocLanglands.cls y.snd.rep).IsCusp := by rw [hcls]; exact hy
  have hdz' : UpperTheory.Zero.LLC.DZ (GlobalTheory.LocLanglands.cls y.snd.rep) := by rw [hcls]; exact hdz
  obtain ⟨τ, hcusp, hinfl⟩ :=
    (UpperTheory.Zero.LLC.typeEx E Ω A v h g i hi y.fst hn y.snd.rep).1 hy' hdz'
  have hchar := hC E v g i hi r y τ hcusp hinfl
  have hnm := hnames τ (fun γ => (hchar γ).trans (htr γ))
  obtain ⟨_, hin⟩ := hty g i hi y.fst hn D R hR θ hreg' τ hcusp hnm y.snd.rep hcls hinfl
  rw [hin t]
  set N := (g ^ f - 1) / (g ^ y.fst - 1) with hN'
  have hdvd : g ^ y.fst - 1 ∣ g ^ f - 1 := by
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, pow_mul]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (g ^ y.fst) 1 m
  have hϖ' : (ϖ ^ N) ^ (g ^ y.fst - 1) = (g : Ω) := by
    rw [← pow_mul, hN', Nat.div_mul_cancel hdvd, hϖ]
  have hz' : ((z ^ N : A) : Ω) = (t : G E Ω) (ϖ ^ N) / ϖ ^ N := by
    rw [map_pow, ← div_pow, ← hz]
    push_cast
    rfl
  have hιR : ι ((R t : D.Kˣ) : D.K) = (IsLocalRing.residue A z) ^ N := by
    rw [hι t (ϖ ^ N) hϖ' (z ^ N) hz', map_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 2
  rw [map_pow, Units.val_pow_eq_pow_val, hθ, hιR, map_pow, ← pow_mul, ← pow_mul]
  ring_nf
