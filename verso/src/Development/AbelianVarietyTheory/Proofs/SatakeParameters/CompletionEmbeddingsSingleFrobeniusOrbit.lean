import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroupStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocalFrobeniusOrbit

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]`. Both sides reduce to the same expression.
-/
theorem norm_algHom_eq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

/- English proof (translation)
Set `Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l)` to `fun g => c.toRatAlgHom.comp g.toAlgHom`. Establish `hinj : Function.Injective Φ`. Introduce `g h hgh`. Use extensionality with `x`. Use `congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh` as an intermediate fact.

Conclude with `c.injective this`. Establish `hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E)`. Rewrite using `[Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]`. Establish `hbij` using `hinj.bijective_of_nat_card_le hcard`. Take `⟨g, hg⟩` from `hbij.2 ρ.toRatAlgHom`.

Conclude with `⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩`.
-/
theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} [Fact l.Prime]
    (c ρ : E →+* PadicAlgCl l) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ρ x = c (g x) := by
  let Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l) := fun g => c.toRatAlgHom.comp g.toAlgHom
  have hinj : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh
    exact c.injective this
  have hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := hbij.2 ρ.toRatAlgHom
  exact ⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩

/- English proof (translation)
Introduce `R H l _ h2 hq hd c K hc hcl P _ _ s hs`. Use `haveI hG : IsGalois ℚ H.E := H.hostE_isGalois`. Establish `hN0 : ¬ l ∣ H.condN`. Rewrite using `[H.dvd_condN_iff_small Fact.out]`. The claim follows by propositional logic.

Establish `hF` using `H.der.frob l hN0`. Establish `hco : Nat.Coprime l H.condN` using `(Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0`. Take `⟨v, hvl, hv⟩` from `GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l H.E c`. Establish `hp : l.Prime` using `Fact.out`. Establish `hpz : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hp`.

Use `haveI := v.isPrime`. Use `haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)`. Establish `hsv : IsArithFrobAt ℤ s v.asIdeal` using `(H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)`. Establish `hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s`. Use `le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)` and prove the remaining obligations.

Take `⟨k, ρ, hρ, rfl⟩` from `Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ`. Rewrite using `[((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]`. Conclude with `Subgroup.npow_mem_zpowers s k`. Establish `hord : orderOf s = orderOf (H.galE s)` using `(H.gal.orderOf_eq s).symm`. Use `set N := orderOf (H.galE s) with hN`.

Establish `hNpos : 0 < N` using `hord ▸ orderOf_pos s`. Use `haveI : NeZero N := ⟨hNpos.ne'⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c)` using `GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' l H.E c K.1 hc K.2 hcl`. Establish `hdeg` using `GlobalTheory.T.finrank_local_field_eq_card_decomposition_group l H.E c v hv`.

Rewrite using `[← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]`. Introduce `τ`. Set `ρ : H.E →+* PadicAlgCl l` to `(τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)`. Take `⟨g, hg⟩` from `exists_aut_comp c ρ`. Establish `hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩` using `fun x => rfl`.

Establish `hgs : g ∈ Subgroup.zpowers s`. Rewrite using `[← hstab]`. Use `Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)` and prove the remaining obligations. Rewrite using `[hv, hv]`. Establish `h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩`.

Rewrite using `[← hρx, hg]`. Both sides reduce to the same expression. Rewrite using `[h1, norm_algHom_eq]`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 hgs`. Establish `hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ))` using `fun j => (zpow_natCast s j.val).symm`.

Use `⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]`. Establish `hgj : g = s ^ j.val`. Use `AlgEquiv.ext fun x => c.injective ?_` and prove the remaining obligations. Rewrite using `[← hg, hρx, hj]`.

Apply `ZMod.val_injective` to reduce the goal to its premises. Establish `h3 : s ^ j.val = s ^ (k : ZMod N).val`. Rewrite using `[← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]`. Establish `h4` using `pow_inj_mod.1 h3`. Rewrite `h4` using `[hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)]`.

Conclude with `h4`.
-/
theorem embeddings_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  intro R H l _ h2 hq hd c K hc hcl P _ _ s hs
  haveI hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hN0 : ¬ l ∣ H.condN := by
    rw [H.dvd_condN_iff_small Fact.out]; tauto
  have hF := H.der.frob l hN0
  have hco : Nat.Coprime l H.condN := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l H.E c
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI := v.isPrime
  haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)
  have hsv : IsArithFrobAt ℤ s v.asIdeal := (H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)
  have hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ
    rw [((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]
    exact Subgroup.npow_mem_zpowers s k
  have hord : orderOf s = orderOf (H.galE s) :=
    (H.gal.orderOf_eq s).symm
  set N := orderOf (H.galE s) with hN
  have hNpos : 0 < N := hord ▸ orderOf_pos s
  haveI : NeZero N := ⟨hNpos.ne'⟩
  refine ⟨?_, ?_⟩
  · have hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c) := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' l H.E c K.1 hc K.2 hcl
    have hdeg := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group l H.E c v hv
    rw [← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]
  · intro τ
    let ρ : H.E →+* PadicAlgCl l := (τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)
    obtain ⟨g, hg⟩ := exists_aut_comp c ρ
    have hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩ := fun x => rfl
    have hgs : g ∈ Subgroup.zpowers s := by
      rw [← hstab]
      refine Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)
      rw [hv, hv]
      have h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩ := by
        rw [← hρx, hg]; rfl
      rw [h1, norm_algHom_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgs
    have hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ)) := fun j => (zpow_natCast s j.val).symm
    refine ⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩
    · rw [← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
    · have hgj : g = s ^ j.val := by
        refine AlgEquiv.ext fun x => c.injective ?_
        rw [← hg, hρx, hj]
      apply ZMod.val_injective
      have h3 : s ^ j.val = s ^ (k : ZMod N).val := by
        rw [← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
      have h4 := pow_inj_mod.1 h3
      rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h4
      exact h4

end GlobalTheory.LocalFrobeniusOrbit
