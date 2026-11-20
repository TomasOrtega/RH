import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.CharAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalExpBoundHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp

noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨⟨h1, h2⟩, -⟩` from `polFacts k`. Take `⟨y, hy⟩` from `valuation_surjective (uniformizer k : ValueGroupWithZero k)`. Conclude with `le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))`.
-/
private theorem valuation_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))

/- English proof (translation)
Use `Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
private theorem resCard_pos : (0 : ℝ) < (resCard k : ℝ) := by
  have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
  exact_mod_cast this

/- English proof (translation)
Establish `hq` using `resCard_pos (k := k)`. Rewrite using `[val_absPow, GlobalTheory.GLDoubling.nabs_unif valuation_unif, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 hq), Complex.ofReal_re, Real.inv_rpow hq.le, Real.rpow_neg hq.le]`.
-/
private theorem norm_absPow_unif (r : ℝ) :
    ‖((absPow k (r : ℂ) (unif k) : ℂˣ) : ℂ)‖ = (resCard k : ℝ) ^ (-r) := by
  have hq := resCard_pos (k := k)
  rw [val_absPow, GlobalTheory.GLDoubling.nabs_unif valuation_unif,
    Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 hq), Complex.ofReal_re, Real.inv_rpow hq.le,
    Real.rpow_neg hq.le]

/- English proof (translation)
Establish `e : θ * (θ * absPow k 1)⁻¹ = (absPow k 1)⁻¹`. Rewrite using `[mul_inv, mul_inv_cancel_left]`. Rewrite using `[e]`. Use `⟨isUnram_inv (isUnram_absPow k 1), ?_⟩` and prove the remaining obligations. Establish `hq : (resCard k : ℂ) ≠ 0`.

Use `Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif valuation_unif]`. Use `push_cast`. Conclude with `inv_inv _`.
-/
private theorem linked (θ : kˣ →* ℂˣ) :
    IsUnram (θ * (θ * absPow k 1)⁻¹) ∧
      (((θ * (θ * absPow k 1)⁻¹) (unif k) : ℂˣ) : ℂ) = (resCard k : ℂ) := by
  have e : θ * (θ * absPow k 1)⁻¹ = (absPow k 1)⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  rw [e]
  refine ⟨isUnram_inv (isUnram_absPow k 1), ?_⟩
  have hq : (resCard k : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
    exact_mod_cast this.ne'
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, val_absPow, Complex.cpow_one,
    GlobalTheory.GLDoubling.nabs_unif valuation_unif]
  push_cast
  exact inv_inv _

/- English proof (translation)
Take `⟨h, δ, Δ, s, hL, hc, hb, hd, ⟨φ⟩⟩` from `PositivityTheory.JsR.localExpBound_holds k N V ρ hs hi hu hg`. Set `D : Fin h → Segment k` to `fun i => (Δ i).nu ((s i : ℝ) : ℂ)`. Establish `hL' : ∀ i, IsLSeg (D i) ((δ i).nu ((s i : ℝ) : ℂ)).rep` using `fun i => GlobalTheory.isLSeg_nu (hL i) _`. Establish `hG : GlobalTheory.Published.GeometricLemma` using `GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds`. Establish `hs2 : HasSupport ρ (∑ i, (D i).ms)` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL' i).hasSupport) hi (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`.

Establish `he` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 hS`. Take `⟨hξ0, hm⟩` from `hξ`. Take `⟨i, -, hi'⟩` from `Multiset.mem_sum.1 (he ▸ hm)`. Establish `hmem : ∀ a : ℕ, a < (D i).len → (D i).first.nu (a : ℂ) ∈ S` using `fun a ha => by`. Rewrite using `[← he]`.

Conclude with `Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨a, ha, rfl⟩)⟩`. Establish `hlen : (D i).len = 1`. Assume the negation of the conclusion as `hne`. Establish `h2 : 1 < (D i).len` using `by have := (D i).len_pos; omega`. Establish `h0` using `hmem 0 (D i).len_pos`.

Establish `h3` using `hmem 1 h2`. Rewrite `h0` using `[Nat.cast_zero, IrrGL.nu_zero]`. Rewrite `h3` using `[Nat.cast_one]`. Take `⟨θ, hθ, e⟩` from `GlobalTheory.RoadU.PlainChars.exists_eq_ofChar (D i).first (h1 _ h0)`. Rewrite `h0`, `h3` using `[e]`.

Establish `e2 : (IrrGL.ofChar θ hθ).nu 1 = IrrGL.ofChar (θ * absPow k 1) (hθ.mul (isSmoothChar_absPow _))` using `IrrGL.tw_ofChar _ _ _ _`. Rewrite `h3` using `[e2]`. Conclude with `hun θ ⟨hθ, h0⟩ _ ⟨_, h3⟩ (linked θ).1 (linked θ).2`. Rewrite `hi'` using `[GlobalTheory.SphUnr.ms_eq_singleton hlen, Multiset.mem_singleton]`. Establish `hμ : IsSmoothChar (ξ * absPow k ((-(s i) : ℝ) : ℂ))` using `hξ0.mul (isSmoothChar_absPow _)`.

Establish `hfirst : (Δ i).first = IrrGL.ofChar (ξ * absPow k ((-(s i) : ℝ) : ℂ)) hμ`. Rewrite using `[← IrrGL.tw_ofChar _ _ hξ0 (isSmoothChar_absPow _)]`. Express the relevant statement in the definitionally equal form `_ = (IrrGL.ofChar ξ hξ0).nu _`. Rewrite using `[hi']`. Express the relevant statement in the definitionally equal form `_ = ((Δ i).first.nu ((s i : ℝ) : ℂ)).nu _`.

Rewrite using `[IrrGL.nu_nu]`. Use `push_cast`. Simplify using the standard rewrite rules. Establish `hcc : HasCentralChar (Δ i).first.rep (ξ * absPow k ((-(s i) : ℝ) : ℂ))`. Rewrite using `[hfirst]`.

Conclude with `GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar _ hμ`. Establish `hcen` using `hc i _ hcc (unif k)`. Establish `hlen' : (Δ i).len = 1` using `hlen`. Rewrite `hcen` using `[hlen']`. Simplify using `only [Nat.cast_one, sub_self, mul_zero, zero_div, neg_zero, zero_mul] at hcen`.

Establish `hn0 : 0 < ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖` using `norm_pos_iff.2 (Units.ne_zero _)`. Establish `h4 : ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖ = 1`. Break down `Real.log_eq_zero.1 hcen with h | h | h` into its components or cases. Conclude with `absurd h hn0.ne'`. Conclude with `h`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h4` using `[MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_unif, neg_neg]`. Establish `hq` using `resCard_pos (k := k)`. Use `⟨s i, hb i, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_neg hq.le]`.

Conclude with `eq_inv_of_mul_eq_one_left h4`.
-/
private theorem exponent_of_unl [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (hu : IsUnitarisable ρ) (hg : IsGeneric ρ) (S : Multiset (IrrGL k)) (hS : HasSupport ρ S)
    (h1 : ∀ y ∈ S, y.1 = 1) (hun : Unl (resCard k) S) {ξ : kˣ →* ℂˣ} (hξ : ξ ∈ chars S) :
    ∃ e : ℝ, |e| < 1 / 2 ∧ ‖((ξ (unif k) : ℂˣ) : ℂ)‖ = (resCard k : ℝ) ^ (-e) := by
  obtain ⟨h, δ, Δ, s, hL, hc, hb, hd, ⟨φ⟩⟩ := PositivityTheory.JsR.localExpBound_holds k N V ρ hs hi hu hg
  let D : Fin h → Segment k := fun i => (Δ i).nu ((s i : ℝ) : ℂ)
  have hL' : ∀ i, IsLSeg (D i) ((δ i).nu ((s i : ℝ) : ℂ)).rep := fun i => GlobalTheory.isLSeg_nu (hL i) _
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport ρ (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL' i).hasSupport) hi
      (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 hS
  obtain ⟨hξ0, hm⟩ := hξ
  obtain ⟨i, -, hi'⟩ := Multiset.mem_sum.1 (he ▸ hm)
  have hmem : ∀ a : ℕ, a < (D i).len → (D i).first.nu (a : ℂ) ∈ S := fun a ha => by
    rw [← he]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨a, ha, rfl⟩)⟩
  have hlen : (D i).len = 1 := by
    by_contra hne
    have h2 : 1 < (D i).len := by have := (D i).len_pos; omega
    have h0 := hmem 0 (D i).len_pos
    have h3 := hmem 1 h2
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    rw [Nat.cast_one] at h3
    obtain ⟨θ, hθ, e⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar (D i).first (h1 _ h0)
    rw [e] at h0 h3
    have e2 : (IrrGL.ofChar θ hθ).nu 1 = IrrGL.ofChar (θ * absPow k 1) (hθ.mul (isSmoothChar_absPow _)) :=
      IrrGL.tw_ofChar _ _ _ _
    rw [e2] at h3
    exact hun θ ⟨hθ, h0⟩ _ ⟨_, h3⟩ (linked θ).1 (linked θ).2
  rw [GlobalTheory.SphUnr.ms_eq_singleton hlen, Multiset.mem_singleton] at hi'
  have hμ : IsSmoothChar (ξ * absPow k ((-(s i) : ℝ) : ℂ)) := hξ0.mul (isSmoothChar_absPow _)
  have hfirst : (Δ i).first = IrrGL.ofChar (ξ * absPow k ((-(s i) : ℝ) : ℂ)) hμ := by
    rw [← IrrGL.tw_ofChar _ _ hξ0 (isSmoothChar_absPow _)]
    change _ = (IrrGL.ofChar ξ hξ0).nu _
    rw [hi']
    change _ = ((Δ i).first.nu ((s i : ℝ) : ℂ)).nu _
    rw [IrrGL.nu_nu]
    push_cast
    simp
  have hcc : HasCentralChar (Δ i).first.rep (ξ * absPow k ((-(s i) : ℝ) : ℂ)) := by
    rw [hfirst]
    exact GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar _ hμ
  have hcen := hc i _ hcc (unif k)
  have hlen' : (Δ i).len = 1 := hlen
  rw [hlen'] at hcen
  simp only [Nat.cast_one, sub_self, mul_zero, zero_div, neg_zero, zero_mul] at hcen
  have hn0 : 0 < ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have h4 : ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖ = 1 := by
    rcases Real.log_eq_zero.1 hcen with h | h | h
    · exact absurd h hn0.ne'
    · exact h
    · linarith
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_unif, neg_neg] at h4
  have hq := resCard_pos (k := k)
  refine ⟨s i, hb i, ?_⟩
  rw [Real.rpow_neg hq.le]
  exact eq_inv_of_mul_eq_one_left h4

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

/- English proof (translation)
Introduce `K _ _ _ n hn π`. Take `⟨π₀, t, hu, he⟩` from `CG.exists_isUnitary_twist_absPow (CG.mk π) hn`. Take `⟨π₀, rfl⟩ : ∃ p : CuspSub K n, CG.mk p = π₀` from `⟨π₀.out, Quotient.out_eq π₀⟩`. Set `χ : Formalism.L2.Host.HChar K` to `GlobalTheory.HeckeGal.Model.absPow K (-t)`. Establish `hiso : CG.mk (π.twist χ) = CG.mk π₀`.

Establish `e1 : CG.mk (π.twist χ) = (CG.mk π).twist χ` using `rfl`. Rewrite using `[e1, he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]`. Establish `hU : (π.twist χ).IsUnitary` using `(CG.isUnitary_mk _).1 (hiso ▸ hu)`. Take `⟨a, ha⟩` from `charAbs K χ`. Use `⟨-a, fun v hT hL => ⟨hT, fun s hs ξ hξ => ?_⟩⟩` and prove the remaining obligations.

Use `haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm v` after adjusting the coercions. Establish `hres` using `GlobalTheory.LFun.SatBoundGL.resCard_completion v`. Take `⟨s', hs', -, hch, hfst⟩` from `suppTw K n hn π v χ s hs`.

Take `⟨σ, hσ, hsup⟩` from `hs'`. Establish `htor` using `((suppFacts K n hn π v).2.2.1 s hs).1.1 hT`. Establish `h1 : ∀ y ∈ s', y.1 = 1` using `fun y hy => by`. Take `⟨y₀, hy₀, e⟩` from `Multiset.mem_map.1 (hfst ▸ Multiset.mem_map_of_mem Sigma.fst hy)`. Rewrite using `[← e]`.

Conclude with `htor y₀ hy₀`. Establish `hun : Unl (resCard (v.adicCompletion K)) s'`. Rewrite using `[hres]`. Introduce `ζ hζ ζ' hζ'`. Take `⟨ξ₁, h₁, rfl⟩` from `(hch ζ).1 hζ`.

Take `⟨ξ₂, h₂, rfl⟩` from `(hch ζ').1 hζ'`. Establish `e : ξ₁ * χ.loc v * (ξ₂ * χ.loc v)⁻¹ = ξ₁ * ξ₂⁻¹`. Rewrite using `[mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]`. Rewrite using `[e]`. Conclude with `hL s hs ξ₁ h₁ ξ₂ h₂`.

Take `⟨e, he1, he2⟩` from `exponent_of_unl σ.ρ σ.smooth σ.irred (GlobalTheory.ResW.isUnitarisable_of_isLocComp_cusp K n _ hn hU v σ hσ) (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp K n _ v σ hσ) s' hsup h1 hun ((hch _).2 ⟨ξ, hξ, rfl⟩)`. Take `⟨-, hav⟩` from `ha v`. Rewrite `he2` using `[hres, MonoidHom.mul_apply, Units.val_mul, norm_mul, hav]`. Establish `hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)` using `by linarith`. Establish `hval : ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-a - e)`.

Rewrite using `[sub_eq_add_neg, Real.rpow_add hq0, ← he2, Real.rpow_neg hq0.le a]`. Clear the denominators using the available nonvanishing facts. Take `⟨hl, hr⟩` from `abs_lt.1 he1`. Rewrite using `[hval]`. Conclude with `⟨Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith), Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)⟩`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinOf := by
  intro K _ _ _ n hn π
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) hn
  obtain ⟨π₀, rfl⟩ : ∃ p : CuspSub K n, CG.mk p = π₀ := ⟨π₀.out, Quotient.out_eq π₀⟩
  let χ : Formalism.L2.Host.HChar K := GlobalTheory.HeckeGal.Model.absPow K (-t)
  have hiso : CG.mk (π.twist χ) = CG.mk π₀ := by
    have e1 : CG.mk (π.twist χ) = (CG.mk π).twist χ := rfl
    rw [e1, he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  have hU : (π.twist χ).IsUnitary := (CG.isUnitary_mk _).1 (hiso ▸ hu)
  obtain ⟨a, ha⟩ := charAbs K χ
  refine ⟨-a, fun v hT hL => ⟨hT, fun s hs ξ hξ => ?_⟩⟩
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hres := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨s', hs', -, hch, hfst⟩ := suppTw K n hn π v χ s hs
  obtain ⟨σ, hσ, hsup⟩ := hs'
  have htor := ((suppFacts K n hn π v).2.2.1 s hs).1.1 hT
  have h1 : ∀ y ∈ s', y.1 = 1 := fun y hy => by
    obtain ⟨y₀, hy₀, e⟩ := Multiset.mem_map.1 (hfst ▸ Multiset.mem_map_of_mem Sigma.fst hy)
    rw [← e]
    exact htor y₀ hy₀
  have hun : Unl (resCard (v.adicCompletion K)) s' := by
    rw [hres]
    intro ζ hζ ζ' hζ'
    obtain ⟨ξ₁, h₁, rfl⟩ := (hch ζ).1 hζ
    obtain ⟨ξ₂, h₂, rfl⟩ := (hch ζ').1 hζ'
    have e : ξ₁ * χ.loc v * (ξ₂ * χ.loc v)⁻¹ = ξ₁ * ξ₂⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rw [e]
    exact hL s hs ξ₁ h₁ ξ₂ h₂
  obtain ⟨e, he1, he2⟩ := exponent_of_unl σ.ρ σ.smooth σ.irred
    (GlobalTheory.ResW.isUnitarisable_of_isLocComp_cusp K n _ hn hU v σ hσ)
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp K n _ v σ hσ) s' hsup h1 hun
    ((hch _).2 ⟨ξ, hξ, rfl⟩)
  obtain ⟨-, hav⟩ := ha v
  rw [hres, MonoidHom.mul_apply, Units.val_mul, norm_mul, hav] at he2
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hval : ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-a - e) := by
    rw [sub_eq_add_neg, Real.rpow_add hq0, ← he2, Real.rpow_neg hq0.le a]
    field_simp
  obtain ⟨hl, hr⟩ := abs_lt.1 he1
  rw [hval]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith), Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)⟩
