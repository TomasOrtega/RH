import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

open private UpperTheory.V.Af.Nf.liftHol from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf

namespace UpperTheory.V.Z.Kato.NewVec

open UpperTheory.V.Sd

/- English proof (translation)
Use `Submodule.disjoint_def.1 hd _ (hU _ hψ) ?_` and prove the remaining obligations. Use `W.neg_mem (hW _ hm)` as an intermediate fact. Rewrite `this` using `[map_sub, h0, zero_sub, neg_neg]`. Then use the resulting hypothesis.
-/
private theorem comp_zero {V : Type} [AddCommGroup V] [Module ℂ V] {U W : Submodule ℂ V} (hd : Disjoint U W) (T : Module.End ℂ V)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) {φ ψ : V} (hψ : ψ ∈ U) (hm : φ - ψ ∈ W) (h0 : T φ = 0) : T ψ = 0 := by
  refine Submodule.disjoint_def.1 hd _ (hU _ hψ) ?_
  have := W.neg_mem (hW _ hm)
  rwa [map_sub, h0, zero_sub, neg_neg] at this

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

/- English proof (translation)
Introduce `x hx` and use `hU (.lie _) x hx`.
-/
private theorem eop_mem {U : Submodule ℂ (TR.Sm ℚ 2)} (hU : TR.IsStable U) (v : InfinitePlace ℚ) (i j : Fin 2) :
    ∀ x ∈ U, TR.Eop v i j x ∈ U := fun x hx => hU (.lie _) x hx

/- English proof (translation)
Rewrite using `[TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]`. Use `congr 2`. Use extensionality with `i j w`. Take `rfl : w = v` from `Subsingleton.elim _ _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem eop_one (v : InfinitePlace ℚ) (φ : TR.Sm ℚ 2) :
    TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = TR.lie ℚ 2 (TR.oneL ℚ 2) φ := by
  classical
  rw [TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
  congr 2
  ext i j w
  obtain rfl : w = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Introduce `hS hA k hk2 f`. Establish `hM : 1 ≤ f.M` using `f.pos`. Establish `hk1 : 1 ≤ k` using `by omega`. Take `⟨ω, hω⟩` from `dirChar f.M hM f.χ`. Take `⟨hfin, hval⟩` from `charVal f.M hM f.χ ω hω`.

Take `⟨φ, hL, hH, hC⟩` from `UpperTheory.V.Af.Nf.liftHol k f.M hM f.χ ω hω f.f f.char`. Establish `hE` using `liftExp k f.M hM f.f φ.1 hL`. Take `⟨-, hz, hl1, hl2, -⟩` from `holLin ℚ k (lev f.M) ω`. Establish `h0 : φ ≠ 0`. Introduce and unpack `rfl`.

Use `(expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot` as an intermediate fact. Rewrite `this` using `[icoef, Ideal.absNorm_top, f.one]`. Conclude with `one_ne_zero this`. Take `⟨h1, -⟩` from `holCap ℚ k _ ω hfin φ hH`. Take `⟨π, ψ, W, hψ, hW, hd, hm⟩` from `split ℚ 2 φ h0 (hS ℚ 2 φ hC ⟨0, by rw [h1, zero_smul]⟩)`.

Establish `hπ : TR.IsStable π.V` using `π.stable`. Use `⟨π, ψ.1, ψ.2, fun e => hψ (Subtype.ext e), fun q u hu => ?_, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩, fun w hw => ?_⟩` and prove the remaining obligations. Establish `key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (locSm ℚ q u - 1 : Module.End ℂ _) x ∈ U` using `fun U hU x hx => U.sub_mem (hU (.fin (locGL ℚ 2 q u)) x hx) hx`. Conclude with `sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.level q u hu)))`. Establish `key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2))) x ∈ U` using `fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)) (U.smul_mem _ hx)`.

Conclude with `sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.wt v)))`. Establish `key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0)) x ∈ U` using `fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)) (U.smul_mem _ (U.add_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)))`. Conclude with `sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.low v)))`. Establish `key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (Eo v 0 0 + Eo v 1 1) x ∈ U` using `fun U hU x hx => U.add_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)`. Conclude with `comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm ((eop_one v φ).trans h1)`.

Establish `hc` using `(places w).2.2.2 f.M hM hw`. Take `⟨h1, -, h2⟩` from `holHk ℚ k hk1 _ ω hfin φ hH w`. Take `⟨c₀, h3⟩` from `h2 _ _ hE`. Establish `h4` using `expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE) fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]`. Rewrite `h4` using `[hc, neg_smul, add_neg_eq_zero]`.

Take `⟨α, β, hv, hsum, hprod⟩` from `satHol ℚ k _ ω φ hH h0 w _ hc h4`. Conclude with `⟨α, β, satOfVec hA ℚ 2 π w ψ _ (satComp ℚ φ π ψ W hψ hW hd hm w _ hv), hsum, by rw [hprod, hval w hw]⟩`.
-/
theorem newVec : Published.CuspSemisimpleReal → Published.AdmissibleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k), ∃ (π₀ : TR.CuspSub ℚ 2) (ψ : TR.Sm ℚ 2), ψ ∈ π₀.V ∧ ψ ≠ 0 ∧ (∀ q : HeightOneSpectrum (𝓞 ℚ), ψ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))) ∧ ((∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = (Complex.I * (k : ℂ)) • ψ) ∧ (∀ v, TR.Eop v 0 0 ψ - TR.Eop v 1 1 ψ = Complex.I • (TR.Eop v 0 1 ψ + TR.Eop v 1 0 ψ)) ∧ (∀ v, TR.Eop v 0 0 ψ + TR.Eop v 1 1 ψ = 0)) ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M) := by
  intro hS hA k hk2 f
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  obtain ⟨φ, hL, hH, hC⟩ := UpperTheory.V.Af.Nf.liftHol k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨h1, -⟩ := holCap ℚ k _ ω hfin φ hH
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split ℚ 2 φ h0 (hS ℚ 2 φ hC ⟨0, by rw [h1, zero_smul]⟩)
  have hπ : TR.IsStable π.V := π.stable
  refine ⟨π, ψ.1, ψ.2, fun e => hψ (Subtype.ext e), fun q u hu => ?_, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩, fun w hw => ?_⟩
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (locSm ℚ q u - 1 : Module.End ℂ _) x ∈ U :=
      fun U hU x hx => U.sub_mem (hU (.fin (locGL ℚ 2 q u)) x hx) hx
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.level q u hu)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2))) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)) (U.smul_mem _ hx)
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.wt v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0)) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx))
        (U.smul_mem _ (U.add_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)))
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.low v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 + Eo v 1 1) x ∈ U :=
      fun U hU x hx => U.add_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)
    exact comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm ((eop_one v φ).trans h1)
  · have hc := (places w).2.2.2 f.M hM hw
    obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
    obtain ⟨c₀, h3⟩ := h2 _ _ hE
    have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
      fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
    rw [hc, neg_smul, add_neg_eq_zero] at h4
    obtain ⟨α, β, hv, hsum, hprod⟩ := satHol ℚ k _ ω φ hH h0 w _ hc h4
    exact ⟨α, β, satOfVec hA ℚ 2 π w ψ _ (satComp ℚ φ π ψ W hψ hW hd hm w _ hv), hsum, by rw [hprod, hval w hw]⟩

end UpperTheory.V.Z.Kato.NewVec
