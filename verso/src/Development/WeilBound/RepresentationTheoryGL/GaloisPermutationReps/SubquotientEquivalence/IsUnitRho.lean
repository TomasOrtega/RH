import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace DepthZeroEigenvalues

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨m, a, rfl, ha⟩` from `hi`. Take `⟨m', b, hb, hbt⟩` from `ht`. Establish `hba : b.Iso a` using `WD.mk_eq_mk.mp hb`. Conclude with `⟨m, a, rfl, ha, fun σ hσ => hba.ρ_eq_one (hbt σ hσ)⟩`.
-/
theorem exists_good {y : WD h} (hi : IsIrrWD y) (ht : IsTameWD y) :
    ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧ a.ρ.IsIrreducible ∧
      ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 := by
  obtain ⟨m, a, rfl, ha⟩ := hi
  obtain ⟨m', b, hb, hbt⟩ := ht
  have hba : b.Iso a := WD.mk_eq_mk.mp hb
  exact ⟨m, a, rfl, ha, fun σ hσ => hba.ρ_eq_one (hbt σ hσ)⟩

/- English proof (translation)
The claim follows from `(Group.isUnit σ).map a.ρ`.
-/
theorem isUnit_rho {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) : IsUnit (a.ρ σ) :=
  (Group.isUnit σ).map a.ρ

/- English proof (translation)
Rewrite using `[WD.eig_mk, Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]`.
-/
theorem eig_prod {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) :
    ((WD.mk a).eig σ).prod = LinearMap.det (a.ρ σ) := by
  rw [WD.eig_mk, Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]

/- English proof (translation)
The claim follows from `resCard_eq_normV w`.
-/
theorem card_res (w : HeightOneSpectrum (𝓞 E)) : Nat.card 𝓀[w.adicCompletion E] = normV w :=
  resCard_eq_normV w

end DepthZeroEigenvalues

open DepthZeroEigenvalues in
/- English proof (translation)
Introduce `h1a h1b h2 h3a E Ω _ _ _ _ _ A w h φ hφ n c hn`. Take `⟨γ, hγ1, hγ2⟩` from `h2 E Ω A w h φ hφ`. Establish `hq : Nat.card 𝓀[w.adicCompletion E] = normV w` using `card_res w`. Establish `: Finite 𝓀[w.adicCompletion E]` using `inferInstance`. Take `⟨lab, hlab1, hlab2⟩` from `h3a 𝓀[w.adicCompletion E] n hn`.

Use `set q := Nat.card 𝓀[w.adicCompletion E] with hqdef`. Set `Pz : WD h → ℂ → Prop` to `fun y z => ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧ a.ρ.IsIrreducible ∧ (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) ∧ Module.End.HasEigenvalue (a.ρ γ) z ∧ ExactPer q n z`. Establish `hex : ∀ y ∈ TameSet φ n c, ∃ z, Pz y z`. Introduce `y hy`. Take `⟨m, a, rfl, hai, hat⟩` from `exists_good hy.1 hy.2.1`.

Establish `hm : Module.finrank ℂ (Fin m → ℂ) = n`. Use `hy.2.2.1` as an intermediate fact. Rewrite `this` using `[WD.lpDim_mk]`. Then use the resulting hypothesis. Take `⟨hc, hirr⟩` from `hγ1 m a hat`. Take `⟨z, hz1, hz2⟩` from `h1a (Fin m → ℂ) (normV w) (a.ρ γ) (a.ρ φ) (isUnit_rho a γ) (isUnit_rho a φ) hc (hirr hai)`.

Use `⟨z, m, a, rfl, hai, hat, hz1, ?_⟩` and prove the remaining obligations. Rewrite `hz2` using `[hm]`. Rewrite using `[hq]`. Conclude with `hz2`. Set `zf : WD h → ℂ` to `fun y => Classical.epsilon (Pz y)`.

Establish `hzf : ∀ y ∈ TameSet φ n c, Pz y (zf y)` using `fun y hy => Classical.epsilon_spec (hex y hy)`. Use `⟨fun y => lab (zf y), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨_, _, _, _, _, _, hz⟩` from `hzf y hy`. Conclude with `hlab1 _ hz`.

Introduce `y hy y' hy' heq`. Take `⟨m, a, rfl, hai, hat, hz1, hz2⟩` from `hzf y hy`. Take `⟨m', a', rfl, hai', hat', hz1', hz2'⟩` from `hzf y' hy'`. Take `⟨i, hi⟩` from `hlab2 _ _ hz2 hz2' heq`. Establish `hm : Module.finrank ℂ (Fin m → ℂ) = n`.

Use `hy.2.2.1` as an intermediate fact. Rewrite `this` using `[WD.lpDim_mk]`. Then use the resulting hypothesis. Establish `hm' : Module.finrank ℂ (Fin m' → ℂ) = n`. Use `hy'.2.2.1` as an intermediate fact. Rewrite `this` using `[WD.lpDim_mk]`. Then use the resulting hypothesis.

Establish `hdet : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ)`. Rewrite using `[← eig_prod, ← eig_prod, hy.2.2.2, hy'.2.2.2]`. Take `⟨hc, -⟩` from `hγ1 m a hat`. Take `⟨hc', -⟩` from `hγ1 m' a' hat'`. Rewrite `hc`, `hc'` using `[← hq]`.

Take `⟨e, he1, he2⟩` from `h1b (Fin m → ℂ) (Fin m' → ℂ) q n i (a.ρ γ) (a.ρ φ) (a'.ρ γ) (a'.ρ φ) (zf (WD.mk a)) hn hm hm' (isUnit_rho a φ) (isUnit_rho a' φ) hc hc' hz2 hz1 (hi ▸ hz1') hdet`. Conclude with `WD.mk_eq_mk.mpr (hγ2 m m' a a' hat hat' hai hai' e he1 he2)`.
-/
theorem st3 : St1a → St1b → St2 → St3a → St3 := by
  intro h1a h1b h2 h3a E Ω _ _ _ _ _ A w h φ hφ n c hn
  obtain ⟨γ, hγ1, hγ2⟩ := h2 E Ω A w h φ hφ
  have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := card_res w
  have : Finite 𝓀[w.adicCompletion E] := inferInstance
  obtain ⟨lab, hlab1, hlab2⟩ := h3a 𝓀[w.adicCompletion E] n hn
  set q := Nat.card 𝓀[w.adicCompletion E] with hqdef

  let Pz : WD h → ℂ → Prop := fun y z => ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧
    a.ρ.IsIrreducible ∧ (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) ∧
    Module.End.HasEigenvalue (a.ρ γ) z ∧ ExactPer q n z
  have hex : ∀ y ∈ TameSet φ n c, ∃ z, Pz y z := by
    intro y hy
    obtain ⟨m, a, rfl, hai, hat⟩ := exists_good hy.1 hy.2.1
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    obtain ⟨hc, hirr⟩ := hγ1 m a hat
    obtain ⟨z, hz1, hz2⟩ := h1a (Fin m → ℂ) (normV w) (a.ρ γ) (a.ρ φ) (isUnit_rho a γ)
      (isUnit_rho a φ) hc (hirr hai)
    refine ⟨z, m, a, rfl, hai, hat, hz1, ?_⟩
    rw [hm] at hz2
    rw [hq]; exact hz2
  let zf : WD h → ℂ := fun y => Classical.epsilon (Pz y)
  have hzf : ∀ y ∈ TameSet φ n c, Pz y (zf y) := fun y hy => Classical.epsilon_spec (hex y hy)
  refine ⟨fun y => lab (zf y), ?_, ?_⟩
  · intro y hy
    obtain ⟨_, _, _, _, _, _, hz⟩ := hzf y hy
    exact hlab1 _ hz
  · intro y hy y' hy' heq
    obtain ⟨m, a, rfl, hai, hat, hz1, hz2⟩ := hzf y hy
    obtain ⟨m', a', rfl, hai', hat', hz1', hz2'⟩ := hzf y' hy'
    obtain ⟨i, hi⟩ := hlab2 _ _ hz2 hz2' heq
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    have hm' : Module.finrank ℂ (Fin m' → ℂ) = n := by
      have := hy'.2.2.1
      rwa [WD.lpDim_mk] at this
    have hdet : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← eig_prod, ← eig_prod, hy.2.2.2, hy'.2.2.2]
    obtain ⟨hc, -⟩ := hγ1 m a hat
    obtain ⟨hc', -⟩ := hγ1 m' a' hat'
    rw [← hq] at hc hc'
    obtain ⟨e, he1, he2⟩ := h1b (Fin m → ℂ) (Fin m' → ℂ) q n i (a.ρ γ) (a.ρ φ) (a'.ρ γ) (a'.ρ φ)
      (zf (WD.mk a)) hn hm hm' (isUnit_rho a φ) (isUnit_rho a' φ) hc hc' hz2 hz1 (hi ▸ hz1') hdet
    exact WD.mk_eq_mk.mpr (hγ2 m m' a a' hat hat' hai hai' e he1 he2)

end PositivityTheory.Rg.DzCount
