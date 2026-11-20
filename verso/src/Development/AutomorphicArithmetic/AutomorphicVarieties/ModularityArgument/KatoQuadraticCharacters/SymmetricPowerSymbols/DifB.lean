import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm u v P Q hP hQ`. Take `⟨-, -, l3, l4, -, l6, -⟩` from `lgB Ω ε X m hm`. Establish `K` using `kaB Ω ε X m hm`. Establish `hu` using `hP.hu`. Establish `hv` using `hP.hv`.

Establish `nz : ∀ (θ : Kb X) (w : X.K), w ≠ 0 → θ ^ m = io X w → θ ≠ 0`. Introduce and unpack `θ w hw h rfl`. Rewrite `h` using `[zero_pow hm.ne']`. Conclude with `hw ((map_eq_zero (io X)).1 h.symm)`. Establish `self0 : ∀ a : Kb X, a ≠ 0 → lg X m a a = 0` using `fun a ha => l3 a a 0 ha (by simp)`.

Use `⟨fun g h hg hh => ?_, ?_, ?_, fun R hR h hh => ?_, fun h hh => ?_, fun σ hσ h hh => ?_, fun τ s hτ σ hσ h hh => ?_⟩` and prove the remaining obligations. Establish `e1` using `hP.cob g h hg hh`. Establish `e2` using `hQ.cob g h hg hh`. Rewrite `e1` using `[(K Q.a u hu.1 hQ.ha).2.1 P.a hP.ha g hg, (K Q.b v hv.1 hQ.hb).2.1 P.b hP.hb h hh]`. Simplify using `only [dif]`.

Rewrite using `[(K Q.a u hu.1 hQ.ha).1 g h hg hh, (K Q.b v hv.1 hQ.hb).1 g h hg hh]`. Take the linear combination `e1 - e2`. Take `⟨B1, h1⟩` from `hP.lc`. Take `⟨B2, h2⟩` from `hQ.lc`. Take `⟨B3, h3⟩` from `(K Q.a u hu.1 hQ.ha).2.2.1`.

Take `⟨B4, h4⟩` from `(K Q.b v hv.1 hQ.hb).2.2.1`. Use `⟨B1 ∪ B2 ∪ B3 ∪ B4, fun h h' hh hh' hB => ?_⟩` and prove the remaining obligations. Simplify using `only [dif]`. Rewrite using `[h1 h h' hh hh' fun b hb => hB b (by simp [hb]), h2 h h' hh hh' fun b hb => hB b (by simp [hb]), h3 h h' hh hh' fun b hb => hB b (by simp [hb]), h4 h h' hh hh' fun b hb => hB b (by simp [hb])]`. Introduce `B h hB hh hi`.

Simplify using `only [dif]`. Rewrite using `[hP.unr B h hB hh hi, hQ.unr B h hB hh hi, (K Q.a u hu.1 hQ.ha).2.2.2.1 hu B h hB hh hi, (K Q.b v hv.1 hQ.hb).2.2.2.1 hv B h hB hh hi]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [dif]`. Rewrite using `[l4 P.a Q.a R.a (nz _ _ hu.1 hR.ha) (hP.ha.trans hQ.ha.symm) (hQ.ha.trans hR.ha.symm), l4 P.b Q.b R.b (nz _ _ hv.1 hR.hb) (hP.hb.trans hQ.hb.symm) (hQ.hb.trans hR.hb.symm), (K R.a u hu.1 hR.ha).2.1 Q.a hQ.ha h hh, (K R.b v hv.1 hR.hb).2.1 Q.b hQ.hb h hh]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [dif]`. Rewrite using `[self0 _ (nz _ _ hu.1 hP.ha), self0 _ (nz _ _ hv.1 hP.hb)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk : InD X (σ⁻¹ * h * σ)` using `fun f => by`.

Establish `: (σ⁻¹ * h * σ) (io X f) = σ.symm (h (σ (io X f)))` using `rfl`. Rewrite using `[this, hσ f, hh f, RingEquiv.symm_apply_eq, hσ f]`. Establish `hm' : σ * (σ⁻¹ * h * σ) = h * σ` using `by group`. Establish `e1` using `hP.cob σ _ hσ hk`. Establish `e2` using `hP.cob h σ hh hσ`.

Establish `e3` using `(K P.b v hv.1 hP.hb).1 σ _ hσ hk`. Establish `e4` using `(K P.b v hv.1 hP.hb).1 h σ hh hσ`. Rewrite `e1`, `e3` using `[hm']`. Establish `e5 : ka X m P.b (σ⁻¹ * h * σ) = ka X m P.b h` using `by linear_combination e4 - e3`. Rewrite `e1` using `[e5]`.

Express the relevant statement in the definitionally equal form `1 ^ 2 * P.η (σ⁻¹ * h * σ) - P.η h + ka X m P.a h * ka X m P.b σ - ka X m P.a σ * ka X m P.b h = 0`. Take the linear combination `e2 - e1`. Simplify using `only [dif, Pt.mv]`. Rewrite using `[((K Q.a u hu.1 hQ.ha).2.2.2.2.1 σ τ s hτ hσ h hh).2, ((K Q.b v hv.1 hQ.hb).2.2.2.2.1 σ τ s hτ hσ h hh).2, l6 σ τ s hτ hσ P.a Q.a (nz _ _ hu.1 hQ.ha) (hP.ha.trans hQ.ha.symm), l6 σ τ s hτ hσ P.b Q.b (nz _ _ hv.1 hQ.hb) (hP.hb.trans hQ.hb.symm)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Kato.Sym.difB :
    UpperTheory.V.Z.Kato.Sym.DifB := by
  classical
  intro Ω _ _ _ ε X m hm u v P Q hP hQ
  obtain ⟨-, -, l3, l4, -, l6, -⟩ := lgB Ω ε X m hm
  have K := kaB Ω ε X m hm
  have hu := hP.hu
  have hv := hP.hv
  have nz : ∀ (θ : Kb X) (w : X.K), w ≠ 0 → θ ^ m = io X w → θ ≠ 0 := by
    rintro θ w hw h rfl
    rw [zero_pow hm.ne'] at h
    exact hw ((map_eq_zero (io X)).1 h.symm)
  have self0 : ∀ a : Kb X, a ≠ 0 → lg X m a a = 0 := fun a ha => l3 a a 0 ha (by simp)
  refine ⟨fun g h hg hh => ?_, ?_, ?_, fun R hR h hh => ?_, fun h hh => ?_, fun σ hσ h hh => ?_,
    fun τ s hτ σ hσ h hh => ?_⟩
  · have e1 := hP.cob g h hg hh
    have e2 := hQ.cob g h hg hh
    rw [(K Q.a u hu.1 hQ.ha).2.1 P.a hP.ha g hg, (K Q.b v hv.1 hQ.hb).2.1 P.b hP.hb h hh] at e1
    simp only [dif]
    rw [(K Q.a u hu.1 hQ.ha).1 g h hg hh, (K Q.b v hv.1 hQ.hb).1 g h hg hh]
    linear_combination e1 - e2
  · obtain ⟨B1, h1⟩ := hP.lc
    obtain ⟨B2, h2⟩ := hQ.lc
    obtain ⟨B3, h3⟩ := (K Q.a u hu.1 hQ.ha).2.2.1
    obtain ⟨B4, h4⟩ := (K Q.b v hv.1 hQ.hb).2.2.1
    refine ⟨B1 ∪ B2 ∪ B3 ∪ B4, fun h h' hh hh' hB => ?_⟩
    simp only [dif]
    rw [h1 h h' hh hh' fun b hb => hB b (by simp [hb]), h2 h h' hh hh' fun b hb => hB b (by simp [hb]),
      h3 h h' hh hh' fun b hb => hB b (by simp [hb]), h4 h h' hh hh' fun b hb => hB b (by simp [hb])]
  · intro B h hB hh hi
    simp only [dif]
    rw [hP.unr B h hB hh hi, hQ.unr B h hB hh hi, (K Q.a u hu.1 hQ.ha).2.2.2.1 hu B h hB hh hi,
      (K Q.b v hv.1 hQ.hb).2.2.2.1 hv B h hB hh hi]
    ring
  · simp only [dif]
    rw [l4 P.a Q.a R.a (nz _ _ hu.1 hR.ha) (hP.ha.trans hQ.ha.symm) (hQ.ha.trans hR.ha.symm),
      l4 P.b Q.b R.b (nz _ _ hv.1 hR.hb) (hP.hb.trans hQ.hb.symm) (hQ.hb.trans hR.hb.symm),
      (K R.a u hu.1 hR.ha).2.1 Q.a hQ.ha h hh, (K R.b v hv.1 hR.hb).2.1 Q.b hQ.hb h hh]
    ring
  · simp only [dif]
    rw [self0 _ (nz _ _ hu.1 hP.ha), self0 _ (nz _ _ hv.1 hP.hb)]
    ring
  · have hk : InD X (σ⁻¹ * h * σ) := fun f => by
      have : (σ⁻¹ * h * σ) (io X f) = σ.symm (h (σ (io X f))) := rfl
      rw [this, hσ f, hh f, RingEquiv.symm_apply_eq, hσ f]
    have hm' : σ * (σ⁻¹ * h * σ) = h * σ := by group
    have e1 := hP.cob σ _ hσ hk
    have e2 := hP.cob h σ hh hσ
    have e3 := (K P.b v hv.1 hP.hb).1 σ _ hσ hk
    have e4 := (K P.b v hv.1 hP.hb).1 h σ hh hσ
    rw [hm'] at e1 e3
    have e5 : ka X m P.b (σ⁻¹ * h * σ) = ka X m P.b h := by linear_combination e4 - e3
    rw [e5] at e1
    change 1 ^ 2 * P.η (σ⁻¹ * h * σ) - P.η h + ka X m P.a h * ka X m P.b σ - ka X m P.a σ * ka X m P.b h = 0
    linear_combination e2 - e1
  · simp only [dif, Pt.mv]
    rw [((K Q.a u hu.1 hQ.ha).2.2.2.2.1 σ τ s hτ hσ h hh).2, ((K Q.b v hv.1 hQ.hb).2.2.2.2.1 σ τ s hτ hσ h hh).2,
      l6 σ τ s hτ hσ P.a Q.a (nz _ _ hu.1 hQ.ha) (hP.ha.trans hQ.ha.symm),
      l6 σ τ s hτ hσ P.b Q.b (nz _ _ hv.1 hQ.hb) (hP.hb.trans hQ.hb.symm)]
    ring
