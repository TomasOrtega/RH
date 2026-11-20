import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiRes

/- English proof (translation)
Introduce `D s φ _hφ hker hres χ c hc`. Take `⟨e, hec, -, hei⟩` from `GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s`. Establish `htame : χ.TameAt s.w` using `GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D χ s.w c hc`. Set `ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ` to `(χ.loc s.w).comp (Units.map e.toRingHom.toMonoidHom)`. Establish `hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1`.

Rewrite using `[← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)`. Establish `h1 : ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1`. Introduce `u hu`. Establish `hu' : Valued.v (e u - 1) < 1`. Use `(GlobalTheory.TypeBlockFix.v_map_lt_one_iff _ _ e hec _).2 hu` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Use `htame (Units.map e.toRingHom.toMonoidHom u) ?_ ?_` and prove the remaining obligations. Use `show Valued.v (e u) = 1`. Use `Valuation.map_one_add_of_lt _ hu'` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Use `show Valued.v (e u - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Break down `eq_or_ne (Valued.v (e u - 1)) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `hu'` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[← WithZero.exp_log h0, WithZero.exp_le_exp]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ k : D.host.Eˣ, ξ (Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k) = χ.locK s.w k`. Introduce `k`.

Use `show χ.loc s.w _ = χ.loc s.w _`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hei k`. Use `⟨ξ, ⟨⟨1, fun u hu => h1 u (lt_of_le_of_lt hu hlt)⟩, h2⟩, ?_⟩` and prove the remaining obligations.

Introduce `u x w hxu hxw`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (w : kP s.w)`. Take `⟨hai, hφa⟩` from `hres a`. Use `haveI : s.w.asIdeal.IsMaximal := s.w.isMaximal`. Use `haveI : Nontrivial (kP s.w) := Ideal.Quotient.nontrivial_iff.2 s.w.isPrime.ne_top`.

Establish `hw0 : (w : kP s.w) ≠ 0` using `w.ne_zero`. Establish `hva : Valued.v (s.i (a : D.host.E)) = 1`. Use `le_antisymm hai (not_lt.1 fun h => hw0 ?_)` and prove the remaining obligations. Rewrite using `[← ha, ← hφa]`. Conclude with `(hker ⟨_, hai⟩).2 h`.

Establish `ha0 : (a : D.host.E) ≠ 0`. Introduce `h0`. Rewrite `hva` using `[h0, map_zero, map_zero]`. Conclude with `zero_ne_one hva`. Establish `hdiff : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1`.

Use `(hker (x - ⟨_, hai⟩)).1 (by rw [map_sub, hxw, hφa, ha, sub_self])` as an intermediate fact. Rewrite using `[← hxu]`. Conclude with `this`. Set `ka : D.host.Eˣ` to `Units.mk0 _ ha0`. Set `ua` to `Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) ka`.

Establish `hua : (ua : s.v.adicCompletion (maximalRealSubfield D.host.E)) = s.i (a : D.host.E)` using `rfl`. Establish `h3 : ξ (u * ua⁻¹) = 1`. Apply `h1` to reduce the goal to its premises. Establish `: ((u * ua⁻¹ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1 = ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - ua) * (ua : s.v.adicCompletion (maximalRealSubfield D.host.E))⁻¹`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ ua.ne_zero]`.

Rewrite using `[this, map_mul, map_inv₀, hua, hva, inv_one, mul_one]`. Conclude with `hdiff`. Establish `h4 : c w = χ.locK s.w ka` using `hc a ka w rfl ha.symm`. Rewrite `h3` using `[map_mul, map_inv, mul_inv_eq_one]`. Rewrite using `[h3, h4]`.

Conclude with `h2 ka`.
-/
theorem exists_isCompAt_res : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) → ∀ (χ : HChar D.host.E) (c : (kP s.w)ˣ →* ℂˣ), IsRes χ s.w c → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = c w := by
  intro D s φ _hφ hker hres χ c hc
  obtain ⟨e, hec, -, hei⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have htame : χ.TameAt s.w := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D χ s.w c hc
  let ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ :=
    (χ.loc s.w).comp (Units.map e.toRingHom.toMonoidHom)
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)

  have h1 : ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1 := by
    intro u hu
    have hu' : Valued.v (e u - 1) < 1 := by
      have := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff _ _ e hec _).2 hu
      rwa [map_sub, map_one] at this
    refine htame (Units.map e.toRingHom.toMonoidHom u) ?_ ?_
    · show Valued.v (e u) = 1
      have := Valuation.map_one_add_of_lt _ hu'
      rwa [add_sub_cancel] at this
    · show Valued.v (e u - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))
      rcases eq_or_ne (Valued.v (e u - 1)) 0 with h0 | h0
      · rw [h0]; exact zero_le'
      · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hu'
        rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
        push_cast; omega
  have h2 : ∀ k : D.host.Eˣ, ξ (Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k) =
      χ.locK s.w k := by
    intro k
    show χ.loc s.w _ = χ.loc s.w _
    congr 1
    apply Units.ext
    exact hei k
  refine ⟨ξ, ⟨⟨1, fun u hu => h1 u (lt_of_le_of_lt hu hlt)⟩, h2⟩, ?_⟩
  intro u x w hxu hxw
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (w : kP s.w)
  obtain ⟨hai, hφa⟩ := hres a
  haveI : s.w.asIdeal.IsMaximal := s.w.isMaximal
  haveI : Nontrivial (kP s.w) := Ideal.Quotient.nontrivial_iff.2 s.w.isPrime.ne_top
  have hw0 : (w : kP s.w) ≠ 0 := w.ne_zero
  have hva : Valued.v (s.i (a : D.host.E)) = 1 := by
    refine le_antisymm hai (not_lt.1 fun h => hw0 ?_)
    rw [← ha, ← hφa]; exact (hker ⟨_, hai⟩).2 h
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero, map_zero] at hva; exact zero_ne_one hva
  have hdiff : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
    have := (hker (x - ⟨_, hai⟩)).1 (by rw [map_sub, hxw, hφa, ha, sub_self])
    rw [← hxu]; exact this
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ua := Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) ka
  have hua : (ua : s.v.adicCompletion (maximalRealSubfield D.host.E)) = s.i (a : D.host.E) := rfl
  have h3 : ξ (u * ua⁻¹) = 1 := by
    apply h1
    have : ((u * ua⁻¹ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1 =
        ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - ua) * (ua : s.v.adicCompletion (maximalRealSubfield D.host.E))⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ ua.ne_zero]
    rw [this, map_mul, map_inv₀, hua, hva, inv_one, mul_one]
    exact hdiff
  have h4 : c w = χ.locK s.w ka := hc a ka w rfl ha.symm
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  rw [h3, h4]
  exact h2 ka

end GlobalTheory.XiRes
