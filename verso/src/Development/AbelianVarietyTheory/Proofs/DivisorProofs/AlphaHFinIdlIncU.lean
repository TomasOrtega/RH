import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.LocalToGlobal.UnitaryNorms.CharShare

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl finIdl_incU)

noncomputable section

namespace GlobalTheory.BottomReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Establish `h1` using `(L.xiH t).2.2 a`. Rewrite `h1` using `[← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU]`. Establish `h2` using `HChar.inf_eq_one_of_order hn ho a`. Rewrite `h2` using `[HChar.inf, MonoidHom.comp_apply]`.

Rewrite `h1` using `[h2, one_mul]`. Conclude with `h1`.
-/
theorem xiH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t : T) (a : D.host.Eˣ) :
    (L.xiH t).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) = 1 := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 := (L.xiH t).2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
  have h2 := HChar.inf_eq_one_of_order hn ho a
  rw [HChar.inf, MonoidHom.comp_apply] at h2
  rw [h2, one_mul] at h1
  exact h1

/- English proof (translation)
Simplify using `only [nuH, Subgroup.coe_div, Subgroup.coe_mul, MonoidHom.div_apply, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]`.
-/
theorem nuH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (nuH G t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (nuH G t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [nuH, Subgroup.coe_div, Subgroup.coe_mul, MonoidHom.div_apply, MonoidHom.mul_apply,
    xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

/- English proof (translation)
Use `set u := Units.mk0 a ha`. Use `set φ := Formalism.L2.Host.embTau D`. Establish `hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) * ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1` using `χ.aut u`. Establish `hB` using `congrArg (fun z : ℂˣ => (z : ℂ)) (hf (GlobalTheory.NormSum.UnramHecke.incU D u))`. Simplify using `only [Units.val_zpow_eq_zpow_val] at hB`.

Establish `hB' : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = (((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D u))) : ℂˣ) : ℂ)⁻¹`. Rewrite using `[← Units.val_inv_eq_inv_val]`. Conclude with `hB`. Establish `hX : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹` using `eq_inv_of_mul_eq_one_left hA`. Rewrite `hB'` using `[hX, inv_zpow', ← Finset.prod_zpow]`.

Repeatedly rewrite using `[mul_comm e, zpow_mul]`. Use `congrArg (·⁻¹) hB'` as an intermediate fact. Simplify using `only [inv_inv] at this`. Rewrite using `[← this, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_neg, neg_neg]`.
-/
theorem prod_pow_eq {N : ℕ} (χ : HeckeU D N) (e : ℤ) (ν : HChar D.host.E) (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x))
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ) =
      ((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D (Units.mk0 a ha))) : ℂˣ) : ℂ) := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := congrArg (fun z : ℂˣ => (z : ℂ)) (hf (GlobalTheory.NormSum.UnramHecke.incU D u))
  simp only [Units.val_zpow_eq_zpow_val] at hB
  have hB' : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e =
      (((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D u))) : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact hB
  have hX : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hA
  rw [hX, inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [mul_comm e, zpow_mul]
  have := congrArg (·⁻¹) hB'
  simp only [inv_inv] at this
  rw [← this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_neg, neg_neg]

/- English proof (translation)
Simplify using `only [alphaH, Subgroup.coe_mul, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]`.
-/
theorem alphaH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (alphaH L t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (alphaH L t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [alphaH, Subgroup.coe_mul, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

/- English proof (translation)
Establish `hc` using `GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D) (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e₁ * χ₁.n τ) (fun a ha => by`. Establish `hne : ∀ τ, Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ) ≠ 0` using `fun τ => div_ne_zero (by simpa using ha) (by exact_mod_cast norm_ne_zero_iff.2 (by simpa using ha))`. Repeatedly rewrite using `[zpow_sub₀ (hne _), Finset.prod_div_distrib, prod_pow_eq χ e _ hf a ha, prod_pow_eq χ₁ e₁ _ hf₁ a ha, hν]`. Conclude with `div_self (Units.ne_zero _))`. Establish `h` using `congrFun hc τ`.

Simplify `h` using `[sub_eq_zero]`.
-/
theorem exps_eq_of {N N₁ : ℕ} (χ : HeckeU D N) (χ₁ : HeckeU D N₁) (e e₁ : ℤ) (ν ν₁ : HChar D.host.E)
    (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x)) (hf₁ : ∀ x, χ₁.f x ^ e₁ = (ν₁⁻¹).1 (finIdl D x)) (τ : D.what₂.Tau) :
    e * χ.n τ = e₁ * χ₁.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e₁ * χ₁.n τ) (fun a ha => by
      have hne : ∀ τ, Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (by simpa using ha) (by exact_mod_cast norm_ne_zero_iff.2 (by simpa using ha))
      simp_rw [zpow_sub₀ (hne _), Finset.prod_div_distrib, prod_pow_eq χ e _ hf a ha, prod_pow_eq χ₁ e₁ _ hf₁ a ha, hν]
      exact div_self (Units.ne_zero _))
  have h := congrFun hc τ
  simpa [sub_eq_zero] using h

/- English proof (translation)
Establish `h` using `exps_eq_of P.W.chV' P₁.W.chV' P.W.ep' P₁.W.ep' ν ν₁ hν hf hf₁`. Use `⟨h, funext fun τ => ?_⟩` and prove the remaining obligations. Establish `h1` using `P.wt τ`. Establish `h2` using `P₁.wt τ`. Rewrite `h1` using `[h τ, hd]`.

Establish `: (P.n τ : ℤ) = P₁.n τ` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem pair_real_eq {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁)
    (ν ν₁ : HChar D.host.E) (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, P.W.chV'.f x ^ P.W.ep' = (ν⁻¹).1 (finIdl D x))
    (hf₁ : ∀ x, P₁.W.chV'.f x ^ P₁.W.ep' = (ν₁⁻¹).1 (finIdl D x)) (hd : P.d = P₁.d) :
    (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧ P.n = P₁.n := by
  have h := exps_eq_of P.W.chV' P₁.W.chV' P.W.ep' P₁.W.ep' ν ν₁ hν hf hf₁
  refine ⟨h, funext fun τ => ?_⟩
  have h1 := P.wt τ
  have h2 := P₁.wt τ
  rw [h τ, hd] at h1
  have : (P.n τ : ℤ) = P₁.n τ := by omega
  exact_mod_cast this

/- English proof (translation)
Take `⟨ha, ha', hd, hd'⟩` from `h.rank`. Take `⟨hb, hb', he, he'⟩` from `h₁.rank`. Establish `hν` using `nuH_finIdl_incU G hL t t' i j`. Establish `hdd : P.d = P₁.d` using `by rw [hd, he]`. Establish `hdd' : P'.d = P₁'.d` using `by rw [hd', he', hdd]`.

Take `⟨r1, r2⟩` from `pair_real_eq P P₁ _ _ hν h.chars.2 h₁.chars.2 hdd`. Take `⟨r1', r2'⟩` from `pair_real_eq P' P₁' _ _ hν h.chars'.2 h₁.chars'.2 hdd'`. Use `⟨⟨by rw [ha, hb], hdd, r2, r1, ?_⟩, ⟨by rw [ha', hb'], hdd', r2', r1', ?_⟩⟩` and prove the remaining obligations. Conclude with `exps_eq_of P.W.chV P₁.W.chV P.W.ep P₁.W.ep _ _ (fun _ => rfl) h.chars.1 h₁.chars.1`. Use `exps_eq_of P'.W.chV P₁'.W.chV P'.W.ep P₁'.W.ep (alphaH L t i j)⁻¹ (alphaH L t' i j)⁻¹ (fun a => ?_) (fun x => by rw [inv_inv]; exact h.chars'.1 x) (fun x => by rw [inv_inv]; exact h₁.chars'.1 x) show ((alphaH L t i j).1 _)⁻¹ = ((alphaH L t' i j).1 _)⁻¹` and prove the remaining obligations.

Rewrite using `[alphaH_finIdl_incU hL t t' i j a]`.
-/
theorem bottom_real_eq {μ₀ : T} (hL : L.Is μ₀) {i j : Fin D.R.m} {t t' : T} {𝔪 𝔪₁ : Ideal (𝓞 D.host.E)}
    {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} {P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q} {P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁}
    (h : IsBottom G t i j 𝔪 P P') (h₁ : IsBottom G t' i j 𝔪₁ P₁ P₁') :
    (P.a = P₁.a ∧ P.d = P₁.d ∧ P.n = P₁.n ∧ (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧
        ∀ τ, P.W.ep * P.W.chV.n τ = P₁.W.ep * P₁.W.chV.n τ) ∧
      (P'.a = P₁'.a ∧ P'.d = P₁'.d ∧ P'.n = P₁'.n ∧ (∀ τ, P'.W.ep' * P'.W.chV'.n τ = P₁'.W.ep' * P₁'.W.chV'.n τ) ∧
        ∀ τ, P'.W.ep * P'.W.chV.n τ = P₁'.W.ep * P₁'.W.chV.n τ) := by
  obtain ⟨ha, ha', hd, hd'⟩ := h.rank
  obtain ⟨hb, hb', he, he'⟩ := h₁.rank
  have hν := nuH_finIdl_incU G hL t t' i j
  have hdd : P.d = P₁.d := by rw [hd, he]
  have hdd' : P'.d = P₁'.d := by rw [hd', he', hdd]
  obtain ⟨r1, r2⟩ := pair_real_eq P P₁ _ _ hν h.chars.2 h₁.chars.2 hdd
  obtain ⟨r1', r2'⟩ := pair_real_eq P' P₁' _ _ hν h.chars'.2 h₁.chars'.2 hdd'
  refine ⟨⟨by rw [ha, hb], hdd, r2, r1, ?_⟩, ⟨by rw [ha', hb'], hdd', r2', r1', ?_⟩⟩
  · exact exps_eq_of P.W.chV P₁.W.chV P.W.ep P₁.W.ep _ _ (fun _ => rfl) h.chars.1 h₁.chars.1
  · refine exps_eq_of P'.W.chV P₁'.W.chV P'.W.ep P₁'.W.ep (alphaH L t i j)⁻¹ (alphaH L t' i j)⁻¹ (fun a => ?_)
      (fun x => by rw [inv_inv]; exact h.chars'.1 x) (fun x => by rw [inv_inv]; exact h₁.chars'.1 x)
    show ((alphaH L t i j).1 _)⁻¹ = ((alphaH L t' i j).1 _)⁻¹
    rw [alphaH_finIdl_incU hL t t' i j a]

end GlobalTheory.BottomReal
