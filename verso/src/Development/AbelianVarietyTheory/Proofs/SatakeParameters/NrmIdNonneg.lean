import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne

namespace GlobalTheory.KerJ.CharVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

/- English proof (translation)
Unfold `lamC`. Rewrite using `[dif_pos h]`.
-/
theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dif_pos h]

/- English proof (translation)
Establish `hx : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `: IsAlgebraic ℚ ((embT D τ).toRatAlgHom x)` using `hx.algHom _`. Conclude with `(mem_algebraicClosure_iff).2 this`.
-/
theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

/- English proof (translation)
Take `⟨-, k, hk, e⟩` from `hp`. Establish `h1 : D.chiD t ^ h = D.chiD (D.e1Dt z)`. Rewrite using `[← map_pow, e, map_mul, D.chiD_UO k hk, mul_one]`. Rewrite using `[← Units.val_pow_eq_pow_val, h1]`. Conclude with `D.rest_detCharacter_on_unitary_eq z`.
-/
theorem chi_pow (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) :
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := by
  obtain ⟨-, k, hk, e⟩ := hp
  have h1 : D.chiD t ^ h = D.chiD (D.e1Dt z) := by
    rw [← map_pow, e, map_mul, D.chiD_UO k hk, mul_one]
  rw [← Units.val_pow_eq_pow_val, h1]
  exact D.rest_detCharacter_on_unitary_eq z

/- English proof (translation)
Establish `h0 : ((D.chiD t : ℂˣ) : ℂ) ^ h ∈ Qbar`. Rewrite using `[chi_pow D t h z hp]`. Conclude with `prod_mem fun τ _ => inv_mem (embT_mem D τ _)`. Conclude with `(mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h0).of_pow hp.1)`.
-/
theorem chi_mem (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) : ((D.chiD t : ℂˣ) : ℂ) ∈ Qbar := by
  have h0 : ((D.chiD t : ℂˣ) : ℂ) ^ h ∈ Qbar := by
    rw [chi_pow D t h z hp]
    exact prod_mem fun τ _ => inv_mem (embT_mem D τ _)
  exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h0).of_pow hp.1)

/- English proof (translation)
Introduce `p _ lam t h z hp`. Use `⟨chi_pow D t h z hp, ?_⟩` and prove the remaining obligations. Establish `hm` using `chi_mem D t h z hp`. Establish `e : (⟨((D.chiD t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ h = ∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar)⁻¹`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `push_cast`. Conclude with `chi_pow D t h z hp`. Rewrite using `[lamC_mem' lam hm, ← norm_pow, ← map_pow, e, map_prod, norm_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_inv₀, norm_inv, lamC_mem' lam (embT_mem D τ _)]`.
-/
theorem chiVal_holds (D : D7) : chiVal D := by
  intro p _ lam t h z hp
  refine ⟨chi_pow D t h z hp, ?_⟩
  have hm := chi_mem D t h z hp
  have e : (⟨((D.chiD t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ h = ∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact chi_pow D t h z hp
  rw [lamC_mem' lam hm, ← norm_pow, ← map_pow, e, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_inv₀, norm_inv, lamC_mem' lam (embT_mem D τ _)]

/- English proof (translation)
Establish `h1 : ‖lam κ‖ = 1`. Establish `: ‖lam κ‖ ^ n = 1` using `by rw [← norm_pow, ← map_pow, hκ, map_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this`. Rewrite using `[← norm_pow, ← map_pow, e, map_mul, norm_mul, h1, mul_one, map_prod, norm_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀, norm_zpow]`.
-/
theorem key_norm {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*} [Fintype ι] (y κ : Qbar) (w : ι → Qbar)
    (s : ι → ℤ) (h n : ℕ) (hn : 0 < n) (e : y ^ h = (∏ τ, w τ ^ s τ) * κ) (hκ : κ ^ n = 1) :
    ‖lam y‖ ^ h = ∏ τ, ‖lam (w τ)‖ ^ s τ := by
  have h1 : ‖lam κ‖ = 1 := by
    have : ‖lam κ‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hκ, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  rw [← norm_pow, ← map_pow, e, map_mul, norm_mul, h1, mul_one, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, norm_zpow]

/- English proof (translation)
Take `⟨-, k, hk, e⟩` from `hp`. Take `⟨n, hn, h1⟩` from `hU k hk`. Establish `h1' : ((ρ k : ℂˣ) : ℂ) ^ n = 1` using `by rw [← Units.val_pow_eq_pow_val, h1]; rfl`. Establish `hkm : ((ρ k : ℂˣ) : ℂ) ∈ Qbar` using `(mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 (h1' ▸ one_mem Qbar)).of_pow hn)`. Establish `e2 : ((ρ t : ℂˣ) : ℂ) ^ h = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) * ((ρ k : ℂˣ) : ℂ)`.

Rewrite using `[← hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, e, map_mul]`. Use `key_norm lam (⟨_, ha⟩ : Qbar) ⟨_, hkm⟩ (fun τ => ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩) s h n hn (by` as an intermediate fact. Apply `(algebraMap Qbar ℂ).injective` to reduce the goal to its premises. Simplify using `only [map_pow, map_mul, map_prod, map_zpow₀]`. Conclude with `e2)`.

Use the proof step `(by`. Apply `(algebraMap Qbar ℂ).injective` to reduce the goal to its premises. Simplify using `only [map_pow, map_one]`. Conclude with `h1')`. Rewrite using `[lamC_mem' lam ha, this]`.

Conclude with `Finset.prod_congr rfl fun τ _ => by rw [lamC_mem' lam (embT_mem D τ _)]`.
-/
theorem val_of (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (ha : ((ρ t : ℂˣ) : ℂ) ∈ Qbar) (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    ‖lamC lam ((ρ t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (s τ) := by
  obtain ⟨-, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have h1' : ((ρ k : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1]; rfl
  have hkm : ((ρ k : ℂˣ) : ℂ) ∈ Qbar :=
    (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 (h1' ▸ one_mem Qbar)).of_pow hn)
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ h = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) * ((ρ k : ℂˣ) : ℂ) := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, e, map_mul]
  have := key_norm lam (⟨_, ha⟩ : Qbar) ⟨_, hkm⟩ (fun τ => ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩) s h n hn
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_mul, map_prod, map_zpow₀]
      exact e2)
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_one]
      exact h1')
  rw [lamC_mem' lam ha, this]
  exact Finset.prod_congr rfl fun τ _ => by rw [lamC_mem' lam (embT_mem D τ _)]

/- English proof (translation)
Introduce `p _ lam t h z hp i hi`. Take `⟨a, b, c⟩` from `hR i hi`. Take `⟨⟨a1, -⟩, ⟨a2, -⟩⟩` from `a t h z hp`. Conclude with `⟨val_of D _ _ lam t h z hp a1 (fun k hk => by obtain ⟨n, hn, x, -⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).1, val_of D _ _ lam t h z hp a2 (fun k hk => by obtain ⟨n, hn, -, x⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).2⟩`.
-/
theorem rhoVal_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (hR : rhoThreeOf D C mt) : rhoValOf D C mt := by
  intro p _ lam t h z hp i hi
  obtain ⟨a, b, c⟩ := hR i hi
  obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := a t h z hp
  exact ⟨val_of D _ _ lam t h z hp a1 (fun k hk => by obtain ⟨n, hn, x, -⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).1,
    val_of D _ _ lam t h z hp a2 (fun k hk => by obtain ⟨n, hn, -, x⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).2⟩

/- English proof (translation)
The claim follows from `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)`.
-/
theorem isUltra (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

/- English proof (translation)
Establish `h1 : IsIntegral (NormedField.valuation (K` using `K)).integer x := hx.tower_top`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1`. Establish `h3 : NormedField.valuation x ≤ 1` using `h2`. Rewrite `h3` using `[NormedField.valuation_apply]`. Conclude with `h3` after adjusting the coercions.
-/
theorem norm_le_one_of_int {K : Type} [NormedField K] [IsUltrametricDist K] (x : K)
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := K)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1
  have h3 : NormedField.valuation x ≤ 1 := h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

/- English proof (translation)
The claim follows from `norm_le_one_of_int _ ((RingOfIntegers.isIntegral_coe a).map (ψ : E →+* K).toIntAlgHom)`.
-/
theorem psi_int (a : 𝓞 E) : ‖ψ (a : E)‖ ≤ 1 :=
  norm_le_one_of_int _ ((RingOfIntegers.isIntegral_coe a).map (ψ : E →+* K).toIntAlgHom)

/- English proof (translation)
The claim follows from `| 0, y, hy => by rw [pow_zero, Submodule.mem_one] at hy obtain ⟨a, rfl⟩ := hy rw [pow_zero] exact psi_int ψ a | n + 1, y, hy => by rw [pow_succ] at hy refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun x y hx hy => ?_) · rw [map_mul, norm_mul, pow_succ] exact mul_le_ …`.
-/
theorem pow_bound (𝔞 : Submodule (𝓞 E) E) (B : ℝ) (hB : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ B) (hB0 : 0 ≤ B) :
    ∀ (n : ℕ), ∀ y ∈ 𝔞 ^ n, ‖ψ y‖ ≤ B ^ n
  | 0, y, hy => by
    rw [pow_zero, Submodule.mem_one] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [pow_zero]
    exact psi_int ψ a
  | n + 1, y, hy => by
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (pow_bound 𝔞 B hB hB0 n m hm) (hB k hk) (norm_nonneg _) (pow_nonneg hB0 n)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

/- English proof (translation)
Use `set S := (fun x : E => ‖ψ x‖) '' (𝔞 : Set E) with hS`. Establish `hne : S.Nonempty` using `⟨_, 0, 𝔞.zero_mem, rfl⟩`. Establish `hpow : ∀ x ∈ 𝔞, ‖ψ x‖ ^ h ≤ ‖ψ z‖`. Introduce `x hx`. Establish `: x ^ h ∈ Submodule.span (𝓞 E) {z}` using `e ▸ Submodule.pow_mem_pow 𝔞 hx h`.

Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 this`. Rewrite using `[← norm_pow, ← map_pow, ← ha, Algebra.smul_def, map_mul, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (psi_int ψ a)`. Use `set b : ℝ := ‖ψ z‖ ^ ((h : ℝ)⁻¹) with hb`. Establish `hb0 : 0 ≤ b` using `Real.rpow_nonneg (norm_nonneg _) _`.

Establish `hbh : b ^ h = ‖ψ z‖` using `Real.rpow_inv_natCast_pow (norm_nonneg _) h0`. Establish `hle : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ b` using `fun x hx => (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 h0).1 (hbh ▸ hpow x hx)`. Establish `hbd : BddAbove S` using `⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩`. Establish `hs0 : 0 ≤ sSup S` using `Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[← hbh]`. Conclude with `pow_le_pow_left₀ hs0 (csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)) h`. Establish `hz : z ∈ 𝔞 ^ h` using `e ▸ Submodule.mem_span_singleton_self z`. Conclude with `pow_bound ψ 𝔞 (sSup S) (fun x hx => le_csSup hbd ⟨x, hx, rfl⟩) hs0 h z hz`.
-/
theorem nu_pow (𝔞 : Submodule (𝓞 E) E) (h : ℕ) (h0 : h ≠ 0) (z : E)
    (e : 𝔞 ^ h = Submodule.span (𝓞 E) {z}) :
    sSup ((fun x : E => ‖ψ x‖) '' (𝔞 : Set E)) ^ h = ‖ψ z‖ := by
  set S := (fun x : E => ‖ψ x‖) '' (𝔞 : Set E) with hS
  have hne : S.Nonempty := ⟨_, 0, 𝔞.zero_mem, rfl⟩
  have hpow : ∀ x ∈ 𝔞, ‖ψ x‖ ^ h ≤ ‖ψ z‖ := by
    intro x hx
    have : x ^ h ∈ Submodule.span (𝓞 E) {z} := e ▸ Submodule.pow_mem_pow 𝔞 hx h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← norm_pow, ← map_pow, ← ha, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (psi_int ψ a)
  set b : ℝ := ‖ψ z‖ ^ ((h : ℝ)⁻¹) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hbh : b ^ h = ‖ψ z‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) h0
  have hle : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ b := fun x hx =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 h0).1 (hbh ▸ hpow x hx)
  have hbd : BddAbove S := ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩
  have hs0 : 0 ≤ sSup S := Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)
  apply le_antisymm
  · rw [← hbh]
    exact pow_le_pow_left₀ hs0 (csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)) h
  · have hz : z ∈ 𝔞 ^ h := e ▸ Submodule.mem_span_singleton_self z
    exact pow_bound ψ 𝔞 (sSup S) (fun x hx => le_csSup hbd ⟨x, hx, rfl⟩) hs0 h z hz

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

/- English proof (translation)
The claim follows from `lamC_mem' lam (embT_mem D τ x)`.
-/
theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

/- English proof (translation)
Unfold `nrmId`. Simplify using `only [lamC_embT]`. Use `haveI := isUltra p`. Conclude with `nu_pow (psiT D lam τ) 𝔞 h h0 z e`.
-/
theorem nrmId_pow (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) (h : ℕ) (h0 : h ≠ 0)
    (z : D.host.E) (e : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {z}) :
    nrmId D lam τ 𝔞 ^ h = ‖lamC lam (embT D τ z)‖ := by
  unfold nrmId
  simp only [lamC_embT]
  haveI := isUltra p
  exact nu_pow (psiT D lam τ) 𝔞 h h0 z e

/- English proof (translation)
The claim follows from `Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)`.
-/
theorem nrmId_nonneg (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) :
    0 ≤ nrmId D lam τ 𝔞 :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)

/- English proof (translation)
Use `(pow_left_inj₀ ha (Finset.prod_nonneg fun τ _ => zpow_nonneg (hν τ) _) h0).1 ?_` and prove the remaining obligations. Rewrite using `[e, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← hf τ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`.
-/
theorem root_eq {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (ν f : ι → ℝ) (hν : ∀ τ, 0 ≤ ν τ) (s : ι → ℤ) (h : ℕ) (h0 : h ≠ 0)
    (hf : ∀ τ, ν τ ^ h = f τ) (e : a ^ h = ∏ τ, f τ ^ s τ) : a = ∏ τ, ν τ ^ s τ := by
  refine (pow_left_inj₀ ha (Finset.prod_nonneg fun τ _ => zpow_nonneg (hν τ) _) h0).1 ?_
  rw [e, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hf τ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/- English proof (translation)
Introduce `idl hpin p _ lam t`. Take `⟨k, z, hp⟩` from `powRatAll_of D idl hpin (GlobalTheory.KernelScalarUnit.normOne_pow D) t`. Take `⟨-, -, hmul, hz, -⟩` from `hpin`. Establish `h0 : k ≠ 0` using `Nat.pos_iff_ne_zero.1 hp.1`. Establish `hid : idl (QuotientGroup.mk t) ^ k = Submodule.span (𝓞 D.host.E) {(z : D.host.E)}`.

Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Take `⟨-, c, hc, e⟩` from `hp`. Rewrite using `[← idl_pow hmul, ← hz z]`. Use `congr 1`. Rewrite using `[← QuotientGroup.mk_pow, e]`.

Conclude with `QuotientGroup.mk_mul_of_mem _ hc`. Establish `hf : ∀ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ k = ‖lamC lam (embT D τ (z : D.host.E))‖` using `fun τ => nrmId_pow D lam τ _ k h0 _ hid`. Establish `hν : ∀ τ, 0 ≤ nrmId D lam τ (idl (QuotientGroup.mk t))` using `fun τ => nrmId_nonneg D lam τ _`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Establish `e` using `(chiVal_holds D p lam t k z hp).2`.

Use `root_eq _ (norm_nonneg _) _ _ hν (fun _ => (-1 : ℤ)) k h0 hf (by simpa only [zpow_neg_one] using e)` as an intermediate fact. Simplify `this` using `only [zpow_neg_one]`. Take `⟨x, y⟩` from `rhoVal_holds D C mt hR p lam t k z hp i hi`. Conclude with `⟨root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf x, root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf y⟩`.
-/
theorem brRho_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u))
    (mt : ℕ → D.Dt →* ℂˣ) (hR : rhoThreeOf D C mt) : brRhoOf D C mt := by
  intro idl hpin p _ lam t
  obtain ⟨k, z, hp⟩ := powRatAll_of D idl hpin (GlobalTheory.KernelScalarUnit.normOne_pow D) t
  obtain ⟨-, -, hmul, hz, -⟩ := hpin
  have h0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hp.1
  have hid : idl (QuotientGroup.mk t) ^ k = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, c, hc, e⟩ := hp
    rw [← idl_pow hmul, ← hz z]
    congr 1
    rw [← QuotientGroup.mk_pow, e]
    exact QuotientGroup.mk_mul_of_mem _ hc
  have hf : ∀ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ k = ‖lamC lam (embT D τ (z : D.host.E))‖ :=
    fun τ => nrmId_pow D lam τ _ k h0 _ hid
  have hν : ∀ τ, 0 ≤ nrmId D lam τ (idl (QuotientGroup.mk t)) := fun τ => nrmId_nonneg D lam τ _
  refine ⟨?_, fun i hi => ?_⟩
  · have e := (chiVal_holds D p lam t k z hp).2
    have := root_eq _ (norm_nonneg _) _ _ hν (fun _ => (-1 : ℤ)) k h0 hf (by simpa only [zpow_neg_one] using e)
    simpa only [zpow_neg_one] using this
  · obtain ⟨x, y⟩ := rhoVal_holds D C mt hR p lam t k z hp i hi
    exact ⟨root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf x, root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf y⟩

end GlobalTheory.KerJ.CharVal
