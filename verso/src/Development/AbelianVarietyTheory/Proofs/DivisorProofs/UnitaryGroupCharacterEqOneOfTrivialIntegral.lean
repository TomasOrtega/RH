import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

open Formalism.UG Matrix GlobalTheory.UnitarySwap

noncomputable section

namespace GlobalTheory.UnitaryCharacter

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

section Abstract

variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L} {B : V →ₛₗ[σ] V →ₗ[L] L}

def ReflIn (B : V →ₛₗ[σ] V →ₗ[L] L) (N : Submonoid (Module.End L V)) (Λ : Set V) : Prop :=
  ∀ w ∈ Λ, ∀ μ : L, μ ≠ 0 → μ⁻¹ ∈ intL L → B w w = μ + σ μ → refl B w μ ∈ N

/- English proof (translation)
Establish `h1 : Valued.v (δ + π * (τ * A)) = 1`. Rewrite using `[Valuation.map_add_eq_of_lt_left _ (by rw [hδ]; exact mul_lt_one hπ (mul_mem hτ hA)), hδ]`. Establish `h0 : δ + π * (τ * A) ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, map_zero]`.

Conclude with `zero_ne_one h1`. Use `⟨π⁻¹ * (δ + π * (τ * A)), mul_ne_zero (inv_ne_zero hπ0) h0, ?_, (δ + π * (τ * A))⁻¹, ?_, ?_, inv_mul_cancel₀ h0⟩` and prove the remaining obligations. Establish `: σ τ = 1 - τ` using `by rw [← hτ1]; ring`. Simplify using `only [map_mul, map_add, map_inv₀, hσπ, hδ', hA', this]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mem_int, map_inv₀, h1, inv_one]`. Rewrite using `[mul_inv, inv_inv]`.
-/
theorem exists_param (hσ : ∀ x, σ (σ x) = x) {τ : L} (hτ : τ ∈ intL L) (hτ1 : τ + σ τ = 1) {δ : L}
    (hδ : Valued.v δ = 1) (hδ' : σ δ = -δ) {π : L} (hπ0 : π ≠ 0) (hπ : Valued.v π < 1) (hσπ : σ π = π)
    {A : L} (hA : A ∈ intL L) (hA' : σ A = A) :
    ∃ μ : L, μ ≠ 0 ∧ A = μ + σ μ ∧ ∃ m ∈ intL L, μ⁻¹ = π * m ∧ m * (δ + π * (τ * A)) = 1 := by
  have h1 : Valued.v (δ + π * (τ * A)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hδ]; exact mul_lt_one hπ (mul_mem hτ hA)), hδ]
  have h0 : δ + π * (τ * A) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨π⁻¹ * (δ + π * (τ * A)), mul_ne_zero (inv_ne_zero hπ0) h0, ?_, (δ + π * (τ * A))⁻¹, ?_, ?_,
    inv_mul_cancel₀ h0⟩
  · have : σ τ = 1 - τ := by rw [← hτ1]; ring
    simp only [map_mul, map_add, map_inv₀, hσπ, hδ', hA', this]
    field_simp
    ring
  · rw [mem_int, map_inv₀, h1, inv_one]
  · rw [mul_inv, inv_inv]

/- English proof (translation)
Establish `hσO : ∀ x ∈ intL L, σ x ∈ intL L` using `fun x hx => by rw [mem_int, hσ]; exact hx`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`.

Establish `hϖ1 : Valued.v ϖ < 1`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Establish `hδ0 : δ ≠ 0`. Introduce `h`.

Rewrite `hδ` using `[h, map_zero]`. Conclude with `zero_ne_one hδ`. Proceed by induction on `m with`. Consider the case `zero => intro W hW`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ m ih`. Introduce `W hW Λ Λ' hΛ hΛ' hR hR' hN`. Establish `hback : ∀ N : ℕ, (∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) → ∀ v ∈ Λ, ϖ ^ N • v ∈ Λ'`. Introduce `N h v hv`. Use `(hΛ' _).2 ⟨W.smul_mem _ ((hΛ v).1 hv).1, fun w hw => ?_⟩` and prove the remaining obligations.

Use `hΛ.pair hv (h w hw)` as an intermediate fact. Simplify `this` using `[map_smulₛₗ, hσϖ]`. Establish `ha` using `Nat.find_spec hN`. Break down `h0 : Nat.find hN with _ | b` into its components or cases. Rewrite `ha` using `[h0]`.

Use `⟨1, one_mem _, fun _ _ => rfl, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `using hback 0 ha v hv`. Establish `hb : ¬ ∀ v ∈ Λ', ϖ ^ b • v ∈ Λ` using `Nat.find_min hN (by omega)`. Rewrite `ha` using `[h0]`. Use `push Not at hb`.

Take `⟨e, he, hne⟩` from `hb`. Establish `heW : e ∈ W` using `((hΛ' e).1 he).1`. Rewrite `hne` using `[hΛ]`. Use `push Not at hne`. Take `⟨y, hy, hy'⟩` from `hne (W.smul_mem _ heW)`.

Use `set π := ϖ ^ (b + 1) with hπdef`. Establish `hπ0 : π ≠ 0` using `pow_ne_zero _ hϖ0`. Establish `hσπ : σ π = π` using `by rw [hπdef, map_pow, hσϖ]`. Establish `hπ1 : Valued.v π < 1`. Rewrite using `[hπdef, map_pow]; exact pow_lt_one₀ zero_le hϖ1 (by omega)`.

Establish `hπO : π ∈ intL L` using `hπ1.le`. Establish `hπe : π • e ∈ Λ` using `ha e he`. Establish `hunit : Valued.v (π * B e y) = 1`. Establish `h1 : Valued.v (π * B e y) ≤ 1`. Use `hΛ.pair hπe hy` as an intermediate fact.

Simplify `this` using `[map_smulₛₗ, hσπ, mem_int]`. Use `le_antisymm h1 ?_` and prove the remaining obligations. Establish `h2 : 1 < Valued.v (ϖ ^ b * B e y)`. Rewrite `hy'` using `[mem_int, not_le]`. Simplify `hy'` using `[map_smulₛₗ, hσϖ]`.

Establish `h3 : π * B e y = ϖ * (ϖ ^ b * B e y)` using `by rw [hπdef]; ring`. Rewrite using `[h3, map_mul, hϖ]`. Establish `h4 : Valued.v (ϖ ^ b * B e y) ≠ 0` using `(lt_trans zero_lt_one h2).ne'`. Rewrite `h2` using `[← WithZero.exp_log h4, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[← WithZero.exp_log h4, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hu0 : π * B e y ≠ 0`. Introduce `h`. Rewrite `hunit` using `[h, map_zero]`. Conclude with `zero_ne_one hunit`.

Establish `hey : B e y ≠ 0` using `right_ne_zero_of_mul hu0`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf, hef⟩ : ∃ f ∈ Λ, B e f = π⁻¹ := by`. Use `⟨(π * B e y)⁻¹ • y, hΛ.smul hσO (by rw [mem_int, map_inv₀, hunit, inv_one]) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Establish `hfe : B f e = π⁻¹` using `by rw [← hB, hef, map_inv₀, hσπ]`. Establish `hfW : f ∈ W` using `((hΛ f).1 hf).1`. Establish `hπf : π • f ∈ Λ'` using `hback _ ha f hf`. Establish `hee` using `hΛ'.pair he he`. Establish `hff` using `hΛ.pair hf hf`.

Establish `hsm : ∀ x v, B (π • x) v = π * B x v`. Introduce `x v`. Simplify using `[map_smulₛₗ, hσπ]`. Establish `hsmall : Valued.v (π * (π * (B e e * B f f))) < 1` using `mul_lt_one hπ1 (mul_mem hπO (mul_mem hee hff))`. Establish `hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ, B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • (π • e) + d • f + v₀`.

Introduce `v hv`. Take `⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩` from `hΛ.decomp hσO hπe hf (by rw [hsm, hef, mul_inv_cancel₀ hπ0]) (by rw [map_smul, hfe, smul_eq_mul, mul_inv_cancel₀ hπ0]) (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv`. Rewrite `h1` using `[hsm]`. Conclude with `⟨c, hc, d, hd, v₀, hv₀, (mul_eq_zero.1 h1).resolve_left hπ0, h2, h3⟩`. Establish `hdec' : ∀ v ∈ Λ', ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ', B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • e + d • (π • f) + v₀`.

Introduce `v hv`. Take `⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩` from `hΛ'.decomp hσO he hπf (by rw [map_smul, hef, smul_eq_mul, mul_inv_cancel₀ hπ0]) (by rw [hsm, hfe, mul_inv_cancel₀ hπ0]) (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv`. Rewrite `h2` using `[hsm]`. Conclude with `⟨c, hc, d, hd, v₀, hv₀, h1, (mul_eq_zero.1 h2).resolve_left hπ0, h3⟩`. Establish `hS` using `hΛ.inter hB (fun v h => by rw [hsm, h, mul_zero]) (fun v h => h) hdec`.

Establish `hS'` using `hΛ'.inter hB (fun v h => h) (fun v h => by rw [hsm, h, mul_zero]) hdec'`. Establish `hlt : perp B W e f < W`. Use `lt_of_le_of_ne inf_le_left fun h => ?_` and prove the remaining obligations. Rewrite `hfW` using `[← h]`. Conclude with `inv_ne_zero hπ0 (hef ▸ (mem_perp.1 hfW).2.1)`.

Take `⟨s₀, i₀, f₀, m₀⟩` from `ih (perp B W e f) (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega) _ _ hS hS' (fun w hw => hR w hw.1) (fun w hw => hR' w hw.1) ⟨b + 1, fun v hv => ⟨ha v hv.1, (perp B W e f).smul_mem _ hv.2⟩⟩`. Establish `hδi : Valued.v (-δ⁻¹) = 1` using `by rw [Valuation.map_neg, map_inv₀, hδ, inv_one]`. Take `⟨μ, hμ0, hμ, p, hp, hμp, hp1⟩` from `exists_param hσσ hτ hτ1 hδ hδ' hπ0 hπ1 hσπ hee (hB e e)`. Take `⟨μ', hμ0', hμ', p', hp', hμp', hp1'⟩` from `exists_param hσσ hτ hτ1 hδi (by rw [map_neg, map_inv₀, hδ', inv_neg]) hπ0 hπ1 hσπ hff (hB f f)`. Establish `r₁` using `hR' e he μ hμ0 (hμp ▸ mul_mem hπO hp) hμ`.

Establish `r₂` using `hR f hf μ' hμ0' (hμp' ▸ mul_mem hπO hp') hμ'`. Establish `f₁ : ∀ v, B e v = 0 → B f v = 0 → refl B f μ' (refl B e μ v) = v`. Introduce `v h1 h2`. Simplify using `[refl_apply, h1, h2]`. Establish `s₀e : s₀ e = e` using `f₀ e fun w hw => by rw [← hB, (mem_perp.1 hw).2.1, map_zero]`.

Establish `s₀f : s₀ f = f` using `f₀ f fun w hw => by rw [← hB, (mem_perp.1 hw).2.2, map_zero]`. Establish `se : refl B f μ' (refl B e μ e) = (1 - π * p * B e e) • e + (-((1 - π * p * B e e) * p')) • f`. Simplify using `only [refl_apply, map_sub, map_smul, hμp, hμp', hfe, smul_eq_mul]`. Apply the tactic sequence `match_scalars <;> field_simp <;> ring`. Establish `key : 1 + p * p' = π * (p * p' * (τ * B e e * (-δ⁻¹) + δ * (τ * B f f) + π * (τ * B e e * (τ * B f f))))`.

Use `mul_inv_cancel₀ hδ0` as an intermediate fact. Take the linear combination `(-(p' * (-δ⁻¹ + π * (τ * B f f)))) * hp1 - hp1' - (p * p') * this`. Establish `sf : refl B f μ' (refl B e μ f) = (-p) • e + (1 + p * p' - π * p' * B f f) • f`. Simplify using `only [refl_apply, map_sub, map_smul, hμp, hμp', hfe, hef, smul_eq_mul]`. Apply the tactic sequence `match_scalars <;> field_simp <;> ring`.

Use `⟨refl B f μ' * refl B e μ * s₀, mul_mem (mul_mem r₂ r₁) i₀, fun u hu => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[f₀ u fun w hw => hu w (mem_perp.1 hw).1, f₁ u (hu e heW) (hu f hfW)]`. Take `⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩` from `hdec v hv`. Establish `h3` using `m₀ v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ v₀).1 hv₀).1, h1, h2⟩⟩`.

Establish `h4` using `mem_perp.1 h3.2`. Establish `h5 : 1 - π * p * B e e ∈ intL L` using `sub_mem (one_mem _) (mul_mem (mul_mem hπO hp) hee)`. Establish `hA` using `mul_mem hτ hee`. Establish `hC` using `mul_mem hτ hff`. Take `⟨z, hz, key⟩ : ∃ z ∈ intL L, 1 + p * p' = π * z` from `⟨_, mul_mem (mul_mem hp hp') (add_mem (add_mem (mul_mem hA hδi.le) (mul_mem hδ.le hC)) (mul_mem hπO (mul_mem hA hC))), key⟩`.

Establish `: (refl B f μ' * refl B e μ * s₀ : Module.End L V) (c • (π • e) + d • f + v₀) = (c * (π * (1 - π * p * B e e)) + d * (-p)) • e + (c * (-((1 - π * p * B e e) * p')) + d * (z - p' * B f f)) • (π • f) + s₀ v₀`. Simplify using `only [Module.End.mul_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf, key]`. Use `module`. Rewrite using `[this]`. Use `hΛ'.add (hΛ'.add (hΛ'.smul hσO ?_ he) (hΛ'.smul hσO ?_ hπf)) h3.1` and prove the remaining obligations.

Conclude with `add_mem (mul_mem hc (mul_mem hπO h5)) (mul_mem hd (neg_mem hp))`. Conclude with `add_mem (mul_mem hc (neg_mem (mul_mem h5 hp'))) (mul_mem hd (sub_mem hz (mul_mem hp' hff)))`.
-/
theorem exists_move [FiniteDimensional L V] (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (hB : ∀ u v, σ (B u v) = B v u) {τ : L} (hτ : τ ∈ intL L) (hτ1 : τ + σ τ = 1) {δ : L}
    (hδ : Valued.v δ = 1) (hδ' : σ δ = -δ) {ϖ : L}
    (hσϖ : σ ϖ = ϖ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (N : Submonoid (Module.End L V)) (m : ℕ) :
    ∀ (W : Submodule L V), Module.finrank L W < m → ∀ Λ Λ' : Set V, SelfDual B W Λ → SelfDual B W Λ' →
      ReflIn B N Λ → ReflIn B N Λ' → (∃ k : ℕ, ∀ v ∈ Λ', ϖ ^ k • v ∈ Λ) →
      ∃ s ∈ N, (∀ u, (∀ w ∈ W, B w u = 0) → s u = u) ∧ (∀ v ∈ Λ, s v ∈ Λ') := by
  classical
  have hσO : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_int, hσ]; exact hx
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hδ; exact zero_ne_one hδ
  induction m with
  | zero => intro W hW; omega
  | succ m ih =>
  intro W hW Λ Λ' hΛ hΛ' hR hR' hN
  have hback : ∀ N : ℕ, (∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) → ∀ v ∈ Λ, ϖ ^ N • v ∈ Λ' := by
    intro N h v hv
    refine (hΛ' _).2 ⟨W.smul_mem _ ((hΛ v).1 hv).1, fun w hw => ?_⟩
    have := hΛ.pair hv (h w hw)
    simpa [map_smulₛₗ, hσϖ] using this
  have ha := Nat.find_spec hN
  rcases h0 : Nat.find hN with _ | b
  · rw [h0] at ha
    refine ⟨1, one_mem _, fun _ _ => rfl, fun v hv => ?_⟩
    simpa using hback 0 ha v hv
  have hb : ¬ ∀ v ∈ Λ', ϖ ^ b • v ∈ Λ := Nat.find_min hN (by omega)
  rw [h0] at ha
  push Not at hb
  obtain ⟨e, he, hne⟩ := hb
  have heW : e ∈ W := ((hΛ' e).1 he).1
  rw [hΛ] at hne
  push Not at hne
  obtain ⟨y, hy, hy'⟩ := hne (W.smul_mem _ heW)
  set π := ϖ ^ (b + 1) with hπdef
  have hπ0 : π ≠ 0 := pow_ne_zero _ hϖ0
  have hσπ : σ π = π := by rw [hπdef, map_pow, hσϖ]
  have hπ1 : Valued.v π < 1 := by
    rw [hπdef, map_pow]; exact pow_lt_one₀ zero_le hϖ1 (by omega)
  have hπO : π ∈ intL L := hπ1.le
  have hπe : π • e ∈ Λ := ha e he
  have hunit : Valued.v (π * B e y) = 1 := by
    have h1 : Valued.v (π * B e y) ≤ 1 := by
      have := hΛ.pair hπe hy
      simpa [map_smulₛₗ, hσπ, mem_int] using this
    refine le_antisymm h1 ?_
    have h2 : 1 < Valued.v (ϖ ^ b * B e y) := by
      rw [mem_int, not_le] at hy'
      simpa [map_smulₛₗ, hσϖ] using hy'
    have h3 : π * B e y = ϖ * (ϖ ^ b * B e y) := by rw [hπdef]; ring
    rw [h3, map_mul, hϖ]
    have h4 : Valued.v (ϖ ^ b * B e y) ≠ 0 := (lt_trans zero_lt_one h2).ne'
    rw [← WithZero.exp_log h4, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_log h4, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hu0 : π * B e y ≠ 0 := by
    intro h; rw [h, map_zero] at hunit; exact zero_ne_one hunit
  have hey : B e y ≠ 0 := right_ne_zero_of_mul hu0
  obtain ⟨f, hf, hef⟩ : ∃ f ∈ Λ, B e f = π⁻¹ := by
    refine ⟨(π * B e y)⁻¹ • y, hΛ.smul hσO (by rw [mem_int, map_inv₀, hunit, inv_one]) hy, ?_⟩
    rw [map_smul, smul_eq_mul]; field_simp
  have hfe : B f e = π⁻¹ := by rw [← hB, hef, map_inv₀, hσπ]
  have hfW : f ∈ W := ((hΛ f).1 hf).1
  have hπf : π • f ∈ Λ' := hback _ ha f hf
  have hee := hΛ'.pair he he
  have hff := hΛ.pair hf hf
  have hsm : ∀ x v, B (π • x) v = π * B x v := by
    intro x v; simp [map_smulₛₗ, hσπ]
  have hsmall : Valued.v (π * (π * (B e e * B f f))) < 1 :=
    mul_lt_one hπ1 (mul_mem hπO (mul_mem hee hff))
  have hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • (π • e) + d • f + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ.decomp hσO hπe hf
      (by rw [hsm, hef, mul_inv_cancel₀ hπ0]) (by rw [map_smul, hfe, smul_eq_mul, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h1
    exact ⟨c, hc, d, hd, v₀, hv₀, (mul_eq_zero.1 h1).resolve_left hπ0, h2, h3⟩
  have hdec' : ∀ v ∈ Λ', ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ',
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • e + d • (π • f) + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ'.decomp hσO he hπf
      (by rw [map_smul, hef, smul_eq_mul, mul_inv_cancel₀ hπ0]) (by rw [hsm, hfe, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h2
    exact ⟨c, hc, d, hd, v₀, hv₀, h1, (mul_eq_zero.1 h2).resolve_left hπ0, h3⟩
  have hS := hΛ.inter hB (fun v h => by rw [hsm, h, mul_zero]) (fun v h => h) hdec
  have hS' := hΛ'.inter hB (fun v h => h) (fun v h => by rw [hsm, h, mul_zero]) hdec'
  have hlt : perp B W e f < W := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    rw [← h] at hfW
    exact inv_ne_zero hπ0 (hef ▸ (mem_perp.1 hfW).2.1)
  obtain ⟨s₀, i₀, f₀, m₀⟩ := ih (perp B W e f)
    (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega) _ _ hS hS'
    (fun w hw => hR w hw.1) (fun w hw => hR' w hw.1)
    ⟨b + 1, fun v hv => ⟨ha v hv.1, (perp B W e f).smul_mem _ hv.2⟩⟩
  have hδi : Valued.v (-δ⁻¹) = 1 := by rw [Valuation.map_neg, map_inv₀, hδ, inv_one]
  obtain ⟨μ, hμ0, hμ, p, hp, hμp, hp1⟩ := exists_param hσσ hτ hτ1 hδ hδ' hπ0 hπ1 hσπ hee (hB e e)
  obtain ⟨μ', hμ0', hμ', p', hp', hμp', hp1'⟩ := exists_param hσσ hτ hτ1 hδi
    (by rw [map_neg, map_inv₀, hδ', inv_neg]) hπ0 hπ1 hσπ hff (hB f f)
  have r₁ := hR' e he μ hμ0 (hμp ▸ mul_mem hπO hp) hμ
  have r₂ := hR f hf μ' hμ0' (hμp' ▸ mul_mem hπO hp') hμ'
  have f₁ : ∀ v, B e v = 0 → B f v = 0 → refl B f μ' (refl B e μ v) = v := by
    intro v h1 h2
    simp [refl_apply, h1, h2]
  have s₀e : s₀ e = e := f₀ e fun w hw => by rw [← hB, (mem_perp.1 hw).2.1, map_zero]
  have s₀f : s₀ f = f := f₀ f fun w hw => by rw [← hB, (mem_perp.1 hw).2.2, map_zero]
  have se : refl B f μ' (refl B e μ e) = (1 - π * p * B e e) • e + (-((1 - π * p * B e e) * p')) • f := by
    simp only [refl_apply, map_sub, map_smul, hμp, hμp', hfe, smul_eq_mul]
    match_scalars <;> field_simp <;> ring
  have key : 1 + p * p' = π * (p * p' * (τ * B e e * (-δ⁻¹) + δ * (τ * B f f) + π * (τ * B e e * (τ * B f f)))) := by
    have := mul_inv_cancel₀ hδ0
    linear_combination (-(p' * (-δ⁻¹ + π * (τ * B f f)))) * hp1 - hp1' - (p * p') * this
  have sf : refl B f μ' (refl B e μ f) = (-p) • e + (1 + p * p' - π * p' * B f f) • f := by
    simp only [refl_apply, map_sub, map_smul, hμp, hμp', hfe, hef, smul_eq_mul]
    match_scalars <;> field_simp <;> ring
  refine ⟨refl B f μ' * refl B e μ * s₀, mul_mem (mul_mem r₂ r₁) i₀, fun u hu => ?_, fun v hv => ?_⟩
  · simp only [Module.End.mul_apply]
    rw [f₀ u fun w hw => hu w (mem_perp.1 hw).1, f₁ u (hu e heW) (hu f hfW)]
  · obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩ := hdec v hv
    have h3 := m₀ v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ v₀).1 hv₀).1, h1, h2⟩⟩
    have h4 := mem_perp.1 h3.2
    have h5 : 1 - π * p * B e e ∈ intL L := sub_mem (one_mem _) (mul_mem (mul_mem hπO hp) hee)
    have hA := mul_mem hτ hee
    have hC := mul_mem hτ hff
    obtain ⟨z, hz, key⟩ : ∃ z ∈ intL L, 1 + p * p' = π * z :=
      ⟨_, mul_mem (mul_mem hp hp') (add_mem (add_mem (mul_mem hA hδi.le) (mul_mem hδ.le hC))
        (mul_mem hπO (mul_mem hA hC))), key⟩
    have : (refl B f μ' * refl B e μ * s₀ : Module.End L V) (c • (π • e) + d • f + v₀) =
        (c * (π * (1 - π * p * B e e)) + d * (-p)) • e +
          (c * (-((1 - π * p * B e e) * p')) + d * (z - p' * B f f)) • (π • f) + s₀ v₀ := by
      simp only [Module.End.mul_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf, key]
      module
    rw [this]
    refine hΛ'.add (hΛ'.add (hΛ'.smul hσO ?_ he) (hΛ'.smul hσO ?_ hπf)) h3.1
    · exact add_mem (mul_mem hc (mul_mem hπO h5)) (mul_mem hd (neg_mem hp))
    · exact add_mem (mul_mem hc (neg_mem (mul_mem h5 hp'))) (mul_mem hd (sub_mem hz (mul_mem hp' hff)))

end Abstract

variable {n : ℕ} {σ : L →+* L}

def kerEnd {J : Matrix (Fin n) (Fin n) L} (ν : UJ σ J →* Circle) : Submonoid (Module.End L (Fin n → L)) where
  carrier := {s | ∃ g : UJ σ J, ν g = 1 ∧ ∀ v, s v = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v}
  one_mem' := ⟨1, map_one ν, fun v => by simp⟩
  mul_mem' := by
    rintro s t ⟨g, hg, es⟩ ⟨h, hh, et⟩
    refine ⟨g * h, by rw [map_mul, hg, hh, mul_one], fun v => ?_⟩
    rw [Module.End.mul_apply, es, et, Matrix.mulVec_mulVec]
    rfl

/- English proof (translation)
Introduce `w hw μ hμ0 hμ hww`. Establish `hσO : ∀ x ∈ intL L, σ x ∈ intL L` using `fun x hx => by rw [mem_int, hσ]; exact hx`. Establish `hΛ'` using `selfDual_image (selfDual_intVec hσ hJ) g.2`. Establish `hs` using `refl_isom (form_herm hσσ hh) w μ hμ0 hww`. Establish `h2 : ∀ v, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ intVec L n → ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ v) ∈ intVec L n`.

Introduce `v hv`. Rewrite using `[refl_apply, sub_eq_add_neg, ← neg_smul]`. Conclude with `hΛ'.add hv (hΛ'.smul hσO (neg_mem (mul_mem hμ (hΛ'.pair hw hv))) hw)`. Take `⟨S, hS'⟩ : ∃ S : Matrix (Fin n) (Fin n) L, Matrix.toLin' S = refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ` from `Matrix.toLin'.surjective _`. Rewrite `hs`, `h2`, the goal using `[← hS']`.

Simplify using `only [Matrix.toLin'_apply] at hs h2`. Establish `hS : cT σ S * J * S = J`. Use extensionality with `i j`. Rewrite using `[← form_single (σ := σ) (cT σ S * (J : Matrix (Fin n) (Fin n) L) * S), ← form_mulVec, hs, form_single]`. Establish `hSi : (((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ S * J)) * S = 1`.

Rewrite using `[Matrix.mul_assoc, hS, Units.inv_mul]`. Set `S' : UJ σ (J : Matrix (Fin n) (Fin n) L)` to `⟨⟨S, _, mul_eq_one_comm.mp hSi, hSi⟩, hS⟩`. Use `⟨S', ?_, fun v => Matrix.toLin'_apply _ _⟩` and prove the remaining obligations. Use `hν (g * S' * g⁻¹) (mem_GLint_of_unitary hσ hJ (g * S' * g⁻¹).2 (entries_mem fun v hv => by` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, ← Matrix.mulVec_mulVec]`.

Apply `h2` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `hv))`. Rewrite `this` using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Then use the resulting hypothesis.
-/
theorem reflIn_image (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    (ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle)
    (hν : ∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1)
    (g : UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ReflIn (form σ (J : Matrix (Fin n) (Fin n) L)) (kerEnd ν)
      {v | ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ intVec L n} := by
  intro w hw μ hμ0 hμ hww
  have hσO : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_int, hσ]; exact hx
  have hΛ' := selfDual_image (selfDual_intVec hσ hJ) g.2
  have hs := refl_isom (form_herm hσσ hh) w μ hμ0 hww
  have h2 : ∀ v, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ intVec L n →
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ v) ∈ intVec L n := by
    intro v hv
    rw [refl_apply, sub_eq_add_neg, ← neg_smul]
    exact hΛ'.add hv (hΛ'.smul hσO (neg_mem (mul_mem hμ (hΛ'.pair hw hv))) hw)
  obtain ⟨S, hS'⟩ : ∃ S : Matrix (Fin n) (Fin n) L,
      Matrix.toLin' S = refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ := Matrix.toLin'.surjective _
  rw [← hS'] at hs h2 ⊢
  simp only [Matrix.toLin'_apply] at hs h2
  have hS : cT σ S * J * S = J := by
    ext i j
    rw [← form_single (σ := σ) (cT σ S * (J : Matrix (Fin n) (Fin n) L) * S), ← form_mulVec, hs, form_single]
  have hSi : (((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ S * J)) * S = 1 := by
    rw [Matrix.mul_assoc, hS, Units.inv_mul]
  let S' : UJ σ (J : Matrix (Fin n) (Fin n) L) := ⟨⟨S, _, mul_eq_one_comm.mp hSi, hSi⟩, hS⟩
  refine ⟨S', ?_, fun v => Matrix.toLin'_apply _ _⟩
  have := hν (g * S' * g⁻¹) (mem_GLint_of_unitary hσ hJ (g * S' * g⁻¹).2 (entries_mem fun v hv => by
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, ← Matrix.mulVec_mulVec]
    apply h2
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hv))
  rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this

/- English proof (translation)
Take `⟨hσσ, hσ, hσϖ, hϖ, ⟨x, hx, hx1⟩, -, -⟩` from `hU`. Establish `hx0 : σ x - x ≠ 0`. Introduce `h`. Rewrite `hx1` using `[h, map_zero]`. Conclude with `zero_ne_one hx1`.

Establish `hτ : σ x * (σ x - x)⁻¹ ∈ intL L` using `mul_mem (by rw [mem_int, hσ]; exact hx) (by rw [mem_int, map_inv₀, hx1, inv_one])`. Establish `hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1`. Rewrite using `[map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]`. Take the linear combination `mul_inv_cancel₀ hx0`. Establish `hΛ` using `selfDual_intVec hσ hJ`.

Establish `hΛ'` using `selfDual_image hΛ g.2`. Establish `hR` using `reflIn_image hσσ hσ hJ hh ν hν 1`. Simplify using `only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, Set.setOf_mem_eq] at hR`. Take `⟨N, hN⟩` from `exists_pow_mem hϖ (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Take `⟨s, ⟨S, hS, es⟩, -, h1⟩` from `exists_move hσσ hσ (form_herm hσσ hh) hτ hτ1 hx1 (by rw [map_sub, hσσ, neg_sub]) hσϖ hϖ (kerEnd ν) _ ⊤ (Nat.lt_succ_self _) _ _ hΛ hΛ' hR (reflIn_image hσσ hσ hJ hh ν hν g) ⟨N, fun v hv => by`.

Use `mulVec_mem (M := ϖ ^ N • (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hN hv` as an intermediate fact. Rewrite using `[Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this⟩` and apply the resulting hypothesis. Use `hν (g * S) (mem_GLint_of_unitary hσ hJ (g * S).2 (entries_mem fun v hv => by` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← es]`. Conclude with `h1 v hv))`.

Rewrite `this` using `[map_mul, hS, mul_one]`. Then use the resulting hypothesis.
-/
theorem eq_one {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    (ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle)
    (hν : ∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1)
    (g : UJ σ (J : Matrix (Fin n) (Fin n) L)) : ν g = 1 := by
  obtain ⟨hσσ, hσ, hσϖ, hϖ, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hτ : σ x * (σ x - x)⁻¹ ∈ intL L :=
    mul_mem (by rw [mem_int, hσ]; exact hx) (by rw [mem_int, map_inv₀, hx1, inv_one])
  have hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
    linear_combination mul_inv_cancel₀ hx0
  have hΛ := selfDual_intVec hσ hJ
  have hΛ' := selfDual_image hΛ g.2
  have hR := reflIn_image hσσ hσ hJ hh ν hν 1
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, Set.setOf_mem_eq] at hR
  obtain ⟨N, hN⟩ := exists_pow_mem hϖ (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  obtain ⟨s, ⟨S, hS, es⟩, -, h1⟩ := exists_move hσσ hσ (form_herm hσσ hh) hτ hτ1 hx1
    (by rw [map_sub, hσσ, neg_sub]) hσϖ hϖ (kerEnd ν) _ ⊤ (Nat.lt_succ_self _)
    _ _ hΛ hΛ' hR (reflIn_image hσσ hσ hJ hh ν hν g) ⟨N, fun v hv => by
      have := mulVec_mem (M := ϖ ^ N • (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hN hv
      rwa [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this⟩
  have := hν (g * S) (mem_GLint_of_unitary hσ hJ (g * S).2 (entries_mem fun v hv => by
    simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← es]
    exact h1 v hv))
  rwa [map_mul, hS, mul_one] at this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ hU _ hJ hh ν hν g` and use `eq_one hU hJ hh ν hν g`.
-/
theorem char_eq_one : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle, (∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1) → ∀ g, ν g = 1 :=
  fun _ _ _ _ _ _ _ _ _ _ hU _ hJ hh ν hν g => eq_one hU hJ hh ν hν g

end GlobalTheory.UnitaryCharacter
