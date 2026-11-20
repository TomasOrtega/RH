import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneB

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

/- English proof (translation)
Establish `key : ∀ q : ℕ, Nat.Coprime q p → q ≠ 0 → (q : K) * hf c v₀ x ≠ 1 → hf c v₀ y ≠ (q : K) → ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1`. Introduce `q hq hq0 hX hY`. Establish `hqK : (q : K) ≠ 0` using `by exact_mod_cast hq0`. Use `⟨(q : K) • x, hU.smul_mem (Rp_natCast q) hx, (q : K)⁻¹ • y, hU.smul_mem (Rp_inv_natCast hq) hy, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_smul_left, hf_smul_right, hxy, map_inv₀, map_natCast, mul_one, mul_inv_cancel₀ hqK]`.

Rewrite using `[hf_smul_right, map_natCast]`. Conclude with `hX`. Rewrite using `[hf_smul_right, map_inv₀, map_natCast]`. Introduce `h`. Apply `hY` to reduce the goal to its premises.

Rewrite `h` using `[inv_mul_eq_iff_eq_mul₀ hqK, mul_one]`. Conclude with `h`. Establish `hp2` using `hp.two_le`. Establish `hp1 : Nat.Coprime (p + 1) p` using `Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)`. Establish `h1 : ((p + 1 : ℕ) : K) ≠ 1` using `by exact_mod_cast (show p + 1 ≠ 1 by omega)`.

Establish `h2 : ((p + 1 : ℕ) : K) ^ 2 ≠ 1`. Conclude with `(show (p + 1) ^ 2 ≠ 1 by intro h; nlinarith)` after adjusting the coercions. Establish `h3 : ((p + 1 : ℕ) : K) ≠ ((p + 1 : ℕ) : K) ^ 2`. Conclude with `(show p + 1 ≠ (p + 1) ^ 2 by intro h; nlinarith)` after adjusting the coercions. Break down `pick (hf c v₀ x) (hf c v₀ y) ((p + 1 : ℕ) : K) h1 h2 h3 with h | h | h` into its components or cases.

Conclude with `key 1 (Nat.coprime_one_left p) one_ne_zero (by simpa using h.1) (by simpa using h.2)`. Conclude with `key (p + 1) hp1 (Nat.succ_ne_zero p) h.1 h.2`. Conclude with `key ((p + 1) ^ 2) (Nat.Coprime.pow_left 2 hp1) (pow_ne_zero _ (Nat.succ_ne_zero p)) (by exact_mod_cast h.1) (by exact_mod_cast h.2)`.
-/
theorem generic_pair {K : Type} [Field K] [NumberField K] {c : K →+* K} (hc : ∀ x, c (c x) = x)
    {p : ℕ} (hp : p.Prime) {ι : Type} [Fintype ι] {L : Set (ι → K)} (hU : Unimod K c p L)
    {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) (v₀ : ι → K) :
    ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
  have key : ∀ q : ℕ, Nat.Coprime q p → q ≠ 0 → (q : K) * hf c v₀ x ≠ 1 → hf c v₀ y ≠ (q : K) →
      ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
    intro q hq hq0 hX hY
    have hqK : (q : K) ≠ 0 := by exact_mod_cast hq0
    refine ⟨(q : K) • x, hU.smul_mem (Rp_natCast q) hx, (q : K)⁻¹ • y,
      hU.smul_mem (Rp_inv_natCast hq) hy, ?_, ?_, ?_⟩
    · rw [hf_smul_left, hf_smul_right, hxy, map_inv₀, map_natCast, mul_one, mul_inv_cancel₀ hqK]
    · rw [hf_smul_right, map_natCast]; exact hX
    · rw [hf_smul_right, map_inv₀, map_natCast]
      intro h; apply hY
      rw [inv_mul_eq_iff_eq_mul₀ hqK, mul_one] at h
      exact h
  have hp2 := hp.two_le
  have hp1 : Nat.Coprime (p + 1) p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have h1 : ((p + 1 : ℕ) : K) ≠ 1 := by exact_mod_cast (show p + 1 ≠ 1 by omega)
  have h2 : ((p + 1 : ℕ) : K) ^ 2 ≠ 1 := by
    exact_mod_cast (show (p + 1) ^ 2 ≠ 1 by intro h; nlinarith)
  have h3 : ((p + 1 : ℕ) : K) ≠ ((p + 1 : ℕ) : K) ^ 2 := by
    exact_mod_cast (show p + 1 ≠ (p + 1) ^ 2 by intro h; nlinarith)
  rcases pick (hf c v₀ x) (hf c v₀ y) ((p + 1 : ℕ) : K) h1 h2 h3 with h | h | h
  · exact key 1 (Nat.coprime_one_left p) one_ne_zero (by simpa using h.1) (by simpa using h.2)
  · exact key (p + 1) hp1 (Nat.succ_ne_zero p) h.1 h.2
  · exact key ((p + 1) ^ 2) (Nat.Coprime.pow_left 2 hp1) (pow_ne_zero _ (Nat.succ_ne_zero p))
      (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/- English proof (translation)
Simplify using `using Rp_natCast (K := K) (p := p) 2`.
-/
theorem rp_two {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (2 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 2

/- English proof (translation)
Simplify using `using Rp_natCast (K := K) (p := p) 4`.
-/
theorem rp_four {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (4 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 4

/- English proof (translation)
Establish `hne` using `ne_of_split c hs`. Take `⟨i0⟩` from `‹Nonempty ι›`. Take `⟨v₀, hv₀def⟩ : ∃ v₀ : ι → K, v₀ = Pi.single i0 1` from `⟨_, rfl⟩`. Establish `hv₀ : hf c v₀ v₀ = 1` using `by rw [hv₀def, hf_single_left]; simp`. Take `⟨x₁, hx₁, y₁, hy₁, hxy₁, hX, hY⟩` from `generic_pair hc hp hU hx hy hxy v₀`.

Take `⟨N, hN0, hNv⟩` from `hS v₀`. Establish `hNK : (N : K) ≠ 0` using `by exact_mod_cast hN0`. Establish `hp0 : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `bound : ∀ z ∈ L, Rp K p ((N : K) * (1 - hf c v₀ z))`. Introduce `z hz`.

Establish `h1` using `hU.hf_mem hz hNv`. Rewrite `h1` using `[hf_smul_right, map_natCast, hf_symm c hc v₀ z]`. Establish `h2` using `Rp_map c h1`. Rewrite `h2` using `[map_mul, map_natCast, hc]`. Rewrite using `[mul_sub, mul_one]`.

Conclude with `Rp_sub (Rp_natCast N) h2`. Take `⟨X, hXdef⟩ : ∃ X : K, X = hf c v₀ x₁` from `⟨_, rfl⟩`. Take `⟨Y, hYdef⟩ : ∃ Y : K, Y = hf c v₀ y₁` from `⟨_, rfl⟩`. Establish `hX1 : (1 : K) - X ≠ 0` using `sub_ne_zero.2 (by rw [hXdef]; exact Ne.symm hX)`. Establish `hY1 : (1 : K) - Y ≠ 0` using `sub_ne_zero.2 (by rw [hYdef]; exact Ne.symm hY)`.

Establish `hbX : Rp K p ((N : K) * (1 - X))` using `by rw [hXdef]; exact bound x₁ hx₁`. Establish `hbY : Rp K p ((N : K) * (1 - Y))` using `by rw [hYdef]; exact bound y₁ hy₁`. Take `⟨J₁, hJ₁⟩` from `dvd_pow_p c hc hK hne hp hbY (mul_ne_zero hNK hY1)`. Take `⟨J₂, hJ₂⟩` from `dvd_pow_p c hc hK hne hp hbX (mul_ne_zero hNK hX1)`. Take `⟨J, hJ⟩ : ∃ J : ℕ, J = J₁ + J₂` from `⟨_, rfl⟩`.

Take `⟨α', hα'def⟩ : ∃ α' : K, α' = (p : K) ^ J / (1 - Y)` from `⟨_, rfl⟩`. Take `⟨γ', hγ'def⟩ : ∃ γ' : K, γ' = (p : K) ^ J / (1 - X)` from `⟨_, rfl⟩`. Establish `hα : Rp K p α'`. Establish `: α' = (N : K) * (p : K) ^ J₂ * ((p : K) ^ J₁ / (N * (1 - Y)))`. Rewrite using `[hα'def, hJ, pow_add]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₂)) hJ₁`. Establish `hγ : Rp K p γ'`. Establish `: γ' = (N : K) * (p : K) ^ J₁ * ((p : K) ^ J₂ / (N * (1 - X)))`.

Rewrite using `[hγ'def, hJ, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₁)) hJ₂`. Take `⟨ε, hε, hsum, hδ⟩` from `eps c hc hK hp hs (J + 1 + 2 * N)`.

Establish `hce : c ε = 1 - ε` using `by linear_combination hsum`. Establish `hcε : Rp K p (c ε)` using `Rp_map c hε`. Take `⟨e', he'def⟩ : ∃ e' : ι → K, e' = ε • x₁ + c ε • y₁` from `⟨_, rfl⟩`. Establish `he' : e' ∈ L` using `by rw [he'def]; exact hU.add_mem (hU.smul_mem hε hx₁) (hU.smul_mem hcε hy₁)`. Take `⟨Z, hZdef⟩ : ∃ Z : K, Z = 2 - hf c x₁ x₁ - hf c y₁ y₁` from `⟨_, rfl⟩`.

Establish `hZ : Rp K p Z`. Rewrite using `[hZdef]`. Conclude with `Rp_sub (Rp_sub rp_two (hU.hf_mem hx₁ hx₁)) (hU.hf_mem hy₁ hy₁)`. Establish `hcZ : c Z = Z`. Rewrite using `[hZdef, map_sub, map_sub, map_ofNat, ← hf_symm c hc x₁ x₁, ← hf_symm c hc y₁ y₁]`.

Establish `hyx : hf c y₁ x₁ = 1` using `by rw [hf_symm c hc x₁ y₁, hxy₁, map_one]`. Take `⟨d, hddef⟩ : ∃ d : K, d = ε * c ε * Z / 2` from `⟨_, rfl⟩`. Establish `hu : hf c e' e' = 1 - 2 * d`. Rewrite using `[he'def, hddef, hZdef]`. Simplify using `only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxy₁, hyx]`.

Take the linear combination `(ε + c ε + 1) * hsum`. Establish `hd : c d = d`. Rewrite using `[hddef, map_div₀, map_mul, map_mul, hc, hcZ, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : hf c v₀ e' = c ε * X + ε * Y`.

Rewrite using `[he'def, hXdef, hYdef]`. Simplify using `only [hf_add_right, hf_smul_right, hc]`. Take `⟨β, hβdef⟩ : ∃ β : K, β = 1 - hf c v₀ e' - d` from `⟨_, rfl⟩`. Take `⟨Γ, hΓdef⟩ : ∃ Γ : K, Γ = ε * α' + c ε * γ'` from `⟨_, rfl⟩`. Establish `hΓ : Rp K p Γ` using `by rw [hΓdef]; exact Rp_add (Rp_mul hε hα) (Rp_mul hcε hγ)`.

Take `⟨C, hCdef⟩ : ∃ C : K, C = ε * c ε / (2 * N * (p : K) ^ (J + 1))` from `⟨_, rfl⟩`. Establish `hC : Rp K p C`. Establish `e1 : C = ε * c ε / (p : K) ^ (J + 1 + 2 * N) * ((p : K) ^ (2 * N) / ((2 * N : ℕ) : K))`. Rewrite using `[hCdef, show (p : K) ^ (J + 1 + 2 * N) = (p : K) ^ (J + 1) * (p : K) ^ (2 * N) by rw [pow_add]]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Conclude with `Rp_mul hδ (rp_pow_div hp (by omega) le_rfl)`. Take `⟨ω, hωdef⟩ : ∃ ω : K, ω = C * ((2 * ((N : K) * (1 - Y)) * γ' + 2 * ((N : K) * (1 - X)) * α') - ((N : K) * Z * Γ + 4 * N * (p : K) ^ J))` from `⟨_, rfl⟩`. Establish `hω : Rp K p ω`.

Rewrite using `[hωdef]`. Use `Rp_mul hC (Rp_sub (Rp_add (Rp_mul (Rp_mul rp_two hbY) hγ) (Rp_mul (Rp_mul rp_two hbX) hα)) (Rp_add (Rp_mul (Rp_mul (Rp_natCast N) hZ) hΓ) (Rp_mul (Rp_mul rp_four (Rp_natCast N)) (rp_pow (Rp_natCast p) J))))` and prove the remaining obligations. Establish `hβΓ : β * Γ = (p : K) ^ J * (1 + (p : K) * ω)`. Rewrite using `[hβdef, hB, hωdef, hCdef, hΓdef, hα'def, hγ'def, hddef, hce]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨hne1, hinv⟩` from `one_add_p_unit c hc hK hne hp hω`. Establish `hPne : (p : K) ^ J * (1 + (p : K) * ω) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hp0) hne1`. Establish `hβ0 : β ≠ 0` using `by rintro h; apply hPne; rw [← hβΓ, h, zero_mul]`. Establish `hΓ0 : Γ ≠ 0` using `by rintro h; apply hPne; rw [← hβΓ, h, mul_zero]`.

Take `⟨η, hηdef⟩ : ∃ η : K, η = d / β` from `⟨_, rfl⟩`. Establish `hβ' : β = (p : K) ^ J * (1 + (p : K) * ω) / Γ` using `by rw [eq_div_iff hΓ0]; exact hβΓ`. Establish `hηN : Rp K p (η / N)`. Establish `e1 : η / N = ((p : K) * C) * (Z * Γ) * (1 + (p : K) * ω)⁻¹`. Rewrite using `[hηdef, hβ', hddef, hCdef, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Conclude with `Rp_mul (Rp_mul (Rp_mul (Rp_natCast p) hC) (Rp_mul hZ hΓ)) hinv`. Establish `hη : Rp K p η`. Establish `: η = (N : K) * (η / N)` using `by field_simp`.

Rewrite using `[this]`. Conclude with `Rp_mul (Rp_natCast N) hηN`. Use `⟨(1 + η) • e' - η • v₀, ?_, refl_norm c hc hv₀ hu hd hβdef hβ0 hηdef⟩` and prove the remaining obligations. Establish `hv : η • v₀ = (η / N) • ((N : K) • v₀)` using `by rw [smul_smul, div_mul_cancel₀ _ hNK]`. Rewrite using `[hv]`.

Conclude with `hU.sub_mem (hU.smul_mem (Rp_add Rp_one hη) he') (hU.smul_mem hηN hNv)`.
-/
theorem normOne_of_pair {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [Nonempty ι] (L : Set (ι → K)) (hK : Module.finrank ℚ K = 2)
    (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) (hU : Unimod K c p L)
    (hS : Spans K L) {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) :
    ∃ e ∈ L, hf c e e = 1 := by
  classical
  have hne := ne_of_split c hs
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : ι → K, v₀ = Pi.single i0 1 := ⟨_, rfl⟩
  have hv₀ : hf c v₀ v₀ = 1 := by rw [hv₀def, hf_single_left]; simp
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hX, hY⟩ := generic_pair hc hp hU hx hy hxy v₀
  obtain ⟨N, hN0, hNv⟩ := hS v₀
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN0
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have bound : ∀ z ∈ L, Rp K p ((N : K) * (1 - hf c v₀ z)) := by
    intro z hz
    have h1 := hU.hf_mem hz hNv
    rw [hf_smul_right, map_natCast, hf_symm c hc v₀ z] at h1
    have h2 := Rp_map c h1
    rw [map_mul, map_natCast, hc] at h2
    rw [mul_sub, mul_one]; exact Rp_sub (Rp_natCast N) h2
  obtain ⟨X, hXdef⟩ : ∃ X : K, X = hf c v₀ x₁ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : K, Y = hf c v₀ y₁ := ⟨_, rfl⟩
  have hX1 : (1 : K) - X ≠ 0 := sub_ne_zero.2 (by rw [hXdef]; exact Ne.symm hX)
  have hY1 : (1 : K) - Y ≠ 0 := sub_ne_zero.2 (by rw [hYdef]; exact Ne.symm hY)
  have hbX : Rp K p ((N : K) * (1 - X)) := by rw [hXdef]; exact bound x₁ hx₁
  have hbY : Rp K p ((N : K) * (1 - Y)) := by rw [hYdef]; exact bound y₁ hy₁
  obtain ⟨J₁, hJ₁⟩ := dvd_pow_p c hc hK hne hp hbY (mul_ne_zero hNK hY1)
  obtain ⟨J₂, hJ₂⟩ := dvd_pow_p c hc hK hne hp hbX (mul_ne_zero hNK hX1)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = J₁ + J₂ := ⟨_, rfl⟩
  obtain ⟨α', hα'def⟩ : ∃ α' : K, α' = (p : K) ^ J / (1 - Y) := ⟨_, rfl⟩
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : K, γ' = (p : K) ^ J / (1 - X) := ⟨_, rfl⟩
  have hα : Rp K p α' := by
    have : α' = (N : K) * (p : K) ^ J₂ * ((p : K) ^ J₁ / (N * (1 - Y))) := by
      rw [hα'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₂)) hJ₁
  have hγ : Rp K p γ' := by
    have : γ' = (N : K) * (p : K) ^ J₁ * ((p : K) ^ J₂ / (N * (1 - X))) := by
      rw [hγ'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₁)) hJ₂

  obtain ⟨ε, hε, hsum, hδ⟩ := eps c hc hK hp hs (J + 1 + 2 * N)
  have hce : c ε = 1 - ε := by linear_combination hsum
  have hcε : Rp K p (c ε) := Rp_map c hε
  obtain ⟨e', he'def⟩ : ∃ e' : ι → K, e' = ε • x₁ + c ε • y₁ := ⟨_, rfl⟩
  have he' : e' ∈ L := by rw [he'def]; exact hU.add_mem (hU.smul_mem hε hx₁) (hU.smul_mem hcε hy₁)
  obtain ⟨Z, hZdef⟩ : ∃ Z : K, Z = 2 - hf c x₁ x₁ - hf c y₁ y₁ := ⟨_, rfl⟩
  have hZ : Rp K p Z := by
    rw [hZdef]; exact Rp_sub (Rp_sub rp_two (hU.hf_mem hx₁ hx₁)) (hU.hf_mem hy₁ hy₁)
  have hcZ : c Z = Z := by
    rw [hZdef, map_sub, map_sub, map_ofNat, ← hf_symm c hc x₁ x₁, ← hf_symm c hc y₁ y₁]
  have hyx : hf c y₁ x₁ = 1 := by rw [hf_symm c hc x₁ y₁, hxy₁, map_one]
  obtain ⟨d, hddef⟩ : ∃ d : K, d = ε * c ε * Z / 2 := ⟨_, rfl⟩
  have hu : hf c e' e' = 1 - 2 * d := by
    rw [he'def, hddef, hZdef]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxy₁, hyx]
    linear_combination (ε + c ε + 1) * hsum
  have hd : c d = d := by
    rw [hddef, map_div₀, map_mul, map_mul, hc, hcZ, map_ofNat]; ring
  have hB : hf c v₀ e' = c ε * X + ε * Y := by
    rw [he'def, hXdef, hYdef]; simp only [hf_add_right, hf_smul_right, hc]
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = 1 - hf c v₀ e' - d := ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : K, Γ = ε * α' + c ε * γ' := ⟨_, rfl⟩
  have hΓ : Rp K p Γ := by rw [hΓdef]; exact Rp_add (Rp_mul hε hα) (Rp_mul hcε hγ)
  obtain ⟨C, hCdef⟩ : ∃ C : K, C = ε * c ε / (2 * N * (p : K) ^ (J + 1)) := ⟨_, rfl⟩
  have hC : Rp K p C := by
    have e1 : C = ε * c ε / (p : K) ^ (J + 1 + 2 * N) * ((p : K) ^ (2 * N) / ((2 * N : ℕ) : K)) := by
      rw [hCdef, show (p : K) ^ (J + 1 + 2 * N) = (p : K) ^ (J + 1) * (p : K) ^ (2 * N) by rw [pow_add]]
      push_cast; field_simp
    rw [e1]
    exact Rp_mul hδ (rp_pow_div hp (by omega) le_rfl)
  obtain ⟨ω, hωdef⟩ : ∃ ω : K, ω = C * ((2 * ((N : K) * (1 - Y)) * γ' + 2 * ((N : K) * (1 - X)) * α')
      - ((N : K) * Z * Γ + 4 * N * (p : K) ^ J)) := ⟨_, rfl⟩
  have hω : Rp K p ω := by
    rw [hωdef]
    refine Rp_mul hC (Rp_sub (Rp_add (Rp_mul (Rp_mul rp_two hbY) hγ) (Rp_mul (Rp_mul rp_two hbX) hα))
      (Rp_add (Rp_mul (Rp_mul (Rp_natCast N) hZ) hΓ)
        (Rp_mul (Rp_mul rp_four (Rp_natCast N)) (rp_pow (Rp_natCast p) J))))
  have hβΓ : β * Γ = (p : K) ^ J * (1 + (p : K) * ω) := by
    rw [hβdef, hB, hωdef, hCdef, hΓdef, hα'def, hγ'def, hddef, hce]
    field_simp
    ring
  obtain ⟨hne1, hinv⟩ := one_add_p_unit c hc hK hne hp hω
  have hPne : (p : K) ^ J * (1 + (p : K) * ω) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hne1
  have hβ0 : β ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, zero_mul]
  have hΓ0 : Γ ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, mul_zero]
  obtain ⟨η, hηdef⟩ : ∃ η : K, η = d / β := ⟨_, rfl⟩
  have hβ' : β = (p : K) ^ J * (1 + (p : K) * ω) / Γ := by rw [eq_div_iff hΓ0]; exact hβΓ
  have hηN : Rp K p (η / N) := by
    have e1 : η / N = ((p : K) * C) * (Z * Γ) * (1 + (p : K) * ω)⁻¹ := by
      rw [hηdef, hβ', hddef, hCdef, pow_succ]
      field_simp
    rw [e1]
    exact Rp_mul (Rp_mul (Rp_mul (Rp_natCast p) hC) (Rp_mul hZ hΓ)) hinv
  have hη : Rp K p η := by
    have : η = (N : K) * (η / N) := by field_simp
    rw [this]; exact Rp_mul (Rp_natCast N) hηN
  refine ⟨(1 + η) • e' - η • v₀, ?_, refl_norm c hc hv₀ hu hd hβdef hβ0 hηdef⟩
  have hv : η • v₀ = (η / N) • ((N : K) • v₀) := by rw [smul_smul, div_mul_cancel₀ _ hNK]
  rw [hv]
  exact hU.sub_mem (hU.smul_mem (Rp_add Rp_one hη) he') (hU.smul_mem hηN hNv)

end PI.KLW.NO

namespace PI.KLW

/- English proof (translation)
Introduce `K _ _ c p ι _ _ L hK hc hp hs hU hS`. Take `⟨x, hx, y, hy, hxy⟩` from `h K c p ι L hK hc hp hs hU hS`. Conclude with `NO.normOne_of_pair c p L hK hc hp hs hU hS hx hy hxy`.
-/
theorem normOne_of (h : PairOne) : NormOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hU hS
  obtain ⟨x, hx, y, hy, hxy⟩ := h K c p ι L hK hc hp hs hU hS
  exact NO.normOne_of_pair c p L hK hc hp hs hU hS hx hy hxy

end PI.KLW
