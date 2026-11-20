import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.IsUnimodularCliffordLatticeStabilizer

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
  {c t s : K} {ε : Oˣ} {β : Etau K τ}

/- English proof (translation)
Rewrite using `[Module.finrank_prod, Module.finrank_self]`. Conclude with `congrArg (1 + ·) (QuadraticAlgebra.finrank_eq_two (-1 : K) τ)`.
-/
theorem finrank_V : Module.finrank K (K × Etau K τ) = 3 := by
  rw [Module.finrank_prod, Module.finrank_self]
  exact congrArg (1 + ·) (QuadraticAlgebra.finrank_eq_two (-1 : K) τ)

/- English proof (translation)
Take `⟨s, hs⟩` from `hS.fg`. Establish `hd : ∀ y : K × Etau K τ, y ∈ Submodule.span O (s : Set (K × Etau K τ)) ↔ ∀ x ∈ Submodule.span O (s : Set (K × Etau K τ)), Bf τ c t x y ∈ (algebraMap O K).range`. Introduce `y`. Use `hS.dual y` as an intermediate fact. Rewrite `this` using `[hs]`.

Conclude with `this`. Take `⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_frame L finrank_V (Bf_symm c t) (Submodule.fg_span (Finset.finite_toSet s)) hd`. Rewrite using `[hs]`. Conclude with `⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩`.
-/
theorem Uni.frame (L : IsLoc O Δ) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, Bf τ c t e e = 0 ∧ Bf τ c t f f = 0 ∧ Bf τ c t e f = 1 ∧ Bf τ c t e h = 0 ∧ Bf τ c t f h = 0 ∧
      Bf τ c t h h = algebraMap O K η ∧ ∀ v ∈ S, ∃ a b d : O, v = a • e + b • f + d • h := by
  obtain ⟨s, hs⟩ := hS.fg
  have hd : ∀ y : K × Etau K τ, y ∈ Submodule.span O (s : Set (K × Etau K τ)) ↔
      ∀ x ∈ Submodule.span O (s : Set (K × Etau K τ)), Bf τ c t x y ∈ (algebraMap O K).range := by
    intro y
    have := hS.dual y
    rw [hs] at this
    exact this
  obtain ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_frame L finrank_V (Bf_symm c t) (Submodule.fg_span (Finset.finite_toSet s)) hd
  rw [hs]
  exact ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩

/- English proof (translation)
Take `⟨e, heS, f, hfS, h, hhS, η, hee, hff, hef, heh, hfh, hhh, hspan⟩` from `Uni.frame L hS`. Use `haveI := L.frac`. Establish `h2O : IsUnit (2 : O)` using `L.two`. Establish `h2 : (2 : K) ≠ 0`. Use `(h2O.map (algebraMap O K)).ne_zero` as an intermediate fact.

Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Use `set E : K := algebraMap O K ε with hE`. Establish `hE0 : E ≠ 0` using `(ε.isUnit.map (algebraMap O K)).ne_zero`. Establish `hinvE : algebraMap O K ↑ε⁻¹ * E = 1`. Rewrite using `[hE, ← map_mul, Units.inv_mul, map_one]`.

Establish `anti : ∀ v w y, E • (psi s β v (psi s β w y) + psi s β w (psi s β v y)) = (2 * Bf τ c t v w) • y` using `fun v w y => psi_anti hc hβ v w y`. Establish `sq0 : ∀ v, Bf τ c t v v = 0 → ∀ y, psi s β v (psi s β v y) = 0`. Introduce `v hv y`. Use `anti v v y` as an intermediate fact. Rewrite `this` using `[hv, mul_zero, zero_smul, ← two_smul K, smul_smul, smul_eq_zero]`.

Break down `this with h0 | h0` into its components or cases. Conclude with `absurd h0 (mul_ne_zero hE0 h2)`. Conclude with `h0`. Establish `orth : ∀ v w, Bf τ c t v w = 0 → ∀ y, psi s β v (psi s β w y) = -psi s β w (psi s β v y)`. Introduce `v w hvw y`.

Use `anti v w y` as an intermediate fact. Rewrite `this` using `[hvw, mul_zero, zero_smul, smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases. Conclude with `absurd h0 hE0`. Conclude with `eq_neg_of_add_eq_zero_left h0`.

Use `set κ : K := algebraMap O K (↑ε⁻¹ * 2) with hκ`. Establish `hκ0 : κ ≠ 0`. Rewrite using `[hκ, map_mul, map_ofNat]`. Conclude with `mul_ne_zero (ε⁻¹.isUnit.map (algebraMap O K)).ne_zero h2`. Establish `ef : ∀ y, psi s β e (psi s β f y) + psi s β f (psi s β e y) = κ • y`.

Introduce `y`. Use `anti e f y` as an intermediate fact. Rewrite `this` using `[hef, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinvE, one_smul]`.

Use `_ = κ • y := by rw [mul_smul, this, smul_smul, hκ, map_mul, map_ofNat]`. Choose the witnesses or unpack the hypotheses as in `⟨w0, hw0⟩ : ∃ w0, psi s β e w0 ≠ 0 := by`. Assume the negation of the conclusion as `H`. Use `push_neg at H`. Use `ef 1` as an intermediate fact.

Rewrite `this` using `[H (psi s β f 1), H 1, map_zero, add_zero, eq_comm, smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases. Conclude with `hκ0 h0`. Conclude with `one_ne_zero h0`. Take `⟨y1, hy1d⟩ : ∃ y1, y1 = psi s β e w0` from `⟨_, rfl⟩`.

Take `⟨y2, hy2d⟩ : ∃ y2, y2 = psi s β f y1` from `⟨_, rfl⟩`. Establish `hy1 : y1 ≠ 0` using `hy1d ▸ hw0`. Establish `pe1 : psi s β e y1 = 0`. Rewrite using `[hy1d]`. Conclude with `sq0 e hee w0`.

Establish `pf2 : psi s β f y2 = 0`. Rewrite using `[hy2d]`. Conclude with `sq0 f hff y1`. Establish `pf1 : psi s β f y1 = y2` using `hy2d.symm`. Establish `pe2 : psi s β e y2 = κ • y1`.

Use `ef y1` as an intermediate fact. Rewrite `this` using `[pe1, map_zero, add_zero, ← hy2d]`. Conclude with `this`. Establish `hind : (y2 * star y1).im ≠ 0`. Introduce `H0`.

Establish `H1 : y2.im * y1.re = y2.re * y1.im`. Simplify using `only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] at H0`. Take the linear combination `H0`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : K, y2 = l • y1 := by`. Distinguish the cases in `hr : y1.re = 0`.

Establish `hi : y1.im ≠ 0` using `fun hi => hy1 (QuadraticAlgebra.ext hr hi)`. Use `⟨y2.im / y1.im, ?_⟩` and prove the remaining obligations. Rewrite `H1` using `[hr, mul_zero]`. Use `ext`. Simplify using `only [QuadraticAlgebra.re_smul, smul_eq_mul, hr, mul_zero]`.

Break down `mul_eq_zero.mp H1.symm with h0 | h0` into its components or cases. Conclude with `h0`. Conclude with `absurd h0 hi`. Simplify using `only [QuadraticAlgebra.im_smul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Use `⟨y2.re / y1.re, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [QuadraticAlgebra.re_smul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [QuadraticAlgebra.im_smul, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `H1`. Use `pe2` as an intermediate fact. Rewrite `this` using `[hl, map_smul, pe1, smul_zero, eq_comm, smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases.

Conclude with `hκ0 h0`. Conclude with `hy1 h0`. Establish `hhe : Bf τ c t h e = 0` using `by rw [Bf_symm, heh]`. Establish `hhf : Bf τ c t h f = 0` using `by rw [Bf_symm, hfh]`. Choose the witnesses or unpack the hypotheses as in `⟨μ, hμ⟩ : ∃ μ : K, psi s β h y1 = μ • y1 := by`.

Take `⟨α, γ, hz⟩ : ∃ α γ : K, psi s β h y1 = α • y1 + γ • y2` from `⟨_, _, coord hind _⟩`. Establish `hpz : psi s β e (psi s β h y1) = 0`. Rewrite using `[orth e h heh, pe1, map_zero, neg_zero]`. Rewrite `hpz` using `[hz, map_add, map_smul, map_smul, pe1, pe2, smul_zero, zero_add, smul_smul, smul_eq_zero]`. Break down `hpz with h0 | h0` into its components or cases.

Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Conclude with `⟨α, by rw [hz, h1, zero_smul, add_zero]⟩`. Conclude with `absurd h1 hκ0`. Conclude with `absurd h0 hy1`. Establish `ph2 : psi s β h y2 = -(μ • y2)`.

Rewrite using `[hy2d, orth h f hhf, hμ, map_smul]`. Establish `hμ2 : E * (μ * μ) = algebraMap O K η`. Use `anti h h y1` as an intermediate fact. Rewrite `this` using `[hhh, hμ, map_smul, hμ, smul_smul, ← two_smul K, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero]`. Break down `this with h0 | h0` into its components or cases.

Establish `h0' : 2 * (E * (μ * μ) - algebraMap O K η) = 0` using `by linear_combination h0`. Break down `mul_eq_zero.mp h0' with h1 | h1` into its components or cases. Conclude with `absurd h1 h2`. Conclude with `sub_eq_zero.mp h1`. Conclude with `absurd h0 hy1`.

Choose the witnesses or unpack the hypotheses as in `⟨mμ, hmμ⟩ : ∃ mμ : O, algebraMap O K mμ = μ := by`. Establish `hint : IsIntegral O μ`. Use `⟨Polynomial.X ^ 2 - Polynomial.C (((ε⁻¹ : Oˣ) : O) * (η : O)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]`. Rewrite using `[map_mul, ← hμ2, ← mul_assoc, hinvE, one_mul, sq, sub_self]`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.mp hint`. Take `⟨Λ, hΛ⟩ : ∃ Λ : Set (Etau K τ), ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y1 + algebraMap O K q • y2` from `⟨_, fun _ => Iff.rfl⟩`. Establish `hy1Λ : y1 ∈ Λ` using `(hΛ _).mpr ⟨1, 0, by simp⟩`. Establish `hy2Λ : y2 ∈ Λ` using `(hΛ _).mpr ⟨0, 1, by simp⟩`. Establish `hLat : IsLat O τ Λ`.

Use `⟨⟨{y1, y2}, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Rewrite using `[hΛ, Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, rfl⟩`.

Conclude with `⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩`. Introduce and unpack `⟨p, q, rfl⟩`. Conclude with `⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩`. Rewrite using `[eq_top_iff]`. Introduce `b _`.

Rewrite using `[coord hind b]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span hy1Λ)) (Submodule.smul_mem _ _ (Submodule.subset_span hy2Λ))`. Establish `hsub : S ⊆ S0 s β Λ`. Introduce `v hv`. Take `⟨a, b, d, rfl⟩` from `hspan v hv`.

Rewrite using `[mem_S0_of_sum_eq hΛ, ← algebraMap_smul K a e, ← algebraMap_smul K b f, ← algebraMap_smul K d h]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, pe1, pe2, pf1, pf2, hμ, ph2]`. Prove the components needed by the constructor for the conclusion. Use `(hΛ _).mpr ⟨d * mμ, b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hmμ]`.

Use `module`. Use `(hΛ _).mpr ⟨a * (↑ε⁻¹ * 2), -(d * mμ), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hκ, map_neg, map_mul, hmμ]`. Use `module`. Establish `hsup : S0 s β Λ ⊆ S`.

Introduce `y hy`. Rewrite using `[hS.dual]`. Introduce `x hx`. Conclude with `Bf_int h2O hc hβ hind hΛ (hsub hx) hy`. Conclude with `⟨Λ, hLat, Set.Subset.antisymm hsub hsup⟩`.
-/
theorem exists_lat (L : IsLoc O Δ) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ Λ, IsLat O τ Λ ∧ S = S0 s β Λ := by
  classical
  obtain ⟨e, heS, f, hfS, h, hhS, η, hee, hff, hef, heh, hfh, hhh, hspan⟩ := Uni.frame L hS
  haveI := L.frac
  have h2O : IsUnit (2 : O) := L.two
  have h2 : (2 : K) ≠ 0 := by
    have := (h2O.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  set E : K := algebraMap O K ε with hE
  have hE0 : E ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hinvE : algebraMap O K ↑ε⁻¹ * E = 1 := by
    rw [hE, ← map_mul, Units.inv_mul, map_one]
  have anti : ∀ v w y, E • (psi s β v (psi s β w y) + psi s β w (psi s β v y))
      = (2 * Bf τ c t v w) • y := fun v w y => psi_anti hc hβ v w y
  have sq0 : ∀ v, Bf τ c t v v = 0 → ∀ y, psi s β v (psi s β v y) = 0 := by
    intro v hv y
    have := anti v v y
    rw [hv, mul_zero, zero_smul, ← two_smul K, smul_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (mul_ne_zero hE0 h2)
    · exact h0
  have orth : ∀ v w, Bf τ c t v w = 0 → ∀ y, psi s β v (psi s β w y) = -psi s β w (psi s β v y) := by
    intro v w hvw y
    have := anti v w y
    rw [hvw, mul_zero, zero_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 hE0
    · exact eq_neg_of_add_eq_zero_left h0
  set κ : K := algebraMap O K (↑ε⁻¹ * 2) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, map_mul, map_ofNat]
    exact mul_ne_zero (ε⁻¹.isUnit.map (algebraMap O K)).ne_zero h2
  have ef : ∀ y, psi s β e (psi s β f y) + psi s β f (psi s β e y) = κ • y := by
    intro y
    have := anti e f y
    rw [hef, mul_one] at this
    calc _ = (algebraMap O K ↑ε⁻¹ * E) • (psi s β e (psi s β f y) + psi s β f (psi s β e y)) := by
          rw [hinvE, one_smul]
      _ = κ • y := by rw [mul_smul, this, smul_smul, hκ, map_mul, map_ofNat]
  obtain ⟨w0, hw0⟩ : ∃ w0, psi s β e w0 ≠ 0 := by
    by_contra H
    push_neg at H
    have := ef 1
    rw [H (psi s β f 1), H 1, map_zero, add_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact one_ne_zero h0
  obtain ⟨y1, hy1d⟩ : ∃ y1, y1 = psi s β e w0 := ⟨_, rfl⟩
  obtain ⟨y2, hy2d⟩ : ∃ y2, y2 = psi s β f y1 := ⟨_, rfl⟩
  have hy1 : y1 ≠ 0 := hy1d ▸ hw0
  have pe1 : psi s β e y1 = 0 := by
    rw [hy1d]
    exact sq0 e hee w0
  have pf2 : psi s β f y2 = 0 := by
    rw [hy2d]
    exact sq0 f hff y1
  have pf1 : psi s β f y1 = y2 := hy2d.symm
  have pe2 : psi s β e y2 = κ • y1 := by
    have := ef y1
    rw [pe1, map_zero, add_zero, ← hy2d] at this
    exact this
  have hind : (y2 * star y1).im ≠ 0 := by
    intro H0
    have H1 : y2.im * y1.re = y2.re * y1.im := by
      simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] at H0
      linear_combination H0
    obtain ⟨l, hl⟩ : ∃ l : K, y2 = l • y1 := by
      by_cases hr : y1.re = 0
      · have hi : y1.im ≠ 0 := fun hi => hy1 (QuadraticAlgebra.ext hr hi)
        refine ⟨y2.im / y1.im, ?_⟩
        rw [hr, mul_zero] at H1
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul, hr, mul_zero]
          rcases mul_eq_zero.mp H1.symm with h0 | h0
          · exact h0
          · exact absurd h0 hi
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
      · refine ⟨y2.re / y1.re, ?_⟩
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul]
          field_simp
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
          linear_combination H1
    have := pe2
    rw [hl, map_smul, pe1, smul_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact hy1 h0
  have hhe : Bf τ c t h e = 0 := by rw [Bf_symm, heh]
  have hhf : Bf τ c t h f = 0 := by rw [Bf_symm, hfh]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, psi s β h y1 = μ • y1 := by
    obtain ⟨α, γ, hz⟩ : ∃ α γ : K, psi s β h y1 = α • y1 + γ • y2 := ⟨_, _, coord hind _⟩
    have hpz : psi s β e (psi s β h y1) = 0 := by
      rw [orth e h heh, pe1, map_zero, neg_zero]
    rw [hz, map_add, map_smul, map_smul, pe1, pe2, smul_zero, zero_add, smul_smul, smul_eq_zero] at hpz
    rcases hpz with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact ⟨α, by rw [hz, h1, zero_smul, add_zero]⟩
      · exact absurd h1 hκ0
    · exact absurd h0 hy1
  have ph2 : psi s β h y2 = -(μ • y2) := by
    rw [hy2d, orth h f hhf, hμ, map_smul]
  have hμ2 : E * (μ * μ) = algebraMap O K η := by
    have := anti h h y1
    rw [hhh, hμ, map_smul, hμ, smul_smul, ← two_smul K, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul,
      smul_eq_zero] at this
    rcases this with h0 | h0
    · have h0' : 2 * (E * (μ * μ) - algebraMap O K η) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp h0' with h1 | h1
      · exact absurd h1 h2
      · exact sub_eq_zero.mp h1
    · exact absurd h0 hy1
  obtain ⟨mμ, hmμ⟩ : ∃ mμ : O, algebraMap O K mμ = μ := by
    have hint : IsIntegral O μ := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (((ε⁻¹ : Oˣ) : O) * (η : O)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [map_mul, ← hμ2, ← mul_assoc, hinvE, one_mul, sq, sub_self]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Set (Etau K τ), ∀ b, b ∈ Λ ↔
      ∃ p q : O, b = algebraMap O K p • y1 + algebraMap O K q • y2 := ⟨_, fun _ => Iff.rfl⟩
  have hy1Λ : y1 ∈ Λ := (hΛ _).mpr ⟨1, 0, by simp⟩
  have hy2Λ : y2 ∈ Λ := (hΛ _).mpr ⟨0, 1, by simp⟩
  have hLat : IsLat O τ Λ := by
    refine ⟨⟨{y1, y2}, ?_⟩, ?_⟩
    · ext b
      rw [hΛ, Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_pair]
      constructor
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
    · rw [eq_top_iff]
      intro b _
      rw [coord hind b]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span hy1Λ))
        (Submodule.smul_mem _ _ (Submodule.subset_span hy2Λ))
  have hsub : S ⊆ S0 s β Λ := by
    intro v hv
    obtain ⟨a, b, d, rfl⟩ := hspan v hv
    rw [mem_S0_of_sum_eq hΛ, ← algebraMap_smul K a e, ← algebraMap_smul K b f, ← algebraMap_smul K d h]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, pe1, pe2, pf1, pf2, hμ, ph2]
    constructor
    · refine (hΛ _).mpr ⟨d * mμ, b, ?_⟩
      rw [map_mul, hmμ]
      module
    · refine (hΛ _).mpr ⟨a * (↑ε⁻¹ * 2), -(d * mμ), ?_⟩
      rw [map_mul, ← hκ, map_neg, map_mul, hmμ]
      module
  have hsup : S0 s β Λ ⊆ S := by
    intro y hy
    rw [hS.dual]
    intro x hx
    exact Bf_int h2O hc hβ hind hΛ (hsub hx) hy
  exact ⟨Λ, hLat, Set.Subset.antisymm hsub hsup⟩

/- English proof (translation)
Take `⟨y₁, y₂, hy, hb⟩` from `lat_basis L hD hΛ`. Establish `h2 : (2 : K) ≠ 0`. Use `(L.two.map (algebraMap O K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨e, f, h, he1, he2, hf1, hf2, -, -⟩` from `exists_efh hD h2 hs hu hy`.

Establish `hy1 : y₁ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hy`. Establish `h0 : (0 : Etau K τ) ∈ Λ` using `(hb 0).mpr ⟨0, 0, by simp⟩`. Establish `hy1m : y₁ ∈ Λ` using `(hb _).mpr ⟨1, 0, by simp⟩`.

Establish `hy2m : y₂ ∈ Λ` using `(hb _).mpr ⟨0, 1, by simp⟩`. Establish `heS : e ∈ S0 s β Λ` using `(mem_S0_of_sum_eq hb).mpr ⟨by rw [he1]; exact h0, by rw [he2]; exact hy1m⟩`. Establish `hfS : f ∈ S0 s β Λ` using `(mem_S0_of_sum_eq hb).mpr ⟨by rw [hf1]; exact hy2m, by rw [hf2]; exact h0⟩`. Rewrite `heS`, `hfS` using `[hS]`. Take `⟨u, hu'⟩` from `hΛ'.fg`.

Establish `hspan` using `hΛ'.span`. Substitute `hu'` using the available equality. Use `set M' : Submodule O (Etau K τ) := Submodule.span O (u : Set (Etau K τ)) with hM'`. Use `set g : K →ₗ[O] Etau K τ := (LinearMap.toSpanSingleton K (Etau K τ) y₁).restrictScalars O with hg`. Establish `hgp : ∀ p, g p = p • y₁` using `fun p => rfl`.

Use `set J : Submodule O K := M'.comap g with hJ`. Establish `hmemJ : ∀ p, p ∈ J ↔ p • y₁ ∈ M'` using `fun p => by rw [hJ, Submodule.mem_comap, hgp]`. Establish `hginj : Function.Injective g`. Introduce `p q hpq`. Rewrite `hpq` using `[hgp, hgp]`.

Conclude with `smul_left_injective K hy1 hpq`. Establish `hJfg : J.FG` using `Submodule.fg_of_fg_map_injective g hginj (Submodule.FG.of_le (Submodule.fg_span (Finset.finite_toSet u)) (Submodule.map_comap_le g M'))`. Use `haveI := L.frac`. Take `⟨k, hk⟩` from `(FractionalIdeal.isPrincipal (⟨J, FractionalIdeal.isFractional_of_fg hJfg⟩ : FractionalIdeal (nonZeroDivisors O) K)).principal`. Express the relevant statement in the definitionally equal form `J = Submodule.span O {k} at hk`.

Establish `hcoef : ∀ b ∈ M', ∀ p q : K, b = p • y₁ + q • y₂ → p ∈ J ∧ q ∈ J`. Introduce `b hbM p q hbpq`. Establish `hE : ∀ y ∈ M', psi s β e y ∈ M'` using `heS`. Establish `hF : ∀ y ∈ M', psi s β f y ∈ M'` using `hfS`. Establish `h1` using `hE _ (hF _ hbM)`.

Establish `h2'` using `hE _ hbM`. Rewrite `h1`, `h2'` using `[hbpq]`. Simplify using `only [map_add, map_smul, he1, he2, hf1, hf2, smul_zero, add_zero, zero_add] at h1 h2'`. Conclude with `⟨(hmemJ p).mpr h1, (hmemJ q).mpr h2'⟩`. Establish `hback : ∀ p q : K, p ∈ J → q ∈ J → p • y₁ + q • y₂ ∈ M'`.

Introduce `p q hp hq`. Establish `hF : ∀ y ∈ M', psi s β f y ∈ M'` using `hfS`. Use `hF _ ((hmemJ q).mp hq)` as an intermediate fact. Simplify using `only [map_smul, hf1] at this`. Conclude with `M'.add_mem ((hmemJ p).mp hp) this`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Establish `hsub : (M' : Set (Etau K τ)) ⊆ {0}`. Introduce `b hbM`. Establish `hc` using `coord hy b`.

Take `⟨hp, hq⟩` from `hcoef b hbM _ _ hc`. Rewrite `hp`, `hq` using `[hk, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot]`. Rewrite using `[hc, hp, hq]`. Simplify using the standard rewrite rules. Establish `: Submodule.span K (M' : Set (Etau K τ)) ≤ ⊥`.

Rewrite using `[Submodule.span_le]`. Simplify using `using hsub`. Rewrite `this` using `[hspan, le_bot_iff]`. Conclude with `hy1 (by simpa [this] using (Submodule.mem_top : y₁ ∈ (⊤ : Submodule K (Etau K τ))))`. Use `⟨Units.mk0 k hk0, ?_⟩` and prove the remaining obligations.

Use extensionality with `b`. Simplify using `only [Units.val_mk0, Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hbM`. Establish `hc` using `coord hy b`.

Take `⟨hp, hq⟩` from `hcoef b hbM _ _ hc`. Rewrite `hp`, `hq` using `[hk, Submodule.mem_span_singleton]`. Take `⟨a, ha⟩` from `hp`. Take `⟨a', ha'⟩` from `hq`. Use `⟨algebraMap O K a • y₁ + algebraMap O K a' • y₂, (hb _).mpr ⟨a, a', rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc, ← ha, ← ha', smul_add, smul_smul, smul_smul, Algebra.smul_def a k, Algebra.smul_def a' k, mul_comm k, mul_comm k]`. Introduce and unpack `⟨y, hyΛ, rfl⟩`. Take `⟨p, q, rfl⟩` from `(hb y).mp hyΛ`. Rewrite using `[smul_add, smul_smul, smul_smul]`. Apply `hback` to reduce the goal to its premises.

Rewrite using `[hk, Submodule.mem_span_singleton]`. Conclude with `⟨p, by rw [Algebra.smul_def, mul_comm]⟩`. Rewrite using `[hk, Submodule.mem_span_singleton]`. Conclude with `⟨q, by rw [Algebra.smul_def, mul_comm]⟩`.
-/
theorem lattice_homothety_of_eq_unimodular (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) {Λ Λ' : Set (Etau K τ)} (hΛ : IsLat O τ Λ) (hΛ' : IsLat O τ Λ')
    (hS : S0 s β Λ = S0 s β Λ') : ∃ k : Kˣ, Λ' = ((k : K) • ·) '' Λ := by
  obtain ⟨y₁, y₂, hy, hb⟩ := lat_basis L hD hΛ
  have h2 : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨e, f, h, he1, he2, hf1, hf2, -, -⟩ := exists_efh hD h2 hs hu hy
  have hy1 : y₁ ≠ 0 := by
    rintro rfl
    simp at hy
  have h0 : (0 : Etau K τ) ∈ Λ := (hb 0).mpr ⟨0, 0, by simp⟩
  have hy1m : y₁ ∈ Λ := (hb _).mpr ⟨1, 0, by simp⟩
  have hy2m : y₂ ∈ Λ := (hb _).mpr ⟨0, 1, by simp⟩
  have heS : e ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [he1]; exact h0, by rw [he2]; exact hy1m⟩
  have hfS : f ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [hf1]; exact hy2m, by rw [hf2]; exact h0⟩
  rw [hS] at heS hfS
  obtain ⟨u, hu'⟩ := hΛ'.fg
  have hspan := hΛ'.span
  subst hu'
  set M' : Submodule O (Etau K τ) := Submodule.span O (u : Set (Etau K τ)) with hM'
  set g : K →ₗ[O] Etau K τ := (LinearMap.toSpanSingleton K (Etau K τ) y₁).restrictScalars O with hg
  have hgp : ∀ p, g p = p • y₁ := fun p => rfl
  set J : Submodule O K := M'.comap g with hJ
  have hmemJ : ∀ p, p ∈ J ↔ p • y₁ ∈ M' := fun p => by rw [hJ, Submodule.mem_comap, hgp]
  have hginj : Function.Injective g := by
    intro p q hpq
    rw [hgp, hgp] at hpq
    exact smul_left_injective K hy1 hpq
  have hJfg : J.FG := Submodule.fg_of_fg_map_injective g hginj
    (Submodule.FG.of_le (Submodule.fg_span (Finset.finite_toSet u)) (Submodule.map_comap_le g M'))
  haveI := L.frac
  obtain ⟨k, hk⟩ := (FractionalIdeal.isPrincipal
    (⟨J, FractionalIdeal.isFractional_of_fg hJfg⟩ : FractionalIdeal (nonZeroDivisors O) K)).principal
  change J = Submodule.span O {k} at hk
  have hcoef : ∀ b ∈ M', ∀ p q : K, b = p • y₁ + q • y₂ → p ∈ J ∧ q ∈ J := by
    intro b hbM p q hbpq
    have hE : ∀ y ∈ M', psi s β e y ∈ M' := heS
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have h1 := hE _ (hF _ hbM)
    have h2' := hE _ hbM
    rw [hbpq] at h1 h2'
    simp only [map_add, map_smul, he1, he2, hf1, hf2, smul_zero, add_zero, zero_add] at h1 h2'
    exact ⟨(hmemJ p).mpr h1, (hmemJ q).mpr h2'⟩
  have hback : ∀ p q : K, p ∈ J → q ∈ J → p • y₁ + q • y₂ ∈ M' := by
    intro p q hp hq
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have := hF _ ((hmemJ q).mp hq)
    simp only [map_smul, hf1] at this
    exact M'.add_mem ((hmemJ p).mp hp) this
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hsub : (M' : Set (Etau K τ)) ⊆ {0} := by
      intro b hbM
      have hc := coord hy b
      obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
      rw [hk, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hp hq
      rw [hc, hp, hq]
      simp
    have : Submodule.span K (M' : Set (Etau K τ)) ≤ ⊥ := by
      rw [Submodule.span_le]
      simpa using hsub
    rw [hspan, le_bot_iff] at this
    exact hy1 (by simpa [this] using (Submodule.mem_top : y₁ ∈ (⊤ : Submodule K (Etau K τ))))
  refine ⟨Units.mk0 k hk0, ?_⟩
  ext b
  simp only [Units.val_mk0, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hbM
    have hc := coord hy b
    obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
    rw [hk, Submodule.mem_span_singleton] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    refine ⟨algebraMap O K a • y₁ + algebraMap O K a' • y₂, (hb _).mpr ⟨a, a', rfl⟩, ?_⟩
    rw [hc, ← ha, ← ha', smul_add, smul_smul, smul_smul, Algebra.smul_def a k, Algebra.smul_def a' k,
      mul_comm k, mul_comm k]
  · rintro ⟨y, hyΛ, rfl⟩
    obtain ⟨p, q, rfl⟩ := (hb y).mp hyΛ
    rw [smul_add, smul_smul, smul_smul]
    apply hback
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨p, by rw [Algebra.smul_def, mul_comm]⟩
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨q, by rw [Algebra.smul_def, mul_comm]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Establish `hq : quo z * quo z⁻¹ = 1`. Simplify using `only [quo, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 1 := by simp`. Establish `hw2 : ∀ w : K × Etau K τ, w = ((w.1, quo z⁻¹ * w.2).1, quo z * (w.1, quo z⁻¹ * w.2).2)`. Introduce `w`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `show w.2 = quo z * (quo z⁻¹ * w.2)`.

Rewrite using `[← mul_assoc, hq, one_mul]`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Use `⟨(w.1, quo z⁻¹ * w.2), ?_, (hw2 w).symm⟩` and prove the remaining obligations.

Introduce `y hy`. Take `⟨x, hx, hxy⟩` from `hw ((z : Etau K τ) * y) ⟨y, hy, rfl⟩`. Rewrite `hxy` using `[hw2 w, psi_quo]`. Use `(Units.mul_right_inj z).mp hxy` as an intermediate fact. Rewrite using `[← this]`.

Conclude with `hx`. Introduce and unpack `⟨v, hv, rfl⟩ _ ⟨y, hy, rfl⟩`. Rewrite using `[psi_quo]`. Conclude with `⟨_, hv y hy, rfl⟩`.
-/
theorem unimodular_image_mul_unit (z : (Etau K τ)ˣ) (Λ : Set (Etau K τ)) :
    S0 s β (((z : Etau K τ) * ·) '' Λ) = (fun v => (v.1, quo z * v.2)) '' S0 s β Λ := by
  have hq : quo z * quo z⁻¹ = 1 := by
    simp only [quo, inv_inv]
    calc (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ))
        = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))
          * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [star_mul']
          ring
      _ = 1 := by simp
  have hw2 : ∀ w : K × Etau K τ, w = ((w.1, quo z⁻¹ * w.2).1, quo z * (w.1, quo z⁻¹ * w.2).2) := by
    intro w
    refine Prod.ext rfl ?_
    show w.2 = quo z * (quo z⁻¹ * w.2)
    rw [← mul_assoc, hq, one_mul]
  ext w
  constructor
  · intro hw
    refine ⟨(w.1, quo z⁻¹ * w.2), ?_, (hw2 w).symm⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hw ((z : Etau K τ) * y) ⟨y, hy, rfl⟩
    rw [hw2 w, psi_quo] at hxy
    have := (Units.mul_right_inj z).mp hxy
    rw [← this]
    exact hx
  · rintro ⟨v, hv, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [psi_quo]
    exact ⟨_, hv y hy, rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Use extensionality with `v`. Simplify using `only [S0, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Use `h ((k : K) • y) ⟨y, hy, rfl⟩` as an intermediate fact.

Rewrite `this` using `[map_smul]`. Take `⟨x, hx, hxy⟩` from `this`. Establish `: x = psi s β v y` using `smul_right_injective _ (Units.ne_zero k) hxy`. Conclude with `this ▸ hx`. Introduce and unpack `h _ ⟨y, hy, rfl⟩`.

Rewrite using `[map_smul]`. Conclude with `⟨_, h y hy, rfl⟩`.
-/
theorem unimodular_image_smul_eq (k : Kˣ) (Λ : Set (Etau K τ)) : S0 s β (((k : K) • ·) '' Λ) = S0 s β Λ := by
  ext v
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro h y hy
    have := h ((k : K) • y) ⟨y, hy, rfl⟩
    rw [map_smul] at this
    obtain ⟨x, hx, hxy⟩ := this
    have : x = psi s β v y := smul_right_injective _ (Units.ne_zero k) hxy
    exact this ▸ hx
  · rintro h _ ⟨y, hy, rfl⟩
    rw [map_smul]
    exact ⟨_, h y hy, rfl⟩

/- English proof (translation)
Take `⟨e, -, f, -, h, -, η, hee, -, hef, -⟩` from `Uni.frame L hS`. Establish `h2 : (2 : K) ≠ 0`. Use `L.two.map (algebraMap O K)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Conclude with `this.ne_zero`.

Take `⟨x, ⟨p, q⟩⟩` from `e`. Rewrite `hee` using `[Bf_apply]`. Simplify using `only [trace_def, re_mul, im_mul, re_star, im_star] at hee`. Establish `hN : (2 * t) * (x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2)) = 0`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hee`. Establish `hN' : x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2) = 0` using `(mul_eq_zero.mp hN).resolve_left (mul_ne_zero h2 ht)`. Distinguish the cases in `hx : x = 0`. Substitute `hx left` using the available equality. Distinguish the cases in `hq : q = 0`.

It suffices to derive a contradiction. Substitute `hq` using the available equality. Establish `hp : p = 0`. Establish `: p ^ 2 = 0` using `by linear_combination hN'`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.mp this`.

Substitute `hp` using the available equality. Establish `: ((0 : K × Etau K τ)) = ((0 : K), (⟨0, 0⟩ : Etau K τ))` using `rfl`. Rewrite `hef` using `[← this, map_zero, LinearMap.zero_apply]`. Conclude with `zero_ne_one hef`. Use `⟨(2 * p + τ * q) / q, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-4) * hN'`. Use `right`. Use `⟨t * (2 * p + τ * q) / x, t * q / x, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Take the linear combination `2 * hee`.
-/
theorem Uni.iso (L : IsLoc O Δ) (ht : t ≠ 0) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    IsSquare (τ ^ 2 - 4) ∨ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = -2 * c * t := by
  obtain ⟨e, -, f, -, h, -, η, hee, -, hef, -⟩ := Uni.frame L hS
  have h2 : (2 : K) ≠ 0 := by
    have := L.two.map (algebraMap O K)
    rw [map_ofNat] at this
    exact this.ne_zero
  obtain ⟨x, ⟨p, q⟩⟩ := e
  rw [Bf_apply] at hee
  simp only [trace_def, re_mul, im_mul, re_star, im_star] at hee
  have hN : (2 * t) * (x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2)) = 0 := by
    field_simp
    linear_combination hee
  have hN' : x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2) = 0 :=
    (mul_eq_zero.mp hN).resolve_left (mul_ne_zero h2 ht)
  by_cases hx : x = 0
  · subst hx
    left
    by_cases hq : q = 0
    · exfalso
      subst hq
      have hp : p = 0 := by
        have : p ^ 2 = 0 := by linear_combination hN'
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hp
      have : ((0 : K × Etau K τ)) = ((0 : K), (⟨0, 0⟩ : Etau K τ)) := rfl
      rw [← this, map_zero, LinearMap.zero_apply] at hef
      exact zero_ne_one hef
    · refine ⟨(2 * p + τ * q) / q, ?_⟩
      field_simp
      linear_combination (-4) * hN'
  · right
    refine ⟨t * (2 * p + τ * q) / x, t * q / x, ?_⟩
    field_simp
    linear_combination 2 * hee

end UpperTheory.V.Z.Sym.Loc.CP
