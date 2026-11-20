import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TeichmullerCharacterSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

/- English proof (translation)
Establish `h : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l])` using `by simp [map_ofNat]`. Rewrite using `[h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.coprime_primes Fact.out Nat.prime_two).2 hl`.
-/
private theorem norm_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ‖(2 : Qbar l)‖ = 1 := by
  have h : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by simp [map_ofNat]
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl

/- English proof (translation)
Rewrite using `[eq_mul_inv_of_mul_eq h, zpow_sub, zpow_add, zpow_one, zpow_natCast, zpow_natCast]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Normalize the expressions using the abelian group laws.
-/
private theorem alg {A : Type} [CommGroup A] (d x o p q f : A) (k e : ℕ)
    (h : d ^ 2 * (x ^ k * q * f) = x * o⁻¹ * q * (x ^ (e : ℤ) * p)) :
    d ^ 2 = x ^ ((e : ℤ) + 1 - k) * (o⁻¹ * p * f⁻¹) := by
  rw [eq_mul_inv_of_mul_eq h, zpow_sub, zpow_add, zpow_one, zpow_natCast, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

/- English proof (translation)
Take `⟨b, rfl⟩` from `hn`. Rewrite using `[pow_mul, h, one_pow]`.
-/
private theorem pow_one_of_dvd {A : Type} [Monoid A] {x : A} {a : ℕ} (h : x ^ a = 1) {n : ℕ} (hn : a ∣ n) : x ^ n = 1 := by
  obtain ⟨b, rfl⟩ := hn
  rw [pow_mul, h, one_pow]

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D T k₀ _ _ φ ι k t r α β R δ h`. Establish `hG` using `h.hyp.good`. Establish `hchi : ∀ g : G T.F Ω, up (chiO ℚ Ω l c.O) (resQ T.F g) = cycBar T.F Ω l g` using `fun g => Units.ext rfl`. Establish `key : ∀ g : G T.F Ω, δ g ^ 2 = cycBar T.F Ω l g ^ ((D.e : ℤ) + 1 - k) * ((up D.om (resQ T.F g))⁻¹ * up D.ψ (resQ T.F g) * (φ (resQ T.F g))⁻¹)`. Introduce `g`.

Apply `alg _ _ _ _ (up D.ξ (resQ T.F g))` to reduce the goal to its premises. Establish `h1` using `h.δ_sq g`. Establish `h2 : up D.th (resQ T.F g) = cycBar T.F Ω l g * (up D.om (resQ T.F g))⁻¹ * up D.ξ (resQ T.F g) * (cycBar T.F Ω l g ^ (D.e : ℤ) * up D.ψ (resQ T.F g))`. Rewrite using `[← hchi]`. Simplify using `only [up, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, map_mul, map_inv, map_zpow]`.

Rewrite using `[← h2, ← h1]`. Both sides reduce to the same expression. Take `⟨m, hm, hψ⟩` from `h.hyp.deep`. Establish `hl1 : 1 < l` using `hl.out.one_lt`. Establish `hm0 : 0 < m`.

Break down `Nat.eq_zero_or_pos m with rfl | h0` into its components or cases. Rewrite `hm` using `[Nat.coprime_zero_right]`. Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hφ : ∀ g, φ g ^ 2 = 1`.

Introduce `g`. Distinguish the cases in `hg : g ∈ k₀.fixingSubgroup`. Rewrite using `[h.hyp.φ_in g hg, one_pow]`. Rewrite using `[h.hyp.φ_out g hg]`. Simplify using the standard rewrite rules.

Establish `hφI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F` using `T.F) A, φ (resQ T.F s) = 1 := by`. Introduce `A hA s hs`. Apply `h.hyp.φ_in` to reduce the goal to its premises. Apply `h.hyp.spl A hA` to reduce the goal to its premises. Conclude with `hs.1`.

Establish `hcont : Continuous (resQ T.F)` using `by haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩`. Conclude with `(galEmbTop ℚ T.F Ω).1.continuous`. Establish `hup : ∀ (χ : G ℚ Ω →* c.Oˣ) g, χ g = 1 → up χ g = 1` using `fun χ g hg => by`. Simplify using `only [up, MonoidHom.comp_apply, hg, map_one]`. Use `⟨(D.e : ℤ) + 1 - k, (l - 1) * m * 2, (D.ψ.ker ⊓ D.om.ker).comap (resQ T.F), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Nat.mul_pos (Nat.mul_pos (by omega) hm0) two_pos`. Introduce `g`. Establish `a1 : up D.om (resQ T.F g) ^ (l - 1) = 1`. Use `DFunLike.congr_fun hG.om_pow (resQ T.F g)` as an intermediate fact. Rewrite `this` using `[MonoidHom.pow_apply, MonoidHom.one_apply]`.

Simplify using `only [up, MonoidHom.comp_apply, ← map_pow, this, map_one]`. Establish `a2 : up D.ψ (resQ T.F g) ^ m = 1`. Simplify using `only [up, MonoidHom.comp_apply, ← map_pow, hψ g, map_one]`. Establish `b1` using `(pow_one_of_dvd a1 (n := (l - 1) * m * 2) ⟨m * 2, by ring⟩)`. Establish `b2` using `(pow_one_of_dvd a2 (n := (l - 1) * m * 2) ⟨(l - 1) * 2, by ring⟩)`.

Establish `b3` using `(pow_one_of_dvd (hφ (resQ T.F g)) (n := (l - 1) * m * 2) ⟨(l - 1) * m, by ring⟩)`. Rewrite using `[key g, zpow_neg, mul_inv_cancel_comm, mul_pow, mul_pow, inv_pow, inv_pow, b1, b2, b3]`. Simplify using the standard rewrite rules. Conclude with `(hG.psi_open.inter h.chars.om_open).preimage hcont`. Introduce `A hA s hs`.

Establish `fin : D.ψ (resQ T.F s) = 1 → D.om (resQ T.F s) = 1 → δ s ^ 2 = cycBar T.F Ω l s ^ ((D.e : ℤ) + 1 - k)`. Introduce `h1 h2`. Rewrite using `[key s, hup _ _ h1, hup _ _ h2, hφI A hA s hs]`. Simplify using the standard rewrite rules. Use `⟨fun hU => fin hU.1 hU.2, fun hc => ?_⟩` and prove the remaining obligations.

Establish `hc' : cycZ ℚ Ω l (resQ T.F s) = 1` using `hc`. Establish `hb : cycBar T.F Ω l s = 1`. Simplify using `only [cycBar, MonoidHom.comp_apply, hc, map_one]`. Establish `hb' : cycBar ℚ Ω l (resQ T.F s) = 1` using `hb`. Establish `ho : D.om (resQ T.F s) = 1`.

Rewrite using `[h.chars.om, hb']`. Simplify using `[Cong]`. Establish `hP : D.Psi (resQ T.F s) = D.ψ (resQ T.F s)`. Simplify using `only [Raw.Psi, UpperTheory.V.Chr.Psi, chiO, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, hc', map_one, one_zpow, one_mul]`. Establish `hp : D.ψ (resQ T.F s) = 1`.

Apply `UpperTheory.teichmuller_character_spec l c _ m hm (hψ s)` to reduce the goal to its premises. Use `congrFun (congrFun (h.hyp.ok.ineL A hA s hs) 1) 1` as an intermediate fact. Rewrite using `[← hP]`. Simplify `this` using `[Raw.rbar, Raw.r0, diagRep, Raw.ps]`. Establish `h2` using `fin hp ho`.

Rewrite `h2` using `[hb, one_zpow]`. Establish `h3 : (δ s : Qbar l) ^ 2 = 1` using `by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]`. Break down `sq_eq_one_iff.1 h3 with h4 | h4` into its components or cases. Conclude with `Units.ext h4`. Establish `h5` using `h.δ_one s`.

Rewrite `h5` using `[Cong, h4, Units.val_one, show (-1 - 1 : Qbar l) = -2 by norm_num, norm_neg, norm_two l hG.l_odd]`. Conclude with `absurd h5 (lt_irrefl _)`.
-/
theorem UpperTheory.induced_deletion_condition :
    UpperTheory.V.Sd.S2.IndDel := by
  intro Ω _ _ _ l hl c D T k₀ _ _ φ ι k t r α β R δ h
  have hG := h.hyp.good
  have hchi : ∀ g : G T.F Ω, up (chiO ℚ Ω l c.O) (resQ T.F g) = cycBar T.F Ω l g := fun g => Units.ext rfl
  have key : ∀ g : G T.F Ω, δ g ^ 2 = cycBar T.F Ω l g ^ ((D.e : ℤ) + 1 - k) *
      ((up D.om (resQ T.F g))⁻¹ * up D.ψ (resQ T.F g) * (φ (resQ T.F g))⁻¹) := by
    intro g
    apply alg _ _ _ _ (up D.ξ (resQ T.F g))
    have h1 := h.δ_sq g
    have h2 : up D.th (resQ T.F g) = cycBar T.F Ω l g * (up D.om (resQ T.F g))⁻¹ * up D.ξ (resQ T.F g) *
        (cycBar T.F Ω l g ^ (D.e : ℤ) * up D.ψ (resQ T.F g)) := by
      rw [← hchi]
      simp only [up, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        MonoidHom.zpow_apply, map_mul, map_inv, map_zpow]
    rw [← h2, ← h1]
    rfl
  obtain ⟨m, hm, hψ⟩ := h.hyp.deep
  have hl1 : 1 < l := hl.out.one_lt
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [Nat.coprime_zero_right] at hm; omega
    · exact h0
  have hφ : ∀ g, φ g ^ 2 = 1 := by
    intro g
    by_cases hg : g ∈ k₀.fixingSubgroup
    · rw [h.hyp.φ_in g hg, one_pow]
    · rw [h.hyp.φ_out g hg]; simp
  have hφI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.F) A, φ (resQ T.F s) = 1 := by
    intro A hA s hs
    apply h.hyp.φ_in
    apply h.hyp.spl A hA
    exact hs.1
  have hcont : Continuous (resQ T.F) := by
    haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    exact (galEmbTop ℚ T.F Ω).1.continuous
  have hup : ∀ (χ : G ℚ Ω →* c.Oˣ) g, χ g = 1 → up χ g = 1 := fun χ g hg => by
    simp only [up, MonoidHom.comp_apply, hg, map_one]
  refine ⟨(D.e : ℤ) + 1 - k, (l - 1) * m * 2, (D.ψ.ker ⊓ D.om.ker).comap (resQ T.F), ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos (by omega) hm0) two_pos
  · intro g
    have a1 : up D.om (resQ T.F g) ^ (l - 1) = 1 := by
      have := DFunLike.congr_fun hG.om_pow (resQ T.F g)
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      simp only [up, MonoidHom.comp_apply, ← map_pow, this, map_one]
    have a2 : up D.ψ (resQ T.F g) ^ m = 1 := by
      simp only [up, MonoidHom.comp_apply, ← map_pow, hψ g, map_one]
    have b1 := (pow_one_of_dvd a1 (n := (l - 1) * m * 2) ⟨m * 2, by ring⟩)
    have b2 := (pow_one_of_dvd a2 (n := (l - 1) * m * 2) ⟨(l - 1) * 2, by ring⟩)
    have b3 := (pow_one_of_dvd (hφ (resQ T.F g)) (n := (l - 1) * m * 2) ⟨(l - 1) * m, by ring⟩)
    rw [key g, zpow_neg, mul_inv_cancel_comm, mul_pow, mul_pow, inv_pow, inv_pow, b1, b2, b3]
    simp
  · exact (hG.psi_open.inter h.chars.om_open).preimage hcont
  · intro A hA s hs
    have fin : D.ψ (resQ T.F s) = 1 → D.om (resQ T.F s) = 1 → δ s ^ 2 = cycBar T.F Ω l s ^ ((D.e : ℤ) + 1 - k) := by
      intro h1 h2
      rw [key s, hup _ _ h1, hup _ _ h2, hφI A hA s hs]
      simp
    refine ⟨fun hU => fin hU.1 hU.2, fun hc => ?_⟩
    have hc' : cycZ ℚ Ω l (resQ T.F s) = 1 := hc
    have hb : cycBar T.F Ω l s = 1 := by
      simp only [cycBar, MonoidHom.comp_apply, hc, map_one]
    have hb' : cycBar ℚ Ω l (resQ T.F s) = 1 := hb
    have ho : D.om (resQ T.F s) = 1 := by
      rw [h.chars.om, hb']
      simp [Cong]
    have hP : D.Psi (resQ T.F s) = D.ψ (resQ T.F s) := by
      simp only [Raw.Psi, UpperTheory.V.Chr.Psi, chiO, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, hc', map_one,
        one_zpow, one_mul]
    have hp : D.ψ (resQ T.F s) = 1 := by
      apply UpperTheory.teichmuller_character_spec l c _ m hm (hψ s)
      have := congrFun (congrFun (h.hyp.ok.ineL A hA s hs) 1) 1
      rw [← hP]
      simpa [Raw.rbar, Raw.r0, diagRep, Raw.ps] using this
    have h2 := fin hp ho
    rw [hb, one_zpow] at h2
    have h3 : (δ s : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    rcases sq_eq_one_iff.1 h3 with h4 | h4
    · exact Units.ext h4
    · have h5 := h.δ_one s
      rw [Cong, h4, Units.val_one, show (-1 - 1 : Qbar l) = -2 by norm_num, norm_neg, norm_two l hG.l_odd] at h5
      exact absurd h5 (lt_irrefl _)
