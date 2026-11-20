import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Introduce `a b c d ha hd lam hlam hok m _ _ Λa g hθ l hl hiso h1 hl1 h2`. Use `set θ := cmTheta b d with hθdef`. Use `set S := stdLat (cmL a b d ha hd lam hlam) m with hSdef`. Use `set X := imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hXdef`. Establish `hθn : θ * ((b : ℂ) - θ) = (a : ℂ) * c` using `theta_norm hok.1`.

Establish `hθθ : θ * θ = (b : ℂ) * θ - (a : ℂ) * c` using `by linear_combination -hθn`. Establish `hXθ : ∀ x ∈ X, θ • x ∈ X`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨θ • y, hθ y hy, by simp⟩`. Establish `hlin : ∀ p q : ℤ, ∀ x ∈ X, ((p : ℂ) + (q : ℂ) * θ) • x ∈ X`.

Introduce `p q x hx`. Rewrite using `[add_smul, mul_smul, Int.cast_smul_eq_zsmul ℂ p, Int.cast_smul_eq_zsmul ℂ q]`. Conclude with `X.add_mem (X.zsmul_mem hx p) (X.zsmul_mem (hXθ x hx) q)`. Take `⟨β, hβ⟩ : ∃ β : ℕ → ℂ, ∀ u, β u = 1 + ((u * l : ℕ) : ℂ) * θ` from `⟨_, fun _ => rfl⟩`. Take `⟨βb, hβb⟩ : ∃ βb : ℕ → ℂ, ∀ u, βb u = 1 + ((u * l : ℕ) : ℂ) * ((b : ℂ) - θ)` from `⟨_, fun _ => rfl⟩`.

Take `⟨K, hKdef⟩ : ∃ K : ℕ → ℤ, ∀ u, K u = 1 + ((u * l : ℕ) : ℤ) * b + ((u * l : ℕ) : ℤ) ^ 2 * a * c` from `⟨_, fun _ => rfl⟩`. Establish `hconj : ∀ u, (starRingEnd ℂ) (β u) = βb u`. Introduce `u`. Rewrite using `[hβ, hβb, map_add, map_one, map_mul, map_natCast, hθdef, theta_conj]`. Establish `hK : ∀ u, β u * βb u = ((K u : ℤ) : ℂ)`.

Introduce `u`. Rewrite using `[hβ, hβb, hKdef]`. Use `push_cast`. Take the linear combination `((u : ℂ) * l) ^ 2 * hθn`. Establish `hKpos : ∀ u, 0 < K u`.

Introduce `u`. Rewrite using `[hKdef]`. Use `set U : ℤ := ((u * l : ℕ) : ℤ) with hU`. Establish `h4` using `hok.1`. Establish `hd1 : (1 : ℤ) ≤ d` using `by exact_mod_cast hd`.

Establish `key : 4 * (1 + U * b + U ^ 2 * a * c) = (2 + U * b) ^ 2 + U ^ 2 * d`. Take the linear combination `U ^ 2 * h4`. Break down `eq_or_ne U 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Evaluate the numerical expressions.

Establish `hU2 : 1 ≤ U ^ 2`. Use `pow_pos (abs_pos.2 h0) 2` as an intermediate fact. Rewrite `this` using `[sq_abs]`. Use linear arithmetic over natural numbers and integers. Use polynomial arithmetic with `[sq_nonneg (2 + U * b)]`.

Establish `hβ0 : ∀ u, β u ≠ 0` using `fun u h => by`. Use `hK u` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `(hKpos u).ne' (by exact_mod_cast this.symm)`. Establish `hβb0 : ∀ u, βb u ≠ 0` using `fun u h => by`.

Use `hK u` as an intermediate fact. Rewrite `this` using `[h, mul_zero]`. Conclude with `(hKpos u).ne' (by exact_mod_cast this.symm)`. Establish `hinj : Function.Injective (fun u => (β u / βb u)⁻¹)`. Introduce `u v huv`.

Simplify using `only [inv_inj] at huv`. Rewrite `huv` using `[div_eq_div_iff (hβb0 u) (hβb0 v), hβ, hβ, hβb, hβb]`. Establish `h2θ : 2 * θ - b ≠ 0` using `two_theta_sub b hd`. Establish `hmul : (((u * l : ℕ) : ℂ) - ((v * l : ℕ) : ℂ)) * (2 * θ - b) = 0`. Take the linear combination `huv`.

Break down `mul_eq_zero.1 hmul with h | h` into its components or cases. Establish `h' : u * l = v * l` using `Nat.cast_injective (sub_eq_zero.1 h)`. Conclude with `Nat.eq_of_mul_eq_mul_right hl.pos h'`. Conclude with `absurd h h2θ`. Establish `hfin` using `Module.End.finite_hasEigenvalue (g : Module.End ℂ (m → ℂ))`.

Take `⟨_, ⟨u, rfl⟩, hu⟩` from `(Set.infinite_range_of_injective hinj).exists_notMem_finite hfin`. Use `set w := β u / βb u with hwdef`. Establish `hw0 : w ≠ 0` using `div_ne_zero (hβ0 u) (hβb0 u)`. Set `δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)` to `g.trans (LinearEquiv.smulOfNeZero ℂ (m → ℂ) w hw0)`. Establish `hδ : ∀ x, δ x = w • g x` using `fun x => rfl`.

Establish `hcb : (starRingEnd ℂ) (βb u) = β u` using `by rw [← hconj u, Complex.conj_conj]`. Establish `hww : (starRingEnd ℂ) w * w = 1`. Rewrite using `[hwdef, map_div₀, hconj u, hcb]`. Clear denominators, using `[hβ0 u, hβb0 u]` for the nonvanishing conditions. Establish `hisoδ : IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))`.

Introduce `x y`. Use `show stdH (cmL a b d ha hd lam hlam) m (w • g x) (w • g y) = stdH (cmL a b d ha hd lam hlam) m x y`. Rewrite using `[LinearMap.map_smul (stdH (cmL a b d ha hd lam hlam) m) w (g x), LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm w, hww, one_mul]`. Conclude with `hiso x y`. Establish `himg : imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa = X.map (smulHom w)`.

Rewrite using `[hXdef]`. Unfold `imgLat`. Rewrite using `[AddSubgroup.map_map]`. Use `congr 1`. Use `set Nn := (K u).toNat with hNndef`.

Establish `hNnZ : ((Nn : ℕ) : ℤ) = K u` using `Int.toNat_of_nonneg (hKpos u).le`. Establish `hNn : ((Nn : ℕ) : ℂ) = β u * βb u`. Rewrite using `[hK u, ← hNnZ, Int.cast_natCast]`. Establish `hN0 : Nn ≠ 0` using `by have := hKpos u; omega`. Establish `ha' : ∀ x ∈ X, (Nn : ℂ) • w • x ∈ X`.

Introduce `x hx`. Establish `heq : (Nn : ℂ) * w = (((1 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) + (((2 * ((u * l : ℕ) : ℤ) + ((u * l : ℕ) : ℤ) ^ 2 * b : ℤ)) : ℂ) * θ`. Rewrite using `[hNn, hwdef]`. Establish `: β u * βb u * (β u / βb u) = β u * β u` using `by field_simp [hβb0 u]`. Rewrite using `[this, hβ]`.

Use `push_cast`. Take the linear combination `((u : ℂ) * l) ^ 2 * hθθ`. Rewrite using `[smul_smul, heq]`. Conclude with `hlin _ _ x hx`. Establish `hb' : ∀ x ∈ X, (Nn : ℂ) • w⁻¹ • x ∈ X`.

Introduce `x hx`. Establish `heq : (Nn : ℂ) * w⁻¹ = ((((1 + ((u * l : ℕ) : ℤ) * b) ^ 2 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) + ((((u * l : ℕ) : ℤ) ^ 2 * b - 2 * (1 + ((u * l : ℕ) : ℤ) * b) * ((u * l : ℕ) : ℤ) : ℤ) : ℂ) * θ`. Rewrite using `[hNn, hwdef, inv_div]`. Establish `: β u * βb u * (βb u / β u) = βb u * βb u` using `by field_simp [hβ0 u]`. Rewrite using `[this, hβb]`.

Use `push_cast`. Take the linear combination `((u : ℂ) * l) ^ 2 * hθθ`. Rewrite using `[smul_smul, heq]`. Conclude with `hlin _ _ x hx`. Take `⟨hi1, hi2⟩` from `comm_smul (S := S) (X := X) hw0 hN0 (stdLat_smul_idx _ m hN0) h1 h2 ha' hb'`.

Establish `hM : ∀ x ∈ X, (S.relIndex X) • x ∈ S`. Introduce `x hx`. Use `AddSubgroup.nsmul_index_mem (S.addSubgroupOf X) ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `this` using `[AddSubgroup.relIndex]`.

Establish `hNl : ¬ l ∣ Nn`. Introduce `hdiv`. Establish `h1' : (l : ℤ) ∣ K u`. Use `Int.natCast_dvd_natCast.2 hdiv` as an intermediate fact. Rewrite `this` using `[hNnZ]`. Then use the resulting hypothesis.

Establish `h2' : (l : ℤ) ∣ K u - 1` using `⟨(u : ℤ) * (b + ((u * l : ℕ) : ℤ) * a * c), by rw [hKdef]; push_cast; ring⟩`. Establish `h3 : (l : ℤ) ∣ 1`. Use `Int.dvd_sub h1' h2'` as an intermediate fact. Simplify using `using this`. Establish `h4 : (l : ℤ) = 1` using `Int.eq_one_of_dvd_one (by positivity) h3`.

Conclude with `hl.one_lt.ne' (by exact_mod_cast h4)`. Establish `hln : ¬ l ∣ S.relIndex X * Nn` using `fun h => ((Nat.Prime.dvd_mul hl).1 h).elim hl1 hNl`. Establish `hdvd` using `not_dvd_relIndex (A := S) (B := X.map (smulHom w)) (l := l) (n := S.relIndex X * Nn) hl hi1 (by`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[smulHom_apply, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ Nn]`.

Conclude with `hM _ (ha' x hx)) hln`. Use `⟨δ, hisoδ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Apply `hu` to reduce the goal to its premises.

Establish `hgx : (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • x`. Rewrite `hx` using `[hδ]`. Combine the equalities or inequalities in the displayed calculation. Use `Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_` and prove the remaining obligations. Use `first`.

Consider the case `exact Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩`. Consider the case `exact ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩`. Unfold `relIdx`. Rewrite using `[himg]`. Conclude with `hi1`.

Unfold `relIdx`. Rewrite using `[himg]`. Conclude with `hdvd`. Unfold `relIdx`. Rewrite using `[himg]`.

Conclude with `hi2`.
-/
theorem stepC : StepC := by
  intro a b c d ha hd lam hlam hok m _ _ Λa g hθ l hl hiso h1 hl1 h2
  classical
  set θ := cmTheta b d with hθdef
  set S := stdLat (cmL a b d ha hd lam hlam) m with hSdef
  set X := imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hXdef
  have hθn : θ * ((b : ℂ) - θ) = (a : ℂ) * c := theta_norm hok.1
  have hθθ : θ * θ = (b : ℂ) * θ - (a : ℂ) * c := by linear_combination -hθn

  have hXθ : ∀ x ∈ X, θ • x ∈ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨θ • y, hθ y hy, by simp⟩
  have hlin : ∀ p q : ℤ, ∀ x ∈ X, ((p : ℂ) + (q : ℂ) * θ) • x ∈ X := by
    intro p q x hx
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul ℂ p, Int.cast_smul_eq_zsmul ℂ q]
    exact X.add_mem (X.zsmul_mem hx p) (X.zsmul_mem (hXθ x hx) q)

  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℂ, ∀ u, β u = 1 + ((u * l : ℕ) : ℂ) * θ := ⟨_, fun _ => rfl⟩
  obtain ⟨βb, hβb⟩ : ∃ βb : ℕ → ℂ, ∀ u, βb u = 1 + ((u * l : ℕ) : ℂ) * ((b : ℂ) - θ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℤ, ∀ u, K u = 1 + ((u * l : ℕ) : ℤ) * b + ((u * l : ℕ) : ℤ) ^ 2 * a * c :=
    ⟨_, fun _ => rfl⟩
  have hconj : ∀ u, (starRingEnd ℂ) (β u) = βb u := by
    intro u
    rw [hβ, hβb, map_add, map_one, map_mul, map_natCast, hθdef, theta_conj]
  have hK : ∀ u, β u * βb u = ((K u : ℤ) : ℂ) := by
    intro u
    rw [hβ, hβb, hKdef]
    push_cast
    linear_combination ((u : ℂ) * l) ^ 2 * hθn
  have hKpos : ∀ u, 0 < K u := by
    intro u
    rw [hKdef]
    set U : ℤ := ((u * l : ℕ) : ℤ) with hU
    have h4 := hok.1
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have key : 4 * (1 + U * b + U ^ 2 * a * c) = (2 + U * b) ^ 2 + U ^ 2 * d := by
      linear_combination U ^ 2 * h4
    rcases eq_or_ne U 0 with h0 | h0
    · rw [h0]
      norm_num
    · have hU2 : 1 ≤ U ^ 2 := by
        have := pow_pos (abs_pos.2 h0) 2
        rw [sq_abs] at this
        omega
      nlinarith [sq_nonneg (2 + U * b)]
  have hβ0 : ∀ u, β u ≠ 0 := fun u h => by
    have := hK u
    rw [h, zero_mul] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)
  have hβb0 : ∀ u, βb u ≠ 0 := fun u h => by
    have := hK u
    rw [h, mul_zero] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)

  have hinj : Function.Injective (fun u => (β u / βb u)⁻¹) := by
    intro u v huv
    simp only [inv_inj] at huv
    rw [div_eq_div_iff (hβb0 u) (hβb0 v), hβ, hβ, hβb, hβb] at huv
    have h2θ : 2 * θ - b ≠ 0 := two_theta_sub b hd
    have hmul : (((u * l : ℕ) : ℂ) - ((v * l : ℕ) : ℂ)) * (2 * θ - b) = 0 := by
      linear_combination huv
    rcases mul_eq_zero.1 hmul with h | h
    · have h' : u * l = v * l := Nat.cast_injective (sub_eq_zero.1 h)
      exact Nat.eq_of_mul_eq_mul_right hl.pos h'
    · exact absurd h h2θ

  have hfin := Module.End.finite_hasEigenvalue (g : Module.End ℂ (m → ℂ))
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finite hfin
  set w := β u / βb u with hwdef
  have hw0 : w ≠ 0 := div_ne_zero (hβ0 u) (hβb0 u)
  let δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := g.trans (LinearEquiv.smulOfNeZero ℂ (m → ℂ) w hw0)
  have hδ : ∀ x, δ x = w • g x := fun x => rfl
  have hcb : (starRingEnd ℂ) (βb u) = β u := by rw [← hconj u, Complex.conj_conj]
  have hww : (starRingEnd ℂ) w * w = 1 := by
    rw [hwdef, map_div₀, hconj u, hcb]
    field_simp [hβ0 u, hβb0 u]
  have hisoδ : IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) := by
    intro x y
    show stdH (cmL a b d ha hd lam hlam) m (w • g x) (w • g y) = stdH (cmL a b d ha hd lam hlam) m x y
    rw [LinearMap.map_smul (stdH (cmL a b d ha hd lam hlam) m) w (g x), LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm w, hww, one_mul]
    exact hiso x y
  have himg : imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa = X.map (smulHom w) := by
    rw [hXdef]
    unfold imgLat
    rw [AddSubgroup.map_map]
    congr 1

  set Nn := (K u).toNat with hNndef
  have hNnZ : ((Nn : ℕ) : ℤ) = K u := Int.toNat_of_nonneg (hKpos u).le
  have hNn : ((Nn : ℕ) : ℂ) = β u * βb u := by
    rw [hK u, ← hNnZ, Int.cast_natCast]
  have hN0 : Nn ≠ 0 := by have := hKpos u; omega
  have ha' : ∀ x ∈ X, (Nn : ℂ) • w • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w = (((1 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        (((2 * ((u * l : ℕ) : ℤ) + ((u * l : ℕ) : ℤ) ^ 2 * b : ℤ)) : ℂ) * θ := by
      rw [hNn, hwdef]
      have : β u * βb u * (β u / βb u) = β u * β u := by field_simp [hβb0 u]
      rw [this, hβ]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  have hb' : ∀ x ∈ X, (Nn : ℂ) • w⁻¹ • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w⁻¹ = ((((1 + ((u * l : ℕ) : ℤ) * b) ^ 2 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        ((((u * l : ℕ) : ℤ) ^ 2 * b - 2 * (1 + ((u * l : ℕ) : ℤ) * b) * ((u * l : ℕ) : ℤ) : ℤ) : ℂ) * θ := by
      rw [hNn, hwdef, inv_div]
      have : β u * βb u * (βb u / β u) = βb u * βb u := by field_simp [hβ0 u]
      rw [this, hβb]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  obtain ⟨hi1, hi2⟩ := comm_smul (S := S) (X := X) hw0 hN0 (stdLat_smul_idx _ m hN0) h1 h2 ha' hb'

  have hM : ∀ x ∈ X, (S.relIndex X) • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf X) ⟨x, hx⟩
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [AddSubgroup.relIndex] using this
  have hNl : ¬ l ∣ Nn := by
    intro hdiv
    have h1' : (l : ℤ) ∣ K u := by
      have := Int.natCast_dvd_natCast.2 hdiv
      rwa [hNnZ] at this
    have h2' : (l : ℤ) ∣ K u - 1 :=
      ⟨(u : ℤ) * (b + ((u * l : ℕ) : ℤ) * a * c), by rw [hKdef]; push_cast; ring⟩
    have h3 : (l : ℤ) ∣ 1 := by
      have := Int.dvd_sub h1' h2'
      simpa using this
    have h4 : (l : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
    exact hl.one_lt.ne' (by exact_mod_cast h4)
  have hln : ¬ l ∣ S.relIndex X * Nn := fun h => ((Nat.Prime.dvd_mul hl).1 h).elim hl1 hNl
  have hdvd := not_dvd_relIndex (A := S) (B := X.map (smulHom w)) (l := l) (n := S.relIndex X * Nn) hl hi1
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [smulHom_apply, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ Nn]
      exact hM _ (ha' x hx)) hln
  refine ⟨δ, hisoδ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hx0
    apply hu
    have hgx : (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • x := by
      rw [hδ] at hx
      calc (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • (w • g x) := by rw [inv_smul_smul₀ hw0]; rfl
        _ = w⁻¹ • x := by rw [hx]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
    first
      | exact Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
      | exact ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
  · unfold relIdx
    rw [himg]
    exact hi1
  · unfold relIdx
    rw [himg]
    exact hdvd
  · unfold relIdx
    rw [himg]
    exact hi2

end PI.UnitaryGroupMassFormula.UnimodLocStd
