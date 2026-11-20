import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.DivAlg

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl : l - 1 ≠ 0` using `by have := hp.two_le; omega`. Take `⟨a, ha⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)`. Rewrite `ha` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Use `set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l]) with hb`.

Establish `hbz : PadicInt.toZMod b = (a : ZMod l)` using `by simp [hb]`. Establish `hker : ∀ x : ℤ_[l], ‖x‖ < 1 ↔ PadicInt.toZMod x = 0` using `fun x => by`. Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.mem_nonunits.symm]`. Both sides reduce to the same expression. Establish `hapow : (a : ZMod l) ^ (l - 1) = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, ← ha, pow_orderOf_eq_one, Units.val_one]`. Set `F : Polynomial ℤ_[l]` to `Polynomial.X ^ (l - 1) - 1`. Establish `h1 : ‖F.aeval b‖ < 1`. Rewrite using `[hker]`. Simplify using `[F, hbz, hapow]`.

Establish `h2 : ‖F.derivative.aeval b‖ = 1`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)` and prove the remaining obligations. Rewrite `h` using `[hker]`. Establish `h3 : ((l - 1 : ℕ) : ZMod l) = -1`. Rewrite using `[Nat.cast_sub hp.one_le]`.

Simplify using the standard rewrite rules. Simplify using `[F, hbz, h3, Polynomial.derivative_X_pow] at h`. Take `⟨z, hz, hzb, -⟩` from `hensels_lemma (F := F) (a := b) (by rw [h2]; simpa using h1)`. Rewrite `hzb` using `[h2, hker, map_sub, hbz, sub_eq_zero]`. Establish `hz1 : z ^ (l - 1) = 1` using `by simpa [F, sub_eq_zero] using hz`.

Use `⟨z, hz1, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha]`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, ← hzb, ← map_pow, hm, map_one, Units.val_one]`.
-/
private theorem prim_root : ∃ z : ℤ_[l], IsPrimitiveRoot z (l - 1) := by
  have hp : l.Prime := Fact.out
  have hl : l - 1 ≠ 0 := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at ha
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l]) with hb
  have hbz : PadicInt.toZMod b = (a : ZMod l) := by simp [hb]
  have hker : ∀ x : ℤ_[l], ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := fun x => by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.mem_nonunits.symm]; rfl
  have hapow : (a : ZMod l) ^ (l - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← ha, pow_orderOf_eq_one, Units.val_one]
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have h1 : ‖F.aeval b‖ < 1 := by
    rw [hker]; simp [F, hbz, hapow]
  have h2 : ‖F.derivative.aeval b‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    rw [hker] at h
    have h3 : ((l - 1 : ℕ) : ZMod l) = -1 := by
      rw [Nat.cast_sub hp.one_le]; simp
    simp [F, hbz, h3, Polynomial.derivative_X_pow] at h
  obtain ⟨z, hz, hzb, -⟩ := hensels_lemma (F := F) (a := b) (by rw [h2]; simpa using h1)
  rw [h2, hker, map_sub, hbz, sub_eq_zero] at hzb
  have hz1 : z ^ (l - 1) = 1 := by simpa [F, sub_eq_zero] using hz
  refine ⟨z, hz1, fun m hm => ?_⟩
  rw [← ha]
  apply orderOf_dvd_of_pow_eq_one
  ext
  rw [Units.val_pow_eq_pow_val, ← hzb, ← map_pow, hm, map_one, Units.val_one]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Both sides reduce to the same expression.
-/
private theorem alg_norm (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Rewrite using `[← norm_eq_zero, ← alg_norm, ha, norm_zero]`.
-/
private theorem alg_inj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← norm_eq_zero, ← alg_norm, ha, norm_zero]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero (l - 1) := ⟨by have := hp.two_le; omega⟩`. Take `⟨z, hz⟩` from `prim_root (l := l)`. Take `⟨i, -, hi⟩` from `(hz.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) alg_inj).eq_pow_of_pow_eq_one hw`. Conclude with `⟨z ^ i, by rw [map_pow, hi]⟩`.
-/
private theorem root_mem {w : Qbar l} (hw : w ^ (l - 1) = 1) : ∃ z : ℤ_[l], algebraMap ℤ_[l] (Qbar l) z = w := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l - 1) := ⟨by have := hp.two_le; omega⟩
  obtain ⟨z, hz⟩ := prim_root (l := l)
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) alg_inj).eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']`.
-/
private theorem norm_nat (m : ℕ) : ‖((m : ℕ) : Qbar l)‖ = ‖((m : ℕ) : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one _ m`.
-/
private theorem norm_nat_le (m : ℕ) : ‖((m : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m

/- English proof (translation)
Rewrite using `[norm_nat]`. Conclude with `Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)`.
-/
private theorem norm_nat_one {m : ℕ} (h : ¬ l ∣ m) : ‖((m : ℕ) : Qbar l)‖ = 1 := by
  rw [norm_nat]
  exact Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)

/- English proof (translation)
Rewrite using `[norm_nat]`. Conclude with `Padic.norm_p_lt_one`.
-/
private theorem norm_l : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_nat]; exact Padic.norm_p_lt_one

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one ha (norm_l (l := l))`. Use `⟨n, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_pow]`. Conclude with `(pow_le_pow_of_le_one (norm_nonneg _) norm_l.le hm).trans hn.le`.
-/
private theorem small {a : ℝ} (ha : 0 < a) : ∃ n : ℕ, ∀ m, n ≤ m → ‖((l : ℕ) : Qbar l) ^ m‖ ≤ a := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha (norm_l (l := l))
  refine ⟨n, fun m hm => ?_⟩
  rw [norm_pow]
  exact (pow_le_pow_of_le_one (norm_nonneg _) norm_l.le hm).trans hn.le

/- English proof (translation)
Rewrite using `[← map_pow, ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff]), map_one]`.
-/
private theorem phi_pow (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : φ (m : ZMod l) ^ (l - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff]), map_one]

/- English proof (translation)
Establish `hl : l - 1 ≠ 0` using `by have := (Fact.out : l.Prime).two_le; omega`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 (by rw [← norm_pow, phi_pow φ h, norm_one])`.
-/
private theorem phi_norm (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : ‖φ (m : ZMod l)‖ = 1 := by
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 (by rw [← norm_pow, phi_pow φ h, norm_one])

/- English proof (translation)
Introduce `h1`. Establish `hl : l - 1 ≠ 0` using `by have := (Fact.out : l.Prime).two_le; omega`. Establish `h2 : ((φ (g : ZMod l) * (g : Qbar l) ^ k) ^ N) ^ (l - 1) = 1` using `by rw [h1, one_pow]`. Rewrite `h2` using `[← pow_mul, mul_comm N, pow_mul, mul_pow, phi_pow φ h, one_mul, ← pow_mul, ← pow_mul]`. Establish `h3 : g ^ (k * ((l - 1) * N)) = 1` using `by exact_mod_cast h2`.

Rewrite `h3` using `[Nat.pow_eq_one]`. Break down `h3 with h3 | h3` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `mul_ne_zero (by omega) (mul_ne_zero hl hN.ne') h3`.
-/
private theorem theta_ne (φ : DirichletCharacter (Qbar l) l) {g k N : ℕ} (h : ¬ l ∣ g) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hN : 0 < N) : (φ (g : ZMod l) * (g : Qbar l) ^ k) ^ N ≠ 1 := by
  intro h1
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have h2 : ((φ (g : ZMod l) * (g : Qbar l) ^ k) ^ N) ^ (l - 1) = 1 := by rw [h1, one_pow]
  rw [← pow_mul, mul_comm N, pow_mul, mul_pow, phi_pow φ h, one_mul, ← pow_mul, ← pow_mul] at h2
  have h3 : g ^ (k * ((l - 1) * N)) = 1 := by exact_mod_cast h2
  rw [Nat.pow_eq_one] at h3
  rcases h3 with h3 | h3
  · omega
  · exact mul_ne_zero (by omega) (mul_ne_zero hl hN.ne') h3

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
private theorem nsub (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simpa using hε`. Consider the case `succ i ih`. Establish `e : q (x * γ ^ (i + 1)) - θ ^ (i + 1) * q x = (q (x * γ ^ i * γ) - θ * q (x * γ ^ i)) + θ * (q (x * γ ^ i) - θ ^ i * q x)`. Rewrite using `[pow_succ γ, mul_assoc x]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h _) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hθ).trans ih`.
-/
private theorem iter {Γ : Type} [Group Γ] (γ : Γ) (θ : Qbar l) (hθ : ‖θ‖ ≤ 1) (q : Γ → Qbar l) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ x, ‖q (x * γ) - θ * q x‖ ≤ ε) (x : Γ) (i : ℕ) : ‖q (x * γ ^ i) - θ ^ i * q x‖ ≤ ε := by
  induction i with
  | zero => simpa using hε
  | succ i ih =>
    have e : q (x * γ ^ (i + 1)) - θ ^ (i + 1) * q x =
        (q (x * γ ^ i * γ) - θ * q (x * γ ^ i)) + θ * (q (x * γ ^ i) - θ ^ i * q x) := by
      rw [pow_succ γ, mul_assoc x]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h _) ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hθ).trans ih

/- English proof (translation)
Establish `e : τ ^ (j % N) - τ ^ j = - (τ ^ (j % N) * ((∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i) * (τ ^ N - 1)))`. Rewrite using `[geom_sum_mul, ← pow_mul, mul_sub, ← pow_add, Nat.mod_add_div]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg, norm_mul, norm_mul]`. Establish `h1 : ‖τ ^ (j % N)‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hτ`.

Establish `h2 : ‖∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i‖ ≤ 1` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by`. Rewrite using `[norm_pow, norm_pow]; exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hτ)`. Conclude with `(mul_le_of_le_one_left (by positivity) h1).trans (mul_le_of_le_one_left (norm_nonneg _) h2)`.
-/
private theorem pow_mod_near (τ : Qbar l) (hτ : ‖τ‖ ≤ 1) (N j : ℕ) : ‖τ ^ (j % N) - τ ^ j‖ ≤ ‖τ ^ N - 1‖ := by
  have e : τ ^ (j % N) - τ ^ j = - (τ ^ (j % N) * ((∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i) * (τ ^ N - 1))) := by
    rw [geom_sum_mul, ← pow_mul, mul_sub, ← pow_add, Nat.mod_add_div]; ring
  rw [e, norm_neg, norm_mul, norm_mul]
  have h1 : ‖τ ^ (j % N)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hτ
  have h2 : ‖∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow, norm_pow]; exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hτ)
  exact (mul_le_of_le_one_left (by positivity) h1).trans (mul_le_of_le_one_left (norm_nonneg _) h2)

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hx`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy`. Establish `e : x⁻¹ - y⁻¹ = -(x - y) * x⁻¹ * y⁻¹` using `by field_simp; ring`. Rewrite using `[e, norm_mul, norm_mul, norm_inv, norm_inv, hx, hy, norm_neg]`. Simplify using the standard rewrite rules.
-/
private theorem inv_near {x y : Qbar l} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x⁻¹ - y⁻¹‖ = ‖x - y‖ := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have e : x⁻¹ - y⁻¹ = -(x - y) * x⁻¹ * y⁻¹ := by field_simp; ring
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, hx, hy, norm_neg]; simp

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hv : ((un g hg r ^ j : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = g ^ j % l ^ r`. Rewrite using `[Units.val_pow_eq_pow_val, un, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]`. Establish `hd : l ∣ l ^ r` using `dvd_pow_self l (by omega)`. Establish `hgj : ¬ l ∣ g ^ j` using `fun h => hg (hp.dvd_of_dvd_pow h)`.

Establish `hY : ¬ l ∣ g ^ j % l ^ r` using `by rwa [Nat.dvd_mod_iff hd]`. Establish `hφ : ((g ^ j % l ^ r : ℕ) : ZMod l) = (g : ZMod l) ^ j`. Rewrite using `[← Nat.cast_pow]`. Conclude with `(ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod_of_dvd _ hd)`. Simplify using `only [eta, hv, hφ, map_pow]`.

Establish `e : ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j = (φ (g : ZMod l) ^ j)⁻¹ * (((g ^ j : ℕ) : Qbar l) ^ k)⁻¹`. Rewrite using `[inv_pow, mul_pow, mul_inv, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]`. Rewrite using `[e, ← mul_sub, norm_mul, norm_inv, norm_pow, phi_norm φ hg, one_pow, inv_one, one_mul, inv_near (by rw [norm_pow, norm_nat_one hY, one_pow]) (by rw [norm_pow, norm_nat_one hgj, one_pow])]`. Take `⟨m, hm⟩` from `Nat.modEq_iff_dvd.1 ((Nat.mod_modEq (g ^ j) (l ^ r)).pow k).symm`. Establish `hmQ : ((g ^ j % l ^ r : ℕ) : Qbar l) ^ k - ((g ^ j : ℕ) : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l)`.

Use `congrArg (fun z : ℤ => (z : Qbar l)) hm` as an intermediate fact. Simplify `this` using `only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Nat.cast_pow, Int.cast_pow]`. Rewrite using `[hmQ, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)`.
-/
private theorem eta_near (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {g : ℕ} (hg : ¬ l ∣ g) {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ‖eta φ k r (un g hg r ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hp : l.Prime := Fact.out
  have hv : ((un g hg r ^ j : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = g ^ j % l ^ r := by
    rw [Units.val_pow_eq_pow_val, un, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
  have hd : l ∣ l ^ r := dvd_pow_self l (by omega)
  have hgj : ¬ l ∣ g ^ j := fun h => hg (hp.dvd_of_dvd_pow h)
  have hY : ¬ l ∣ g ^ j % l ^ r := by rwa [Nat.dvd_mod_iff hd]
  have hφ : ((g ^ j % l ^ r : ℕ) : ZMod l) = (g : ZMod l) ^ j := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod_of_dvd _ hd)
  simp only [eta, hv, hφ, map_pow]
  have e : ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j = (φ (g : ZMod l) ^ j)⁻¹ * (((g ^ j : ℕ) : Qbar l) ^ k)⁻¹ := by
    rw [inv_pow, mul_pow, mul_inv, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e, ← mul_sub, norm_mul, norm_inv, norm_pow, phi_norm φ hg, one_pow, inv_one, one_mul,
    inv_near (by rw [norm_pow, norm_nat_one hY, one_pow]) (by rw [norm_pow, norm_nat_one hgj, one_pow])]
  obtain ⟨m, hm⟩ := Nat.modEq_iff_dvd.1 ((Nat.mod_modEq (g ^ j) (l ^ r)).pow k).symm
  have hmQ : ((g ^ j % l ^ r : ℕ) : Qbar l) ^ k - ((g ^ j : ℕ) : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l) := by
    have := congrArg (fun z : ℤ => (z : Qbar l)) hm
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Nat.cast_pow, Int.cast_pow] using this
  rw [hmQ, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)

/- English proof (translation)
Use `ext`. Simplify using `[red, un]`.
-/
private theorem red_un {g : ℕ} (hg : ¬ l ∣ g) (r : ℕ) : red l r (un g hg (r + 1)) = un g hg r := by
  ext
  simp [red, un]

/- English proof (translation)
Establish `key : ∀ s, r ≤ s → ∃ f' : (ZMod (l ^ s))ˣ → Qbar l, (∀ j : ℕ, ‖f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ a) ∧ ∑ x, f' x * μ s x = ∑ x, f x * μ r x`. Introduce `s hs`. Proceed by induction on `s, hs using Nat.le_induction with`. Consider the case `base => exact ⟨f, hf, rfl⟩`. Consider the case `succ s hs ih`.

Take `⟨f', h1, h2⟩` from `ih`. Use `⟨fun y => f' (red l s y), fun j => by simpa only [map_pow, red_un] using h1 j, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2, ← Finset.sum_fiberwise Finset.univ (red l s)]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hn s x, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[(Finset.mem_filter.1 hy).2]`. Take `⟨n, hn'⟩` from `small (l := l) ha`. Take `⟨r₀, hr₀⟩` from `h0 n`.

Use `set s := r + r₀ + n + 1 with hs`. Take `⟨f', h1, h2⟩` from `key s (by omega)`. Establish `h3 : ‖∑ x, eta φ k s x * μ s x‖ ≤ a`. Use `hr₀ s (by omega)` as an intermediate fact. Rewrite `this` using `[Cg, sub_zero]`.

Conclude with `this.trans (hn' n le_rfl)`. Establish `e : ∑ x, f' x * μ s x = ∑ x, (f' x - eta φ k s x) * μ s x + ∑ x, eta φ k s x * μ s x`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`. Rewrite using `[← h2, e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h3)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha.le fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `(mul_le_of_le_one_right (norm_nonneg _) (hμ s x)).trans ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `(mem_powers_iff_mem_zpowers.2 (hgen s x) : x ∈ Submonoid.powers (un g hg s))`.

Establish `h4` using `nsub (f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j) (eta φ k s (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j)`. Rewrite `h4` using `[sub_sub_sub_cancel_right]`. Conclude with `h4.trans (max_le (h1 j) ((eta_near φ k hg (by omega) j).trans (hn' s (by omega))))`.
-/
private theorem sum_bound (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {g : ℕ} (hg : ¬ l ∣ g)
    (hgen : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), x ∈ Subgroup.zpowers (un g hg r))
    (μ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (hμ : ∀ r x, ‖μ r x‖ ≤ 1)
    (hn : ∀ r (x : (ZMod (l ^ r))ˣ), μ r x =
      ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ => red l r x' = x), μ (r + 1) x')
    (h0 : ∀ n : ℕ, ∃ r₀, ∀ r, r₀ ≤ r → Cg n (∑ x, eta φ k r x * μ r x) 0)
    (a : ℝ) (ha : 0 < a) (r : ℕ) (f : (ZMod (l ^ r))ˣ → Qbar l)
    (hf : ∀ j : ℕ, ‖f (un g hg r ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ a) :
    ‖∑ x, f x * μ r x‖ ≤ a := by
  have key : ∀ s, r ≤ s → ∃ f' : (ZMod (l ^ s))ˣ → Qbar l,
      (∀ j : ℕ, ‖f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ a) ∧
        ∑ x, f' x * μ s x = ∑ x, f x * μ r x := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact ⟨f, hf, rfl⟩
    | succ s hs ih =>
      obtain ⟨f', h1, h2⟩ := ih
      refine ⟨fun y => f' (red l s y), fun j => by simpa only [map_pow, red_un] using h1 j, ?_⟩
      rw [← h2, ← Finset.sum_fiberwise Finset.univ (red l s)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hn s x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      beta_reduce
      rw [(Finset.mem_filter.1 hy).2]
  obtain ⟨n, hn'⟩ := small (l := l) ha
  obtain ⟨r₀, hr₀⟩ := h0 n
  set s := r + r₀ + n + 1 with hs
  obtain ⟨f', h1, h2⟩ := key s (by omega)
  have h3 : ‖∑ x, eta φ k s x * μ s x‖ ≤ a := by
    have := hr₀ s (by omega)
    rw [Cg, sub_zero] at this
    exact this.trans (hn' n le_rfl)
  have e : ∑ x, f' x * μ s x = ∑ x, (f' x - eta φ k s x) * μ s x + ∑ x, eta φ k s x * μ s x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [← h2, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h3)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha.le fun x _ => ?_
  rw [norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (hμ s x)).trans ?_
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hgen s x) : x ∈ Submonoid.powers (un g hg s))
  have h4 := nsub (f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j)
    (eta φ k s (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j)
  rw [sub_sub_sub_cancel_right] at h4
  exact h4.trans (max_le (h1 j) ((eta_near φ k hg (by omega) j).trans (hn' s (by omega))))

/- English proof (translation)
Use `⟨fun y => ∑ i ∈ Finset.range (orderOf γ), if γ ^ i = y then τ ^ i else 0, fun j => ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Finset.sum_eq_single (j % orderOf γ)]`. Rewrite using `[if_pos (pow_mod_orderOf γ j)]`. Introduce `i hi hne`.

Rewrite using `[if_neg]`. Introduce `h`. Rewrite `h` using `[pow_inj_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]`. Conclude with `hne h`. Introduce `h`.

Conclude with `absurd (Finset.mem_range.2 (Nat.mod_lt _ (orderOf_pos γ))) h`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem logfun {Γ : Type} [Group Γ] [Fintype Γ] (γ : Γ) (τ : Qbar l) (μ : Γ → Qbar l) :
    ∃ f : Γ → Qbar l, (∀ j : ℕ, f (γ ^ j) = τ ^ (j % orderOf γ)) ∧
      ∑ x, f x * μ x = ∑ i ∈ Finset.range (orderOf γ), τ ^ i * μ (γ ^ i) := by
  classical
  refine ⟨fun y => ∑ i ∈ Finset.range (orderOf γ), if γ ^ i = y then τ ^ i else 0, fun j => ?_, ?_⟩
  · beta_reduce
    rw [Finset.sum_eq_single (j % orderOf γ)]
    · rw [if_pos (pow_mod_orderOf γ j)]
    · intro i hi hne
      rw [if_neg]
      intro h
      rw [pow_inj_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)] at h
      exact hne h
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ (orderOf_pos γ))) h
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

/- English proof (translation)
Take `⟨⟨β⟩, h⟩` from `pBasEx l c`. Establish `h1` using `(h β).1`. Establish `e` using `congrArg (fun y : c.O => (y : Qbar l)) (β.e.sum_repr ⟨x, hx⟩)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Algebra.smul_def] at e`. Rewrite using `[← e]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Establish `h2 : ‖((β.e i : c.O) : Qbar l)‖ ≤ 1` using `h1 i`. Rewrite using `[Subalgebra.coe_mul, Subalgebra.coe_algebraMap, norm_mul, alg_norm]`. Conclude with `mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h2`.
-/
private theorem coef_norm (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  have h1 := (h β).1
  have e := congrArg (fun y : c.O => (y : Qbar l)) (β.e.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Algebra.smul_def] at e
  rw [← e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  have h2 : ‖((β.e i : c.O) : Qbar l)‖ ≤ 1 := h1 i
  rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, norm_mul, alg_norm]
  exact mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h2

/- English proof (translation)
Take `⟨⟨β⟩, h⟩` from `pBasEx l c`. Establish `hs` using `PadicInt.unitCoeff_spec ht`. Use `set u := PadicInt.unitCoeff ht`. Use `set m := t.valuation`. Establish `hu : ‖algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l])‖ = 1` using `by rw [alg_norm]; exact PadicInt.norm_units u`.

Establish `e : algebraMap ℤ_[l] (Qbar l) t = algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) * (l : Qbar l) ^ m`. Rewrite using `[hs, map_mul, map_pow, map_natCast]`. Take `⟨y, hy⟩` from `(h β).2.2.1 m ⟨x, hx⟩ (by`. Rewrite `hle` using `[e, norm_mul, hu, one_mul]`. Simplify `hle)` using `[Cg]`.

Establish `hy' : x = (l : Qbar l) ^ m * (y : Qbar l)` using `by simpa using congrArg (fun y : c.O => (y : Qbar l)) hy`. Establish `hl : (l : Qbar l) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hu0 : algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) ≠ 0` using `by intro h0; simp [h0] at hu`. Establish `e2 : x / algebraMap ℤ_[l] (Qbar l) t = (y : Qbar l) * (algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]))⁻¹`. Rewrite using `[e, hy']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Conclude with `mul_mem y.2 ((h β).2.2.2 _ (c.O.algebraMap_mem _) hu)`.
-/
private theorem coef_div (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) {t : ℤ_[l]} (ht : t ≠ 0)
    (hle : ‖x‖ ≤ ‖algebraMap ℤ_[l] (Qbar l) t‖) : x / algebraMap ℤ_[l] (Qbar l) t ∈ c.O := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  have hs := PadicInt.unitCoeff_spec ht
  set u := PadicInt.unitCoeff ht
  set m := t.valuation
  have hu : ‖algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l])‖ = 1 := by rw [alg_norm]; exact PadicInt.norm_units u
  have e : algebraMap ℤ_[l] (Qbar l) t = algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) * (l : Qbar l) ^ m := by
    rw [hs, map_mul, map_pow, map_natCast]
  obtain ⟨y, hy⟩ := (h β).2.2.1 m ⟨x, hx⟩ (by
    rw [e, norm_mul, hu, one_mul] at hle
    simpa [Cg] using hle)
  have hy' : x = (l : Qbar l) ^ m * (y : Qbar l) := by simpa using congrArg (fun y : c.O => (y : Qbar l)) hy
  have hl : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) ≠ 0 := by intro h0; simp [h0] at hu
  have e2 : x / algebraMap ℤ_[l] (Qbar l) t = (y : Qbar l) * (algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]))⁻¹ := by
    rw [e, hy']; field_simp
  rw [e2]
  exact mul_mem y.2 ((h β).2.2.2 _ (c.O.algebraMap_mem _) hu)

end UpperTheory.Kd.C7.DivAlg

open UpperTheory.Kd.C7.DivAlg in
/- English proof (translation)
Introduce `l _ c g hg h2 hgen φ k hk`. Establish `hθ : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1`. Rewrite using `[norm_mul, norm_pow, phi_norm φ hg, norm_nat_one hg, one_pow, one_mul]`. Establish `hne` using `fun r => theta_ne φ hg h2 hk (orderOf_pos (un g hg r))`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z : ℤ_[l], algebraMap ℤ_[l] (Qbar l) z = (φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹ := by`.

Take `⟨w, hw⟩` from `root_mem (phi_pow φ hg)`. Establish `e : algebraMap ℤ_[l] (Qbar l) (w * (g : ℤ_[l]) ^ k) = φ (g : ZMod l) * (g : Qbar l) ^ k`. Rewrite using `[map_mul, map_pow, map_natCast, hw]`. Establish `hu : IsUnit (w * (g : ℤ_[l]) ^ k)` using `by rw [PadicInt.isUnit_iff, ← alg_norm, e, hθ]`. Take `⟨v, hv⟩` from `hu.exists_right_inv`.

Use `⟨v, eq_inv_of_mul_eq_one_right ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← map_mul, hv, map_one]`. Establish `hsum` using `sum_bound φ k hg hgen`. Generalize the expression as in `φ (g : ZMod l) * (g : Qbar l) ^ k = θ at hθ hne hz hsum ⊢`. Establish `hθ0 : θ ≠ 0` using `by rintro rfl; simp at hθ`.

Use `⟨fun r => ?_, fun μ hμ hn h0 r => ?_⟩` and prove the remaining obligations. Establish `hpos : 0 < ‖1 - θ ^ orderOf (un g hg r)‖` using `norm_pos_iff.2 (sub_ne_zero.2 (hne r).symm)`. Take `⟨c₃, hc⟩` from `small (l := l) hpos`. Use `⟨c₃, fun q n h x => ?_⟩` and prove the remaining obligations. Establish `h1` using `iter (un g hg r) θ hθ.le q ‖((l : ℕ) : Qbar l) ^ (n + c₃)‖ (norm_nonneg _) (fun x => by simpa only [Cg, sub_zero] using h x) x (orderOf (un g hg r))`.

Rewrite `h1` using `[pow_orderOf_eq_one, mul_one, ← one_sub_mul, norm_mul, pow_add, norm_mul]`. Rewrite using `[Cg, sub_zero]`. Establish `h3` using `h1.trans (mul_le_mul_of_nonneg_left (hc c₃ le_rfl) (norm_nonneg _))`. Rewrite `h3` using `[mul_comm]`. Conclude with `le_of_mul_le_mul_right h3 hpos`.

Use `set γ := un g hg r with hγ set N := orderOf γ with hN set τ := θ⁻¹ with hτ`. Establish `hτn : ‖τ‖ = 1` using `by rw [hτ, norm_inv, hθ, inv_one]`. Establish `hτ1 : τ ^ N - 1 ≠ 0`. Rewrite using `[sub_ne_zero, hτ, inv_pow, Ne, inv_eq_one]`. Conclude with `hne r`.

Establish `hτO : τ ∈ c.O` using `hz ▸ c.O.algebraMap_mem z`. Establish `hμn : ∀ r x, ‖μ r x‖ ≤ 1` using `fun r x => coef_norm c (hμ r x)`. Set `S : (ZMod (l ^ r))ˣ → Qbar l` to `fun x => ∑ i ∈ Finset.range N, τ ^ i * μ r (x * γ ^ i)`. Establish `hS : ∀ x, τ * S (x * γ) - S x = (τ ^ N - 1) * μ r x` using `fun x => by`. Establish `e` using `Finset.sum_range_sub (fun i => τ ^ i * μ r (x * γ ^ i)) N`.

Rewrite `e` using `[hN, pow_orderOf_eq_one, ← hN]`. Simplify using `only [pow_zero, mul_one, one_mul] at e`. Rewrite using `[sub_mul, one_mul, ← e, Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ' τ, pow_succ' γ, mul_assoc, mul_assoc]`. Establish `hS1 : ‖S 1‖ ≤ ‖τ ^ N - 1‖`. Take `⟨f, hf1, hf2⟩` from `logfun γ τ (μ r)`. Use `hsum μ hμn hn h0 _ (norm_pos_iff.2 hτ1) r f (fun j => by` as an intermediate fact.

Rewrite using `[hf1]`. Conclude with `pow_mod_near τ hτn.le N j)`. Rewrite `this` using `[hf2]`. Simplify `this` using `only [S, one_mul]`. Establish `hSx : ∀ x, ‖S x‖ ≤ ‖τ ^ N - 1‖` using `fun x => by`.

Take `⟨j, rfl⟩` from `(mem_powers_iff_mem_zpowers.2 (hgen r x) : x ∈ Submonoid.powers γ)`. Use `beta_reduce`. Proceed by induction on `j with`. Consider the case `zero => simpa using hS1`. Consider the case `succ j ih`.

Establish `e : τ * S (γ ^ (j + 1)) = (τ ^ N - 1) * μ r (γ ^ j) + S (γ ^ j)`. Rewrite using `[← hS, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖τ * S (γ ^ (j + 1))‖ ≤ ‖τ ^ N - 1‖`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hμn _ _)`. Rewrite `h1` using `[norm_mul, hτn, one_mul]`. Then use the resulting hypothesis. Establish `hSO : ∀ x, S x ∈ c.O` using `fun x => sum_mem fun i _ => mul_mem (pow_mem hτO i) (hμ r _)`.

Establish `ht : algebraMap ℤ_[l] (Qbar l) (z ^ N - 1) = τ ^ N - 1` using `by rw [map_sub, map_pow, hz, map_one]`. Establish `ht0 : z ^ N - 1 ≠ 0` using `fun h => hτ1 (by rw [← ht, h, map_zero])`. Use `⟨fun x => τ * (S x / (τ ^ N - 1)), fun x => mul_mem hτO ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← ht]`. Conclude with `coef_div c (hSO x) ht0 (by rw [ht]; exact hSx x)`.

Establish `e : θ * τ = 1` using `mul_inv_cancel₀ hθ0 beta_reduce`. Rewrite using `[← mul_assoc θ, e, one_mul, ← mul_div_assoc, ← sub_div, hS, mul_div_cancel_left₀ _ hτ1]`.
-/
theorem UpperTheory.Kd.C7.pDivAlg :
    UpperTheory.Kd.C7.SDivAlg := by
  intro l _ c g hg h2 hgen φ k hk
  have hθ : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1 := by
    rw [norm_mul, norm_pow, phi_norm φ hg, norm_nat_one hg, one_pow, one_mul]
  have hne := fun r => theta_ne φ hg h2 hk (orderOf_pos (un g hg r))
  obtain ⟨z, hz⟩ : ∃ z : ℤ_[l], algebraMap ℤ_[l] (Qbar l) z = (φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹ := by
    obtain ⟨w, hw⟩ := root_mem (phi_pow φ hg)
    have e : algebraMap ℤ_[l] (Qbar l) (w * (g : ℤ_[l]) ^ k) = φ (g : ZMod l) * (g : Qbar l) ^ k := by
      rw [map_mul, map_pow, map_natCast, hw]
    have hu : IsUnit (w * (g : ℤ_[l]) ^ k) := by rw [PadicInt.isUnit_iff, ← alg_norm, e, hθ]
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine ⟨v, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← e, ← map_mul, hv, map_one]
  have hsum := sum_bound φ k hg hgen
  generalize φ (g : ZMod l) * (g : Qbar l) ^ k = θ at hθ hne hz hsum ⊢
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  refine ⟨fun r => ?_, fun μ hμ hn h0 r => ?_⟩
  · have hpos : 0 < ‖1 - θ ^ orderOf (un g hg r)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne r).symm)
    obtain ⟨c₃, hc⟩ := small (l := l) hpos
    refine ⟨c₃, fun q n h x => ?_⟩
    have h1 := iter (un g hg r) θ hθ.le q ‖((l : ℕ) : Qbar l) ^ (n + c₃)‖ (norm_nonneg _)
      (fun x => by simpa only [Cg, sub_zero] using h x) x (orderOf (un g hg r))
    rw [pow_orderOf_eq_one, mul_one, ← one_sub_mul, norm_mul, pow_add, norm_mul] at h1
    rw [Cg, sub_zero]
    have h3 := h1.trans (mul_le_mul_of_nonneg_left (hc c₃ le_rfl) (norm_nonneg _))
    rw [mul_comm] at h3
    exact le_of_mul_le_mul_right h3 hpos
  · set γ := un g hg r with hγ
    set N := orderOf γ with hN
    set τ := θ⁻¹ with hτ
    have hτn : ‖τ‖ = 1 := by rw [hτ, norm_inv, hθ, inv_one]
    have hτ1 : τ ^ N - 1 ≠ 0 := by
      rw [sub_ne_zero, hτ, inv_pow, Ne, inv_eq_one]; exact hne r
    have hτO : τ ∈ c.O := hz ▸ c.O.algebraMap_mem z
    have hμn : ∀ r x, ‖μ r x‖ ≤ 1 := fun r x => coef_norm c (hμ r x)
    let S : (ZMod (l ^ r))ˣ → Qbar l := fun x => ∑ i ∈ Finset.range N, τ ^ i * μ r (x * γ ^ i)
    have hS : ∀ x, τ * S (x * γ) - S x = (τ ^ N - 1) * μ r x := fun x => by
      have e := Finset.sum_range_sub (fun i => τ ^ i * μ r (x * γ ^ i)) N
      rw [hN, pow_orderOf_eq_one, ← hN] at e
      simp only [pow_zero, mul_one, one_mul] at e
      rw [sub_mul, one_mul, ← e, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ' τ, pow_succ' γ, mul_assoc, mul_assoc]
    have hS1 : ‖S 1‖ ≤ ‖τ ^ N - 1‖ := by
      obtain ⟨f, hf1, hf2⟩ := logfun γ τ (μ r)
      have := hsum μ hμn hn h0 _ (norm_pos_iff.2 hτ1) r f (fun j => by
        rw [hf1]; exact pow_mod_near τ hτn.le N j)
      rw [hf2] at this
      simpa only [S, one_mul] using this
    have hSx : ∀ x, ‖S x‖ ≤ ‖τ ^ N - 1‖ := fun x => by
      obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hgen r x) : x ∈ Submonoid.powers γ)
      beta_reduce
      induction j with
      | zero => simpa using hS1
      | succ j ih =>
        have e : τ * S (γ ^ (j + 1)) = (τ ^ N - 1) * μ r (γ ^ j) + S (γ ^ j) := by
          rw [← hS, pow_succ]; ring
        have h1 : ‖τ * S (γ ^ (j + 1))‖ ≤ ‖τ ^ N - 1‖ := by
          rw [e]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hμn _ _)
        rwa [norm_mul, hτn, one_mul] at h1
    have hSO : ∀ x, S x ∈ c.O := fun x => sum_mem fun i _ => mul_mem (pow_mem hτO i) (hμ r _)
    have ht : algebraMap ℤ_[l] (Qbar l) (z ^ N - 1) = τ ^ N - 1 := by rw [map_sub, map_pow, hz, map_one]
    have ht0 : z ^ N - 1 ≠ 0 := fun h => hτ1 (by rw [← ht, h, map_zero])
    refine ⟨fun x => τ * (S x / (τ ^ N - 1)), fun x => mul_mem hτO ?_, fun x => ?_⟩
    · rw [← ht]
      exact coef_div c (hSO x) ht0 (by rw [ht]; exact hSx x)
    · have e : θ * τ = 1 := mul_inv_cancel₀ hθ0
      beta_reduce
      rw [← mul_assoc θ, e, one_mul, ← mul_div_assoc, ← sub_div, hS, mul_div_cancel_left₀ _ hτ1]
