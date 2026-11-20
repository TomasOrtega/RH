import Mathlib

namespace GlobalTheory.HeckeTate

section Ring

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `htop : Ideal.span {N, 1 - x} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨q, hq, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `h1 : N ∈ q` using `hle (Ideal.subset_span (by simp))`. Establish `h2 : 1 - x ∈ q` using `hle (Ideal.subset_span (by simp))`.

Conclude with `hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (hx q hq h1)))`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 htop)`. Take `⟨c, hc⟩` from `h`. Conclude with `⟨a * x + b * c, by linear_combination (-x) * hab + b * hc⟩`.
-/
theorem dvd_of_idem {N x : R} (h : N ∣ x * (1 - x))
    (hx : ∀ q : Ideal R, q.IsMaximal → N ∈ q → x ∈ q) : N ∣ x := by
  have htop : Ideal.span {N, 1 - x} = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : N ∈ q := hle (Ideal.subset_span (by simp))
    have h2 : 1 - x ∈ q := hle (Ideal.subset_span (by simp))
    exact hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (hx q hq h1)))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 htop)
  obtain ⟨c, hc⟩ := h
  exact ⟨a * x + b * c, by linear_combination (-x) * hab + b * hc⟩

/- English proof (translation)
Apply `dvd_of_idem` to reduce the goal to its premises. Take `⟨a, ha⟩` from `hf`. Take `⟨b, hb⟩` from `hg`. Conclude with `⟨a * g * g + f * b, by linear_combination (g * g) * ha + f * hb⟩`. Introduce `q hq hN`.

Break down `h q hq hN with h | h` into its components or cases. Conclude with `q.mul_mem_right _ h`. Conclude with `q.mul_mem_left _ h`.
-/
theorem dvd_mul_of_idem {N f g : R} (hf : N ∣ f * (1 - f)) (hg : N ∣ g * (1 - g))
    (h : ∀ q : Ideal R, q.IsMaximal → N ∈ q → f ∈ q ∨ g ∈ q) : N ∣ f * g := by
  apply dvd_of_idem
  · obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a * g * g + f * b, by linear_combination (g * g) * ha + f * hb⟩
  · intro q hq hN
    rcases h q hq hN with h | h
    · exact q.mul_mem_right _ h
    · exact q.mul_mem_left _ h

def IsPart (P : Ideal R) (N e : R) : Prop :=
  N ∣ e * (1 - e) ∧ 1 - e ∈ P ∧ ∀ q : Ideal R, q.IsMaximal → N ∈ q → q ≠ P → e ∈ q

/- English proof (translation)
Assemble the required witnesses or components as `⟨hN.trans h.1, h.2.1, fun q hq hq' hne => h.2.2 q hq (q.mem_of_dvd hN hq') hne⟩`.
-/
theorem IsPart.of_dvd {P : Ideal R} {N N' e : R} (h : IsPart P N' e) (hN : N ∣ N') : IsPart P N e :=
  ⟨hN.trans h.1, h.2.1, fun q hq hq' hne => h.2.2 q hq (q.mem_of_dvd hN hq') hne⟩

/- English proof (translation)
Establish `key : ∀ {f g : R}, IsPart P N f → IsPart P N g → N ∣ f * (1 - g)`. Introduce `f g hf hg`. Use `dvd_mul_of_idem hf.1 (by simpa [mul_comm] using hg.1) fun q hq hN => ?_` and prove the remaining obligations. Distinguish the cases in `hqP : q = P`. Conclude with `Or.inr (hqP ▸ hg.2.1)`.

Conclude with `Or.inl (hf.2.2 q hq hN hqP)`. Use `(key h h').sub (key h' h)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsPart.unique {P : Ideal R} {N e e' : R} (h : IsPart P N e) (h' : IsPart P N e') :
    N ∣ e - e' := by
  have key : ∀ {f g : R}, IsPart P N f → IsPart P N g → N ∣ f * (1 - g) := by
    intro f g hf hg
    refine dvd_mul_of_idem hf.1 (by simpa [mul_comm] using hg.1) fun q hq hN => ?_
    by_cases hqP : q = P
    · exact Or.inr (hqP ▸ hg.2.1)
    · exact Or.inl (hf.2.2 q hq hN hqP)
  have := (key h h').sub (key h' h)
  convert this using 1
  ring

/- English proof (translation)
Establish `htop : Ideal.span {N, s, 1 - e} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨q, hq, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `h1 : N ∈ q` using `hle (Ideal.subset_span (by simp))`. Establish `h2 : 1 - e ∈ q` using `hle (Ideal.subset_span (by simp))`.

Establish `h3 : s ∈ q` using `hle (Ideal.subset_span (by simp))`. Distinguish the cases in `hqP : q = P`. Conclude with `hs (hqP ▸ h3)`. Conclude with `hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (h.2.2 q hq h1 hqP)))`. Take `⟨a, b, c, habc⟩` from `Submodule.mem_span_triple.1 ((Ideal.eq_top_iff_one _).1 htop)`.

Simplify using `only [smul_eq_mul] at habc`. Take `⟨d, hd⟩` from `h.1`. Conclude with `⟨b, -(a * e) - c * d, by linear_combination e * habc - c * hd⟩`.
-/
theorem IsPart.exists_inv {P : Ideal R} {N e s : R} (h : IsPart P N e) (hs : s ∉ P) :
    ∃ w, N ∣ w * s * e - e := by
  have htop : Ideal.span {N, s, 1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : N ∈ q := hle (Ideal.subset_span (by simp))
    have h2 : 1 - e ∈ q := hle (Ideal.subset_span (by simp))
    have h3 : s ∈ q := hle (Ideal.subset_span (by simp))
    by_cases hqP : q = P
    · exact hs (hqP ▸ h3)
    · exact hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (h.2.2 q hq h1 hqP)))
  obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.1 ((Ideal.eq_top_iff_one _).1 htop)
  simp only [smul_eq_mul] at habc
  obtain ⟨d, hd⟩ := h.1
  exact ⟨b, -(a * e) - c * d, by linear_combination e * habc - c * hd⟩

/- English proof (translation)
Establish `h0 : Ideal.span {N} ≠ (0 : Ideal R)` using `by simpa using hN`. Take `⟨k, C, hC, hk⟩` from `WfDvdMonoid.max_power_factor' (x := P) h0 (fun h => hP.ne_top (Ideal.isUnit_iff.1 h))`. Establish `hCP : P ⊔ C = ⊤`. Assume the negation of the conclusion as `hne`. Use `hP.eq_of_le hne le_sup_left` as an intermediate fact.

Conclude with `hC (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))`. Establish `hCP' : P ^ (k + 1) ⊔ C = ⊤` using `Ideal.pow_sup_eq_top hCP`. Take `⟨x, hx, e, he, hxe⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hCP')`. Establish `hx' : 1 - e = x` using `by rw [← hxe]; ring`. Use `⟨e, ?_, ?_, fun q hq hNq hne => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.mem_span_singleton, hk, hx', mul_comm e]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_le_pow_right (Nat.le_succ k) hx) he`. Rewrite using `[hx']`. Conclude with `Ideal.pow_le_self (Nat.succ_ne_zero k) hx`. Establish `: P ^ k * C ≤ q` using `by rw [← hk]; simpa using hNq`.

Break down `hq.isPrime.mul_le.1 this with h | h` into its components or cases. Conclude with `absurd (hP.eq_of_le hq.ne_top (Ideal.IsPrime.le_of_pow_le (hP := hq.isPrime) h)).symm hne`. Conclude with `h he`.
-/
theorem exists_isPart [IsDedekindDomain R] {P : Ideal R} (hP : P.IsMaximal) {N : R} (hN : N ≠ 0) :
    ∃ e, IsPart P N e := by
  have h0 : Ideal.span {N} ≠ (0 : Ideal R) := by simpa using hN
  obtain ⟨k, C, hC, hk⟩ := WfDvdMonoid.max_power_factor' (x := P) h0
    (fun h => hP.ne_top (Ideal.isUnit_iff.1 h))
  have hCP : P ⊔ C = ⊤ := by
    by_contra hne
    have := hP.eq_of_le hne le_sup_left
    exact hC (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
  have hCP' : P ^ (k + 1) ⊔ C = ⊤ := Ideal.pow_sup_eq_top hCP
  obtain ⟨x, hx, e, he, hxe⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hCP')
  have hx' : 1 - e = x := by rw [← hxe]; ring
  refine ⟨e, ?_, ?_, fun q hq hNq hne => ?_⟩
  · rw [← Ideal.mem_span_singleton, hk, hx', mul_comm e]
    exact Ideal.mul_mem_mul (Ideal.pow_le_pow_right (Nat.le_succ k) hx) he
  · rw [hx']; exact Ideal.pow_le_self (Nat.succ_ne_zero k) hx
  · have : P ^ k * C ≤ q := by rw [← hk]; simpa using hNq
    rcases hq.isPrime.mul_le.1 this with h | h
    · exact absurd (hP.eq_of_le hq.ne_top (Ideal.IsPrime.le_of_pow_le (hP := hq.isPrime) h)).symm hne
    · exact h he

end Ring

section Module

variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

def mults (M : Type) [AddCommGroup M] [Module R M] (N : R) : Submodule R M :=
  LinearMap.range (N • (LinearMap.id : M →ₗ[R] M))

/- English proof (translation)
Simplify using `[mults, eq_comm]`.
-/
theorem mem_mults {N : R} {x : M} : x ∈ mults M N ↔ ∃ y, x = N • y := by
  simp [mults, eq_comm]

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Conclude with `mem_mults.2 ⟨c • x, mul_smul _ _ _⟩`.
-/
theorem smul_mem_mults {N r : R} (h : N ∣ r) (x : M) : r • x ∈ mults M N := by
  obtain ⟨c, rfl⟩ := h
  exact mem_mults.2 ⟨c • x, mul_smul _ _ _⟩

/- English proof (translation)
Establish `: (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x = (a₁ * b₂) • w₂ (u₁ x) + (a₁ * b₃) • w₃ (u₁ x) + (a₂ * b₁) • w₁ (u₂ x) + (a₂ * b₃) • w₃ (u₂ x) + (a₃ * b₁) • w₁ (u₃ x) + (a₃ * b₂) • w₂ (u₃ x) + (a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) • x`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, h₁, h₂, h₃]`. Use `module`. Rewrite using `[this]`. Use the proof step `repeat' apply Submodule.add_mem`.

Apply the tactic sequence `all_goals exact smul_mem_mults (by assumption) _`.
-/
theorem comp_sub_mem {N : R} (u₁ u₂ u₃ : M →ₗ[R] M') (w₁ w₂ w₃ : M' →ₗ[R] M) {t₁ t₂ t₃ a₁ a₂ a₃ b₁ b₂ b₃ : R}
    (h₁ : ∀ x, w₁ (u₁ x) = t₁ • x) (h₂ : ∀ x, w₂ (u₂ x) = t₂ • x) (h₃ : ∀ x, w₃ (u₃ x) = t₃ • x)
    (h12 : N ∣ a₁ * b₂) (h13 : N ∣ a₁ * b₃) (h21 : N ∣ a₂ * b₁) (h23 : N ∣ a₂ * b₃)
    (h31 : N ∣ a₃ * b₁) (h32 : N ∣ a₃ * b₂)
    (h : N ∣ a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) (x : M) :
    (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x ∈ mults M N := by
  have : (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x =
      (a₁ * b₂) • w₂ (u₁ x) + (a₁ * b₃) • w₃ (u₁ x) + (a₂ * b₁) • w₁ (u₂ x) + (a₂ * b₃) • w₃ (u₂ x) +
      (a₃ * b₁) • w₁ (u₃ x) + (a₃ * b₂) • w₂ (u₃ x) +
      (a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) • x := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, h₁, h₂, h₃]
    module
  rw [this]
  repeat' apply Submodule.add_mem
  all_goals exact smul_mem_mults (by assumption) _

def IsUnimod (σ : R ≃+* R) (B : M →+ M →+ ℤ) : Prop :=
  (∀ x y, B x y = -B y x) ∧ (∀ (a : R) x y, B (a • x) y = B x (σ a • y)) ∧ Function.Bijective B

variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}

/- English proof (translation)
The claim follows from `h.1 x y`.
-/
theorem IsUnimod.skew (h : IsUnimod σ B) (x y : M) : B x y = -B y x := h.1 x y

/- English proof (translation)
The claim follows from `h.2.1 a x y`.
-/
theorem IsUnimod.adj (h : IsUnimod σ B) (a : R) (x y : M) : B (a • x) y = B x (σ a • y) := h.2.1 a x y

/- English proof (translation)
The claim follows from `h.2.2`.
-/
theorem IsUnimod.bij (h : IsUnimod σ B) : Function.Bijective B := h.2.2

/- English proof (translation)
The claim follows from `h.bij.1 (AddMonoidHom.ext fun a => by rw [h.skew x, h.skew y, e])`.
-/
theorem IsUnimod.ext (h : IsUnimod σ B) {x y : M} (e : ∀ a, B a x = B a y) : x = y :=
  h.bij.1 (AddMonoidHom.ext fun a => by rw [h.skew x, h.skew y, e])

/- English proof (translation)
Use `choose v hv using fun y => h.bij.2 ((B' y).comp u.toAddMonoidHom)`. Establish `hv' : ∀ a y, B' (u a) y = B a (v y)` using `fun a y => by`. Rewrite using `[h.skew a, hv, h'.skew]`. Both sides reduce to the same expression. Use `⟨⟨⟨v, fun x y => h.ext fun a => ?_⟩, fun r y => h.ext fun a => ?_⟩, hv'⟩` and prove the remaining obligations.

Rewrite using `[map_add, ← hv', ← hv', ← hv', map_add]`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[← hv', ← hσ r, ← h'.adj, ← h.adj, ← hv', map_smul u]`.
-/
theorem exists_adjoint (h : IsUnimod σ B) (h' : IsUnimod σ B') (hσ : ∀ a, σ (σ a) = a) (u : M →ₗ[R] M') :
    ∃ v : M' →ₗ[R] M, ∀ a y, B' (u a) y = B a (v y) := by
  choose v hv using fun y => h.bij.2 ((B' y).comp u.toAddMonoidHom)
  have hv' : ∀ a y, B' (u a) y = B a (v y) := fun a y => by
    rw [h.skew a, hv, h'.skew]; rfl
  refine ⟨⟨⟨v, fun x y => h.ext fun a => ?_⟩, fun r y => h.ext fun a => ?_⟩, hv'⟩
  · rw [map_add, ← hv', ← hv', ← hv', map_add]
  · simp only [RingHom.id_apply]
    rw [← hv', ← hσ r, ← h'.adj, ← h.adj, ← hv', map_smul u]

/- English proof (translation)
Use `h.ext fun a => mul_left_cancel₀ (Int.natCast_ne_zero.2 hn) ?_` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, e]`.
-/
theorem IsUnimod.smul_cancel (h : IsUnimod σ B) {n : ℕ} (hn : n ≠ 0) {x y : M}
    (e : (n : R) • x = (n : R) • y) : x = y := by
  refine h.ext fun a => mul_left_cancel₀ (Int.natCast_ne_zero.2 hn) ?_
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul R,
    ← Nat.cast_smul_eq_nsmul R, e]

/- English proof (translation)
Take `⟨y, rfl⟩` from `mem_mults.1 hx`. Conclude with `mem_mults.2 ⟨u y, map_smul u _ _⟩`.
-/
theorem map_mem_mults {N : R} (u : M →ₗ[R] M') {x : M} (hx : x ∈ mults M N) : u x ∈ mults M' N := by
  obtain ⟨y, rfl⟩ := mem_mults.1 hx
  exact mem_mults.2 ⟨u y, map_smul u _ _⟩

/- English proof (translation)
Establish `hpR : (p : R) ≠ 0` using `Nat.cast_ne_zero.2 hp0`. Establish `hex : ∀ n : ℕ, ∃ e : R, 1 - e ∈ P ∧ σ e ∈ P ∧ (0 < n → IsPart P ((n : R) * p ^ 2) e)`. Introduce `n`. Take `⟨e, he⟩` from `exists_isPart hP (N := ((max n 1 : ℕ) : R) * p ^ 2) (mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (pow_ne_zero _ hpR))`. Use `⟨e, he.2.1, ?_, fun hn => by rwa [max_eq_left (show 1 ≤ n from hn)] at he⟩` and prove the remaining obligations.

Establish `hq : (P.comap (σ : R →+* R)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ σ.surjective`. Use `he.2.2 _ hq ?_ fun hne => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, map_mul, map_pow, map_natCast, map_natCast]`. Conclude with `P.mul_mem_left _ (Ideal.pow_mem_of_mem P hpP 2 two_pos)`. Apply `hP.ne_top` to reduce the goal to its premises.

Rewrite using `[← hPP, eq_comm, sup_eq_left, Ideal.map_le_iff_le_comap, hne]`. Use `choose e he1 heσ he using hex`. Establish `hexw : ∀ n : ℕ, ∃ w : R, 0 < n → (n : R) * p ^ 2 ∣ w * s * e n - e n` using `fun n => by`. Distinguish the cases in `hn : 0 < n`. Take `⟨w, hw⟩` from `(he n hn).exists_inv hs`.

Conclude with `⟨w, fun _ => hw⟩`. Conclude with `⟨0, fun h => absurd h hn⟩`. Use `choose w hw using hexw`. Establish `hexπ : ∀ n : ℕ, ∃ π : M →ₗ[R] M', ∀ a, i (π a) = ((1 - e n - σ (e n)) * p) • a` using `fun n => by choose f hf using hlow _ (P.sub_mem (he1 n) (heσ n))`. Conclude with `⟨⟨⟨f, fun x y => hi (by rw [map_add, hf, hf, hf, smul_add])⟩, fun r x => hi (by simp only [RingHom.id_apply]; rw [map_smul, hf, hf, smul_comm])⟩, hf⟩`.

Use `choose π hπ using hexπ`. Use `choose ρ hρ using fun n => exists_adjoint h h' hσ (π n)`. Take `⟨φa, hφa⟩` from `exists_adjoint h h' hσ φ`. Take `⟨χ, hχ0⟩` from `exists_adjoint h' h hσ φ'`. Establish `hχ : ∀ a y, B' (χ a) y = B a (φ' y)` using `fun a y => by rw [h'.skew, ← hχ0, ← h.skew]`.

Establish `hφχ : ∀ a, φa (χ a) = σ s • a` using `fun a => h.ext fun b => by`. Rewrite using `[← hφa, ← hχ0, hφ, h.adj]`. Establish `hχφ : ∀ y, χ (φa y) = σ s • y` using `fun y => h'.ext fun b => by`. Rewrite using `[← hχ0, ← hφa, hφ', h'.adj]`. Establish `hσ3 : ∀ n, σ (1 - e n - σ (e n)) = 1 - e n - σ (e n)` using `fun n => by`.

Rewrite using `[map_sub, map_sub, map_one, hσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρp : ∀ n y, (p : R) • ρ n y = (1 - e n - σ (e n)) • i y` using `fun n y => h.ext fun a => by`. Apply `mul_left_cancel₀ (Int.natCast_ne_zero.2 hp0)` to reduce the goal to its premises. Establish `h1` using `hB (π n a) y`.

Rewrite `h1` using `[hπ, hρ, h.adj, map_mul, map_natCast, hσ3, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]`. Rewrite using `[Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρπ : ∀ n a, ρ n (π n a) = ((1 - e n - σ (e n)) ^ 2) • a` using `fun n a => h.smul_cancel hp0 (by rw [hρp, hπ]; module)`. Establish `hπρ : ∀ n y, π n (ρ n y) = ((1 - e n - σ (e n)) ^ 2) • y` using `fun n y => hi (by rw [hπ, mul_smul, hρp, map_smul]; module)`.

Establish `hσdvd : ∀ (n : ℕ) (x : R), (n : R) * p ^ 2 ∣ x → (n : R) * p ^ 2 ∣ σ x` using `fun n x hx => by`. Simplify using `using map_dvd σ hx`. Set `G : ℕ → M →ₗ[R] M'` to `fun n => e n • φ + (σ (e n) * σ (w n)) • χ + (1 - e n - σ (e n)) • π n`. Set `H : ℕ → M' →ₗ[R] M` to `fun n => σ (e n) • φa + (e n * w n) • φ' + (1 - e n - σ (e n)) • ρ n`. Establish `hGH : ∀ n a y, B' (G n a) y = B a (H n y)` using `fun n a y => by`.

Simplify using `only [G, H, LinearMap.add_apply, LinearMap.smul_apply, map_add, AddMonoidHom.add_apply, h'.adj, hφa, hχ, hρ, map_smul, map_mul, hσ, hσ3]`. Establish `hcong : ∀ n : ℕ, 0 < n → ∃ c₁ c₂ c₃ c₄ c₅ : R, e n * (1 - e n) = n * c₁ ∧ σ (e n) * (1 - σ (e n)) = n * c₂ ∧ e n * σ (e n) = n * c₃ ∧ w n * s * e n - e n = n * c₄ ∧ σ (w n) * σ s * σ (e n) - σ (e n) = n * c₅` using `fun n hn => by`. Establish `d : (n : R) ∣ (n : R) * p ^ 2` using `dvd_mul_right _ _`. Establish `d2` using `hσdvd n _ (he n hn).1`. Rewrite `d2` using `[map_mul, map_sub, map_one]`.

Establish `d5` using `hσdvd n _ (hw n hn)`. Rewrite `d5` using `[map_sub, map_mul, map_mul]`. Establish `d3` using `dvd_mul_of_idem (he n hn).1 d2 fun q hq hN => by`. Distinguish the cases in `hqP : q = P`. Conclude with `Or.inr (hqP ▸ heσ n)`.

Conclude with `Or.inl ((he n hn).2.2 q hq hN hqP)`. Take `⟨c₁, h₁⟩` from `d.trans (he n hn).1`. Take `⟨c₂, h₂⟩` from `d.trans d2`. Take `⟨c₃, h₃⟩` from `d.trans d3`. Take `⟨c₄, h₄⟩` from `d.trans (hw n hn)`.

Take `⟨c₅, h₅⟩` from `d.trans d5`. Conclude with `⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩`. Establish `hdv : ∀ n : ℕ, 0 < n → ∀ x : R, Ideal.Quotient.mk (Ideal.span {(n : R)}) x = 0 → (n : R) ∣ x` using `fun n _ x hx => Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)`. Establish `hinv : ∀ n : ℕ, 0 < n → (∀ a, H n (G n a) - a ∈ mults M (n : R)) ∧ ∀ y, G n (H n y) - y ∈ mults M' (n : R)` using `fun n hn => by`. Take `⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩` from `hcong n hn`.

Establish `k13 : (n : R) ∣ e n * (1 - e n - σ (e n))` using `⟨c₁ - c₃, by linear_combination h₁ - h₃⟩`. Establish `k23 : (n : R) ∣ σ (e n) * (1 - e n - σ (e n))` using `⟨c₂ - c₃, by linear_combination h₂ - h₃⟩`. Establish `k12 : (n : R) ∣ e n * σ (e n)` using `⟨c₃, h₃⟩`. Establish `k : (n : R) ∣ e n * (e n * w n) * s + σ (e n) * σ (w n) * σ (e n) * σ s + (1 - e n - σ (e n)) * (1 - e n - σ (e n)) * (1 - e n - σ (e n)) ^ 2 - 1`. Use `((((k13.add k23).mul_left (1 + (1 - e n - σ (e n)) + (1 - e n - σ (e n)) ^ 2)).neg_right.sub ⟨c₁, h₁⟩).sub ⟨c₂, h₂⟩).add ((Dvd.dvd.mul_left ⟨c₄, h₄⟩ (e n)).add (Dvd.dvd.mul_left ⟨c₅, h₅⟩ (σ (e n))))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hH : H n = (e n * w n) • φ' + σ (e n) • φa + (1 - e n - σ (e n)) • ρ n`. Simplify using `only [H]`. Normalize the expressions using the abelian group laws.

Use `⟨fun a => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hH]`. Use `comp_sub_mem φ χ (π n) φ' φa (ρ n) hφ hφχ (hρπ n) k12 k13 ?_ ?_ ?_ ?_ k a` and prove the remaining obligations. Use `k12.mul_left (σ (w n) * w n) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `k23.mul_left (σ (w n)) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `k13.mul_left (w n) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_comm]` and apply the resulting hypothesis.

Rewrite using `[hH]`. Use `comp_sub_mem φ' φa (ρ n) φ χ (π n) hφ' hχφ (hπρ n) ?_ ?_ ?_ k23 ?_ ?_ ?_ y` and prove the remaining obligations. Use `k12.mul_left (σ (w n) * w n) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `k13.mul_left (w n) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_comm]` and apply the resulting hypothesis. Rewrite using `[mul_comm]` and apply the resulting hypothesis. Use `k23.mul_left (σ (w n)) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `k using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `⟨G, fun n hn a ha => ?_, fun n hn y => ⟨H n y, (hinv n hn).2 y⟩, fun n m hn hm a => ?_, fun n hn a b => ?_, fun n hn hnp a => ?_⟩` and prove the remaining obligations. Simplify using `using (mults M (n : R)).sub_mem (map_mem_mults (H n) ha) ((hinv n hn).1 a)`. Establish `hnm : 0 < n * m` using `Nat.mul_pos hn hm`.

Establish `d0 : (n : R) * p ^ 2 ∣ ((n * m : ℕ) : R) * p ^ 2` using `⟨m, by push_cast; ring⟩`. Establish `d : (n : R) ∣ (n : R) * p ^ 2` using `dvd_mul_right _ _`. Establish `u1` using `((he _ hnm).of_dvd d0).unique (he n hn)`. Establish `u2` using `hσdvd n _ u1`. Rewrite `u2` using `[map_sub]`.

Establish `u3 : (n : R) * p ^ 2 ∣ e (n * m) * w (n * m) - e n * w n`. Use `((u1.mul_left (w (n * m) - w (n * m) * s * w n)).add ((d0.trans (hw _ hnm)).mul_left (w n))).sub ((hw n hn).mul_left (w (n * m)))` as an intermediate fact. Use `this.add (u1.mul_left (w n))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `u4` using `hσdvd n _ u3`. Rewrite `u4` using `[map_sub, map_mul, map_mul]`. Take `⟨c, hc⟩` from `(u1.add u2).mul_left (-((1 - e (n * m) - σ (e (n * m))) + (1 - e n - σ (e n))))`. Take `⟨y, hy⟩` from `hsq ((c * p) • a)`. Establish `u5 : (1 - e (n * m) - σ (e (n * m))) • π (n * m) a - (1 - e n - σ (e n)) • π n a = (n : R) • y`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[map_sub, map_smul, map_smul, map_smul, hπ, hπ, hy, smul_smul, smul_smul, smul_smul, smul_smul, ← sub_smul]`. Use `congr 1`. Take the linear combination `(p : R) * hc`. Establish `: G (n * m) a - G n a = (e (n * m) - e n) • φ a + (σ (e (n * m)) * σ (w (n * m)) - σ (e n) * σ (w n)) • χ a + (n : R) • y`.

Rewrite using `[← u5]`. Simplify using `only [G, LinearMap.add_apply, LinearMap.smul_apply]`. Use `module`. Rewrite using `[this]`. Conclude with `add_mem (add_mem (smul_mem_mults (d.trans u1) _) (smul_mem_mults (d.trans u4) _)) (smul_mem_mults dvd_rfl _)`.

Take `⟨y, hy⟩` from `mem_mults.1 ((hinv n hn).1 b)`. Rewrite using `[hGH, ← map_sub, hy, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`. Establish `d : (n : R) ∣ (n : R) * p ^ 2` using `dvd_mul_right _ _`. Establish `hen : (n : R) ∣ e n`.

Establish `he'` using `(he n hn).of_dvd d`. Use `dvd_of_idem he'.1 fun q hq hN => he'.2.2 q hq hN fun hqP => hP.ne_top ?_` and prove the remaining obligations. Take `⟨u, v, huv⟩` from `(Nat.isCoprime_iff_coprime.2 hnp).map (Int.castRingHom R)`. Rewrite using `[Ideal.eq_top_iff_one, ← huv]`. Conclude with `P.add_mem (P.mul_mem_left _ (by simpa [hqP] using hN)) (P.mul_mem_left _ (by simpa using hpP))`.

Establish `hen' : (n : R) ∣ σ (e n)` using `by simpa using map_dvd σ hen`. Establish `: i (G n a) - (p : R) • a = e n • i (φ a) + (σ (e n) * σ (w n)) • i (χ a) + ((e n + σ (e n)) * ((e n + σ (e n) - 2) * p)) • a`. Simplify using `only [G, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hπ]`. Use `module`. Rewrite using `[this]`.

Conclude with `add_mem (add_mem (smul_mem_mults hen _) (smul_mem_mults (hen'.mul_right _) _)) (smul_mem_mults ((hen.add hen').mul_right _) _)`.
-/
theorem exists_glued [IsDedekindDomain R] [CharZero R] (h : IsUnimod σ B) (h' : IsUnimod σ B')
    (hσ : ∀ a, σ (σ a) = a) {P : Ideal R} (hP : P.IsMaximal) (hPP : P ⊔ P.map (σ : R →+* R) = ⊤)
    {p : ℕ} (hp0 : p ≠ 0) (hpP : (p : R) ∈ P) (i : M' →ₗ[R] M) (hi : Function.Injective i)
    (hB : ∀ x y, B (i x) (i y) = (p : ℤ) ^ 2 * B' x y)
    (hsq : ∀ a, ∃ y, i y = (p : R) ^ 2 • a) (hlow : ∀ γ ∈ P, ∀ a, ∃ y, i y = (γ * p) • a)
    (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) {s : R} (hs : s ∉ P) (hφ : ∀ a, φ' (φ a) = s • a)
    (hφ' : ∀ y, φ (φ' y) = s • y) :
    ∃ G : ℕ → M →ₗ[R] M',
      (∀ n : ℕ, 0 < n → ∀ a, G n a ∈ mults M' (n : R) → a ∈ mults M (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ y, ∃ a, G n a - y ∈ mults M' (n : R)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, G (n * m) a - G n a ∈ mults M' (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ B' (G n a) (G n b) - B a b) ∧
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, i (G n a) - (p : R) • a ∈ mults M (n : R)) := by
  have hpR : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp0

  have hex : ∀ n : ℕ, ∃ e : R, 1 - e ∈ P ∧ σ e ∈ P ∧ (0 < n → IsPart P ((n : R) * p ^ 2) e) := by
    intro n
    obtain ⟨e, he⟩ := exists_isPart hP (N := ((max n 1 : ℕ) : R) * p ^ 2)
      (mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (pow_ne_zero _ hpR))
    refine ⟨e, he.2.1, ?_, fun hn => by rwa [max_eq_left (show 1 ≤ n from hn)] at he⟩
    have hq : (P.comap (σ : R →+* R)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ σ.surjective
    refine he.2.2 _ hq ?_ fun hne => ?_
    · rw [Ideal.mem_comap, map_mul, map_pow, map_natCast, map_natCast]
      exact P.mul_mem_left _ (Ideal.pow_mem_of_mem P hpP 2 two_pos)
    · apply hP.ne_top
      rw [← hPP, eq_comm, sup_eq_left, Ideal.map_le_iff_le_comap, hne]
  choose e he1 heσ he using hex
  have hexw : ∀ n : ℕ, ∃ w : R, 0 < n → (n : R) * p ^ 2 ∣ w * s * e n - e n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨w, hw⟩ := (he n hn).exists_inv hs
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose w hw using hexw
  have hexπ : ∀ n : ℕ, ∃ π : M →ₗ[R] M', ∀ a, i (π a) = ((1 - e n - σ (e n)) * p) • a := fun n => by
    choose f hf using hlow _ (P.sub_mem (he1 n) (heσ n))
    exact ⟨⟨⟨f, fun x y => hi (by rw [map_add, hf, hf, hf, smul_add])⟩,
      fun r x => hi (by simp only [RingHom.id_apply]; rw [map_smul, hf, hf, smul_comm])⟩, hf⟩
  choose π hπ using hexπ
  choose ρ hρ using fun n => exists_adjoint h h' hσ (π n)
  obtain ⟨φa, hφa⟩ := exists_adjoint h h' hσ φ
  obtain ⟨χ, hχ0⟩ := exists_adjoint h' h hσ φ'
  have hχ : ∀ a y, B' (χ a) y = B a (φ' y) := fun a y => by rw [h'.skew, ← hχ0, ← h.skew]
  have hφχ : ∀ a, φa (χ a) = σ s • a := fun a => h.ext fun b => by
    rw [← hφa, ← hχ0, hφ, h.adj]
  have hχφ : ∀ y, χ (φa y) = σ s • y := fun y => h'.ext fun b => by
    rw [← hχ0, ← hφa, hφ', h'.adj]
  have hσ3 : ∀ n, σ (1 - e n - σ (e n)) = 1 - e n - σ (e n) := fun n => by
    rw [map_sub, map_sub, map_one, hσ]; ring
  have hρp : ∀ n y, (p : R) • ρ n y = (1 - e n - σ (e n)) • i y := fun n y => h.ext fun a => by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hp0)
    have h1 := hB (π n a) y
    rw [hπ, hρ, h.adj, map_mul, map_natCast, hσ3, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul,
      map_nsmul, nsmul_eq_mul] at h1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, h1]
    ring
  have hρπ : ∀ n a, ρ n (π n a) = ((1 - e n - σ (e n)) ^ 2) • a := fun n a =>
    h.smul_cancel hp0 (by rw [hρp, hπ]; module)
  have hπρ : ∀ n y, π n (ρ n y) = ((1 - e n - σ (e n)) ^ 2) • y := fun n y =>
    hi (by rw [hπ, mul_smul, hρp, map_smul]; module)
  have hσdvd : ∀ (n : ℕ) (x : R), (n : R) * p ^ 2 ∣ x → (n : R) * p ^ 2 ∣ σ x := fun n x hx => by
    simpa using map_dvd σ hx

  let G : ℕ → M →ₗ[R] M' := fun n =>
    e n • φ + (σ (e n) * σ (w n)) • χ + (1 - e n - σ (e n)) • π n
  let H : ℕ → M' →ₗ[R] M := fun n =>
    σ (e n) • φa + (e n * w n) • φ' + (1 - e n - σ (e n)) • ρ n
  have hGH : ∀ n a y, B' (G n a) y = B a (H n y) := fun n a y => by
    simp only [G, H, LinearMap.add_apply, LinearMap.smul_apply, map_add, AddMonoidHom.add_apply,
      h'.adj, hφa, hχ, hρ, map_smul, map_mul, hσ, hσ3]
  have hcong : ∀ n : ℕ, 0 < n → ∃ c₁ c₂ c₃ c₄ c₅ : R,
      e n * (1 - e n) = n * c₁ ∧ σ (e n) * (1 - σ (e n)) = n * c₂ ∧ e n * σ (e n) = n * c₃ ∧
      w n * s * e n - e n = n * c₄ ∧ σ (w n) * σ s * σ (e n) - σ (e n) = n * c₅ := fun n hn => by
    have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have d2 := hσdvd n _ (he n hn).1
    rw [map_mul, map_sub, map_one] at d2
    have d5 := hσdvd n _ (hw n hn)
    rw [map_sub, map_mul, map_mul] at d5
    have d3 := dvd_mul_of_idem (he n hn).1 d2 fun q hq hN => by
      by_cases hqP : q = P
      · exact Or.inr (hqP ▸ heσ n)
      · exact Or.inl ((he n hn).2.2 q hq hN hqP)
    obtain ⟨c₁, h₁⟩ := d.trans (he n hn).1
    obtain ⟨c₂, h₂⟩ := d.trans d2
    obtain ⟨c₃, h₃⟩ := d.trans d3
    obtain ⟨c₄, h₄⟩ := d.trans (hw n hn)
    obtain ⟨c₅, h₅⟩ := d.trans d5
    exact ⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩
  have hdv : ∀ n : ℕ, 0 < n → ∀ x : R,
      Ideal.Quotient.mk (Ideal.span {(n : R)}) x = 0 → (n : R) ∣ x := fun n _ x hx =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have hinv : ∀ n : ℕ, 0 < n → (∀ a, H n (G n a) - a ∈ mults M (n : R)) ∧
      ∀ y, G n (H n y) - y ∈ mults M' (n : R) := fun n hn => by
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩ := hcong n hn
    have k13 : (n : R) ∣ e n * (1 - e n - σ (e n)) := ⟨c₁ - c₃, by linear_combination h₁ - h₃⟩
    have k23 : (n : R) ∣ σ (e n) * (1 - e n - σ (e n)) := ⟨c₂ - c₃, by linear_combination h₂ - h₃⟩
    have k12 : (n : R) ∣ e n * σ (e n) := ⟨c₃, h₃⟩
    have k : (n : R) ∣ e n * (e n * w n) * s + σ (e n) * σ (w n) * σ (e n) * σ s +
        (1 - e n - σ (e n)) * (1 - e n - σ (e n)) * (1 - e n - σ (e n)) ^ 2 - 1 := by
      have := ((((k13.add k23).mul_left
        (1 + (1 - e n - σ (e n)) + (1 - e n - σ (e n)) ^ 2)).neg_right.sub ⟨c₁, h₁⟩).sub ⟨c₂, h₂⟩).add
        ((Dvd.dvd.mul_left ⟨c₄, h₄⟩ (e n)).add (Dvd.dvd.mul_left ⟨c₅, h₅⟩ (σ (e n))))
      convert this using 1
      ring
    have hH : H n = (e n * w n) • φ' + σ (e n) • φa + (1 - e n - σ (e n)) • ρ n := by
      simp only [H]; abel
    refine ⟨fun a => ?_, fun y => ?_⟩
    · rw [hH]
      refine comp_sub_mem φ χ (π n) φ' φa (ρ n) hφ hφχ (hρπ n) k12 k13 ?_ ?_ ?_ ?_ k a
      · convert k12.mul_left (σ (w n) * w n) using 1; ring
      · convert k23.mul_left (σ (w n)) using 1; ring
      · convert k13.mul_left (w n) using 1; ring
      · rwa [mul_comm]
    · rw [hH]
      refine comp_sub_mem φ' φa (ρ n) φ χ (π n) hφ' hχφ (hπρ n) ?_ ?_ ?_ k23 ?_ ?_ ?_ y
      · convert k12.mul_left (σ (w n) * w n) using 1; ring
      · convert k13.mul_left (w n) using 1; ring
      · rwa [mul_comm]
      · rwa [mul_comm]
      · convert k23.mul_left (σ (w n)) using 1; ring
      · convert k using 1; ring
  refine ⟨G, fun n hn a ha => ?_, fun n hn y => ⟨H n y, (hinv n hn).2 y⟩, fun n m hn hm a => ?_,
    fun n hn a b => ?_, fun n hn hnp a => ?_⟩
  · simpa using (mults M (n : R)).sub_mem (map_mem_mults (H n) ha) ((hinv n hn).1 a)
  · have hnm : 0 < n * m := Nat.mul_pos hn hm
    have d0 : (n : R) * p ^ 2 ∣ ((n * m : ℕ) : R) * p ^ 2 := ⟨m, by push_cast; ring⟩
    have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have u1 := ((he _ hnm).of_dvd d0).unique (he n hn)
    have u2 := hσdvd n _ u1
    rw [map_sub] at u2
    have u3 : (n : R) * p ^ 2 ∣ e (n * m) * w (n * m) - e n * w n := by
      have := ((u1.mul_left (w (n * m) - w (n * m) * s * w n)).add
        ((d0.trans (hw _ hnm)).mul_left (w n))).sub ((hw n hn).mul_left (w (n * m)))
      have := this.add (u1.mul_left (w n))
      convert this using 1
      ring
    have u4 := hσdvd n _ u3
    rw [map_sub, map_mul, map_mul] at u4
    obtain ⟨c, hc⟩ := (u1.add u2).mul_left
      (-((1 - e (n * m) - σ (e (n * m))) + (1 - e n - σ (e n))))
    obtain ⟨y, hy⟩ := hsq ((c * p) • a)
    have u5 : (1 - e (n * m) - σ (e (n * m))) • π (n * m) a - (1 - e n - σ (e n)) • π n a =
        (n : R) • y := by
      apply hi
      rw [map_sub, map_smul, map_smul, map_smul, hπ, hπ, hy, smul_smul, smul_smul, smul_smul, smul_smul,
        ← sub_smul]
      congr 1
      linear_combination (p : R) * hc
    have : G (n * m) a - G n a = (e (n * m) - e n) • φ a +
        (σ (e (n * m)) * σ (w (n * m)) - σ (e n) * σ (w n)) • χ a + (n : R) • y := by
      rw [← u5]
      simp only [G, LinearMap.add_apply, LinearMap.smul_apply]
      module
    rw [this]
    exact add_mem (add_mem (smul_mem_mults (d.trans u1) _) (smul_mem_mults (d.trans u4) _))
      (smul_mem_mults dvd_rfl _)
  · obtain ⟨y, hy⟩ := mem_mults.1 ((hinv n hn).1 b)
    rw [hGH, ← map_sub, hy, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have hen : (n : R) ∣ e n := by
      have he' := (he n hn).of_dvd d
      refine dvd_of_idem he'.1 fun q hq hN => he'.2.2 q hq hN fun hqP => hP.ne_top ?_
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hnp).map (Int.castRingHom R)
      rw [Ideal.eq_top_iff_one, ← huv]
      exact P.add_mem (P.mul_mem_left _ (by simpa [hqP] using hN)) (P.mul_mem_left _ (by simpa using hpP))
    have hen' : (n : R) ∣ σ (e n) := by simpa using map_dvd σ hen
    have : i (G n a) - (p : R) • a = e n • i (φ a) + (σ (e n) * σ (w n)) • i (χ a) +
        ((e n + σ (e n)) * ((e n + σ (e n) - 2) * p)) • a := by
      simp only [G, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hπ]
      module
    rw [this]
    exact add_mem (add_mem (smul_mem_mults hen _) (smul_mem_mults (hen'.mul_right _) _))
      (smul_mem_mults ((hen.add hen').mul_right _) _)

end Module

end GlobalTheory.HeckeTate
