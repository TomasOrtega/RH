import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

def Dom (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) : Prop :=
  (∀ P ∈ S, localization₂ P.asIdeal M₂ ≤ localization₂ P.asIdeal M₁) ∧ ∀ Q, Q ∉ S → localization₂ Q.asIdeal M₁ ≤ localization₂ Q.asIdeal M₂

def Full (M : Submodule (𝓞 E) W) : Prop := ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • x ∈ M

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩`.
-/
theorem Dom.refl (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) : Dom S M M :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun P hP => (h'.1 P hP).trans (h.1 P hP), fun Q hQ => (h.2 Q hQ).trans (h'.2 Q hQ)⟩`.
-/
theorem Dom.trans {S : Finset (HeightOneSpectrum (𝓞 E))} {M₁ M₂ M₃ : Submodule (𝓞 E) W} (h : Dom S M₁ M₂) (h' : Dom S M₂ M₃) :
    Dom S M₁ M₃ :=
  ⟨fun P hP => (h'.1 P hP).trans (h.1 P hP), fun Q hQ => (h.2 Q hQ).trans (h'.2 Q hQ)⟩

/- English proof (translation)
Introduce `x`. Take `⟨n, hn, hx⟩` from `h x`. Take `⟨m, hm, hy⟩` from `h' x`. Use `⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`.

Conclude with `M.smul_mem _ hx`. Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `M'.smul_mem _ hy`.
-/
theorem Full.inf {M M' : Submodule (𝓞 E) W} (h : Full M) (h' : Full M') : Full (M ⊓ M') := by
  intro x
  obtain ⟨n, hn, hx⟩ := h x
  obtain ⟨m, hm, hy⟩ := h' x
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
  · rw [Nat.cast_mul, mul_smul]; exact M'.smul_mem _ hy

/- English proof (translation)
Introduce `_ ⟨s, hs, hx⟩` and use `⟨s, hs, h hx⟩`.
-/
theorem localization_mono (Q : HeightOneSpectrum (𝓞 E)) {M M' : Submodule (𝓞 E) W} (h : M ≤ M') :
    localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal M' := fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

/- English proof (translation)
Use `le_antisymm ?_ fun x hx => ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩` and prove the remaining obligations. Introduce and unpack `x ⟨s, hs, t, ht, hx⟩`. Conclude with `⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, by rwa [mul_smul]⟩`.
-/
theorem localization_localization₂ (Q : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (localization₂ Q.asIdeal M) = localization₂ Q.asIdeal M := by
  refine le_antisymm ?_ fun x hx => ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rintro x ⟨s, hs, t, ht, hx⟩
  exact ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, by rwa [mul_smul]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤` using `fun e => hx (by`. Establish `: (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)` using `e ▸ Submodule.mem_top`. Simplify using `using this)`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨s, hs, hsx⟩` from `h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩`. Conclude with `hs (hle (by simpa using hsx))`.
-/
theorem mem_of_locP {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

/- English proof (translation)
Establish `key : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J₁ J₂ : Ideal (𝓞 E), I = J₁ * J₂ ∧ (∀ P ∈ S, ¬ J₂ ≤ P.asIdeal) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ¬ J₁ ≤ Q.asIdeal`. Introduce `I`. Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro h`. Conclude with `absurd rfl h`.

Consider the case `h₂ u hu`. Introduce `_`. Rewrite `hu` using `[Ideal.isUnit_iff]`. Conclude with `⟨⊤, ⊤, by simp [hu], fun P _ h => P.isPrime.ne_top (top_le_iff.1 h), fun P _ h => P.isPrime.ne_top (top_le_iff.1 h)⟩`. Consider the case `h₃ I p hI hp ih`.

Introduce `_`. Take `⟨J₁, J₂, rfl, h1, h2⟩` from `ih hI`. Set `P₀ : HeightOneSpectrum (𝓞 E)` to `⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩`. Establish `hmax : ∀ Q : HeightOneSpectrum (𝓞 E), p ≤ Q.asIdeal → Q = P₀` using `fun Q h => HeightOneSpectrum.ext (P₀.isMaximal.eq_of_le Q.isPrime.ne_top h).symm`. Distinguish the cases in `hS : P₀ ∈ S`.

Use `⟨p * J₁, J₂, by ring, h1, fun Q hQ h => ?_⟩` and prove the remaining obligations. Break down `(Q.isPrime.mul_le).1 h with h | h` into its components or cases. Conclude with `hQ (hmax Q h ▸ hS)`. Conclude with `h2 Q hQ h`. Use `⟨J₁, p * J₂, by ring, fun Q hQ h => ?_, h2⟩` and prove the remaining obligations.

Break down `(Q.isPrime.mul_le).1 h with h | h` into its components or cases. Conclude with `hS (hmax Q h ▸ hQ)`. Conclude with `h1 Q hQ h`. Take `⟨J₁, J₂, hJ, h1, h2⟩` from `key (Ideal.span {a}) (by simpa using ha)`. Establish `hsup : J₁ ⊔ J₂ = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `Q : HeightOneSpectrum (𝓞 E)` to `⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩`. Distinguish the cases in `hQ : Q ∈ S`. Conclude with `h1 Q hQ (le_sup_right.trans hle)`.

Conclude with `h2 Q hQ (le_sup_left.trans hle)`. Take `⟨u, hu, r, hr, hur⟩` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ J₁ ⊔ J₂)`. Use `⟨r, fun P hP => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hs'⟩` from `SetLike.not_le_iff_exists.1 (h1 P hP)`. Use `⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩` and prove the remaining obligations.

Rewrite using `[hJ, show s * (r - 1) = (-u) * s by rw [← hur]; ring]`. Conclude with `Ideal.mul_mem_mul (J₁.neg_mem hu) hs`. Take `⟨s, hs, hs'⟩` from `SetLike.not_le_iff_exists.1 (h2 Q hQ)`. Use `⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩` and prove the remaining obligations. Rewrite using `[hJ]`.

Conclude with `Ideal.mul_mem_mul hs hr`.
-/
theorem exists_idem (S : Finset (HeightOneSpectrum (𝓞 E))) {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ r : 𝓞 E, (∀ P ∈ S, ∃ s, s ∉ P.asIdeal ∧ a ∣ s * (r - 1)) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ∃ s, s ∉ Q.asIdeal ∧ a ∣ s * r := by
  classical

  have key : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J₁ J₂ : Ideal (𝓞 E), I = J₁ * J₂ ∧ (∀ P ∈ S, ¬ J₂ ≤ P.asIdeal) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ¬ J₁ ≤ Q.asIdeal := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ u hu =>
      intro _
      rw [Ideal.isUnit_iff] at hu
      exact ⟨⊤, ⊤, by simp [hu], fun P _ h => P.isPrime.ne_top (top_le_iff.1 h), fun P _ h => P.isPrime.ne_top (top_le_iff.1 h)⟩
    | h₃ I p hI hp ih =>
      intro _
      obtain ⟨J₁, J₂, rfl, h1, h2⟩ := ih hI
      let P₀ : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
      have hmax : ∀ Q : HeightOneSpectrum (𝓞 E), p ≤ Q.asIdeal → Q = P₀ := fun Q h =>
        HeightOneSpectrum.ext (P₀.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
      by_cases hS : P₀ ∈ S
      · refine ⟨p * J₁, J₂, by ring, h1, fun Q hQ h => ?_⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hQ (hmax Q h ▸ hS)
        · exact h2 Q hQ h
      · refine ⟨J₁, p * J₂, by ring, fun Q hQ h => ?_, h2⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hS (hmax Q h ▸ hQ)
        · exact h1 Q hQ h
  obtain ⟨J₁, J₂, hJ, h1, h2⟩ := key (Ideal.span {a}) (by simpa using ha)
  have hsup : J₁ ⊔ J₂ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    by_cases hQ : Q ∈ S
    · exact h1 Q hQ (le_sup_right.trans hle)
    · exact h2 Q hQ (le_sup_left.trans hle)
  obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ J₁ ⊔ J₂)
  refine ⟨r, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h1 P hP)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ, show s * (r - 1) = (-u) * s by rw [← hur]; ring]
    exact Ideal.mul_mem_mul (J₁.neg_mem hu) hs
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h2 Q hQ)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ]
    exact Ideal.mul_mem_mul hs hr

/- English proof (translation)
Take `⟨n, hn, hx⟩` from `hM x`. Take `⟨r, h1, h2⟩` from `exists_idem S (a := (n : 𝓞 E)) (by exact_mod_cast hn.ne')`. Use `⟨r • x, fun P hP => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, k, hk⟩` from `h1 P hP`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[show s • (r • x - x) = (s * (r - 1)) • x by rw [mul_smul, sub_smul, one_smul], hk, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ hx`. Take `⟨s, hs, k, hk⟩` from `h2 Q hQ`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_smul, hk, mul_comm, mul_smul]`.

Conclude with `M.smul_mem _ hx`.
-/
theorem Full.approx {M : Submodule (𝓞 E) W} (hM : Full M) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : W) :
    ∃ t : W, (∀ P ∈ S, t - x ∈ localization₂ P.asIdeal M) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → t ∈ localization₂ Q.asIdeal M := by
  obtain ⟨n, hn, hx⟩ := hM x
  obtain ⟨r, h1, h2⟩ := exists_idem S (a := (n : 𝓞 E)) (by exact_mod_cast hn.ne')
  refine ⟨r • x, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, k, hk⟩ := h1 P hP
    refine ⟨s, hs, ?_⟩
    rw [show s • (r • x - x) = (s * (r - 1)) • x by rw [mul_smul, sub_smul, one_smul], hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx
  · obtain ⟨s, hs, k, hk⟩ := h2 Q hQ
    refine ⟨s, hs, ?_⟩
    rw [← mul_smul, hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩`.
-/
theorem mem_localization_of_mem (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

/- English proof (translation)
Use `le_antisymm (le_inf (localization_mono Q inf_le_left) (localization_mono Q inf_le_right)) ?_` and prove the remaining obligations. Introduce and unpack `x ⟨⟨s, hs, hx⟩, t, ht, hy⟩`. Conclude with `⟨s * t, Q.asIdeal.primeCompl.mul_mem hs ht, by rw [mul_comm, mul_smul]; exact M.smul_mem _ hx, by rw [mul_smul]; exact M'.smul_mem _ hy⟩`.
-/
theorem localization_inf (Q : HeightOneSpectrum (𝓞 E)) (M M' : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (M ⊓ M') = localization₂ Q.asIdeal M ⊓ localization₂ Q.asIdeal M' := by
  refine le_antisymm (le_inf (localization_mono Q inf_le_left) (localization_mono Q inf_le_right)) ?_
  rintro x ⟨⟨s, hs, hx⟩, t, ht, hy⟩
  exact ⟨s * t, Q.asIdeal.primeCompl.mul_mem hs ht, by rw [mul_comm, mul_smul]; exact M.smul_mem _ hx,
    by rw [mul_smul]; exact M'.smul_mem _ hy⟩

/- English proof (translation)
Establish `hmem : ∀ y : W, y ∈ twist₂ M c e ↔ ∀ Q' : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q')⁻¹ • y ∈ localization₂ Q'.asIdeal M` using `fun y => by`. Simplify using `[twist₂, Submodule.mem_iInf]`. Establish `hcE : (c : E) ≠ 0` using `by exact_mod_cast hc.ne'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`.

Rewrite using `[← localization_localization₂]`. Conclude with `⟨s, hs, by rw [smul_comm]; exact (hmem _).1 hx Q⟩`. Introduce and unpack `⟨s, hs, hx⟩`. Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot`. Take `⟨r, h1, h2⟩` from `exists_idem {Q} (a := (c : 𝓞 E) ^ 2 * p) (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hc.ne')) hp0)`.

Take `⟨t, ht, k, hk⟩` from `h1 Q (Finset.mem_singleton_self Q)`. Establish `hr : r ∉ Q.asIdeal` using `fun hr => by`. Establish `h3 : t * (r - 1) ∈ Q.asIdeal` using `hk ▸ Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_left _ hp)`. Establish `h4` using `(Q.isPrime.mem_or_mem h3).resolve_left ht`. Conclude with `Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Q.asIdeal.sub_mem hr h4))`.

Use `⟨r * s, Q.asIdeal.primeCompl.mul_mem hr hs, (hmem _).2 fun Q' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hQ : Q' = Q`. Substitute `hQ` using the available equality. Use `mem_localization_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[smul_comm, mul_smul]`.

Conclude with `M.smul_mem _ hx`. Take `⟨t', ht', k', hk'⟩` from `h2 Q' (by simpa using hQ)`. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ 2 - e Q' + e Q by have := he Q; have := he Q'; omega)`. Use `⟨t', ht', ?_⟩` and prove the remaining obligations. Establish `h5 : t' • ((c : E) ^ e Q')⁻¹ • (r * s) • x = ((c : 𝓞 E) ^ m * (p * k')) • s • ((c : E) ^ e Q)⁻¹ • x`.

Establish `h6` using `congrArg (algebraMap (𝓞 E) E) hk'`. Establish `h7 : (c : E) ^ m = (c : E) ^ 2 * ((c : E) ^ e Q')⁻¹ * (c : E) ^ e Q`. Rewrite using `[← zpow_natCast, ← hm, zpow_add₀ hcE, zpow_sub₀ hcE, div_eq_mul_inv, zpow_ofNat]`. Simplify using `only [map_mul, map_pow, map_natCast] at h6`. Simplify using `only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul, map_pow, map_natCast]`.

Use `congr 1`. Rewrite using `[h7]`. Use `zpow_ne_zero (e Q) hcE` as an intermediate fact. Use `zpow_ne_zero (e Q') hcE` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(algebraMap (𝓞 E) E s) * h6`. Rewrite using `[h5]`. Conclude with `M.smul_mem _ hx`.
-/
theorem mem_localization_twist [Module E W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (Q : HeightOneSpectrum (𝓞 E)) (x : W) :
    x ∈ localization₂ Q.asIdeal (twist₂ M c e) ↔ ((c : E) ^ e Q)⁻¹ • x ∈ localization₂ Q.asIdeal M := by
  have hmem : ∀ y : W, y ∈ twist₂ M c e ↔ ∀ Q' : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q')⁻¹ • y ∈ localization₂ Q'.asIdeal M := fun y => by
    simp [twist₂, Submodule.mem_iInf]
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  constructor
  · rintro ⟨s, hs, hx⟩
    rw [← localization_localization₂]
    exact ⟨s, hs, by rw [smul_comm]; exact (hmem _).1 hx Q⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    obtain ⟨r, h1, h2⟩ := exists_idem {Q} (a := (c : 𝓞 E) ^ 2 * p)
      (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hc.ne')) hp0)
    obtain ⟨t, ht, k, hk⟩ := h1 Q (Finset.mem_singleton_self Q)
    have hr : r ∉ Q.asIdeal := fun hr => by
      have h3 : t * (r - 1) ∈ Q.asIdeal := hk ▸ Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_left _ hp)
      have h4 := (Q.isPrime.mem_or_mem h3).resolve_left ht
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Q.asIdeal.sub_mem hr h4))
    refine ⟨r * s, Q.asIdeal.primeCompl.mul_mem hr hs, (hmem _).2 fun Q' => ?_⟩
    by_cases hQ : Q' = Q
    · subst hQ
      refine mem_localization_of_mem _ ?_
      rw [smul_comm, mul_smul]
      exact M.smul_mem _ hx
    · obtain ⟨t', ht', k', hk'⟩ := h2 Q' (by simpa using hQ)
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 2 - e Q' + e Q by have := he Q; have := he Q'; omega)
      refine ⟨t', ht', ?_⟩
      have h5 : t' • ((c : E) ^ e Q')⁻¹ • (r * s) • x = ((c : 𝓞 E) ^ m * (p * k')) • s • ((c : E) ^ e Q)⁻¹ • x := by
        have h6 := congrArg (algebraMap (𝓞 E) E) hk'
        have h7 : (c : E) ^ m = (c : E) ^ 2 * ((c : E) ^ e Q')⁻¹ * (c : E) ^ e Q := by
          rw [← zpow_natCast, ← hm, zpow_add₀ hcE, zpow_sub₀ hcE, div_eq_mul_inv, zpow_ofNat]
        simp only [map_mul, map_pow, map_natCast] at h6
        simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul, map_pow, map_natCast]
        congr 1
        rw [h7]
        have := zpow_ne_zero (e Q) hcE
        have := zpow_ne_zero (e Q') hcE
        field_simp
        linear_combination (algebraMap (𝓞 E) E s) * h6
      rw [h5]
      exact M.smul_mem _ hx

/- English proof (translation)
Unfold `expS`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem expS_bound [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    -1 ≤ expS S Q ∧ expS S Q ≤ 1 := by
  unfold expS
  split_ifs <;> omega

def cosSum {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L : Submodule (𝓞 E) W)
    (θ : V → ℂ) (Ξ : W → ℂ) (z : V) : ℂ :=
  latSum As L fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)

def volExp {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : ℤ :=
  (b : ℤ) * ordDet P N - (a : ℤ) * ordDet P N'

end Loc

section Ambient

variable {X : Fields} (A : Amb X) {a b : ℕ}

abbrev lam (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : AddSubgroup (VCx X.Tau a b) :=
  LamC (X.embC A.σ₀) A.δ A.AA N N'

def vac (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : VCx X.Tau a b → ℂ :=
  fun z => (A.chiF a b N N')⁻¹ * A.e a b N N' z

variable (a b) in

def Moves : Prop :=
  A.δ ≠ 0 ∧ Nonempty X.Tau ∧ A.AA.FG ∧ A.AA ≠ ⊥ ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.chiF a b N N' ≠ 0 ∧ vac A N N' ∈ Th (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') ∧
      LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' N'' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → IsSdLat N'' →
    vac A N N'' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N N'') (vac A N N')) ∧
  ∀ (N N₁ : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N₁ → IsSdLat N' →
    vac A N₁ N' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N₁ N') (vac A N N')

end Ambient

/- English proof (translation)
Introduce `x y`. Simplify using `[Formalism.L2.Ker.HV, map_sum, mul_comm]`.
-/
theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (Formalism.L2.Ker.HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

/- English proof (translation)
Introduce `x y h`. Take `⟨τ⟩` from `‹Nonempty ι›`. Use `LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)` and prove the remaining obligations. Use `congrFun (congrFun (congrFun h τ) i) j` as an intermediate fact. Conclude with `(emb τ).injective (by simpa [embH, hδ] using this)`.
-/
theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  exact (emb τ).injective (by simpa [embH, hδ] using this)

end GlobalTheory.ThetaMove
