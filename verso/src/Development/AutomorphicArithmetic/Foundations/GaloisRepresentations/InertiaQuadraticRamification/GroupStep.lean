import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Set `f : H →* ℂˣ` to `s.comp H.subtype`. Establish `hker : f.ker = H'.subgroupOf H`. Use extensionality with `g`. Rewrite using `[MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hH']`.

Simplify using `[f]`. Establish `hidx : H'.relIndex H = Nat.card f.range`. Rewrite using `[Subgroup.relIndex, ← hker, Subgroup.index_ker]`. Establish `hle : f.range ≤ rootsOfUnity p ℂ`. Introduce and unpack `_ ⟨g, rfl⟩`.

Rewrite using `[mem_rootsOfUnity]`. Conclude with `hs g g.2`. Establish `hcard : Nat.card (rootsOfUnity p ℂ) = p`. Conclude with `Complex.card_rootsOfUnity p`. Establish `hdvd : Nat.card f.range ∣ p`.

Use `Subgroup.card_dvd_of_le hle` as an intermediate fact. Rewrite `this` using `[hcard]`. Then use the resulting hypothesis. Establish `hne : Nat.card f.range ≠ 1`. Introduce `h1`. Establish `hbot : f.range = ⊥` using `by haveI : Finite (rootsOfUnity p ℂ) := inferInstance`.

Conclude with `(Subgroup.eq_bot_iff_card _).2 h1`. Establish `: f ⟨τ, hτ⟩ ∈ f.range` using `⟨_, rfl⟩`. Rewrite `this` using `[hbot, Subgroup.mem_bot]`. Conclude with `hτs this`. Rewrite using `[hidx]`.

Break down `(Nat.dvd_prime hp).1 hdvd with h | h` into its components or cases. Conclude with `absurd h hne`. Rewrite using `[h]` and apply the resulting hypothesis.
-/
private theorem relIndex_ker_prime {Γ : Type} [Group Γ] (H H' : Subgroup Γ) (s : Γ →* ℂˣ) (p : ℕ) (hp : p.Prime)
    (hH' : ∀ g, g ∈ H' ↔ g ∈ H ∧ s g = 1) (hs : ∀ g ∈ H, s g ^ p = 1) (τ : Γ) (hτ : τ ∈ H) (hτs : s τ ≠ 1) :
    (H'.relIndex H).Prime := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : H →* ℂˣ := s.comp H.subtype
  have hker : f.ker = H'.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hH']
    simp [f]
  have hidx : H'.relIndex H = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hle : f.range ≤ rootsOfUnity p ℂ := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hs g g.2
  have hcard : Nat.card (rootsOfUnity p ℂ) = p := by
    exact Complex.card_rootsOfUnity p
  have hdvd : Nat.card f.range ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard] at this
  have hne : Nat.card f.range ≠ 1 := by
    intro h1
    have hbot : f.range = ⊥ := by
      haveI : Finite (rootsOfUnity p ℂ) := inferInstance
      exact (Subgroup.eq_bot_iff_card _).2 h1
    have : f ⟨τ, hτ⟩ ∈ f.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hτs this
  rw [hidx]
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact absurd h hne
  · rwa [h]

/- English proof (translation)
Introduce `Γ _ Gd P D Pl Dc I hI hinf hmono hpsi hstep H₀ r hH₀ hP hr n hn hrn`. Establish `hpowk : ∀ (s : Γ →* ℂˣ) (k : ℕ), Gd s.ker → Gd (s ^ k).ker`. Introduce `s k hs`. Use `hmono _ _ (fun g hg => ?_) hs` and prove the remaining obligations. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`.

Rewrite using `[MonoidHom.pow_apply, hg, one_pow]`. Establish `key : ∀ n : ℕ, 0 < n → ∀ r : Γ →* ℂˣ, Gd r.ker → P (H₀ ⊓ (r ^ n).ker) → ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker)`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `hn r hr hP`. Break down `Nat.lt_or_ge 1 n with h1 | h1` into its components or cases. Use `swap`. Establish `hn1 : n = 1` using `by omega`. Substitute `hn1` using the available equality.

Conclude with `⟨r, hr, fun _ _ => rfl, by simpa using hP⟩`. Take `⟨p, hp, n', rfl⟩` from `Nat.exists_prime_and_dvd (show n ≠ 1 by omega)`. Establish `hn' : 0 < n'` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hn)`. Establish `hlt : n' < p * n'`. Use `hp.two_le` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨ψ, hψk, hψn, hψD, u, hDc, τ, hτ, hτo⟩` from `hpsi (H₀ ⊓ r.ker) (hinf _ _ hH₀ hr) (p * n') hn`. Establish `hr1 : Gd (r * ψ).ker`. Use `hmono _ _ (fun g hg => ?_) (hinf _ _ hr hψk)` and prove the remaining obligations. Establish `h1 : r g = 1` using `hg.1`.

Establish `h2 : ψ g = 1` using `hg.2`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]`. Establish `hr1n : (r * ψ) ^ (p * n') = r ^ (p * n')`. Rewrite using `[mul_pow, hψn, mul_one]`. Establish `hτU : τ ∈ H₀ ⊓ r.ker` using `hDc (hI u hτ)`.

Establish `hτr : r τ = 1` using `hτU.2`. Establish `hGH : Gd (H₀ ⊓ (r ^ (p * n')).ker)` using `hinf _ _ hH₀ (hpowk _ _ hr)`. Establish `hGH' : Gd (H₀ ⊓ ((r * ψ) ^ n').ker)` using `hinf _ _ hH₀ (hpowk _ _ hr1)`. Establish `hval : ∀ g, ((r * ψ) ^ n') g ^ p = (r ^ (p * n')) g`. Introduce `g`.

Rewrite using `[← hr1n, MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, mul_comm n' p]`. Establish `hle : H₀ ⊓ ((r * ψ) ^ n').ker ≤ H₀ ⊓ (r ^ (p * n')).ker`. Introduce `g hg`. Use `⟨hg.1, ?_⟩` and prove the remaining obligations. Establish `h1 : ((r * ψ) ^ n') g = 1` using `hg.2`.

Use `show (r ^ (p * n')) g = 1`. Rewrite using `[← hval, h1, one_pow]`. Establish `hUH : H₀ ⊓ r.ker ≤ H₀ ⊓ (r ^ (p * n')).ker`. Introduce `g hg`. Use `⟨hg.1, ?_⟩` and prove the remaining obligations.

Establish `h1 : r g = 1` using `hg.2`. Use `show (r ^ (p * n')) g = 1`. Rewrite using `[MonoidHom.pow_apply, h1, one_pow]`. Establish `hτs : ((r * ψ) ^ n') τ ≠ 1`. Introduce `h`.

Rewrite `h` using `[MonoidHom.pow_apply, MonoidHom.mul_apply, hτr, one_mul]`. Use `Nat.le_of_dvd hn' (orderOf_dvd_of_pow_eq_one h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hprime : ((H₀ ⊓ ((r * ψ) ^ n').ker).relIndex (H₀ ⊓ (r ^ (p * n')).ker)).Prime`. Use `relIndex_ker_prime _ _ ((r * ψ) ^ n') p hp (fun g => ?_) (fun g hg => ?_) τ (hUH hτU) hτs` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Conclude with `⟨hle hg, hg.2⟩`. Introduce and unpack `⟨hg, hs⟩`. Conclude with `⟨hg.1, hs⟩`.

Establish `h1 : (r ^ (p * n')) g = 1` using `hg.2`. Rewrite using `[hval, h1]`. Establish `hP' : P (H₀ ⊓ ((r * ψ) ^ n').ker)` using `hstep _ _ u hGH hGH' hP hle hprime (fun x hx => hUH (hDc hx)) ⟨τ, hτ, fun h => hτs h.2⟩`. Take `⟨r', h1, h2, h3⟩` from `ih n' hlt hn' (r * ψ) hr1 hP'`. Use `⟨r', h1, fun g hg => ?_, h3⟩` and prove the remaining obligations.

Rewrite using `[h2 g hg, MonoidHom.mul_apply, hψD g hg, mul_one]`. Use `key n hn r hr ?_` and prove the remaining obligations. Rewrite using `[hrn, MonoidHom.ker_one, inf_top_eq]`. Conclude with `hP`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.groupStep :
    GroupStep := by
  intro Γ _ Gd P D Pl Dc I hI hinf hmono hpsi hstep H₀ r hH₀ hP hr n hn hrn
  have hpowk : ∀ (s : Γ →* ℂˣ) (k : ℕ), Gd s.ker → Gd (s ^ k).ker := by
    intro s k hs
    refine hmono _ _ (fun g hg => ?_) hs
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.pow_apply, hg, one_pow]
  have key : ∀ n : ℕ, 0 < n → ∀ r : Γ →* ℂˣ, Gd r.ker → P (H₀ ⊓ (r ^ n).ker) →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn r hr hP
      rcases Nat.lt_or_ge 1 n with h1 | h1
      swap
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨r, hr, fun _ _ => rfl, by simpa using hP⟩
      obtain ⟨p, hp, n', rfl⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hn' : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hlt : n' < p * n' := by
        have := hp.two_le
        nlinarith
      obtain ⟨ψ, hψk, hψn, hψD, u, hDc, τ, hτ, hτo⟩ := hpsi (H₀ ⊓ r.ker) (hinf _ _ hH₀ hr) (p * n') hn
      have hr1 : Gd (r * ψ).ker := by
        refine hmono _ _ (fun g hg => ?_) (hinf _ _ hr hψk)
        have h1 : r g = 1 := hg.1
        have h2 : ψ g = 1 := hg.2
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]
      have hr1n : (r * ψ) ^ (p * n') = r ^ (p * n') := by
        rw [mul_pow, hψn, mul_one]
      have hτU : τ ∈ H₀ ⊓ r.ker := hDc (hI u hτ)
      have hτr : r τ = 1 := hτU.2
      have hGH : Gd (H₀ ⊓ (r ^ (p * n')).ker) := hinf _ _ hH₀ (hpowk _ _ hr)
      have hGH' : Gd (H₀ ⊓ ((r * ψ) ^ n').ker) := hinf _ _ hH₀ (hpowk _ _ hr1)
      have hval : ∀ g, ((r * ψ) ^ n') g ^ p = (r ^ (p * n')) g := by
        intro g
        rw [← hr1n, MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, mul_comm n' p]
      have hle : H₀ ⊓ ((r * ψ) ^ n').ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : ((r * ψ) ^ n') g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [← hval, h1, one_pow]
      have hUH : H₀ ⊓ r.ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : r g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [MonoidHom.pow_apply, h1, one_pow]
      have hτs : ((r * ψ) ^ n') τ ≠ 1 := by
        intro h
        rw [MonoidHom.pow_apply, MonoidHom.mul_apply, hτr, one_mul] at h
        have := Nat.le_of_dvd hn' (orderOf_dvd_of_pow_eq_one h)
        omega
      have hprime : ((H₀ ⊓ ((r * ψ) ^ n').ker).relIndex (H₀ ⊓ (r ^ (p * n')).ker)).Prime := by
        refine relIndex_ker_prime _ _ ((r * ψ) ^ n') p hp (fun g => ?_) (fun g hg => ?_) τ (hUH hτU) hτs
        · constructor
          · intro hg
            exact ⟨hle hg, hg.2⟩
          · rintro ⟨hg, hs⟩
            exact ⟨hg.1, hs⟩
        · have h1 : (r ^ (p * n')) g = 1 := hg.2
          rw [hval, h1]
      have hP' : P (H₀ ⊓ ((r * ψ) ^ n').ker) :=
        hstep _ _ u hGH hGH' hP hle hprime (fun x hx => hUH (hDc hx))
          ⟨τ, hτ, fun h => hτs h.2⟩
      obtain ⟨r', h1, h2, h3⟩ := ih n' hlt hn' (r * ψ) hr1 hP'
      refine ⟨r', h1, fun g hg => ?_, h3⟩
      rw [h2 g hg, MonoidHom.mul_apply, hψD g hg, mul_one]
  refine key n hn r hr ?_
  rw [hrn, MonoidHom.ker_one, inf_top_eq]
  exact hP
