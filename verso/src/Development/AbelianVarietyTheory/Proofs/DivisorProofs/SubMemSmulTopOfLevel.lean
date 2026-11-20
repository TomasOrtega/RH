import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimes
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

noncomputable section
namespace GlobalTheory.NeatOne

/- English proof (translation)
Take `⟨F, hF⟩` from `exists_add_pow_prime_eq hg (Polynomial.X : Polynomial ℤ) 1`. Establish `h1` using `congrArg (fun q : Polynomial ℤ => q.coeff 1) hF`. Establish `hg1 : (1 : ℕ) ≠ g` using `hg.one_lt.ne`. Establish `e : ((g : Polynomial ℤ) * Polynomial.X * 1 * F) = Polynomial.C (g : ℤ) * (Polynomial.X * F)`. Simplify using `[mul_assoc]`.

Simplify using `only [Polynomial.coeff_X_add_one_pow, one_pow, Polynomial.coeff_add, Polynomial.coeff_X_pow, e, Polynomial.coeff_C_mul, Nat.choose_one_right, if_neg hg1] at h1`. Establish `h2 : (Polynomial.X * F).coeff 1 = F.coeff 0` using `Polynomial.coeff_X_mul F 0`. Rewrite `h1` using `[h2, Polynomial.coeff_one]`. Establish `h3 : F.coeff 0 = 1`. Establish `hg0 : (g : ℤ) ≠ 0` using `by exact_mod_cast hg.ne_zero`.

Simplify using `only [one_ne_zero, if_false, add_zero, zero_add] at h1`. Conclude with `(mul_eq_left₀ hg0).1 h1.symm`. Use `⟨F.divX, ?_⟩` and prove the remaining obligations. Establish `h4 : F = 1 + Polynomial.X * F.divX` using `by conv_lhs => rw [← Polynomial.X_mul_divX_add F, h3]`. Simplify using `[add_comm]`.

Rewrite using `[hF, ← h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_poly {g : ℕ} (hg : g.Prime) : ∃ Q : Polynomial ℤ,
    (Polynomial.X + 1 : Polynomial ℤ) ^ g = Polynomial.X ^ g + 1 + (g : Polynomial ℤ) * (Polynomial.X * (1 + Polynomial.X * Q)) := by
  obtain ⟨F, hF⟩ := exists_add_pow_prime_eq hg (Polynomial.X : Polynomial ℤ) 1
  have h1 := congrArg (fun q : Polynomial ℤ => q.coeff 1) hF
  have hg1 : (1 : ℕ) ≠ g := hg.one_lt.ne
  have e : ((g : Polynomial ℤ) * Polynomial.X * 1 * F) = Polynomial.C (g : ℤ) * (Polynomial.X * F) := by
    simp [mul_assoc]
  simp only [Polynomial.coeff_X_add_one_pow, one_pow, Polynomial.coeff_add, Polynomial.coeff_X_pow, e, Polynomial.coeff_C_mul,
    Nat.choose_one_right, if_neg hg1] at h1
  have h2 : (Polynomial.X * F).coeff 1 = F.coeff 0 := Polynomial.coeff_X_mul F 0
  rw [h2, Polynomial.coeff_one] at h1
  have h3 : F.coeff 0 = 1 := by
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne_zero
    simp only [one_ne_zero, if_false, add_zero, zero_add] at h1
    exact (mul_eq_left₀ hg0).1 h1.symm
  refine ⟨F.divX, ?_⟩
  have h4 : F = 1 + Polynomial.X * F.divX := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add F, h3]
    simp [add_comm]
  rw [hF, ← h4]; ring

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/- English proof (translation)
Take `⟨Q, hQ⟩` from `exists_poly hg`. Use `set N : Module.End R M := β - 1 with hN`. Establish `hQ'` using `congrArg (Polynomial.aeval N) hQ`. Simplify using `only [map_pow, map_add, map_mul, Polynomial.aeval_X, map_one, map_natCast] at hQ'`. Use `set q : Module.End R M := Polynomial.aeval N Q with hq`.

Establish `hcomm : N * q = q * N`. Use `congrArg (Polynomial.aeval N) (mul_comm Polynomial.X Q)` as an intermediate fact. Simplify `this` using `only [map_mul, Polynomial.aeval_X]`. Rewrite `hQ'` using `[hN, sub_add_cancel, hβ, ← hN]`. Establish `hrel : ∀ z, (g : R) • (N z + N (N (q z))) = - (N ^ g) z`.

Introduce `z`. Use `congrArg (fun T : Module.End R M => T z) hQ'` as an intermediate fact. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, Module.End.natCast_apply, map_add] at this`. Rewrite using `[Nat.cast_smul_eq_nsmul, eq_neg_iff_add_eq_zero]`. Establish `e : z + ((g • (N z + N (N (q z)))) + (N ^ g) z) = z + 0`.

Rewrite using `[add_zero, smul_add]`. Use `conv_rhs => rw [this]`. Normalize the expressions using the abelian group laws. Conclude with `add_left_cancel e`. Establish `hdiv : ∀ y ∈ I • (⊤ : Submodule R M), ∃ w, s • y = (g : R) • w`.

Introduce `y hy`. Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha m _`. Take `⟨c, hc⟩` from `hs a ha`. Conclude with `⟨c • m, by rw [smul_smul, smul_smul, hc]⟩`.

Introduce and unpack `x y ⟨w, hw⟩ ⟨w', hw'⟩`. Conclude with `⟨w + w', by rw [smul_add, smul_add, hw, hw']⟩`. Establish `hstep : ∀ z, ∃ z', s • N z = N (N z')`. Introduce `z`. Take `⟨w, hw⟩` from `hdiv _ (h z)`.

Take `⟨d, hd⟩ : ∃ d, g = 2 + d + r` from `⟨g - r - 2, by omega⟩`. Establish `e1 : (N ^ g) z = N (N ((N ^ d) ((N ^ r) z)))` using `by conv_lhs => rw [hd]`. Rewrite using `[pow_add, pow_add, pow_two]`. Both sides reduce to the same expression. Establish `e2 : (g : R) • (s • (N z + N (N (q z)))) = (g : R) • (- N (N ((N ^ d) w)))`.

Rewrite using `[smul_comm, hrel, e1, smul_neg, smul_neg, ← map_smul, ← map_smul, ← map_smul, hw, map_smul, map_smul, map_smul]`. Establish `e3` using `smul_right_injective M hg0 e2`. Use `⟨- (N ^ d) w - s • q z, ?_⟩` and prove the remaining obligations. Rewrite `e3` using `[smul_add]`. Rewrite using `[map_sub, map_sub, map_neg, map_neg, ← e3, map_smul, map_smul]`.

Normalize the expressions using the abelian group laws. Establish `hpow : ∀ k : ℕ, ∀ z, ∃ z', s ^ k • N z = N ((N ^ k) z')`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z; exact ⟨z, by simp⟩`.

Consider the case `succ k ih`. Introduce `z`. Take `⟨z₁, h₁⟩` from `ih z`. Take `⟨z₂, h₂⟩` from `hstep z₁`. Use `⟨z₂, ?_⟩` and prove the remaining obligations.

Establish `c : ∀ y, N ((N ^ k) y) = (N ^ k) (N y)` using `fun y => by`. Rewrite using `[← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]`. Rewrite using `[pow_succ', mul_smul, h₁, c, ← map_smul, h₂, pow_succ, Module.End.mul_apply, c]`. Use `set P : Submodule R M := LinearMap.range N with hP`. Establish `hPI : P ≤ I • P`.

Introduce and unpack `y ⟨z, rfl⟩`. Take `⟨z', hz'⟩` from `hpow r z`. Establish `h1 : N ((N ^ r) z') ∈ I • P`. Establish `: (I • (⊤ : Submodule R M)).map N ≤ I • P`. Rewrite using `[Submodule.map_smul'', Submodule.map_top]`.

Conclude with `this ⟨_, h z', rfl⟩`. Establish `h2 : 1 - s ^ r ∈ I`. Take `⟨c, hc⟩` from `one_sub_dvd_one_sub_pow s r`. Rewrite using `[hc]`. Conclude with `I.mul_mem_right c hs1`.

Establish `hsplit : N z = (1 - s ^ r) • N z + s ^ r • N z`. Rewrite using `[← add_smul, sub_add_cancel, one_smul]`. Rewrite using `[hsplit, hz']`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem_smul h2 ⟨z, rfl⟩) h1`. Take `⟨t, ht1, ht0⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I P (IsNoetherian.noetherian P) hPI`.

Establish `htne : t ≠ 0`. Introduce and unpack `rfl`. Apply `hI` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using I.neg_mem ht1`.

Use extensionality with `x`. Establish `hx` using `ht0 _ (LinearMap.mem_range_self N x)`. Rewrite `hx` using `[smul_eq_zero_iff_right htne, hN, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using hx`.
-/
theorem eq_one_of_prime_order [IsDomain R] [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (I : Ideal R) (hI : I ≠ ⊤) {g r : ℕ} (hg : g.Prime) (hg0 : (g : R) ≠ 0) (hr : r + 1 < g)
    (s : R) (hs1 : 1 - s ∈ I) (hs : ∀ a ∈ I, (g : R) ∣ s * a) (β : Module.End R M) (hβ : β ^ g = 1)
    (h : ∀ x, ((β - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) : β = 1 := by
  obtain ⟨Q, hQ⟩ := exists_poly hg
  set N : Module.End R M := β - 1 with hN
  have hQ' := congrArg (Polynomial.aeval N) hQ
  simp only [map_pow, map_add, map_mul, Polynomial.aeval_X, map_one, map_natCast] at hQ'
  set q : Module.End R M := Polynomial.aeval N Q with hq
  have hcomm : N * q = q * N := by
    have := congrArg (Polynomial.aeval N) (mul_comm Polynomial.X Q)
    simpa only [map_mul, Polynomial.aeval_X] using this
  rw [hN, sub_add_cancel, hβ, ← hN] at hQ'
  have hrel : ∀ z, (g : R) • (N z + N (N (q z))) = - (N ^ g) z := by
    intro z
    have := congrArg (fun T : Module.End R M => T z) hQ'
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, Module.End.natCast_apply, map_add] at this
    rw [Nat.cast_smul_eq_nsmul, eq_neg_iff_add_eq_zero]
    have e : z + ((g • (N z + N (N (q z)))) + (N ^ g) z) = z + 0 := by
      rw [add_zero, smul_add]; conv_rhs => rw [this]
      abel
    exact add_left_cancel e
  have hdiv : ∀ y ∈ I • (⊤ : Submodule R M), ∃ w, s • y = (g : R) • w := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha m _
      obtain ⟨c, hc⟩ := hs a ha
      exact ⟨c • m, by rw [smul_smul, smul_smul, hc]⟩
    · rintro x y ⟨w, hw⟩ ⟨w', hw'⟩
      exact ⟨w + w', by rw [smul_add, smul_add, hw, hw']⟩
  have hstep : ∀ z, ∃ z', s • N z = N (N z') := by
    intro z
    obtain ⟨w, hw⟩ := hdiv _ (h z)
    obtain ⟨d, hd⟩ : ∃ d, g = 2 + d + r := ⟨g - r - 2, by omega⟩
    have e1 : (N ^ g) z = N (N ((N ^ d) ((N ^ r) z))) := by
      conv_lhs => rw [hd]
      rw [pow_add, pow_add, pow_two]; rfl
    have e2 : (g : R) • (s • (N z + N (N (q z)))) = (g : R) • (- N (N ((N ^ d) w))) := by
      rw [smul_comm, hrel, e1, smul_neg, smul_neg, ← map_smul, ← map_smul, ← map_smul, hw, map_smul, map_smul, map_smul]
    have e3 := smul_right_injective M hg0 e2
    refine ⟨- (N ^ d) w - s • q z, ?_⟩
    rw [smul_add] at e3
    rw [map_sub, map_sub, map_neg, map_neg, ← e3, map_smul, map_smul]; abel
  have hpow : ∀ k : ℕ, ∀ z, ∃ z', s ^ k • N z = N ((N ^ k) z') := by
    intro k
    induction k with
    | zero => intro z; exact ⟨z, by simp⟩
    | succ k ih =>
      intro z
      obtain ⟨z₁, h₁⟩ := ih z
      obtain ⟨z₂, h₂⟩ := hstep z₁
      refine ⟨z₂, ?_⟩
      have c : ∀ y, N ((N ^ k) y) = (N ^ k) (N y) := fun y => by
        rw [← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]
      rw [pow_succ', mul_smul, h₁, c, ← map_smul, h₂, pow_succ, Module.End.mul_apply, c]
  set P : Submodule R M := LinearMap.range N with hP
  have hPI : P ≤ I • P := by
    rintro y ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ := hpow r z
    have h1 : N ((N ^ r) z') ∈ I • P := by
      have : (I • (⊤ : Submodule R M)).map N ≤ I • P := by
        rw [Submodule.map_smul'', Submodule.map_top]
      exact this ⟨_, h z', rfl⟩
    have h2 : 1 - s ^ r ∈ I := by
      obtain ⟨c, hc⟩ := one_sub_dvd_one_sub_pow s r
      rw [hc]; exact I.mul_mem_right c hs1
    have hsplit : N z = (1 - s ^ r) • N z + s ^ r • N z := by
      rw [← add_smul, sub_add_cancel, one_smul]
    rw [hsplit, hz']
    exact Submodule.add_mem _ (Submodule.smul_mem_smul h2 ⟨z, rfl⟩) h1
  obtain ⟨t, ht1, ht0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I P
    (IsNoetherian.noetherian P) hPI
  have htne : t ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem ht1
  ext x
  have hx := ht0 _ (LinearMap.mem_range_self N x)
  rw [smul_eq_zero_iff_right htne, hN, LinearMap.sub_apply, sub_eq_zero] at hx
  simpa using hx

/- English proof (translation)
Establish `key : ∃ a : ℕ, α ^ g ^ a = 1`. Take `⟨a, b, hpb, hmab⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm.ne' g hg.one_lt.ne'`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hcop : Nat.Coprime g (b ^ (r + 1))` using `Nat.Coprime.pow_right _ ((hg.coprime_iff_not_dvd).2 hpb)`. Take `⟨u, v, huv⟩` from `Nat.Coprime.cast (R := R) hcop`.

Use `GlobalTheory.Neat.eq_one_of_unipotent_mod_of_unit I hI (α ^ g ^ a) b r ?_ v ?_ (GlobalTheory.Neat.pow_prime_pow_unipotent I α hg hgI a r h)` and prove the remaining obligations. Rewrite using `[← pow_mul, ← hmab, hα]`. Establish `: 1 - v * (b : R) ^ (r + 1) = u * g`. Rewrite using `[← huv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `I.mul_mem_left u hgI`. Take `⟨a, ha⟩` from `key`. Proceed by induction on `a with`.

Consider the case `zero => simpa using ha`. Consider the case `succ a ih`. Apply `ih` to reduce the goal to its premises. Conclude with `eq_one_of_prime_order I hI hg hg0 hr s hs1 hs _ (by rw [← pow_mul, ← pow_succ, ha]) (GlobalTheory.Neat.pow_prime_pow_unipotent I α hg hgI a r h)`.
-/
theorem eq_one_of_finite_order [IsDomain R] [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (I : Ideal R) (hI : I ≠ ⊤) {g r : ℕ} (hg : g.Prime) (hg0 : (g : R) ≠ 0) (hgI : (g : R) ∈ I)
    (hr : r + 1 < g) (s : R) (hs1 : 1 - s ∈ I) (hs : ∀ a ∈ I, (g : R) ∣ s * a) (α : Module.End R M) {m : ℕ} (hm : 0 < m)
    (hα : α ^ m = 1) (h : ∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) : α = 1 := by
  have key : ∃ a : ℕ, α ^ g ^ a = 1 := by
    obtain ⟨a, b, hpb, hmab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' g hg.one_lt.ne'
    refine ⟨a, ?_⟩
    have hcop : Nat.Coprime g (b ^ (r + 1)) :=
      Nat.Coprime.pow_right _ ((hg.coprime_iff_not_dvd).2 hpb)
    obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := R) hcop
    refine GlobalTheory.Neat.eq_one_of_unipotent_mod_of_unit I hI (α ^ g ^ a) b r ?_ v ?_
      (GlobalTheory.Neat.pow_prime_pow_unipotent I α hg hgI a r h)
    · rw [← pow_mul, ← hmab, hα]
    · have : 1 - v * (b : R) ^ (r + 1) = u * g := by
        rw [← huv]; push_cast; ring
      rw [this]; exact I.mul_mem_left u hgI
  obtain ⟨a, ha⟩ := key
  induction a with
  | zero => simpa using ha
  | succ a ih =>
    apply ih
    exact eq_one_of_prime_order I hI hg hg0 hr s hs1 hs _ (by rw [← pow_mul, ← pow_succ, ha])
      (GlobalTheory.Neat.pow_prime_pow_unipotent I α hg hgI a r h)

/- English proof (translation)
Establish `hevJ : ∀ c : 𝓞 E, c ∈ J → ∀ a, c • ev a = 0`. Introduce `c hc a`. Rewrite using `[← map_smul, hev]`. Conclude with `Submodule.smul_mem_smul hc trivial`. Establish `hevψ : ∀ a, ∃ μ, ψ μ = ev a`.

Introduce `a`. Apply `hψs` to reduce the goal to its premises. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `hevJ _ hnJ a`. Use `set G := F ^ (N - 1) with hGdef`.

Establish `hGF : G * F = 1`. Rewrite using `[hGdef, ← pow_succ, Nat.sub_add_cancel hN, hFN]`. Establish `hFG : F * G = 1`. Rewrite using `[hGdef, ← pow_succ', Nat.sub_add_cancel hN, hFN]`. Establish `hFGl : ∀ l, F (G l) = l` using `fun l => by`.

Rewrite using `[← Module.End.mul_apply, hFG, Module.End.one_apply]`. Establish `hGFl : ∀ l, G (F l) = l` using `fun l => by`. Rewrite using `[← Module.End.mul_apply, hGF, Module.End.one_apply]`. Establish `hkey : ∀ (l : Λ) (a : La), ψ l = ev a → ψ (G l) = ev (gM a)`. Introduce `l a hla`.

Take `⟨μ, hμ⟩` from `hevψ (gM a)`. Establish `h1 : ψ (F (μ - G l)) = 0`. Rewrite using `[map_sub, map_sub, hFθ, hμ, hθ, hFGl, hla, sub_self]`. Take `⟨b', hb'⟩` from `(hψ _).1 h1`. Establish `h2 : μ - G l = n • G b'`.

Rewrite using `[← map_nsmul, ← hb', hGFl]`. Establish `h3 : ψ (μ - G l) = 0` using `(hψ _).2 ⟨G b', h2⟩`. Rewrite `h3` using `[map_sub, sub_eq_zero]`. Rewrite using `[← h3, hμ]`. Set `W : Submodule (𝓞 E) Λ` to `(LinearMap.range ev).comap ψ`.

Establish `hGW : ∀ l ∈ W, G l ∈ W`. Introduce and unpack `l ⟨a, ha⟩`. Conclude with `⟨gM a, (hkey l a ha.symm).symm⟩`. Take `⟨J', hJ'⟩ : J ∣ Ideal.span {(n : 𝓞 E)}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hnJ)`. Establish `hJ'W : ∀ c' : 𝓞 E, c' ∈ J' → ∀ l, c' • l ∈ W`.

Introduce `c' hc' l`. Take `⟨a, ha⟩` from `hevs (ψ (c' • l)) (by`. Introduce `c hc`. Establish `hcc : c * c' ∈ Ideal.span {(n : 𝓞 E)}` using `by rw [hJ']; exact Ideal.mul_mem_mul hc hc'`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hcc`.

Rewrite using `[← map_smul, smul_smul, ← hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `(hψ _).2 ⟨_, rfl⟩)`. Conclude with `⟨a, ha⟩`. Establish `hnW : ∀ I : Ideal (𝓞 E), J ≤ I → ∀ l : Λ, n • l ∈ I • W`. Introduce `I hJI l`.

Establish `h1 : (n : 𝓞 E) • l ∈ (J * J') • (⊤ : Submodule (𝓞 E) Λ)` using `Submodule.smul_mem_smul (by rw [← hJ']; exact Ideal.mem_span_singleton_self _) trivial`. Rewrite `h1` using `[Submodule.mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `Submodule.smul_mono hJI (Submodule.smul_le.2 fun c' hc' l _ => hJ'W c' hc' l) h1`. Establish `hpow : ∀ k (l : Λ) (a : La), ψ l = ev a → ψ (((G - 1 : Module.End (𝓞 E) Λ) ^ k) l) = ev (((gM - 1 : Module.End (𝓞 E) La) ^ k) a)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro l a h`. Simplify using `using h`. Consider the case `succ k ih`. Introduce `l a h`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]`. Apply `ih` to reduce the goal to its premises. Simplify using `[map_sub, hkey l a h, h]`. Establish `hunipW : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∀ l ∈ W, ((G - 1) ^ m) l ∈ I • W`. Introduce and unpack `I hJI hu l ⟨a, ha⟩`.

Establish `hx` using `hpow m l a ha.symm`. Establish `hmem : ev (((gM - 1) ^ m) a) ∈ (I • W).map ψ`. Establish `h1 : ev (((gM - 1) ^ m) a) ∈ (I • (⊤ : Submodule (𝓞 E) La)).map ev` using `⟨_, hu a, rfl⟩`. Rewrite `h1` using `[Submodule.map_smul'', Submodule.map_top]`. Rewrite using `[Submodule.map_smul'']`.

Use `Submodule.smul_mono le_rfl ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Take `⟨μ, hμ⟩` from `hevψ b`. Conclude with `⟨μ, ⟨b, hμ.symm⟩, hμ⟩`. Take `⟨z, hz, hzx⟩` from `hmem`.

Establish `hd : ψ (((G - 1) ^ m) l - z) = 0` using `by rw [map_sub, hzx, hx, sub_self]`. Take `⟨b', hb'⟩` from `(hψ _).1 hd`. Establish `: ((G - 1) ^ m) l = z + n • b'` using `by rw [← hb']; abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hz (hnW I hJI b')`.

Use `haveI := hfin`. Use `haveI := htf`. Set `Gr : Module.End (𝓞 E) W` to `G.restrict hGW`. Establish `hGr : ∀ y : W, ((Gr y : W) : Λ) = G y` using `fun y => rfl`. Establish `hGr1 : ∀ y : W, (((Gr - 1) y : W) : Λ) = (G - 1) y` using `fun y => rfl`.

Establish `hGN : G ^ N = 1`. Rewrite using `[hGdef, ← pow_mul, mul_comm, pow_mul, hFN, one_pow]`. Establish `hGrN : Gr ^ N = 1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.NeatLevel.val_pow_apply W Gr G hGr, hGN]`. Both sides reduce to the same expression. Establish `hsub : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∀ y : W, ((Gr - 1) ^ m) y ∈ I • (⊤ : Submodule (𝓞 E) W)`. Introduce `I hJI hu y`.

Establish `h1 : ((((Gr - 1) ^ m) y : W) : Λ) ∈ (I • (⊤ : Submodule (𝓞 E) W)).map W.subtype`. Rewrite using `[Submodule.map_smul'', Submodule.map_subtype_top, GlobalTheory.NeatLevel.val_pow_apply W (Gr - 1) (G - 1) hGr1]`. Conclude with `hunipW I hJI hu y y.2`. Take `⟨z, hz, hzy⟩` from `h1`. Establish `hzz : z = ((Gr - 1) ^ m) y` using `Subtype.ext hzy`.

Rewrite using `[← hzz]` and apply the resulting hypothesis. Establish `hGr1' : Gr = 1` using `eq_one_of_finite_order I hI hg (by exact_mod_cast hg.ne_zero) hgI hr s hs1 hs Gr hN hGrN (hsub I hJI hu)`. Introduce `a`. Take `⟨l, hl⟩` from `hevψ a`. Establish `hlW : l ∈ W` using `⟨a, hl.symm⟩`.

Establish `hGl : G l = l`. Use `congrArg (fun T : Module.End (𝓞 E) W => ((T ⟨l, hlW⟩ : W) : Λ)) hGr1'` as an intermediate fact. Conclude with `(hGr ⟨l, hlW⟩).symm.trans (by simpa using this)`. Establish `h` using `hkey l a hl`. Rewrite `h` using `[hGl, hl]`.

Rewrite using `[← hev, map_sub, ← h, sub_self]`.
-/
theorem sub_mem_smul_top_of_level (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La]
    [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g : ℕ) (I : Ideal (𝓞 E))
    (s : 𝓞 E) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La)
    (hfin : Module.Finite (𝓞 E) Λ) (htf : Module.IsTorsionFree (𝓞 E) Λ) (hnJ : (n : 𝓞 E) ∈ J)
    (hev : ∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) (hevs : ∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q)
    (hψ : ∀ b, ψ b = 0 ↔ ∃ b', b = n • b') (hψs : ∀ q : Q, n • q = 0 → ∃ b, ψ b = q) (hFθ : ∀ b, ψ (F b) = θ (ψ b))
    (hθ : ∀ a, θ (ev (gM a)) = ev a) (hN : 0 < N) (hFN : F ^ N = 1) (hg : g.Prime) (hI : I ≠ ⊤) (hgI : (g : 𝓞 E) ∈ I)
    (hr : m + 1 < g) (hs1 : 1 - s ∈ I) (hs : ∀ a ∈ I, (g : 𝓞 E) ∣ s * a) (hJI : J ≤ I)
    (hu : ∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) :
    ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by
  have hevJ : ∀ c : 𝓞 E, c ∈ J → ∀ a, c • ev a = 0 := by
    intro c hc a
    rw [← map_smul, hev]
    exact Submodule.smul_mem_smul hc trivial
  have hevψ : ∀ a, ∃ μ, ψ μ = ev a := by
    intro a; apply hψs
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact hevJ _ hnJ a
  set G := F ^ (N - 1) with hGdef
  have hGF : G * F = 1 := by
    rw [hGdef, ← pow_succ, Nat.sub_add_cancel hN, hFN]
  have hFG : F * G = 1 := by
    rw [hGdef, ← pow_succ', Nat.sub_add_cancel hN, hFN]
  have hFGl : ∀ l, F (G l) = l := fun l => by
    rw [← Module.End.mul_apply, hFG, Module.End.one_apply]
  have hGFl : ∀ l, G (F l) = l := fun l => by
    rw [← Module.End.mul_apply, hGF, Module.End.one_apply]
  have hkey : ∀ (l : Λ) (a : La), ψ l = ev a → ψ (G l) = ev (gM a) := by
    intro l a hla
    obtain ⟨μ, hμ⟩ := hevψ (gM a)
    have h1 : ψ (F (μ - G l)) = 0 := by
      rw [map_sub, map_sub, hFθ, hμ, hθ, hFGl, hla, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 h1
    have h2 : μ - G l = n • G b' := by
      rw [← map_nsmul, ← hb', hGFl]
    have h3 : ψ (μ - G l) = 0 := (hψ _).2 ⟨G b', h2⟩
    rw [map_sub, sub_eq_zero] at h3
    rw [← h3, hμ]
  let W : Submodule (𝓞 E) Λ := (LinearMap.range ev).comap ψ
  have hGW : ∀ l ∈ W, G l ∈ W := by
    rintro l ⟨a, ha⟩; exact ⟨gM a, (hkey l a ha.symm).symm⟩
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {(n : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hnJ)
  have hJ'W : ∀ c' : 𝓞 E, c' ∈ J' → ∀ l, c' • l ∈ W := by
    intro c' hc' l
    obtain ⟨a, ha⟩ := hevs (ψ (c' • l)) (by
      intro c hc
      have hcc : c * c' ∈ Ideal.span {(n : 𝓞 E)} := by rw [hJ']; exact Ideal.mul_mem_mul hc hc'
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hcc
      rw [← map_smul, smul_smul, ← hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
      exact (hψ _).2 ⟨_, rfl⟩)
    exact ⟨a, ha⟩
  have hnW : ∀ I : Ideal (𝓞 E), J ≤ I → ∀ l : Λ, n • l ∈ I • W := by
    intro I hJI l
    have h1 : (n : 𝓞 E) • l ∈ (J * J') • (⊤ : Submodule (𝓞 E) Λ) :=
      Submodule.smul_mem_smul (by rw [← hJ']; exact Ideal.mem_span_singleton_self _) trivial
    rw [Submodule.mul_smul, Nat.cast_smul_eq_nsmul] at h1
    exact Submodule.smul_mono hJI (Submodule.smul_le.2 fun c' hc' l _ => hJ'W c' hc' l) h1
  have hpow : ∀ k (l : Λ) (a : La), ψ l = ev a → ψ (((G - 1 : Module.End (𝓞 E) Λ) ^ k) l) = ev (((gM - 1 : Module.End (𝓞 E) La) ^ k) a) := by
    intro k
    induction k with
    | zero => intro l a h; simpa using h
    | succ k ih =>
      intro l a h
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      apply ih
      simp [map_sub, hkey l a h, h]
  have hunipW : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ l ∈ W, ((G - 1) ^ m) l ∈ I • W := by
    rintro I hJI hu l ⟨a, ha⟩
    have hx := hpow m l a ha.symm
    have hmem : ev (((gM - 1) ^ m) a) ∈ (I • W).map ψ := by
      have h1 : ev (((gM - 1) ^ m) a) ∈ (I • (⊤ : Submodule (𝓞 E) La)).map ev := ⟨_, hu a, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top] at h1
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_ h1
      rintro _ ⟨b, rfl⟩
      obtain ⟨μ, hμ⟩ := hevψ b
      exact ⟨μ, ⟨b, hμ.symm⟩, hμ⟩
    obtain ⟨z, hz, hzx⟩ := hmem
    have hd : ψ (((G - 1) ^ m) l - z) = 0 := by rw [map_sub, hzx, hx, sub_self]
    obtain ⟨b', hb'⟩ := (hψ _).1 hd
    have : ((G - 1) ^ m) l = z + n • b' := by rw [← hb']; abel
    rw [this]; exact Submodule.add_mem _ hz (hnW I hJI b')
  haveI := hfin; haveI := htf
  let Gr : Module.End (𝓞 E) W := G.restrict hGW
  have hGr : ∀ y : W, ((Gr y : W) : Λ) = G y := fun y => rfl
  have hGr1 : ∀ y : W, (((Gr - 1) y : W) : Λ) = (G - 1) y := fun y => rfl
  have hGN : G ^ N = 1 := by
    rw [hGdef, ← pow_mul, mul_comm, pow_mul, hFN, one_pow]
  have hGrN : Gr ^ N = 1 := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    rw [GlobalTheory.NeatLevel.val_pow_apply W Gr G hGr, hGN]; rfl
  have hsub : ∀ I : Ideal (𝓞 E), J ≤ I → (∀ x, ((gM - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) La)) →
      ∀ y : W, ((Gr - 1) ^ m) y ∈ I • (⊤ : Submodule (𝓞 E) W) := by
    intro I hJI hu y
    have h1 : ((((Gr - 1) ^ m) y : W) : Λ) ∈ (I • (⊤ : Submodule (𝓞 E) W)).map W.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top, GlobalTheory.NeatLevel.val_pow_apply W (Gr - 1) (G - 1) hGr1]
      exact hunipW I hJI hu y y.2
    obtain ⟨z, hz, hzy⟩ := h1
    have hzz : z = ((Gr - 1) ^ m) y := Subtype.ext hzy
    rwa [← hzz]
  have hGr1' : Gr = 1 := eq_one_of_finite_order I hI hg (by exact_mod_cast hg.ne_zero) hgI hr s hs1 hs Gr
    hN hGrN (hsub I hJI hu)
  intro a
  obtain ⟨l, hl⟩ := hevψ a
  have hlW : l ∈ W := ⟨a, hl.symm⟩
  have hGl : G l = l := by
    have := congrArg (fun T : Module.End (𝓞 E) W => ((T ⟨l, hlW⟩ : W) : Λ)) hGr1'
    exact (hGr ⟨l, hlW⟩).symm.trans (by simpa using this)
  have h := hkey l a hl
  rw [hGl, hl] at h
  rw [← hev, map_sub, ← h, sub_self]

open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `g k _ _ y y' hR hx`. Take `⟨ρ, ν, -, hlev, hmove⟩` from `hR`. Establish `hfix : y.x ≫ ρ = y.x` using `hmove.1.symm.trans hx`. Take `⟨x', hx'⟩` from `GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint E H Dw l Xo k y.x ρ hfix`. Take `⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩` from `GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'`.

Establish `hM0 : 0 < l.M` using `by have := l.three_le; omega`. Take `⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩` from `GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism E P act θ N l.M hθ hN hθN hcomm hM0`. Use `letI := P.isAb.comm`. Use `letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := GlobalTheory.FreeLev.ptModule P act`. Set `evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)` to `{ toFun := fun a => Additive.ofMul (ev a) map_add' := fun a b => congrArg Additive.ofMul (hadd a b) map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }`.

Set `ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)` to `{ toFun := fun a => Additive.ofMul (ψ a) map_add' := fun a b => congrArg Additive.ofMul (hψadd a b) map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }`. Set `θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)` to `{ toFun := fun q => Additive.ofMul (q.toMul ≫ θ) map_add' := fun q q' => by show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)`. Rewrite using `[MonObj.mul_comp]`. Use the proof step `map_smul' := fun c q => by show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)`. Rewrite using `[Category.assoc, Category.assoc, hcomm] }`.

Establish `hMmem : (l.M : 𝓞 E) ∈ l.Mb`. Establish `h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)}` using `Ideal.subset_span rfl`. Rewrite `h1` using `[← l.prod]`. Conclude with `Ideal.mul_le_left h1`. Use `hfaith g (sub_mem_smul_top_of_level E Dw.La Λ _ l.Mb l.M N m q₀ I s evL ψL θL F (h g) hfin htf hMmem (fun a => by show Additive.ofMul (ev a) = 0 ↔ _` and prove the remaining obligations.

Rewrite using `[← hker a]`. Conclude with `ofMul_eq_zero)`. Use the proof step `(fun q hq => by`. Take `⟨a, ha⟩` from `honto q.toMul (fun c hc => by`. Use `hq c hc` as an intermediate fact.

Conclude with `congrArg Additive.toMul this)`. Conclude with `⟨a, congrArg Additive.ofMul ha⟩)`. Use the proof step `(fun b => by show Additive.ofMul (ψ b) = 0 ↔ _`. Rewrite using `[← hψker b]`. Conclude with `ofMul_eq_zero)`.

Use the proof step `(fun q hq => by`. Take `⟨b, hb⟩` from `hψonto q.toMul (by`. Use `congrArg Additive.toMul hq` as an intermediate fact. Rewrite using `[toMul_nsmul] at this)` and apply the resulting hypothesis. Conclude with `⟨b, congrArg Additive.ofMul hb⟩)`.

Use the proof step `(fun b => congrArg Additive.ofMul (hψF b))`. Use the proof step `(fun a => congrArg Additive.ofMul (hrel a))`. Use `hN hFN hq hI hqI hr hs1 hs hMb (hu g))`.
-/
theorem free_of_unip_one (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m q₀ : ℕ)
    (I : Ideal (𝓞 E)) (s : 𝓞 E) (hq : q₀.Prime) (hI : I ≠ ⊤) (hqI : (q₀ : 𝓞 E) ∈ I) (hr : m + 1 < q₀) (hs1 : 1 - s ∈ I)
    (hs : ∀ a ∈ I, (q₀ : 𝓞 E) ∣ s * a) (hMb : l.Mb ≤ I)
    (hu : ∀ g x, ((h g - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La))
    (hfaith : ∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) :
    FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  intro g k _ _ y y' hR hx
  obtain ⟨ρ, ν, -, hlev, hmove⟩ := hR
  have hfix : y.x ≫ ρ = y.x := hmove.1.symm.trans hx
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint E H Dw l Xo k y.x ρ hfix
  obtain ⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩ :=
    GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'
  have hM0 : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩ :=
    GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism E P act θ N l.M hθ hN hθN hcomm hM0
  letI := P.isAb.comm
  letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := GlobalTheory.FreeLev.ptModule P act
  let evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_add' := fun a b => congrArg Additive.ofMul (hadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }
  let ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ψ a)
      map_add' := fun a b => congrArg Additive.ofMul (hψadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }
  let θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun q => Additive.ofMul (q.toMul ≫ θ)
      map_add' := fun q q' => by
        show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)
        rw [MonObj.mul_comp]
      map_smul' := fun c q => by
        show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)
        rw [Category.assoc, Category.assoc, hcomm] }
  have hMmem : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact Ideal.mul_le_left h1
  refine hfaith g (sub_mem_smul_top_of_level E Dw.La Λ _ l.Mb l.M N m q₀ I s evL ψL θL F (h g) hfin htf hMmem
    (fun a => by
      show Additive.ofMul (ev a) = 0 ↔ _
      rw [← hker a]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨a, ha⟩ := honto q.toMul (fun c hc => by
        have := hq c hc
        exact congrArg Additive.toMul this)
      exact ⟨a, congrArg Additive.ofMul ha⟩)
    (fun b => by
      show Additive.ofMul (ψ b) = 0 ↔ _
      rw [← hψker b]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨b, hb⟩ := hψonto q.toMul (by
        have := congrArg Additive.toMul hq
        rwa [toMul_nsmul] at this)
      exact ⟨b, congrArg Additive.ofMul hb⟩)
    (fun b => congrArg Additive.ofMul (hψF b))
    (fun a => congrArg Additive.ofMul (hrel a))
    hN hFN hq hI hqI hr hs1 hs hMb (hu g))

end GlobalTheory.NeatOne
