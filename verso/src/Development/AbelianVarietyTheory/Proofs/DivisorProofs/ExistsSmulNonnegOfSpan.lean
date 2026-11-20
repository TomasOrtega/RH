import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLatOfOfLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions

namespace GlobalTheory.IntCuspLat

section Abstract

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R] {Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)}

/- English proof (translation)
Rewrite using `[← algebraMap_smul K a f]`. Distinguish the cases in `ha : (a : K) = 0`. Rewrite using `[show algebraMap (𝓞 K) K a = 0 from ha, zero_smul, (hV la v hv).zero]`. Conclude with `le_top`. Rewrite using `[(hV la v hv).smul _ _ ha]`.

Conclude with `add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) hf`.
-/
theorem nonneg_smul (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal}
    (hv : v ∈ Vs la) (a : 𝓞 K) {f : R} (hf : 0 ≤ v f) : 0 ≤ v (a • f) := by
  rw [← algebraMap_smul K a f]
  by_cases ha : (a : K) = 0
  · rw [show algebraMap (𝓞 K) K a = 0 from ha, zero_smul, (hV la v hv).zero]; exact le_top
  · rw [(hV la v hv).smul _ _ ha]
    exact add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) hf

def intOn (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (p : HeightOneSpectrum (𝓞 K) → Prop) : Submodule (𝓞 K) R where
  carrier := {f | ∀ la, p la → ∀ v ∈ Vs la, 0 ≤ v f}
  zero_mem' := fun la _ v hv => by rw [(hV la v hv).zero]; exact le_top
  add_mem' := fun {_ _} hf hg la hp v hv => (le_min (hf la hp v hv) (hg la hp v hv)).trans ((hV la v hv).add _ _)
  smul_mem' := fun a _ hf la hp v hv => nonneg_smul hV hv a (hf la hp v hv)

/- English proof (translation)
Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set R) f hf`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.ne_zero t.2, ht⟩`.
-/
theorem exists_smul_mem {M : Submodule (𝓞 K) R} {f : R} (hf : f ∈ Submodule.span K (M : Set R)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ s • f ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set R) f hf
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

/- English proof (translation)
Use `Submodule.smul_mem (Submodule.span K S) t⁻¹ (Submodule.subset_span hf)` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ ht, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_span_of_smul_mem {S : Set R} {t : K} (ht : t ≠ 0) {f : R} (hf : t • f ∈ S) : f ∈ Submodule.span K S := by
  have := Submodule.smul_mem (Submodule.span K S) t⁻¹ (Submodule.subset_span hf)
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

/- English proof (translation)
Use `haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot`. Use `haveI := la.isPrime`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 K ⧸ la.asIdeal)`. Use `⟨p, (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) p).resolve_right (CharP.char_ne_zero_of_finite (𝓞 K ⧸ la.asIdeal) p), ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]`.
-/
theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ la.asIdeal := by
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  haveI := la.isPrime
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ la.asIdeal)
  refine ⟨p, (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ la.asIdeal) p), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]

/- English proof (translation)
Set `I : ℕ → Submodule K R` to `fun N => Submodule.span K (intOn hV fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ la.asIdeal ∧ ¬ ℓ ∣ N : Set R)`. Establish `mono : ∀ {N N' : ℕ}, N ∣ N' → I N ≤ I N'` using `fun h => Submodule.span_mono fun g hg la ⟨ℓ, h1, h2, h3⟩ => hg la ⟨ℓ, h1, h2, fun h4 => h3 (h4.trans h)⟩`. Establish `h1 : ∀ g ∈ Submodule.span K (Gen 1), ∃ N, 0 < N ∧ g ∈ I N`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem g hg`. Take `⟨t, N, ht, hN, h⟩` from `hG 1 one_pos g hg`. Conclude with `⟨N, hN, mem_span_of_smul_mem ht fun la ⟨ℓ, a, b, c⟩ => h la ℓ a b (Or.inr c)⟩`. Consider the case `zero => exact ⟨1, one_pos, zero_mem _⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨N, hN, hx⟩` from `hx`. Take `⟨N', hN', hy⟩` from `hy`. Conclude with `⟨N * N', Nat.mul_pos hN hN', add_mem (mono (dvd_mul_right _ _) hx) (mono (dvd_mul_left _ _) hy)⟩`. Consider the case `smul a x _ hx`. Take `⟨N, hN, hx⟩` from `hx`.

Conclude with `⟨N, hN, Submodule.smul_mem _ a hx⟩`. Take `⟨N, hN, h2⟩` from `h1 f (hf 1 one_pos)`. Establish `h3 : f ∈ Submodule.span K (intOn hV fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ la.asIdeal ∧ ℓ ∣ N : Set R)`. Use `Submodule.span_le.2 (fun g hg => ?_) (hf N hN)` and prove the remaining obligations. Take `⟨t, N', ht, -, h⟩` from `hG N hN g hg`.

Conclude with `mem_span_of_smul_mem ht fun la ⟨ℓ, a, b, c⟩ => h la ℓ a b (Or.inl c)`. Take `⟨s, hs, h4⟩` from `exists_smul_mem h2`. Take `⟨s', hs', h5⟩` from `exists_smul_mem h3`. Use `⟨s * s', mul_ne_zero hs hs', fun la v hv => ?_⟩` and prove the remaining obligations. Take `⟨ℓ, hℓ, hm⟩` from `exists_prime_mem la`.

Distinguish the cases in `hd : ℓ ∣ N`. Rewrite using `[mul_smul]`. Conclude with `nonneg_smul hV hv s (h5 la ⟨ℓ, hℓ, hm, hd⟩ v hv)`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `nonneg_smul hV hv s' (h4 la ⟨ℓ, hℓ, hm, hd⟩ v hv)`.
-/
theorem exists_smul_nonneg_of_span (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (Gen : ℕ → Set R) {f : R}
    (hf : ∀ b, 0 < b → f ∈ Submodule.span K (Gen b))
    (hG : ∀ b, 0 < b → ∀ g ∈ Gen b, ∃ (t : K) (N : ℕ), t ≠ 0 ∧ 0 < N ∧ ∀ la (ℓ : ℕ), ℓ.Prime →
      (ℓ : 𝓞 K) ∈ la.asIdeal → (ℓ ∣ b ∨ ¬ ℓ ∣ N) → ∀ v ∈ Vs la, 0 ≤ v (t • g)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f) := by
  let I : ℕ → Submodule K R := fun N => Submodule.span K
    (intOn hV fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ la.asIdeal ∧ ¬ ℓ ∣ N : Set R)
  have mono : ∀ {N N' : ℕ}, N ∣ N' → I N ≤ I N' := fun h =>
    Submodule.span_mono fun g hg la ⟨ℓ, h1, h2, h3⟩ => hg la ⟨ℓ, h1, h2, fun h4 => h3 (h4.trans h)⟩
  have h1 : ∀ g ∈ Submodule.span K (Gen 1), ∃ N, 0 < N ∧ g ∈ I N := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨t, N, ht, hN, h⟩ := hG 1 one_pos g hg
      exact ⟨N, hN, mem_span_of_smul_mem ht fun la ⟨ℓ, a, b, c⟩ => h la ℓ a b (Or.inr c)⟩
    | zero => exact ⟨1, one_pos, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨N, hN, hx⟩ := hx
      obtain ⟨N', hN', hy⟩ := hy
      exact ⟨N * N', Nat.mul_pos hN hN', add_mem (mono (dvd_mul_right _ _) hx) (mono (dvd_mul_left _ _) hy)⟩
    | smul a x _ hx =>
      obtain ⟨N, hN, hx⟩ := hx
      exact ⟨N, hN, Submodule.smul_mem _ a hx⟩
  obtain ⟨N, hN, h2⟩ := h1 f (hf 1 one_pos)
  have h3 : f ∈ Submodule.span K (intOn hV fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ la.asIdeal ∧ ℓ ∣ N : Set R) := by
    refine Submodule.span_le.2 (fun g hg => ?_) (hf N hN)
    obtain ⟨t, N', ht, -, h⟩ := hG N hN g hg
    exact mem_span_of_smul_mem ht fun la ⟨ℓ, a, b, c⟩ => h la ℓ a b (Or.inl c)
  obtain ⟨s, hs, h4⟩ := exists_smul_mem h2
  obtain ⟨s', hs', h5⟩ := exists_smul_mem h3
  refine ⟨s * s', mul_ne_zero hs hs', fun la v hv => ?_⟩
  obtain ⟨ℓ, hℓ, hm⟩ := exists_prime_mem la
  by_cases hd : ℓ ∣ N
  · rw [mul_smul]
    exact nonneg_smul hV hv s (h5 la ⟨ℓ, hℓ, hm, hd⟩ v hv)
  · rw [mul_comm, mul_smul]
    exact nonneg_smul hV hv s' (h4 la ⟨ℓ, hℓ, hm, hd⟩ v hv)

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_le]`. Establish `key : ∀ m : ℕ, v ((s • f) ^ (m + 1)) < 0` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => rwa [zero_add, pow_one]`.

Consider the case `succ m ih`. Rewrite using `[pow_succ, (hV la v hv).mul]`. Conclude with `lt_of_le_of_lt ((add_le_add le_rfl hn.le).trans (add_zero _).le) ih`. Establish `h1` using `nonneg_smul hV hv (s ^ k) h`. Rewrite `h1` using `[smul_smul, ← pow_succ, ← smul_pow]`.

Conclude with `absurd (key k) (not_lt.2 h1)`.
-/
theorem nonneg_of_pow (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal}
    (hv : v ∈ Vs la) (s : 𝓞 K) (f : R) (k : ℕ) (h : 0 ≤ v (s • f ^ (k + 1))) : 0 ≤ v (s • f) := by
  by_contra hn
  rw [not_le] at hn
  have key : ∀ m : ℕ, v ((s • f) ^ (m + 1)) < 0 := fun m => by
    induction m with
    | zero => rwa [zero_add, pow_one]
    | succ m ih =>
      rw [pow_succ, (hV la v hv).mul]
      exact lt_of_le_of_lt ((add_le_add le_rfl hn.le).trans (add_zero _).le) ih
  have h1 := nonneg_smul hV hv (s ^ k) h
  rw [smul_smul, ← pow_succ, ← smul_pow] at h1
  exact absurd (key k) (not_lt.2 h1)

/- English proof (translation)
Use `eq_top_iff.2 fun f _ => ?_` and prove the remaining obligations. Take `⟨s, hs, h1⟩` from `h f.1 f.2`. Establish `hs' : algebraMap (𝓞 K) K s ≠ 0` using `by simpa using hs`. Establish `h2 : algebraMap (𝓞 K) K s • f ∈ (latOf C Vs hV : Set C)` using `fun la v hv => by`. Rewrite using `[Submodule.coe_smul, algebraMap_smul]`.

Conclude with `h1 la v hv`. Use `Submodule.smul_mem (Submodule.span K (latOf C Vs hV : Set C)) (algebraMap (𝓞 K) K s)⁻¹ (Submodule.subset_span h2)` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hs', one_smul]`. Then use the resulting hypothesis.
-/
theorem span_latOf_eq_top (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (C : Submodule K R)
    (h : ∀ f ∈ C, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f)) :
    Submodule.span K (latOf C Vs hV : Set C) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨s, hs, h1⟩ := h f.1 f.2
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := by simpa using hs
  have h2 : algebraMap (𝓞 K) K s • f ∈ (latOf C Vs hV : Set C) := fun la v hv => by
    rw [Submodule.coe_smul, algebraMap_smul]
    exact h1 la v hv
  have := Submodule.smul_mem (Submodule.span K (latOf C Vs hV : Set C)) (algebraMap (𝓞 K) K s)⁻¹
    (Submodule.subset_span h2)
  rwa [smul_smul, inv_mul_cancel₀ hs', one_smul] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fg_latOf_of_lowerBound C Vs hV N hN B hB, span_latOf_eq_top hV C h⟩`.
-/
theorem fullLat_of (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (C : Submodule K R) [FiniteDimensional K C]
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F))
    (h : ∀ f ∈ C, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f)) : Formalism.IndefR.FWT.FullLat C Vs hV :=
  ⟨fg_latOf_of_lowerBound C Vs hV N hN B hB, span_latOf_eq_top hV C h⟩

end Abstract

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `h2 : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La` using `hN.2.2.trans inf_le_left`. Use `⟨N, ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h).symm, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Introduce and unpack `_ ⟨v, hv, rfl⟩ j -`. Establish `hw : (N : 𝓞 E) • (Pi.single j 1 : Fin n → E) ∈ Λ.La` using `h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun i _ => by`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `[Submodule.one_le.1 le_rfl]`. Simplify using `[hi])`. Take `⟨a, ha⟩` from `(hU _).1 hw v hv`.

Rewrite `ha` using `[Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]`. Use `Submodule.mem_one.2 ⟨a, ha.trans ?_⟩` and prove the remaining obligations. Simplify using `[Nat.cast_smul_eq_nsmul]`.
-/
theorem trivAt_of_not_dvd {Λ : GenLat E n} {N M ℓ : ℕ} (hU : Λ.Unimod) (hN : Λ.LevOK N M) (hℓ : ℓ.Prime)
    (h : ¬ ℓ ∣ N) : Λ.TrivAt ℓ := by
  classical
  have h2 : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hN.2.2.trans inf_le_left
  refine ⟨N, ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h).symm, ?_, h2⟩
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨v, hv, rfl⟩ j -
  have hw : (N : 𝓞 E) • (Pi.single j 1 : Fin n → E) ∈ Λ.La :=
    h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun i _ => by
      by_cases hi : i = j
      · subst hi; simp [Submodule.one_le.1 le_rfl]
      · simp [hi])
  obtain ⟨a, ha⟩ := (hU _).1 hw v hv
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at ha
  refine Submodule.mem_one.2 ⟨a, ha.trans ?_⟩
  simp [Nat.cast_smul_eq_nsmul]

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `h.imp fun _ hk => ⟨hk.1.coprime_dvd_right hd, hk.2⟩`.
-/
theorem trivAt_of_dvd {Λ : GenLat E n} {b ℓ : ℕ} (h : Λ.TrivAt b) (hd : ℓ ∣ b) : Λ.TrivAt ℓ :=
  h.imp fun _ hk => ⟨hk.1.coprime_dvd_right hd, hk.2⟩

end Lattices

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨-, hA, -, -, -, -, hnum⟩` from `GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins`. Take `⟨hpq, hr, -⟩` from `hnum j hj`. Establish `hC` using `GlobalTheory.ChartFree.chartIndep`. Establish `hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))` using `h.unf j hj _ T.good_σ₀`. Establish `hP : ∀ k, GlobalTheory.Dict.HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M`.

Introduce `k ga hga hv`. Use `GlobalTheory.RunIn.gamAt_of_lawsM D T h j hj _ T.good_σ₀ k ga hga fun x hx => ?_` and prove the remaining obligations. Take `⟨u, hu, he⟩` from `hv x hx`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[he, Nat.cast_smul_eq_nsmul]`.

Conclude with `add_sub_cancel_left _ _`. Establish `hsf : Squarefree T.Q.l.M`. Rewrite using `[show T.Q.l.M = _ from h.pins.2.1.1, Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]`. Conclude with `⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩`. Establish `hχ` using `fun k => h.chiTriv j hj T.σ₀ T.good_σ₀ a n hdom k`.

Establish `hf'` using `(mem_cusp _ _ _ a n f).1 hf`. Establish `h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q` using `hpq ▸ hr`. Establish `hL : Out.Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hB : Out.SecBaseChangeSt` using `hL.secBaseChange`. Establish `hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n`.

Establish `h0 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Establish `: D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r` using `Nat.le_mul_of_pos_left _ h0`. Use linear arithmetic over natural numbers and integers. Establish `hd : ∃ d : DeltaDat (T.Q.Xo j) T.Q.c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧ d.pd = 1 ∧ d.l₂.A = T.Q.l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀`. Take `⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩` from `GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) T.Q.c h1 n 1 ⊤ T.Q.l (T.Q.Xo j) T.Q.c rfl ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)`.

Take `⟨f, ph, x₀, hpin⟩` from `GlobalTheory.exists_phiPin_of_character _ _ _ _ (T.Q.Xo j) T.Q.c n d hlev hnr 1`. Conclude with `⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩`. Take `⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩` from `hd`. Establish `hT : AllTest d.Xo₂ d.c₂` using `GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂`. Take `⟨_, nab, -⟩` from `GlobalTheory.CanonConn.exists_isNab hL _ _ _ _ (T.Q.Xo j) T.Q.c`.

Establish `hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y = 1` using `fun k _ _ y => by`. Rewrite using `[hδ]`. Conclude with `evalAt_one _ _ _ (hT _ _)`. Establish `hunit : GlobalTheory.Dict.UnitC d` using `fun A y => by`. Establish `: evR d.Xo₂ d.c₂ d.cδ y = 1`.

Rewrite using `[hδ]`. Conclude with `evalAt_one _ _ _ (hT _ _)`. Rewrite using `[this, norm_one]`. Establish `h3 : ¬ 3 ∣ d.pd` using `by rw [hpe]; decide`. Establish `htie : d.PsiTie 1`.

Introduce `k g ρ _ _ _ _ K _ _ _ y y' _`. Express the relevant statement in the definitionally equal form `evR d.Xo₂ d.c₂ d.cδ y' = algebraMap d.c₂.F K (d.eF ((1 : T.Q.c.Fˣ) : T.Q.c.F)) * evR d.Xo₂ d.c₂ d.cδ y`. Rewrite using `[hone K y, hone K y']`. Simplify using the standard rewrite rules. Establish `hind` using `(GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀ D.R.r _ hU a n).1`.

Use `exists_smul_nonneg_of_span (fun la => isVal_valSet la) (fun b => shortGen (T.Q.Xo j) T.Q.c nab b 0 a n d) (fun b hb => ?_) fun b hb g hg => ?_` and prove the remaining obligations. Establish `htot : ShortValTot (T.Q.Xo j) T.Q.c nab b 0 a n d` using `GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ (T.Q.Xo j) T.Q.c n d (GlobalTheory.levelMaps_closed hL _ _ _ h1) (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (T.Q.Xo j) T.Q.c) (GlobalTheory.Frames …`. Establish `hsp` using `GlobalTheory.Dict.holSub0_le_span_shortGen hC _ _ _ _ (T.Q.Xo j) T.Q.c n d T.σ₀ D.R.r _ T.good_σ₀ hU hr hA hG hP hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab b 0 a hb hdom hn hχ htot`. Use `GlobalTheory.mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))) (sec (T.Q.Xo j) T.Q.c a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)` and prove the remaining obligations. Conclude with `⟨hf'.2 _ T.good_σ₀, fun k x hx => dif_neg hx⟩`.

Take `⟨hsec, Λ, N, x0, P, hUn, hTb, hTM, hN, -, hPl, hR⟩` from `hg`. Take `⟨inst, hnab⟩` from `hnab`. Take `⟨t, ht, hb'⟩` from `exists_smul_nonneg_of_shortRule D _ _ _ (T.Q.Xo j) T.Q.c n d hlev hnab (fun k _ _ y => by rw [hone k y, one_pow]) (GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ (T.Q.Xo j) T.Q.c n d hlev ph 1 x₀ hpin) (by rw [hlev.2.1, hpe, mul_one]; exact hsf) Λ N hUn hTM hN a P hPl x0 g hsec h …`. Conclude with `⟨t, N, ht, hN.1.pos, fun la ℓ hℓ hm hor => hb' la ℓ hℓ hm (hor.elim (trivAt_of_dvd hTb) (trivAt_of_not_dvd hUn hN hℓ))⟩`.
-/
theorem exists_smul_nonneg_large (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j)
    (hG : ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n)
    (f : T.R j) (hf : f ∈ T.cuspA j a n) :
    ∃ s : 𝓞 T.Q.c.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v (s • f) := by
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have hC := GlobalTheory.ChartFree.chartIndep
  have hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) := h.unf j hj _ T.good_σ₀
  have hP : ∀ k, GlobalTheory.Dict.HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M := by
    intro k ga hga hv
    refine GlobalTheory.RunIn.gamAt_of_lawsM D T h j hj _ T.good_σ₀ k ga hga fun x hx => ?_
    obtain ⟨u, hu, he⟩ := hv x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    exact add_sub_cancel_left _ _
  have hsf : Squarefree T.Q.l.M := by
    rw [show T.Q.l.M = _ from h.pins.2.1.1,
      Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
    exact ⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩
  have hχ := fun k => h.chiTriv j hj T.σ₀ T.good_σ₀ a n hdom k
  have hf' := (mem_cusp _ _ _ a n f).1 hf
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hpq ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat (T.Q.Xo j) T.Q.c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
      d.cδ = 1 ∧ d.pd = 1 ∧ d.l₂.A = T.Q.l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) T.Q.c h1 n 1 ⊤ T.Q.l (T.Q.Xo j) T.Q.c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ (T.Q.Xo j) T.Q.c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ _ _ (T.Q.Xo j) T.Q.c
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y = 1 :=
    fun k _ _ y => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : GlobalTheory.Dict.UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : T.Q.c.Fˣ) : T.Q.c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
    D.R.r _ hU a n).1
  refine exists_smul_nonneg_of_span (fun la => isVal_valSet la)
    (fun b => shortGen (T.Q.Xo j) T.Q.c nab b 0 a n d) (fun b hb => ?_) fun b hb g hg => ?_
  · have htot : ShortValTot (T.Q.Xo j) T.Q.c nab b 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ (T.Q.Xo j) T.Q.c n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (T.Q.Xo j) T.Q.c)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab b 0 a
    have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC _ _ _ _ (T.Q.Xo j) T.Q.c n d T.σ₀ D.R.r _ T.good_σ₀ hU hr hA hG hP
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab b 0 a hb hdom hn hχ htot
    refine GlobalTheory.mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)))
      (sec (T.Q.Xo j) T.Q.c a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ T.good_σ₀, fun k x hx => dif_neg hx⟩
  · obtain ⟨hsec, Λ, N, x0, P, hUn, hTb, hTM, hN, -, hPl, hR⟩ := hg
    obtain ⟨inst, hnab⟩ := hnab
    obtain ⟨t, ht, hb'⟩ := exists_smul_nonneg_of_shortRule D _ _ _ (T.Q.Xo j) T.Q.c n d hlev hnab
      (fun k _ _ y => by rw [hone k y, one_pow])
      (GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ (T.Q.Xo j) T.Q.c n d hlev ph 1 x₀ hpin)
      (by rw [hlev.2.1, hpe, mul_one]; exact hsf) Λ N hUn hTM hN a P hPl x0 g hsec hR
    exact ⟨t, N, ht, hN.1.pos, fun la ℓ hℓ hm hor =>
      hb' la ℓ hℓ hm (hor.elim (trivAt_of_dvd hTb) (trivAt_of_not_dvd hUn hN hℓ))⟩

/- English proof (translation)
Establish `hmul : CuspMul (T.Q.Xo j) T.Q.c (T.U j)` using `cusp_mul_of_M5 siegelSpaceAlgebra_holds _`. Establish `hD : ∀ k : ℕ, Dom (k • a) (k * n)` using `fun k => ⟨fun τ i i' hi => Nat.mul_le_mul_left k (hdom.1 τ hi), hdom.2.mul_left k⟩`. Establish `hpow : ∀ k : ℕ, f ^ (k + 1) ∈ T.cuspA j ((k + 1) • a) ((k + 1) * n)` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => simpa using hf`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, succ_nsmul a (k + 1), Nat.succ_mul (k + 1)]`. Conclude with `hmul _ _ _ _ _ _ (hD _) hdom ih hf`. Take `⟨s, hs, h1⟩` from `exists_smul_nonneg_large D T h j hj hG _ _ (hD (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1)) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn)) _ (hpow _)`. Conclude with `⟨s, hs, fun la v hv => nonneg_of_pow (fun la => isVal_valSet la) hv s f _ (h1 la v hv)⟩`.
-/
theorem exists_smul_nonneg (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j)
    (hG : ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) (hn : n ≠ 0) (f : T.R j) (hf : f ∈ T.cuspA j a n) :
    ∃ s : 𝓞 T.Q.c.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v (s • f) := by
  have hmul : CuspMul (T.Q.Xo j) T.Q.c (T.U j) := cusp_mul_of_M5 siegelSpaceAlgebra_holds _
  have hD : ∀ k : ℕ, Dom (k • a) (k * n) := fun k =>
    ⟨fun τ i i' hi => Nat.mul_le_mul_left k (hdom.1 τ hi), hdom.2.mul_left k⟩
  have hpow : ∀ k : ℕ, f ^ (k + 1) ∈ T.cuspA j ((k + 1) • a) ((k + 1) * n) := fun k => by
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ, succ_nsmul a (k + 1), Nat.succ_mul (k + 1)]
      exact hmul _ _ _ _ _ _ (hD _) hdom ih hf
  obtain ⟨s, hs, h1⟩ := exists_smul_nonneg_large D T h j hj hG _ _ (hD (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1))
    (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn)) _ (hpow _)
  exact ⟨s, hs, fun la v hv => nonneg_of_pow (fun la => isVal_valSet la) hv s f _ (h1 la v hv)⟩

/- English proof (translation)
Establish `: FiniteDimensional T.Q.c.F (T.C j w)` using `h.cuspFD j hj _ _ (dom_wtA w)`. Take `⟨B, hB⟩` from `exists_lowerBound D T h j hj w`. Conclude with `fullLat_of _ _ (T.Ns j w) (fun σ => (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf) B hB (exists_smul_nonneg D T h j hj hG _ _ (dom_wtA w) hn)`.
-/
theorem fullLat_of_lawsM (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j)
    (hG : ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (w : WeightFamilies.Wt D j) (hn : w.n ≠ 0) :
    Formalism.IndefR.FWT.FullLat (T.C j w) (T.Vs j) fun la => isVal_valSet la := by
  have : FiniteDimensional T.Q.c.F (T.C j w) := h.cuspFD j hj _ _ (dom_wtA w)
  obtain ⟨B, hB⟩ := exists_lowerBound D T h j hj w
  exact fullLat_of _ _ (T.Ns j w)
    (fun σ => (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf) B hB
    (exists_smul_nonneg D T h j hj hG _ _ (dom_wtA w) hn)

open Formalism.IndefR.FWT

/- English proof (translation)
Introduce `i` and use `by obtain ⟨_, hW⟩ := h.modelW _ (inR i) _ T.toCore.good_σ₀ exact fullLat_of_lawsM D T.toCore h.toLawsM _ (inR i) (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩) (κ i) (hn i)`.
-/
theorem latFull_of_ne_zero (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (h : LawsJ T)
    (hn : ∀ i, (κ i).n ≠ 0) : LatFull T κ := fun i => by
  obtain ⟨_, hW⟩ := h.modelW _ (inR i) _ T.toCore.good_σ₀
  exact fullLat_of_lawsM D T.toCore h.toLawsM _ (inR i)
    (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩) (κ i) (hn i)

/- English proof (translation)
Use `D.R.m_add_three_le_k` as an intermediate fact. Simplify using `only [Ranks.nV, Ranks.r]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nV_ne_zero (D : D7) : D.R.nV ≠ 0 := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r]
  omega

/- English proof (translation)
Introduce `D T κ h hκ` and use `latFull_of_ne_zero D T κ h fun i => by rw [(hκ i (D.eTau.symm 1)).2.2] exact nV_ne_zero D`.
-/
theorem latFull : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)),
    LawsJ T → KapIs κ → LatFull T κ := fun D T κ h hκ =>
  latFull_of_ne_zero D T κ h fun i => by
    rw [(hκ i (D.eTau.symm 1)).2.2]
    exact nV_ne_zero D

/- English proof (translation)
The claim follows from `latFull D T κ t.laws t.kap`.
-/
theorem latFull_of_tie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {R : Formalism.IndefR.Links.RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : LatFull T κ :=
  latFull D T κ t.laws t.kap

end GlobalTheory.IntCuspLat
