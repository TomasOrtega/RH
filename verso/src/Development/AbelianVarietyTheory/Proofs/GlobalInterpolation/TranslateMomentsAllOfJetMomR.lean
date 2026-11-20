import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WopAddLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCoprimeMulIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRatNear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousCharacter
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgEntireTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.MomentCombSplitting

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

/- English proof (translation)
Take `⟨u, v, h⟩` from `Nat.isCoprime_iff_coprime.2 hab`. Establish `: x = u • a • x + v • b • x`. Rewrite using `[← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, h, one_smul]`. Rewrite using `[this]`. Conclude with `add_mem (zsmul_mem ha _) (zsmul_mem hb _)`.
-/
theorem mem_of_coprime {A : Type*} [AddCommGroup A] (H : AddSubgroup A) {x : A} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a • x ∈ H) (hb : b • x ∈ H) : x ∈ H := by
  obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.2 hab
  have : x = u • a • x + v • b • x := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, h, one_smul]
  rw [this]
  exact add_mem (zsmul_mem ha _) (zsmul_mem hb _)

/- English proof (translation)
Establish `h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p])` using `by simp`. Rewrite using `[norm_pow, h, norm_algebraMap', Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]`.
-/
theorem norm_p_pow (n : ℕ) : ‖(p : ℂ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
  rw [norm_pow, h, norm_algebraMap', Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

/- English proof (translation)
Establish `h1` using `norm_algebraMap' ℂ_[p] (s : ℚ_[p])`. Rewrite `h1` using `[Padic.norm_natCast_eq_one_iff.2 h.symm]`. Simplify using `using h1`.
-/
theorem norm_coprime {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 := norm_algebraMap' ℂ_[p] (s : ℚ_[p])
  rw [Padic.norm_natCast_eq_one_iff.2 h.symm] at h1
  simpa using h1

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hp0 : (p : D.host.K) ^ n ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)`. Establish `hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ))` using `zpow_pos (by exact_mod_cast hp.pos) _`. Take `⟨s, hs, z, hz⟩` from `GlobalTheory.IntegralAtBothPrimes.exists_coprime_mul_integral D p lam ((u : D.host.K) / (p : D.host.K) ^ n) (by rw [atP₂, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div_le_one hpos]; exact h1) (by rw [atPbar_eq, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div …`. Take `⟨a, b, h⟩` from `Nat.isCoprime_iff_coprime.2 (hs.pow_right n)`.

Establish `h' : (a : D.host.K) * s + b * (p : D.host.K) ^ n = 1` using `by exact_mod_cast h`. Use `⟨a * z + b * u, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[RingOfIntegers.coe_eq_algebraMap]`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast] at hz ⊢`. Rewrite using `[← hz]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(u : D.host.K)) * h'`.
-/
theorem exists_eq_pow_mul (n : ℕ) (u : 𝓞 D.host.K) (h1 : ‖homP D lam (u : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ)))
    (h2 : ‖homPbar D lam (u : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    ∃ v : 𝓞 D.host.K, (u : D.host.K) = (p : D.host.K) ^ n * (v : D.host.K) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hp.pos) _
  obtain ⟨s, hs, z, hz⟩ := GlobalTheory.IntegralAtBothPrimes.exists_coprime_mul_integral D p lam ((u : D.host.K) / (p : D.host.K) ^ n)
    (by rw [atP₂, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div_le_one hpos]; exact h1)
    (by rw [atPbar_eq, map_div₀, map_pow, map_natCast, norm_div, norm_p_pow, div_le_one hpos]; exact h2)
  obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.2 (hs.pow_right n)
  have h' : (a : D.host.K) * s + b * (p : D.host.K) ^ n = 1 := by exact_mod_cast h
  refine ⟨a * z + b * u, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap] at hz
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast] at hz ⊢
  rw [← hz]
  field_simp
  linear_combination (-(u : D.host.K)) * h'

/- English proof (translation)
Rewrite using `[← CU.star_conj]`. Conclude with `host_star_emb D _ x`.
-/
theorem phi_conj (x : D.host.E) : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
  rw [← CU.star_conj]
  exact host_star_emb D _ x

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

/- English proof (translation)
Use `IO.HfInt_closure _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨κ, hκ, x, hx, rfl⟩ _ ⟨κ', hκ', x', hx', rfl⟩`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Express the relevant statement in the definitionally equal form `‖atPbar D lam _‖ ≤ _ at hκ hκ'`. Rewrite `hκ`, `hκ'` using `[atPbar_eq]`.

Take `⟨v, hv⟩` from `exists_eq_pow_mul lam (2 * n) (κ * conjO D κ') (by`. Use `push_cast`. Rewrite using `[map_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (norm_int_le D _ κ)).trans hκ')`. Use the proof step `(by`.

Use `push_cast`. Rewrite using `[map_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ)`. Establish `hv' : D.host.φ₀ ((κ : D.host.K) : D.host.E) * starRingEnd ℂ (D.host.φ₀ ((κ' : D.host.K) : D.host.E)) = (p : ℂ) ^ (2 * n) * D.host.φ₀ ((v : D.host.K) : D.host.E)`. Use `congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) hv` as an intermediate fact.

Move the coercions through the operations in `at this`. Simplify using `only [map_mul, map_pow, map_natCast] at this`. Rewrite using `[← this, ← phi_conj]`. Both sides reduce to the same expression. Use `hI _ (int_smul_mem_La D cc δ L L' v (nsmul_mem hx N₀)) _ (nsmul_mem hx' N₀)` as an intermediate fact.

Rewrite `this` using `[← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, IO.Hf_smul]`. Rewrite using `[IO.Hf_smul]`. Express the relevant statement in the definitionally equal form `IO.Good D _ at this`. Use `this using 2` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_div₀, map_pow, map_natCast]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(N₀ : ℂ) ^ 2 * hv'`.
-/
theorem hfInt_goodLifts (hI : IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L')) (N₀ n : ℕ) :
    IO.HfInt (tor0 D cc δ) (goodLifts D (tor0 D cc δ) lam N₀ n L L') := by
  refine IO.HfInt_closure _ _ ?_
  rintro _ ⟨κ, hκ, x, hx, rfl⟩ _ ⟨κ', hκ', x', hx', rfl⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  change ‖atPbar D lam _‖ ≤ _ at hκ hκ'
  rw [atPbar_eq] at hκ hκ'
  obtain ⟨v, hv⟩ := exists_eq_pow_mul lam (2 * n) (κ * conjO D κ')
    (by
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le D _ κ)).trans hκ')
    (by
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ)
  have hv' : D.host.φ₀ ((κ : D.host.K) : D.host.E) * starRingEnd ℂ (D.host.φ₀ ((κ' : D.host.K) : D.host.E)) =
      (p : ℂ) ^ (2 * n) * D.host.φ₀ ((v : D.host.K) : D.host.E) := by
    have := congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) hv
    push_cast at this
    simp only [map_mul, map_pow, map_natCast] at this
    rw [← this, ← phi_conj]
    rfl
  have := hI _ (int_smul_mem_La D cc δ L L' v (nsmul_mem hx N₀)) _ (nsmul_mem hx' N₀)
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, IO.Hf_smul] at this
  rw [IO.Hf_smul]
  change IO.Good D _ at this
  convert this using 2
  simp only [map_mul, map_div₀, map_pow, map_natCast]
  field_simp
  linear_combination (N₀ : ℂ) ^ 2 * hv'

abbrev mulSub (n₀ : ℕ) (Λ : AddSubgroup (VC D N N')) : AddSubgroup (VC D N N') := Λ.map (nsmulAddMonoidHom n₀)

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `nsmul_mem hx n₀`.
-/
theorem mulSub_le (n₀ : ℕ) (Λ : AddSubgroup (VC D N N')) : mulSub n₀ Λ ≤ Λ := by
  rintro _ ⟨x, hx, rfl⟩
  exact nsmul_mem hx n₀

/- English proof (translation)
Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨κ, -, x, hx, rfl⟩` from `hz`. Use `⟨_, int_smul_mem_La D cc δ L L' κ hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem pow_smul_goodLifts {N₀ n : ℕ} {y : VC D N N'} (hy : y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L') :
    p ^ n • y ∈ mulSub N₀ (La D (tor0 D cc δ) L L') := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨κ, -, x, hx, rfl⟩ := hz
    refine ⟨_, int_smul_mem_La D cc δ L L' κ hx, ?_⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Use `⟨IO.U_diff T t hG.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ z`. Rewrite using `[nsmulAddMonoidHom_apply]`. Take `⟨a, b, -, h⟩` from `hI x hx _ ht`. Establish `h1 : (Hf D T (n₀ • x) t).im = b` using `by rw [GlobalTheory.CommutatorCharacter.Hf_nsmul_swap, h]; simp`.

Establish `h2 : (Hf D T t (n₀ • x)).im = ((-b : ℤ) : ℝ)` using `by rw [IO.Hf_herm, Complex.conj_im, h1]; simp`. Establish `h3 : U D T t G z = al D T (n₀ • x) * IO.cf T t (n₀ • x) * U D T (t + n₀ • x) G z` using `by conv_lhs => rw [← IO.fix_eq T hG (nsmul_mem hx n₀)]`. Rewrite using `[IO.U_smul, IO.U_U]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, IO.U_U, IO.cf_int T _ _ _ h1, IO.cf_int T _ _ _ h2, add_comm t, IO.neg_one_zpow_congr (n := -b) (m := - -b) ⟨-b, by ring⟩]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_mem_ThSp (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : IO.HfInt T Λ) {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T Λ)
    {n₀ : ℕ} {t : VC D N N'} (ht : n₀ • t ∈ Λ) : U D T t G ∈ ThSp D T (mulSub n₀ Λ) := by
  refine ⟨IO.U_diff T t hG.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ z
  rw [nsmulAddMonoidHom_apply]
  obtain ⟨a, b, -, h⟩ := hI x hx _ ht
  have h1 : (Hf D T (n₀ • x) t).im = b := by rw [GlobalTheory.CommutatorCharacter.Hf_nsmul_swap, h]; simp
  have h2 : (Hf D T t (n₀ • x)).im = ((-b : ℤ) : ℝ) := by rw [IO.Hf_herm, Complex.conj_im, h1]; simp
  have h3 : U D T t G z = al D T (n₀ • x) * IO.cf T t (n₀ • x) * U D T (t + n₀ • x) G z := by
    conv_lhs => rw [← IO.fix_eq T hG (nsmul_mem hx n₀)]
    rw [IO.U_smul, IO.U_U]; ring
  rw [h3, IO.U_U, IO.cf_int T _ _ _ h1, IO.cf_int T _ _ _ h2, add_comm t,
    IO.neg_one_zpow_congr (n := -b) (m := - -b) ⟨-b, by ring⟩]
  ring

/- English proof (translation)
Establish `hx'` using `IO.La_le_gen cc δ L L' hx`. Use `clear hx`. Proceed by induction on `hx' using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨c₀, -, A, hA, rfl⟩` from `hz`.

Take `⟨s, hs, c, hc⟩` from `hb.2.2 A hA`. Use `⟨s, hs, fun i => c₀ * c i, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (GlobalTheory.CommutatorCharacter.vecHom cc δ) hc`. Rewrite `h1` using `[map_sum, Nat.cast_smul_eq_nsmul, map_nsmul]`. Simplify using `only [GlobalTheory.CommutatorCharacter.vecHom_apply, vecOf_smul] at h1`.

Establish `h2 : (δ * D.host.φ₀ ((c₀ : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) A = D.host.φ₀ ((c₀ : D.host.K) : D.host.E) • vecOf D cc δ A` using `by rw [vecOf, smul_smul, mul_comm]`. Rewrite using `[h2, smul_comm, Nat.cast_smul_eq_nsmul, h1, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← map_mul]`. Both sides reduce to the same expression.

Consider the case `zero => exact ⟨1, by simp, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, c, hc⟩` from `hx`. Take `⟨s', hs', c', hc'⟩` from `hy`. Use `⟨s * s', Nat.Coprime.mul_left hs hs', fun i => s' * c i + s * c' i, ?_⟩` and prove the remaining obligations.

Establish `: ((s * s' : ℕ) : ℂ) • (x + y) = (s' : ℂ) • (s : ℂ) • x + (s : ℂ) • (s' : ℂ) • y` using `by push_cast; module`. Rewrite using `[this, hc, hc', Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, ← add_smul]`. Simplify using the standard rewrite rules.

Consider the case `neg x _ hx`. Take `⟨s, hs, c, hc⟩` from `hx`. Use `⟨s, hs, fun i => - c i, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg, hc, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem exists_coords {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : LocBasis D p (YYl D L L') b)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 D.host.K,
      (s : ℂ) • x = ∑ i, D.host.φ₀ ((c i : D.host.K) : D.host.E) • vecOf D cc δ (b i) := by
  have hx' := IO.La_le_gen cc δ L L' hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c₀, -, A, hA, rfl⟩ := hz
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, fun i => c₀ * c i, ?_⟩
    have h1 := congrArg (GlobalTheory.CommutatorCharacter.vecHom cc δ) hc
    rw [map_sum, Nat.cast_smul_eq_nsmul, map_nsmul] at h1
    simp only [GlobalTheory.CommutatorCharacter.vecHom_apply, vecOf_smul] at h1
    have h2 : (δ * D.host.φ₀ ((c₀ : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) A =
        D.host.φ₀ ((c₀ : D.host.K) : D.host.E) • vecOf D cc δ A := by rw [vecOf, smul_smul, mul_comm]
    rw [h2, smul_comm, Nat.cast_smul_eq_nsmul, h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← map_mul]
    rfl
  | zero => exact ⟨1, by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, c, hc⟩ := hx
    obtain ⟨s', hs', c', hc'⟩ := hy
    refine ⟨s * s', Nat.Coprime.mul_left hs hs', fun i => s' * c i + s * c' i, ?_⟩
    have : ((s * s' : ℕ) : ℂ) • (x + y) = (s' : ℂ) • (s : ℂ) • x + (s : ℂ) • (s' : ℂ) • y := by
      push_cast; module
    rw [this, hc, hc', Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
    simp
  | neg x _ hx =>
    obtain ⟨s, hs, c, hc⟩ := hx
    refine ⟨s, hs, fun i => - c i, ?_⟩
    rw [smul_neg, hc, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

def liftZ (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') : (Fin r → ℤ) →+ VC D N N' :=
  AddMonoidHom.mk' (fun z => (D.host.φ₀ ((ε : D.host.K) : D.host.E) / (p : ℂ) ^ n) • ∑ i, z i • v i) fun z z' => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftZ_apply (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') (z : Fin r → ℤ) :
    liftZ p n ε v z = (D.host.φ₀ ((ε : D.host.K) : D.host.E) / (p : ℂ) ^ n) • ∑ i, z i • v i := rfl

/- English proof (translation)
Establish `h` using `vecOf_smul D cc δ ((ε : D.host.K) / (p : D.host.K) ^ n) (∑ i, (((y i : ℕ) : D.host.E)) • b i)`. Move the coercions through the operations in `at h`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[liftZ_apply, ← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum, map_div₀, map_pow, map_natCast]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]`. Both sides reduce to the same expression.
-/
theorem liftY_eq (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin (p ^ n)) :
    liftY D (tor0 D cc δ) δ p n ε b y = liftZ p n ε (fun i => vecOf D cc δ (b i)) fun i => ((y i : ℕ) : ℤ) := by
  have h := vecOf_smul D cc δ ((ε : D.host.K) / (p : D.host.K) ^ n) (∑ i, (((y i : ℕ) : D.host.E)) • b i)
  push_cast at h
  refine h.trans ?_
  rw [liftZ_apply, ← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum, map_div₀, map_pow, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]
  rfl

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Take `⟨h1, h2⟩` from `(isIdem_iff D lam n ε).1 (I3.JetMomEq.isIdem_mono lam ε hε hm)`. Take `⟨s, hs, c, hc⟩` from `exists_coords hb.1 hx`. Establish `hMs : ‖((M * s : ℕ) : ℂ_[p])‖ = 1` using `norm_coprime (Nat.Coprime.mul_left hM hs)`.

Establish `hMs0 : ((M * s : ℕ) : ℂ_[p]) ≠ 0` using `fun h => by simp [h] at hMs`. Establish `key : ∀ i, ∃ (k : ℕ) (v : 𝓞 D.host.K), (κ : D.host.K) * (c i : D.host.K) - (ε : D.host.K) * k * ((M * s : ℕ) : D.host.K) = (p : D.host.K) ^ n * (v : D.host.K)`. Introduce `i`. Establish `hκc : ‖homP D lam (κ : D.host.K) * homP D lam (c i : D.host.K)‖ ≤ 1`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ (norm_int_le D _ _) (norm_nonneg _) (norm_int_le D _ _)`. Take `⟨k, -, hk⟩` from `(GlobalTheory.PlaceApprox.approx D p lam hE ((κ : D.host.K) * (c i : D.host.K) / ((M * s : ℕ) : D.host.K))).1 (by rw [atP₂, map_div₀, map_natCast, norm_div, hMs, div_one, map_mul]; exact hκc) n`. Rewrite `hk` using `[atP₂, map_div₀, map_natCast, map_mul]`. Establish `hk1 : ‖(k : ℂ_[p])‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ _`. Take `⟨v, hv⟩` from `exists_eq_pow_mul lam n (κ * c i - ε * (k : 𝓞 D.host.K) * ((M * s : ℕ) : 𝓞 D.host.K)) (by`.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hk h1 ⊢`. Use `set a := homP D lam (algebraMap _ _ κ) * homP D lam (algebraMap _ _ (c i))`. Use `set e := homP D lam (algebraMap _ _ ε)`. Establish `: a - e * k * ((M * s : ℕ) : ℂ_[p]) = ((M * s : ℕ) : ℂ_[p]) * (a / ((M * s : ℕ) : ℂ_[p]) - k) + -((e - 1) * k * ((M * s : ℕ) : ℂ_[p]))`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hMs, one_mul]`. Conclude with `hk`.

Rewrite using `[norm_neg, norm_mul, hMs, mul_one, norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) hk1).trans h1)`. Use the proof step `(by`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hκ h2 ⊢`. Rewrite using `[sub_eq_add_neg]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ`. Rewrite using `[norm_neg, norm_mul, hMs, mul_one, norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) hk1).trans h2)`.

Use `⟨k, v, ?_⟩` and prove the remaining obligations. Simplify `hv` using `only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast]`. Use `choose k v hv using key`. Establish `hv' : ∀ i, D.host.φ₀ ((κ : D.host.K) : D.host.E) * D.host.φ₀ ((c i : D.host.K) : D.host.E) - D.host.φ₀ ((ε : D.host.K) : D.host.E) * k i * (M * s) = (p : ℂ) ^ n * D.host.φ₀ ((v i : D.host.K) : D.host.E)`. Introduce `i`.

Use `congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) (hv i)` as an intermediate fact. Move the coercions through the operations in `at this`. Simplify `this` using `only [map_sub, map_mul, map_pow, map_natCast]`. Use `⟨fun i => k i, mem_of_coprime _ (hs.pow_right n) ?_ ?_⟩` and prove the remaining obligations. Establish `: s • ((D.host.φ₀ ((κ : D.host.K) : D.host.E) / (p : ℂ) ^ n) • x - liftZ p n ε (fun i => M • vecOf D cc δ (b i)) fun i => (k i : ℤ)) = ∑ i, D.host.φ₀ ((v i : D.host.K) : D.host.E) • vecOf D cc δ (b i)`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_comm, hc, liftZ_apply, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Simplify using `only [smul_smul, ← sub_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hv' i`. Rewrite using `[this]`. Conclude with `sum_mem fun i _ => int_smul_mem_La D cc δ L L' _ (hb.2 i)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_sub, liftZ_apply, smul_smul, smul_smul, Nat.cast_pow, mul_div_cancel₀ _ (pow_ne_zero n hp0), mul_div_cancel₀ _ (pow_ne_zero n hp0)]`.

Conclude with `sub_mem (int_smul_mem_La D cc δ L L' _ hx) (int_smul_mem_La D cc δ L L' _ (sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _))`.
-/
theorem exists_congr (hE : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : NNBasis D (tor0 D cc δ) δ p L L' b) {M n m : ℕ} (hM : Nat.Coprime M p)
    (hm : n ≤ m) {ε : 𝓞 D.host.K} (hε : IsIdem D lam m ε) (κ : 𝓞 D.host.K)
    (hκ : ‖homPbar D lam (κ : D.host.K)‖ ≤ (p : ℝ) ^ (-(n : ℤ))) {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z : Fin r → ℤ, (D.host.φ₀ ((κ : D.host.K) : D.host.E) / (p : ℂ) ^ n) • x -
      liftZ p n ε (fun i => M • vecOf D cc δ (b i)) z ∈ La D (tor0 D cc δ) L L' := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨h1, h2⟩ := (isIdem_iff D lam n ε).1 (I3.JetMomEq.isIdem_mono lam ε hε hm)
  obtain ⟨s, hs, c, hc⟩ := exists_coords hb.1 hx
  have hMs : ‖((M * s : ℕ) : ℂ_[p])‖ = 1 := norm_coprime (Nat.Coprime.mul_left hM hs)
  have hMs0 : ((M * s : ℕ) : ℂ_[p]) ≠ 0 := fun h => by simp [h] at hMs
  have key : ∀ i, ∃ (k : ℕ) (v : 𝓞 D.host.K), (κ : D.host.K) * (c i : D.host.K) - (ε : D.host.K) * k * ((M * s : ℕ) : D.host.K) =
      (p : D.host.K) ^ n * (v : D.host.K) := by
    intro i
    have hκc : ‖homP D lam (κ : D.host.K) * homP D lam (c i : D.host.K)‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ (norm_int_le D _ _) (norm_nonneg _) (norm_int_le D _ _)
    obtain ⟨k, -, hk⟩ := (GlobalTheory.PlaceApprox.approx D p lam hE ((κ : D.host.K) * (c i : D.host.K) / ((M * s : ℕ) : D.host.K))).1
      (by rw [atP₂, map_div₀, map_natCast, norm_div, hMs, div_one, map_mul]; exact hκc) n
    rw [atP₂, map_div₀, map_natCast, map_mul] at hk
    have hk1 : ‖(k : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    obtain ⟨v, hv⟩ := exists_eq_pow_mul lam n (κ * c i - ε * (k : 𝓞 D.host.K) * ((M * s : ℕ) : 𝓞 D.host.K))
      (by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hk h1 ⊢
        set a := homP D lam (algebraMap _ _ κ) * homP D lam (algebraMap _ _ (c i))
        set e := homP D lam (algebraMap _ _ ε)
        have : a - e * k * ((M * s : ℕ) : ℂ_[p]) =
            ((M * s : ℕ) : ℂ_[p]) * (a / ((M * s : ℕ) : ℂ_[p]) - k) + -((e - 1) * k * ((M * s : ℕ) : ℂ_[p])) := by
          field_simp
          ring
        rw [this]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_mul, hMs, one_mul]; exact hk
        · rw [norm_neg, norm_mul, hMs, mul_one, norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) hk1).trans h1)
      (by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] at hκ h2 ⊢
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le D _ _)).trans hκ
        · rw [norm_neg, norm_mul, hMs, mul_one, norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) hk1).trans h2)
    refine ⟨k, v, ?_⟩
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul, map_natCast] using hv
  choose k v hv using key
  have hv' : ∀ i, D.host.φ₀ ((κ : D.host.K) : D.host.E) * D.host.φ₀ ((c i : D.host.K) : D.host.E) -
      D.host.φ₀ ((ε : D.host.K) : D.host.E) * k i * (M * s) = (p : ℂ) ^ n * D.host.φ₀ ((v i : D.host.K) : D.host.E) := by
    intro i
    have := congrArg (fun c : D.host.K => D.host.φ₀ (c : D.host.E)) (hv i)
    push_cast at this
    simpa only [map_sub, map_mul, map_pow, map_natCast] using this
  refine ⟨fun i => k i, mem_of_coprime _ (hs.pow_right n) ?_ ?_⟩
  · have : s • ((D.host.φ₀ ((κ : D.host.K) : D.host.E) / (p : ℂ) ^ n) • x -
        liftZ p n ε (fun i => M • vecOf D cc δ (b i)) fun i => (k i : ℤ)) =
        ∑ i, D.host.φ₀ ((v i : D.host.K) : D.host.E) • vecOf D cc δ (b i) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_comm, hc, liftZ_apply, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
      simp only [smul_smul, ← sub_smul]
      congr 1
      field_simp
      linear_combination hv' i
    rw [this]
    exact sum_mem fun i _ => int_smul_mem_La D cc δ L L' _ (hb.2 i)
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub, liftZ_apply, smul_smul, smul_smul, Nat.cast_pow,
      mul_div_cancel₀ _ (pow_ne_zero n hp0), mul_div_cancel₀ _ (pow_ne_zero n hp0)]
    exact sub_mem (int_smul_mem_La D cc δ L L' _ hx)
      (int_smul_mem_La D cc δ L L' _ (sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _))

/- English proof (translation)
Rewrite using `[liftZ_apply, liftZ_apply, smul_comm n₀, Finset.smul_sum (r := n₀)]`. Simplify using `only [smul_comm n₀]`.
-/
theorem liftZ_nsmul (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') (z : Fin r → ℤ) (n₀ : ℕ) :
    liftZ p n ε (fun i => n₀ • v i) z = n₀ • liftZ p n ε v z := by
  rw [liftZ_apply, liftZ_apply, smul_comm n₀, Finset.smul_sum (r := n₀)]
  simp only [smul_comm n₀]

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.one_lt.le`. Use `set w : Fin r → VC D N N' := fun i => M • vecOf D cc δ (b i) with hw`. Establish `hwm : ∀ z : Fin r → ℤ, ∑ i, z i • w i ∈ La D (tor0 D cc δ) L L'` using `fun z => sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _`.

Establish `hv : (fun i => vecOf D cc δ (((n₀ * M : ℕ) : D.host.E) • b i)) = fun i => n₀ • w i`. Use function extensionality and compare the values at `i`. Rewrite using `[← GlobalTheory.CommutatorCharacter.vecHom_apply, Nat.cast_smul_eq_nsmul, map_nsmul, mul_smul]`. Both sides reduce to the same expression. Establish `h1 : ∃ z : Fin r → ℤ, y - n₀ • liftZ p n ε w z ∈ mulSub n₀ (La D (tor0 D cc δ) L L')`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨κ, hκ, x, hx, rfl⟩` from `hy`. Express the relevant statement in the definitionally equal form `‖atPbar D lam _‖ ≤ _ at hκ`. Rewrite `hκ` using `[atPbar_eq]`.

Take `⟨z, hz⟩` from `exists_congr lam hE hb hM (by omega : n ≤ 2 * n + 2) hε κ (hκ.trans (zpow_le_zpow_right₀ hp1 (by omega))) hx`. Use `⟨z, _, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[nsmulAddMonoidHom_apply, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ n₀ (_ • x), smul_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨z, hz⟩` from `hx`. Take `⟨z', hz'⟩` from `hy`. Conclude with `⟨z + z', by rw [map_add, smul_add, add_sub_add_comm]; exact add_mem hz hz'⟩`.

Consider the case `neg x _ hx`. Take `⟨z, hz⟩` from `hx`. Conclude with `⟨-z, by rw [map_neg, smul_neg, neg_sub_neg, ← neg_sub]; exact neg_mem hz⟩`. Establish `hg : ∀ z : Fin r → ℤ, n₀ • liftZ p n ε w z ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L'`. Introduce `z`.

Use `AddSubgroup.subset_closure ⟨ε, hε.2.trans (zpow_le_zpow_right₀ hp1 (by omega)), _, hwm z, ?_⟩` and prove the remaining obligations. Rewrite using `[liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ n₀, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz⟩` from `h1`.

Establish `hq : (0 : ℤ) < ((p ^ n : ℕ) : ℤ)` using `by exact_mod_cast pow_pos hp.pos n`. Use `⟨fun i => ⟨(z i % ((p ^ n : ℕ) : ℤ)).toNat, by` and prove the remaining obligations. Use `Int.emod_lt_of_pos (z i) hq` as an intermediate fact. Use `Int.emod_nonneg (z i) hq.ne'` as an intermediate fact. Use the proof step `omega⟩, ?_, ?_⟩`.

Rewrite using `[liftY_eq, hv, liftZ_nsmul]`. Conclude with `hg _`. Rewrite using `[liftY_eq, hv, liftZ_nsmul]`. Establish `hd : z = (fun i => (((z i % ((p ^ n : ℕ) : ℤ)).toNat : ℕ) : ℤ)) + p ^ n • fun i => z i / ((p ^ n : ℕ) : ℤ)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.add_apply, Pi.smul_apply, Int.toNat_of_nonneg (Int.emod_nonneg (z i) hq.ne'), nsmul_eq_mul, Int.emod_add_mul_ediv]`. Establish `hl : p ^ n • liftZ p n ε w (fun i => z i / ((p ^ n : ℕ) : ℤ)) ∈ La D (tor0 D cc δ) L L'`. Rewrite using `[liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_pow, mul_div_cancel₀ _ (pow_ne_zero n hp0)]`. Conclude with `int_smul_mem_La D cc δ L L' _ (hwm _)`. Rewrite `hz` using `[hd, map_add, map_nsmul, smul_add, ← sub_sub]`.

Simplify using `using add_mem hz (AddSubgroup.mem_map_of_mem (nsmulAddMonoidHom n₀) hl)`.
-/
theorem exists_liftY (hE : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : NNBasis D (tor0 D cc δ) δ p L L' b) {M n n₀ : ℕ} (hM : Nat.Coprime M p)
    {ε : 𝓞 D.host.K} (hε : IsIdem D lam (2 * n + 2) ε) {y : VC D N N'} (hy : y ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L') :
    ∃ yt : Fin r → Fin (p ^ n),
      liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * M : ℕ) : D.host.E) • b i) yt ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' ∧
      y - liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * M : ℕ) : D.host.E) • b i) yt ∈ mulSub n₀ (La D (tor0 D cc δ) L L') := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  set w : Fin r → VC D N N' := fun i => M • vecOf D cc δ (b i) with hw
  have hwm : ∀ z : Fin r → ℤ, ∑ i, z i • w i ∈ La D (tor0 D cc δ) L L' := fun z =>
    sum_mem fun i _ => zsmul_mem (nsmul_mem (hb.2 i) M) _
  have hv : (fun i => vecOf D cc δ (((n₀ * M : ℕ) : D.host.E) • b i)) = fun i => n₀ • w i := by
    funext i
    rw [← GlobalTheory.CommutatorCharacter.vecHom_apply, Nat.cast_smul_eq_nsmul, map_nsmul, mul_smul]
    rfl
  have h1 : ∃ z : Fin r → ℤ, y - n₀ • liftZ p n ε w z ∈ mulSub n₀ (La D (tor0 D cc δ) L L') := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
      change ‖atPbar D lam _‖ ≤ _ at hκ
      rw [atPbar_eq] at hκ
      obtain ⟨z, hz⟩ := exists_congr lam hE hb hM (by omega : n ≤ 2 * n + 2) hε κ
        (hκ.trans (zpow_le_zpow_right₀ hp1 (by omega))) hx
      refine ⟨z, _, hz, ?_⟩
      rw [nsmulAddMonoidHom_apply, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ n₀ (_ • x), smul_smul]
      congr 2
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz⟩ := hx
      obtain ⟨z', hz'⟩ := hy
      exact ⟨z + z', by rw [map_add, smul_add, add_sub_add_comm]; exact add_mem hz hz'⟩
    | neg x _ hx =>
      obtain ⟨z, hz⟩ := hx
      exact ⟨-z, by rw [map_neg, smul_neg, neg_sub_neg, ← neg_sub]; exact neg_mem hz⟩
  have hg : ∀ z : Fin r → ℤ, n₀ • liftZ p n ε w z ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' := by
    intro z
    refine AddSubgroup.subset_closure ⟨ε, hε.2.trans (zpow_le_zpow_right₀ hp1 (by omega)), _, hwm z, ?_⟩
    rw [liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ n₀, smul_smul]
    congr 1
    ring
  obtain ⟨z, hz⟩ := h1
  have hq : (0 : ℤ) < ((p ^ n : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.pos n
  refine ⟨fun i => ⟨(z i % ((p ^ n : ℕ) : ℤ)).toNat, by
    have := Int.emod_lt_of_pos (z i) hq
    have := Int.emod_nonneg (z i) hq.ne'
    omega⟩, ?_, ?_⟩
  · rw [liftY_eq, hv, liftZ_nsmul]
    exact hg _
  · rw [liftY_eq, hv, liftZ_nsmul]
    have hd : z = (fun i => (((z i % ((p ^ n : ℕ) : ℤ)).toNat : ℕ) : ℤ)) + p ^ n • fun i => z i / ((p ^ n : ℕ) : ℤ) := by
      funext i
      rw [Pi.add_apply, Pi.smul_apply, Int.toNat_of_nonneg (Int.emod_nonneg (z i) hq.ne'), nsmul_eq_mul, Int.emod_add_mul_ediv]
    have hl : p ^ n • liftZ p n ε w (fun i => z i / ((p ^ n : ℕ) : ℤ)) ∈ La D (tor0 D cc δ) L L' := by
      rw [liftZ_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_pow, mul_div_cancel₀ _ (pow_ne_zero n hp0)]
      exact int_smul_mem_La D cc δ L L' _ (hwm _)
    rw [hd, map_add, map_nsmul, smul_add, ← sub_sub] at hz
    simpa using add_mem hz (AddSubgroup.mem_map_of_mem (nsmulAddMonoidHom n₀) hl)

/- English proof (translation)
Set `_` to `D.host.cmStar`. Take `⟨k, hk, z, hz, hspan⟩` from `CU.pow_unitary D ha`. Establish `hzu : z ∈ unitary D.host.E`. Rewrite using `[Unitary.mem_iff, CU.star_conj]`. Conclude with `⟨by rw [mul_comm]; exact hz, hz⟩`.

Establish `h` using `hχ.2 ⟨z, hzu⟩`. Simplify using `only at h`. Rewrite `h` using `[← hspan, CU.chi_pow D χ hχ ha k hk]`. Use `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `prod_mem fun τ _ => inv_mem (emb_mem D _ _)`.
-/
theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

/- English proof (translation)
The claim follows from `mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _) (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)`.
-/
theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

/- English proof (translation)
Establish `h0` using `GlobalTheory.NormalisedTranslate.delta_ne_zero B`. Establish `h1 : B.thMoved N N' L L' ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L')` using `IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA)) (IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L _ ⟨hA.1, hA.2.1, hA.2.2.1, GlobalTheory.FourthRootStd.stdL_isSD D N'⟩)) (Gl …`. Use `⟨h1.1.const_mul _, fun x hx z => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * U D _ x (fun w => _ * B.thMoved N N' L L' w) z = _ * B.thMoved N N' L L' z`. Rewrite using `[IO.U_smul, mul_left_comm, h1.2 x hx z]`.
-/
theorem eNat_mem (B : Base D cc δ) (χ : IdE D → ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : admitted D N N' L L') :
    B.eNat χ N N' L L' ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := by
  have h0 := GlobalTheory.NormalisedTranslate.delta_ne_zero B
  have h1 : B.thMoved N N' L L' ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
    IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA))
      (IO.Iop_mem_ThSp _ (IO.semiChar_of_HfInt _ (hermitian_form_integral_values D cc hcc δ hδ h0 N N' L _
        ⟨hA.1, hA.2.1, hA.2.2.1, GlobalTheory.FourthRootStd.stdL_isSD D N'⟩))
        (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK B hcc hδ) N N'))
  refine ⟨h1.1.const_mul _, fun x hx z => ?_⟩
  change _ * U D _ x (fun w => _ * B.thMoved N N' L L' w) z = _ * B.thMoved N N' L L' z
  rw [IO.U_smul, mul_left_comm, h1.2 x hx z]

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hC : StandardLatticesGL3.Crv D cc δ` using `⟨hcc, hδ⟩`. Establish `hs` using `GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2`. Establish `hT` using `(GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2).transl hC (GlobalTheory.ThetaAlgebraic.sat_of_nsmul h0 (hs ht))`. Establish `e : Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (B.eNat χ N N' L L')) = fun z => (wPh D (tor0 D cc δ) p y * Base.chiFac χ N N' L L') * U D (tor0 D cc δ) y (U D (tor0 D cc δ) t (B.thMoved N N' L L')) z`.

Use function extensionality and compare the values at `z`. Simplify using `only [Wop, U, Base.eNat]`. Expand and normalize the polynomial expressions, which then agree. Introduce `α`. Rewrite using `[e, GlobalTheory.ThetaConj.taylor_mul D _ (IO.U_diff _ _ hT.1)]`.

Conclude with `mul_mem (mul_mem (GlobalTheory.NormalisedTranslate.wPh_mem _ (hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA) hp hy) (chiFac_mem hχ hA)) (hT.2 y (GlobalTheory.ThetaAlgebraic.sat_of_nsmul (pow_pos hp.pos n) (hs hy)) α)`.
-/
theorem coefIn_Wop (B : Base D cc δ) {χ : IdE D → ℂ} (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ)
    (hA : admitted D N N' L L') {t y : VC D N N'} {n₀ n : ℕ} (h0 : 0 < n₀) (ht : n₀ • t ∈ La D (tor0 D cc δ) L L')
    (hy : p ^ n • y ∈ La D (tor0 D cc δ) L L') :
    CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (B.eNat χ N N' L L'))) Qbar := by
  have hp := (Fact.out : p.Prime)
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hs := GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2
  have hT := (GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2).transl hC
    (GlobalTheory.ThetaAlgebraic.sat_of_nsmul h0 (hs ht))
  have e : Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (B.eNat χ N N' L L')) =
      fun z => (wPh D (tor0 D cc δ) p y * Base.chiFac χ N N' L L') *
        U D (tor0 D cc δ) y (U D (tor0 D cc δ) t (B.thMoved N N' L L')) z := by
    funext z
    simp only [Wop, U, Base.eNat]
    ring
  intro α
  rw [e, GlobalTheory.ThetaConj.taylor_mul D _ (IO.U_diff _ _ hT.1)]
  exact mul_mem (mul_mem (GlobalTheory.NormalisedTranslate.wPh_mem _
    (hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA) hp hy) (chiFac_mem hχ hA))
    (hT.2 y (GlobalTheory.ThetaAlgebraic.sat_of_nsmul (pow_pos hp.pos n) (hs hy)) α)

def scale (p : ℕ) [Fact p.Prime] (r M : ℕ) : C(Fin r → ℤ_[p], Fin r → ℤ_[p]) := ⟨fun a i => (M : ℤ_[p]) * a i, by fun_prop⟩

/- English proof (translation)
Set `l : C(Y, ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p]` to `{ toFun := fun g => μ (g.comp f) map_add' := fun g g' => by rw [ContinuousMap.add_comp, map_add] map_smul' := fun c g => by rw [ContinuousMap.smul_comp, map_smul]; rfl }`. Establish `hl : ∀ g, ‖l g‖ ≤ 1 * ‖g‖` using `fun g => (μ.le_opNorm _).trans (mul_le_mul hμ ((ContinuousMap.norm_le _ (norm_nonneg g)).2 fun x => g.norm_coe_le_norm _) (norm_nonneg _) zero_le_one)`. Conclude with `⟨l.mkContinuous 1 hl, LinearMap.mkContinuous_norm_le _ zero_le_one _, fun g => rfl⟩`.
-/
theorem exists_image {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] (f : C(X, Y))
    (μ : C(X, ℂ_[p]) →L[ℂ_[p]] ℂ_[p]) (hμ : ‖μ‖ ≤ 1) :
    ∃ ν : C(Y, ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖ν‖ ≤ 1 ∧ ∀ g, ν g = μ (g.comp f) := by
  let l : C(Y, ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] :=
    { toFun := fun g => μ (g.comp f)
      map_add' := fun g g' => by rw [ContinuousMap.add_comp, map_add]
      map_smul' := fun c g => by rw [ContinuousMap.smul_comp, map_smul]; rfl }
  have hl : ∀ g, ‖l g‖ ≤ 1 * ‖g‖ := fun g => (μ.le_opNorm _).trans
    (mul_le_mul hμ ((ContinuousMap.norm_le _ (norm_nonneg g)).2 fun x => g.norm_coe_le_norm _) (norm_nonneg _) zero_le_one)
  exact ⟨l.mkContinuous 1 hl, LinearMap.mkContinuous_norm_le _ zero_le_one _, fun g => rfl⟩

/- English proof (translation)
Unfold `pairN`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h : hYY D y ((M : D.host.E) • b i) = M • hYY D y (b i)`. Unfold `hYY`.

Rewrite using `[← map_nsmul]`. Use `congr 1`. Simplify using `only [Finset.smul_sum, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[h, lamC_emb, lamC_emb]`.

Simplify using `only [zc, nsmul_eq_mul]`. Use `push_cast`. Simplify using `only [map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairN_smul (Ω : ℂ_[p]) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (M : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]) :
    pairN D lam Ω (fun i => (M : D.host.E) • b i) y a = pairN D lam Ω b y fun i => (M : ℤ_[p]) * a i := by
  unfold pairN
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : hYY D y ((M : D.host.E) • b i) = M • hYY D y (b i) := by
    unfold hYY
    rw [← map_nsmul]
    congr 1
    simp only [Finset.smul_sum, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h, lamC_emb, lamC_emb]
  simp only [zc, nsmul_eq_mul]
  push_cast
  simp only [map_mul, map_natCast]
  ring

/- English proof (translation)
Take `⟨a, b, -, h⟩` from `hI w hw l hl`. Establish `him : (Hf D T w l).im = b` using `by rw [h]; simp`. Unfold `kap`. Rewrite using `[IO.Hf_add_right, Complex.add_im, him, Complex.exp_eq_exp_iff_exists_int]`. Conclude with `⟨-b, by push_cast; ring⟩`.
-/
theorem kap_add_right (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : IO.HfInt T Λ) {w l : VC D N N'} (x : VC D N N')
    (hw : w ∈ Λ) (hl : l ∈ Λ) : kap D T w (x + l) = kap D T w x := by
  obtain ⟨a, b, -, h⟩ := hI w hw l hl
  have him : (Hf D T w l).im = b := by rw [h]; simp
  unfold kap
  rw [IO.Hf_add_right, Complex.add_im, him, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hE` using `GlobalTheory.ApproxIdem.exists_isIdem D p lam hs`. Introduce `N N' L L' hA t ht`. Establish `hI` using `hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA`. Take `⟨s, -, hsp, hh⟩` from `h N N' L L' hA 1 (fun _ => t) (fun _ => L) (fun _ => L') (fun _ => ht) (fun _ => ⟨hA, ⟨1, by simp, by simp, by simp⟩, ⟨1, by simp, by simp, by simp⟩⟩)`.

Take `⟨n₀, h0, hn₀, ht⟩` from `ht`. Use `⟨n₀, hn₀, fun r b hb => ?_⟩` and prove the remaining obligations. Take `⟨hb', hm⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.MomentCombSplitting.goodBasis_smul D cc δ L L' (Nat.Coprime.mul_left hn₀ hsp) b hb`. Take `⟨μ, hμ, -, h1, -⟩` from `hh (fun _ => 1) (fun _ => ⟨one_mem _, by rw [I3.JetMomEq.lamC_one]; simp⟩) r _ hb' fun i => by`. Take `⟨x, hx, e⟩` from `hm i`.

Conclude with `⟨n₀ • x, nsmul_mem hx _, e.trans (by rw [mul_comm, mul_smul])⟩`. Simplify using `only [one_mul, Finset.univ_unique, Finset.sum_singleton] at h1`. Take `⟨ν, hν, hνμ⟩` from `exists_image (scale p r (n₀ * s)) μ hμ`. Use `⟨ν, hν, fun n y hy => ⟨coefIn_Wop B hcc hδ hχ hA h0 ht (mulSub_le _ _ (pow_smul_goodLifts lam hy)), ?_⟩⟩` and prove the remaining obligations. Introduce `m y' g hg`.

Take `⟨ε, hε⟩` from `hE (2 * n + 2)`. Take `⟨yt, hx, hl⟩` from `exists_liftY lam hE hb hsp hε hy`. Use `set x := liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) yt with hxd`. Take `⟨l, rfl⟩ : ∃ l, y = x + l` from `⟨y - x, by abel⟩`. Establish `hlg : l ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L'` using `by simpa using sub_mem hy hx`.

Rewrite `hl` using `[add_sub_cancel_left]`. Rewrite using `[GlobalTheory.ThetaShift.Wop_add_lattice D _ N N' _ p hp (IO.HfInt_mono _ (mulSub_le n₀ _) hI) _ (U_mem_ThSp _ hI (eNat_mem B χ hcc hδ hA) ht) x l hl ⟨n, pow_smul_goodLifts lam hx⟩ (hfInt_goodLifts lam hI n₀ n x hx l hlg), hνμ]`. Use `h1 n ε hε yt m y' _ ?_` and prove the remaining obligations. Take `⟨ψ, hψ, hψ'⟩` from `GlobalTheory.CommutatorCharacter.exists_continuous_character D cc δ p lam N N' _ hI n r _ x hb'.2 (mulSub_le _ _ (pow_smul_goodLifts lam hx))`. Establish `hd : DenseRange fun (a : Fin r → ℕ) (i : Fin r) => (a i : ℤ_[p])` using `DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)`.

Establish `key : g.comp (scale p r (n₀ * s)) = ψ * ∏ j, pairC D lam Ω (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) (y' j)`. Use `ContinuousMap.coe_injective (hd.equalizer (by fun_prop) (by fun_prop) (funext fun a => ?_))` and prove the remaining obligations. Establish `e1` using `hg fun i => n₀ * s * a i`. Establish `e2` using `hψ' fun i => (a i : ℤ)`. Establish `e3 : ∑ i, ((n₀ * s * a i : ℕ) : D.host.E) • b i = ∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i` using `Finset.sum_congr rfl fun i _ => by rw [smul_smul, Nat.cast_mul _ (a i), mul_comm]`.

Establish `hw : vecOf D cc δ (∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i) ∈ La D (tor0 D cc δ) L L'`. Rewrite using `[← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum]`. Conclude with `sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul, map_nsmul]; exact nsmul_mem (hb'.2 i) _`. Rewrite `e1` using `[e3]`. Express the relevant statement in the definitionally equal form `_ = lamC lam (kap D _ (vecOf D cc δ _) _) * _ at e1`.

Rewrite `e1` using `[kap_add_right _ hI x hw (mulSub_le _ _ hl)]`. Simplify using `only [Int.cast_natCast] at e2`. Simplify using `only [Nat.cast_mul _ (a _)] at e1`. Simplify using `only [Function.comp_apply, ContinuousMap.mul_apply, ContinuousMap.prod_apply, ContinuousMap.comp_apply, e2]`. Use `e1.trans ?_` and prove the remaining obligations.

Use `congr 1`. Conclude with `Finset.prod_congr rfl fun j _ => (pairN_smul lam Ω b _ _ _).symm`. Introduce `a`. Rewrite using `[key, ContinuousMap.mul_apply, hψ, ContinuousMap.prod_apply]`. Both sides reduce to the same expression.
-/
theorem momentsAt_of_momComb (B : Base D cc δ) {χ : IdE D → ℂ} (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ)
    (hs : SplitK D p) {Ω : ℂ_[p]} (h : I3.JetMomEq.MomComb D cc δ B χ p lam Ω) : MomentsAt D cc δ (B.eNat χ) lam Ω := by
  have hp := (Fact.out : p.Prime)
  have hE := GlobalTheory.ApproxIdem.exists_isIdem D p lam hs
  intro N N' L L' hA t ht
  have hI := hermitian_form_integral_values D cc hcc δ hδ (GlobalTheory.NormalisedTranslate.delta_ne_zero B) N N' L L' hA
  obtain ⟨s, -, hsp, hh⟩ := h N N' L L' hA 1 (fun _ => t) (fun _ => L) (fun _ => L') (fun _ => ht)
    (fun _ => ⟨hA, ⟨1, by simp, by simp, by simp⟩, ⟨1, by simp, by simp, by simp⟩⟩)
  obtain ⟨n₀, h0, hn₀, ht⟩ := ht
  refine ⟨n₀, hn₀, fun r b hb => ?_⟩
  obtain ⟨hb', hm⟩ := GlobalTheory.IndefiniteRowSideFullHecke.MomentCombSplitting.goodBasis_smul D cc δ L L' (Nat.Coprime.mul_left hn₀ hsp) b hb
  obtain ⟨μ, hμ, -, h1, -⟩ := hh (fun _ => 1) (fun _ => ⟨one_mem _, by rw [I3.JetMomEq.lamC_one]; simp⟩) r _ hb' fun i => by
    obtain ⟨x, hx, e⟩ := hm i
    exact ⟨n₀ • x, nsmul_mem hx _, e.trans (by rw [mul_comm, mul_smul])⟩
  simp only [one_mul, Finset.univ_unique, Finset.sum_singleton] at h1
  obtain ⟨ν, hν, hνμ⟩ := exists_image (scale p r (n₀ * s)) μ hμ
  refine ⟨ν, hν, fun n y hy => ⟨coefIn_Wop B hcc hδ hχ hA h0 ht (mulSub_le _ _ (pow_smul_goodLifts lam hy)), ?_⟩⟩
  intro m y' g hg
  obtain ⟨ε, hε⟩ := hE (2 * n + 2)
  obtain ⟨yt, hx, hl⟩ := exists_liftY lam hE hb hsp hε hy
  set x := liftY D (tor0 D cc δ) δ p n ε (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) yt with hxd
  obtain ⟨l, rfl⟩ : ∃ l, y = x + l := ⟨y - x, by abel⟩
  have hlg : l ∈ goodLifts D (tor0 D cc δ) lam n₀ n L L' := by simpa using sub_mem hy hx
  rw [add_sub_cancel_left] at hl
  rw [GlobalTheory.ThetaShift.Wop_add_lattice D _ N N' _ p hp (IO.HfInt_mono _ (mulSub_le n₀ _) hI) _
    (U_mem_ThSp _ hI (eNat_mem B χ hcc hδ hA) ht) x l hl ⟨n, pow_smul_goodLifts lam hx⟩
    (hfInt_goodLifts lam hI n₀ n x hx l hlg), hνμ]
  refine h1 n ε hε yt m y' _ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := GlobalTheory.CommutatorCharacter.exists_continuous_character D cc δ p lam N N' _ hI n r _ x hb'.2
    (mulSub_le _ _ (pow_smul_goodLifts lam hx))
  have hd : DenseRange fun (a : Fin r → ℕ) (i : Fin r) => (a i : ℤ_[p]) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  have key : g.comp (scale p r (n₀ * s)) = ψ * ∏ j, pairC D lam Ω (fun i => ((n₀ * s : ℕ) : D.host.E) • b i) (y' j) := by
    refine ContinuousMap.coe_injective (hd.equalizer (by fun_prop) (by fun_prop) (funext fun a => ?_))
    have e1 := hg fun i => n₀ * s * a i
    have e2 := hψ' fun i => (a i : ℤ)
    have e3 : ∑ i, ((n₀ * s * a i : ℕ) : D.host.E) • b i = ∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i :=
      Finset.sum_congr rfl fun i _ => by rw [smul_smul, Nat.cast_mul _ (a i), mul_comm]
    have hw : vecOf D cc δ (∑ i, (a i : D.host.E) • ((n₀ * s : ℕ) : D.host.E) • b i) ∈ La D (tor0 D cc δ) L L' := by
      rw [← GlobalTheory.CommutatorCharacter.vecHom_apply, map_sum]
      exact sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul, map_nsmul]; exact nsmul_mem (hb'.2 i) _
    rw [e3] at e1
    change _ = lamC lam (kap D _ (vecOf D cc δ _) _) * _ at e1
    rw [kap_add_right _ hI x hw (mulSub_le _ _ hl)] at e1
    simp only [Int.cast_natCast] at e2
    simp only [Nat.cast_mul _ (a _)] at e1
    simp only [Function.comp_apply, ContinuousMap.mul_apply, ContinuousMap.prod_apply, ContinuousMap.comp_apply, e2]
    refine e1.trans ?_
    congr 1
    exact Finset.prod_congr rfl fun j _ => (pairN_smul lam Ω b _ _ _).symm
  intro a
  rw [key, ContinuousMap.mul_apply, hψ, ContinuousMap.prod_apply]
  rfl

/- English proof (translation)
Introduce `h D cc δ B χ hcc hδ hχ p _ lam hs hc`. Take `⟨-, ⟨Ω, hΩ, -, hC⟩, -⟩` from `h D cc δ B hcc hδ χ hχ p hs hc lam`. Conclude with `⟨Ω, hΩ, momentsAt_of_momComb lam B hcc hδ hχ hs hC⟩`.
-/
theorem translateMomentsAll_of_jetMomR : Formalism.L2.Ker.I3.JetMomEq.JetMomR → GlobalTheory.MomT.TranslateMomentsAll := by
  intro h D cc δ B χ hcc hδ hχ p _ lam hs hc
  obtain ⟨-, ⟨Ω, hΩ, -, hC⟩, -⟩ := h D cc δ B hcc hδ χ hχ p hs hc lam
  exact ⟨Ω, hΩ, momentsAt_of_momComb lam B hcc hδ hχ hs hC⟩

end GlobalTheory.MomT.FromComb
