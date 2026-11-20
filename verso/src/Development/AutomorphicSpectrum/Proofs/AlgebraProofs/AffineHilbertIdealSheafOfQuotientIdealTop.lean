import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsUniformDenominator

namespace GlobalTheory.CompanionTheory.Ar.Num.DualLattice

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.Reflexive

/- English proof (translation)
Introduce `o Ω _ _ _ R E E₁ _ _ _ _ β hβ r L L₁ h h₁`. Use `⟨?_, fun v => ⟨fun hv w hw => (h₁ w).1 hw v hv, fun hv => ?_⟩⟩` and prove the remaining obligations. Use `swap`. Use `locFree_reflexive R r L h v fun ψ hψ => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hβ.2 ψ`.

Conclude with `hv w ((h₁ w).2 hψ)`. Establish `h'` using `h`. Take `⟨hL, k, f, c, hf, hc, h1, hb⟩` from `h'`. Use `⟨fun a ha w hw => (h₁ _).2 fun v hv => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`.

Conclude with `R.mul_mem ha ((h₁ w).1 hw v hv)`. Take `⟨b, hli, hsp, hb⟩` from `hb l`. Set `B : Module.Basis (Fin r) Ω E` to `Module.Basis.mk hli hsp.ge`. Establish `hB : ∀ q, B q = b q` using `fun q => Module.Basis.mk_apply _ _ q`. Set `e : E₁ ≃ₗ[Ω] Module.Dual Ω E` to `LinearEquiv.ofBijective β.flip hβ`.

Set `C : Module.Basis (Fin r) Ω E₁` to `B.dualBasis.map e.symm`. Establish `hrepr : ∀ w q, C.repr w q = β (b q) w` using `fun w q => by`. Simplify using `[C, e, ← hB]`. Establish `hsum : ∀ (a : Fin r → Ω) q, β (b q) (∑ q', a q' • C q') = a q` using `fun a q => by`. Rewrite using `[← hrepr]`.

Conclude with `congrFun (C.repr_sum_self a) q`. Use `⟨C, C.linearIndependent, C.span_eq, fun w => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨n, hn⟩`. Use `⟨fun q => C.repr w q, fun q => ?_, (C.sum_repr w).symm⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, f l ^ m • b q ∈ L := by`.

Use `(hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : q' = q`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hq]`.

Simplify using `[Pi.single_apply]`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `h2` using `(h₁ _).1 hn _ hm`. Establish `h3 : β (f l ^ m • b q) (f l ^ n • w) = f l ^ (n + m) * C.repr w q`. Rewrite using `[hrepr]`.

Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Introduce and unpack `⟨a, ha, rfl⟩`. Set `R' : AddSubgroup Ω` to `R.toSubring.toAddSubgroup`.

Establish `hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R'` using `fun a ha e he => R.mul_mem ha he`. Take `⟨m, hm⟩` from `exists_uniform_denominator R r L h (f l) (hf l) (β.flip (∑ q, a q • C q)) fun v hv => by`. Take `⟨a', ha', rfl⟩` from `(hb v).1 ⟨0, by simpa using hv⟩`. Establish `key : ∀ q, ∃ n : ℕ, f l ^ n • (a' q * a q) ∈ R'` using `fun q => by`. Take `⟨n, hn⟩` from `ha q`.

Take `⟨n', hn'⟩` from `ha' q`. Use `⟨n' + n, ?_⟩` and prove the remaining obligations. Establish `h4 : f l ^ (n' + n) • (a' q * a q) = f l ^ n' * a' q * (f l ^ n * a q)`. Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Conclude with `R.mul_mem hn' hn`. Take `⟨n, hn⟩` from `exists_uniform_pow R R' hR' (f l) (hf l) _ key`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h5 : β.flip (∑ q, a q • C q) (∑ q, a' q • b q) = ∑ q, a' q * a q`.

Rewrite using `[map_sum (β.flip (∑ q, a q • C q))]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.flip_apply, hsum, smul_eq_mul]`. Rewrite using `[h5, Finset.mul_sum]`. Conclude with `R'.sum_mem fun q _ => hn q`.

Use `⟨m, (h₁ _).2 fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `hm v hv`.
-/
theorem locFree_dual : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (β : E →ₗ[Ω] E₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∀ (r : ℕ) (L : AddSubgroup E) (L₁ : AddSubgroup E₁), LocFree R r L → (∀ w, w ∈ L₁ ↔ ∀ v ∈ L, β v w ∈ R) → LocFree R r L₁ ∧ ∀ v, v ∈ L ↔ ∀ w ∈ L₁, β v w ∈ R := by
  intro o Ω _ _ _ R E E₁ _ _ _ _ β hβ r L L₁ h h₁
  classical
  refine ⟨?_, fun v => ⟨fun hv w hw => (h₁ w).1 hw v hv, fun hv => ?_⟩⟩
  swap
  · refine locFree_reflexive R r L h v fun ψ hψ => ?_
    obtain ⟨w, rfl⟩ := hβ.2 ψ
    exact hv w ((h₁ w).2 hψ)
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine ⟨fun a ha w hw => (h₁ _).2 fun v hv => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact R.mul_mem ha ((h₁ w).1 hw v hv)
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  let e : E₁ ≃ₗ[Ω] Module.Dual Ω E := LinearEquiv.ofBijective β.flip hβ
  let C : Module.Basis (Fin r) Ω E₁ := B.dualBasis.map e.symm
  have hrepr : ∀ w q, C.repr w q = β (b q) w := fun w q => by
    simp [C, e, ← hB]
  have hsum : ∀ (a : Fin r → Ω) q, β (b q) (∑ q', a q' • C q') = a q := fun a q => by
    rw [← hrepr]
    exact congrFun (C.repr_sum_self a) q
  refine ⟨C, C.linearIndependent, C.span_eq, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => C.repr w q, fun q => ?_, (C.sum_repr w).symm⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, f l ^ m • b q ∈ L := by
      refine (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · by_cases hq : q' = q
        · subst hq; simp
        · simp [hq]
      · simp [Pi.single_apply]
    refine ⟨n + m, ?_⟩
    have h2 := (h₁ _).1 hn _ hm
    have h3 : β (f l ^ m • b q) (f l ^ n • w) = f l ^ (n + m) * C.repr w q := by
      rw [hrepr]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rwa [h3] at h2
  · rintro ⟨a, ha, rfl⟩
    let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
    have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
    obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l)
      (β.flip (∑ q, a q • C q)) fun v hv => by
        obtain ⟨a', ha', rfl⟩ := (hb v).1 ⟨0, by simpa using hv⟩
        have key : ∀ q, ∃ n : ℕ, f l ^ n • (a' q * a q) ∈ R' := fun q => by
          obtain ⟨n, hn⟩ := ha q
          obtain ⟨n', hn'⟩ := ha' q
          refine ⟨n' + n, ?_⟩
          have h4 : f l ^ (n' + n) • (a' q * a q) = f l ^ n' * a' q * (f l ^ n * a q) := by
            rw [smul_eq_mul]; ring
          rw [h4]
          exact R.mul_mem hn' hn
        obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f l) (hf l) _ key
        refine ⟨n, ?_⟩
        have h5 : β.flip (∑ q, a q • C q) (∑ q, a' q • b q) = ∑ q, a' q * a q := by
          rw [map_sum (β.flip (∑ q, a q • C q))]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, LinearMap.flip_apply, hsum, smul_eq_mul]
        rw [h5, Finset.mul_sum]
        exact R'.sum_mem fun q _ => hn q
    refine ⟨m, (h₁ _).2 fun v hv => ?_⟩
    rw [map_smul, smul_eq_mul]
    exact hm v hv

end GlobalTheory.CompanionTheory.Ar.Num.DualLattice
