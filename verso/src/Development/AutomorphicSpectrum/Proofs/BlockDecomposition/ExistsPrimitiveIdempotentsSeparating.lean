import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Take `⟨a, b, hab⟩` from `(hp.coprime_iff_not_dvd).2 hn`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p (ne_of_gt (degree_pos_of_irreducible hp))`. Establish `hroot : (γ.map (algebraMap K (AlgebraicClosure K))).charpoly.IsRoot α`. Take `⟨c, hc⟩` from `hpc`.

Rewrite using `[Matrix.charpoly_map, hc, IsRoot, eval_map_algebraMap, map_mul, hα, zero_mul]`. Establish `hs : α ∈ spectrum (AlgebraicClosure K) (γ.map (algebraMap K (AlgebraicClosure K)))` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot`. Establish `h2` using `spectrum.subset_polynomial_aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) ⟨α, hs, rfl⟩`. Establish `h3 : aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) = 0`. Use `aeval_algHom_apply ((Algebra.ofId K (AlgebraicClosure K)).mapMatrix (m := Fin n)) γ g` as an intermediate fact.

Rewrite `this` using `[hg, map_zero]`. Rewrite using `[aeval_map_algebraMap]`. Conclude with `this`. Rewrite `h2` using `[h3]`. Establish `h4 : aeval α g = 0`.

Assume the negation of the conclusion as `hne`. Apply `h2` to reduce the goal to its premises. Simplify using `only [eval_map_algebraMap]`. Rewrite using `[spectrum.mem_resolventSet_iff, sub_zero]`. Conclude with `(Ne.isUnit hne).map (algebraMap (AlgebraicClosure K) (Matrix (Fin n) (Fin n) (AlgebraicClosure K)))`.

Establish `h5` using `congrArg (aeval α) hab`. Simplify using `[hα, h4] at h5`.
-/
theorem dvd_of_aeval_eq_zero_of_dvd_charpoly {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) {p g : K[X]} (hp : Irreducible p) (hpc : p ∣ γ.charpoly)
    (hg : aeval γ g = 0) : p ∣ g := by
  classical
  by_contra hn
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd).2 hn
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p (ne_of_gt (degree_pos_of_irreducible hp))
  have hroot : (γ.map (algebraMap K (AlgebraicClosure K))).charpoly.IsRoot α := by
    obtain ⟨c, hc⟩ := hpc
    rw [Matrix.charpoly_map, hc, IsRoot, eval_map_algebraMap, map_mul, hα, zero_mul]
  have hs : α ∈ spectrum (AlgebraicClosure K) (γ.map (algebraMap K (AlgebraicClosure K))) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval (γ.map (algebraMap K (AlgebraicClosure K)))
    (g.map (algebraMap K (AlgebraicClosure K))) ⟨α, hs, rfl⟩
  have h3 : aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) = 0 := by
    have := aeval_algHom_apply ((Algebra.ofId K (AlgebraicClosure K)).mapMatrix (m := Fin n)) γ g
    rw [hg, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this
  rw [h3] at h2
  have h4 : aeval α g = 0 := by
    by_contra hne
    apply h2
    simp only [eval_map_algebraMap]
    rw [spectrum.mem_resolventSet_iff, sub_zero]
    exact (Ne.isUnit hne).map (algebraMap (AlgebraicClosure K) (Matrix (Fin n) (Fin n) (AlgebraicClosure K)))
  have h5 := congrArg (aeval α) hab
  simp [hα, h4] at h5

/- English proof (translation)
Take `⟨q, hq⟩` from `hpc`. Establish `hχ : aeval γ (p * q) = 0` using `by rw [← hq]; exact Matrix.aeval_self_charpoly γ`. Take `⟨b, u, hbu⟩ : IsCoprime p q` from `(hq ▸ hs : (p * q).Separable).isCoprime`. Establish `hnd : ∀ c : K[X], aeval γ (c * (p * q)) = 0` using `fun c => by rw [map_mul, hχ, mul_zero]`. Establish `hsub : (1 : K[X]) - u * q = b * p` using `by rw [← hbu]; ring`.

Establish `hdvd : p ∣ 1 - u * q` using `⟨b, by rw [hsub]; ring⟩`. Use `⟨aeval γ (u * q), ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩, _, rfl, hdvd⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Establish `: u * q * (u * q) = u * q - (u * b) * (p * q)` using `by linear_combination (-(u * q)) * hsub`. Rewrite using `[this, map_sub, hnd, sub_zero]`.

Introduce `h0`. Establish `h1` using `dvd_of_aeval_eq_zero_of_dvd_charpoly γ hp ⟨q, hq⟩ h0`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hdvd h1))`. Introduce `h hne`. Establish `hnp : ¬ p ∣ h`.

Introduce and unpack `⟨c, rfl⟩`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← map_mul]`. Establish `: p * c * (u * q) = (c * u) * (p * q)` using `by ring`. Rewrite using `[this, hnd]`.

Take `⟨a', a, haa⟩` from `(hp.coprime_iff_not_dvd).2 hnp`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul]`. Establish `: a * (h * (u * q)) = u * q - (a' * u) * (p * q)` using `by linear_combination (u * q) * haa`. Rewrite using `[this, map_sub, hnd, sub_zero]`.
-/
theorem exists_prim_of_irreducible {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) {p : K[X]} (hp : Irreducible p)
    (hpc : p ∣ γ.charpoly) :
    ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := by
  obtain ⟨q, hq⟩ := hpc
  have hχ : aeval γ (p * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly γ
  obtain ⟨b, u, hbu⟩ : IsCoprime p q := (hq ▸ hs : (p * q).Separable).isCoprime
  have hnd : ∀ c : K[X], aeval γ (c * (p * q)) = 0 := fun c => by rw [map_mul, hχ, mul_zero]
  have hsub : (1 : K[X]) - u * q = b * p := by rw [← hbu]; ring
  have hdvd : p ∣ 1 - u * q := ⟨b, by rw [hsub]; ring⟩
  refine ⟨aeval γ (u * q), ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩, _, rfl, hdvd⟩
  · rw [← map_mul]
    have : u * q * (u * q) = u * q - (u * b) * (p * q) := by linear_combination (-(u * q)) * hsub
    rw [this, map_sub, hnd, sub_zero]
  · intro h0
    have h1 := dvd_of_aeval_eq_zero_of_dvd_charpoly γ hp ⟨q, hq⟩ h0
    exact hp.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hdvd h1))
  · intro h hne
    have hnp : ¬ p ∣ h := by
      rintro ⟨c, rfl⟩
      apply hne
      rw [← map_mul]
      have : p * c * (u * q) = (c * u) * (p * q) := by ring
      rw [this, hnd]
    obtain ⟨a', a, haa⟩ := (hp.coprime_iff_not_dvd).2 hnp
    refine ⟨a, ?_⟩
    rw [← map_mul, ← map_mul]
    have : a * (h * (u * q)) = u * q - (a' * u) * (p * q) := by linear_combination (u * q) * haa
    rw [this, map_sub, hnd, sub_zero]

/- English proof (translation)
Establish `key : ∀ p : K[X], p ∈ UniqueFactorizationMonoid.normalizedFactors γ.charpoly → ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f` using `fun p hp => exists_prim_of_irreducible γ hs (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)`. Use `choose! E hE using key`. Establish `hχ0 : γ.charpoly ≠ 0` using `(Matrix.charpoly_monic γ).ne_zero`. Use `⟨(UniqueFactorizationMonoid.normalizedFactors γ.charpoly).toFinset.image E, ?_, ?_⟩` and prove the remaining obligations. Introduce `e he`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 he`. Conclude with `(hE p (Multiset.mem_toFinset.1 hp)).1`. Introduce `x hx`. Set `I : Ideal K[X]` to `{ carrier := {f | x ᵥ* aeval γ f = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[map_add, Matrix.vecMul_add, ha, hb, add_zero]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c f hf => by`. Simplify using `only [Set.mem_setOf_eq] at hf ⊢`. Rewrite using `[smul_eq_mul, mul_comm, map_mul, ← Matrix.vecMul_vecMul, hf, Matrix.zero_vecMul] }`.

Establish `hmem : ∀ f, f ∈ I ↔ x ᵥ* aeval γ f = 0` using `fun f => Iff.rfl`. Use `set a := Submodule.IsPrincipal.generator I with ha`. Establish `hdiv : ∀ f, f ∈ I ↔ a ∣ f` using `fun f => Submodule.IsPrincipal.mem_iff_generator_dvd I`. Establish `haχ : a ∣ γ.charpoly` using `(hdiv _).1 (by`. Rewrite using `[hmem, Matrix.aeval_self_charpoly, Matrix.vecMul_zero])`.

Establish `ha0 : a ≠ 0` using `fun h => hχ0 (by simpa [h] using haχ)`. Establish `hau : ¬ IsUnit a` using `fun h => hx (by`. Establish `h1 : (1 : K[X]) ∈ I` using `(hdiv 1).2 h.dvd`. Rewrite `h1` using `[hmem, map_one, Matrix.vecMul_one]`. Conclude with `h1)`.

Take `⟨i, hi, hia⟩` from `WfDvdMonoid.exists_irreducible_factor hau ha0`. Take `⟨p, hp, hip⟩` from `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hχ0 hi (hia.trans haχ)`. Take `⟨hprim, f, hf, hpf⟩` from `hE p hp`. Use `⟨E p, Finset.mem_image.2 ⟨p, Multiset.mem_toFinset.2 hp, rfl⟩, fun h0 => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[hf]`.

Establish `h1 : a ∣ f` using `(hdiv f).1 h0`. Establish `h2 : p ∣ f` using `hip.symm.dvd.trans (hia.trans h1)`. Establish `hpi : Irreducible p` using `UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp`. Conclude with `hpi.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hpf h2))`.
-/
theorem exists_prim_cover (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧
      ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  classical
  have key : ∀ p : K[X], p ∈ UniqueFactorizationMonoid.normalizedFactors γ.charpoly →
      ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := fun p hp =>
    exists_prim_of_irreducible γ hs (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  choose! E hE using key
  have hχ0 : γ.charpoly ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors γ.charpoly).toFinset.image E, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    exact (hE p (Multiset.mem_toFinset.1 hp)).1
  · intro x hx
    let I : Ideal K[X] :=
      { carrier := {f | x ᵥ* aeval γ f = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add, Matrix.vecMul_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c f hf => by
          simp only [Set.mem_setOf_eq] at hf ⊢
          rw [smul_eq_mul, mul_comm, map_mul, ← Matrix.vecMul_vecMul, hf, Matrix.zero_vecMul] }
    have hmem : ∀ f, f ∈ I ↔ x ᵥ* aeval γ f = 0 := fun f => Iff.rfl
    set a := Submodule.IsPrincipal.generator I with ha
    have hdiv : ∀ f, f ∈ I ↔ a ∣ f := fun f => Submodule.IsPrincipal.mem_iff_generator_dvd I
    have haχ : a ∣ γ.charpoly := (hdiv _).1 (by
      rw [hmem, Matrix.aeval_self_charpoly, Matrix.vecMul_zero])
    have ha0 : a ≠ 0 := fun h => hχ0 (by simpa [h] using haχ)
    have hau : ¬ IsUnit a := fun h => hx (by
      have h1 : (1 : K[X]) ∈ I := (hdiv 1).2 h.dvd
      rw [hmem, map_one, Matrix.vecMul_one] at h1
      exact h1)
    obtain ⟨i, hi, hia⟩ := WfDvdMonoid.exists_irreducible_factor hau ha0
    obtain ⟨p, hp, hip⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hχ0 hi (hia.trans haχ)
    obtain ⟨hprim, f, hf, hpf⟩ := hE p hp
    refine ⟨E p, Finset.mem_image.2 ⟨p, Multiset.mem_toFinset.2 hp, rfl⟩, fun h0 => ?_⟩
    rw [hf] at h0
    have h1 : a ∣ f := (hdiv f).1 h0
    have h2 : p ∣ f := hip.symm.dvd.trans (hia.trans h1)
    have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    exact hpi.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hpf h2))

end GlobalTheory.CompanionTheory.TorusCh
