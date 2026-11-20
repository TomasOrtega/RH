import Mathlib
open NumberField

namespace GlobalTheory

open NumberField Polynomial Matrix in
/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Rewrite using `[← Polynomial.map_dvd_map' (algebraMap K Ω), Polynomial.map_pow, ← Matrix.charpoly_map]`. Use `set N' := N.map (algebraMap K Ω)`. Establish `hs` using `IsAlgClosed.splits N'.charpoly`. Establish `hroot : ∀ μ ∈ N'.charpoly.roots, (φ.map (algebraMap K Ω)).IsRoot μ`.

Introduce `μ hμ`. Establish `h1` using `Matrix.mem_spectrum_of_isRoot_charpoly ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).1 hμ)`. Establish `h2` using `spectrum.subset_polynomial_aeval N' (φ.map (algebraMap K Ω)) ⟨μ, h1, rfl⟩`. Establish `h3 : aeval N' (φ.map (algebraMap K Ω)) = 0`. Rewrite using `[Polynomial.aeval_map_algebraMap]`.

Use `Polynomial.aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId K Ω) : Matrix (Fin r) (Fin r) K →ₐ[K] _) N φ` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `this`. Rewrite `h2` using `[h3, spectrum.zero_eq]`. Conclude with `h2`.

Establish `hcard : N'.charpoly.roots.card = r`. Rewrite using `[← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Rewrite using `[hs.eq_prod_roots_of_monic (Matrix.charpoly_monic _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Multiset.map_const', Multiset.prod_replicate, hcard]`.
-/
private lemma charpoly_dvd_pow_card_of_aeval_eq_zero {K : Type} [Field K] {r : ℕ} [NeZero r]
    (N : Matrix (Fin r) (Fin r) K) (φ : K[X]) (h : aeval N φ = 0) : N.charpoly ∣ φ ^ r := by
  let Ω := AlgebraicClosure K
  rw [← Polynomial.map_dvd_map' (algebraMap K Ω), Polynomial.map_pow, ← Matrix.charpoly_map]
  set N' := N.map (algebraMap K Ω)
  have hs := IsAlgClosed.splits N'.charpoly
  have hroot : ∀ μ ∈ N'.charpoly.roots, (φ.map (algebraMap K Ω)).IsRoot μ := by
    intro μ hμ
    have h1 := Matrix.mem_spectrum_of_isRoot_charpoly
      ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).1 hμ)
    have h2 := spectrum.subset_polynomial_aeval N' (φ.map (algebraMap K Ω)) ⟨μ, h1, rfl⟩
    have h3 : aeval N' (φ.map (algebraMap K Ω)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      have := Polynomial.aeval_algHom_apply
        (AlgHom.mapMatrix (Algebra.ofId K Ω) : Matrix (Fin r) (Fin r) K →ₐ[K] _) N φ
      rw [h, map_zero] at this
      exact this
    rw [h3, spectrum.zero_eq] at h2
    exact h2
  have hcard : N'.charpoly.roots.card = r := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic _)]
  calc (Multiset.map (fun x ↦ X - C x) N'.charpoly.roots).prod
      ∣ (Multiset.map (fun _ ↦ φ.map (algebraMap K Ω)) N'.charpoly.roots).prod :=
        Multiset.prod_dvd_prod_of_dvd _ _ fun μ hμ => Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)
    _ = (φ.map (algebraMap K Ω)) ^ r := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard]

open NumberField Polynomial Matrix in

/- English proof (translation)
Introduce `K _ _ r L N P n hL hspan hP hN hNn`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Conclude with `⟨0, P.zero_mem, by simp [Matrix.trace]⟩`. Use `haveI : NeZero r := ⟨hr.ne'⟩`. Use `set m := n + 1 with hm`.

Establish `hNm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ P • L` using `fun x hx => by`. Rewrite using `[hm, pow_succ, ← Matrix.mulVec_mulVec]`. Conclude with `hNn _ (hN x hx)`. Establish `hLm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ L` using `fun x hx => Submodule.smul_le_right (hNm x hx)`. Use `haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL`.

Set `f : Module.End (𝓞 K) L` to `((Matrix.toLin' (N ^ m)).restrictScalars (𝓞 K)).restrict (fun x hx => by show Matrix.toLin' (N ^ m) x ∈ L`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `hLm x hx)`. Establish `hf : ∀ y : L, ((f y : L) : Fin r → K) = (N ^ m) *ᵥ (y : Fin r → K)` using `fun y => by show Matrix.toLin' (N ^ m) (y : Fin r → K) = _`. Conclude with `Matrix.toLin'_apply _ _`.

Establish `hpow : ∀ (i : ℕ) (y : L), (((f ^ i) y : L) : Fin r → K) = ((N ^ m) ^ i) *ᵥ (y : Fin r → K)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules.

Consider the case `succ i ih => intro y`. Rewrite using `[pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']`. Establish `hrange : LinearMap.range f ≤ P • ⊤`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Submodule.mem_smul_top_iff, hf]`.

Conclude with `hNm _ y.2`. Take `⟨q, hqm, -, hqc, hq0⟩` from `LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul (𝓞 K) f P hrange`. Establish `hzero : aeval (N ^ m) q = 0`. Establish `hon : ∀ x ∈ L, (aeval (N ^ m) q) *ᵥ x = 0`. Introduce `x hx`.

Use `congrArg (fun g : Module.End (𝓞 K) L => ((g ⟨x, hx⟩ : L) : Fin r → K)) hq0` as an intermediate fact. Simplify using `only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, Submodule.coe_zero] at this`. Rewrite using `[Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]`. Use `(Finset.sum_congr rfl fun i _ => ?_).trans this` and prove the remaining obligations. Conclude with `Matrix.smul_mulVec _ _ _`.

Establish `h1 : Matrix.toLin' (aeval (N ^ m) q) = 0` using `LinearMap.ext_on hspan (fun x hx => by simpa using hon x hx)`. Conclude with `Matrix.toLin'.injective (h1.trans (map_zero _).symm)`. Establish `hmpos : 0 < m` using `by omega`. Use `set φ := expand (𝓞 K) m q with hφdef`. Establish `hφm : φ.Monic` using `hqm.expand hmpos`.

Establish `hφ : aeval N (φ.map (algebraMap (𝓞 K) K)) = 0`. Rewrite using `[aeval_map_algebraMap, hφdef, expand_aeval, hzero]`. Establish `hdvd` using `charpoly_dvd_pow_card_of_aeval_eq_zero N _ hφ`. Rewrite `hdvd` using `[← Polynomial.map_pow]`. Take `⟨χ, hχ⟩` from `IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hφm.pow r) hdvd`.

Rewrite `hχ` using `[(Matrix.charpoly_monic N).leadingCoeff, C_1, mul_one]`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) K)` using `IsFractionRing.injective (𝓞 K) K`. Establish `hχm : χ.Monic`. Use `Matrix.charpoly_monic N` as an intermediate fact. Rewrite `this` using `[← hχ]`.

Conclude with `Polynomial.monic_of_injective hinj this`. Establish `hχdvd : χ ∣ φ ^ r` using `(Polynomial.map_dvd_map _ hinj hχm).1 (hχ ▸ hdvd)`. Establish `hχdeg : χ.natDegree = r`. Rewrite using `[← natDegree_map_eq_of_injective hinj, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hqπ : q.map (Ideal.Quotient.mk P) = X ^ q.natDegree`.

Use extensionality with `k`. Rewrite using `[coeff_map, coeff_X_pow]`. Break down `lt_trichotomy k q.natDegree with hk | rfl | hk` into its components or cases. Rewrite using `[if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_le_self (by omega) (hqc k)`.

Simplify using `[hqm.coeff_natDegree]`. Rewrite using `[if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]`. Establish `hφπ : φ.map (Ideal.Quotient.mk P) = X ^ (m * q.natDegree)`. Rewrite using `[hφdef, map_expand, hqπ, map_pow, expand_X, ← pow_mul]`. Establish `hdvdπ : χ.map (Ideal.Quotient.mk P) ∣ X ^ (m * q.natDegree * r)`.

Rewrite using `[pow_mul, ← hφπ, ← Polynomial.map_pow]`. Conclude with `Polynomial.map_dvd _ hχdvd`. Use `haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain P`. Take `⟨i, -, hi⟩` from `(dvd_prime_pow Polynomial.prime_X _).1 hdvdπ`. Establish `hχπ : χ.map (Ideal.Quotient.mk P) = X ^ i` using `eq_of_monic_of_associated (hχm.map _) (monic_X_pow i) hi`.

Establish `hir : i = r`. Use `congrArg natDegree hχπ` as an intermediate fact. Rewrite `this` using `[hχm.natDegree_map, natDegree_X_pow, hχdeg]`. Conclude with `this.symm`. Establish `hcoeff : χ.coeff (r - 1) ∈ P`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Use `congrArg (fun p => p.coeff (r - 1)) hχπ` as an intermediate fact. Simplify using `only [coeff_map, coeff_X_pow, hir] at this`. Rewrite using `[this, if_neg (by omega)]`. Use `⟨-χ.coeff (r - 1), P.neg_mem hcoeff, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hχ, coeff_map]`. Use `show algebraMap (𝓞 K) K (-χ.coeff (r - 1)) = _`. Rewrite using `[map_neg]`.
-/
theorem _root_.GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (L : Submodule (𝓞 K) (Fin r → K))
      (N : Matrix (Fin r) (Fin r) K) (P : Ideal (𝓞 K)) (n : ℕ), L.FG →
      Submodule.span K (L : Set (Fin r → K)) = ⊤ → P.IsPrime → (∀ x ∈ L, N.mulVec x ∈ L) →
      (∀ x ∈ L, (N ^ n).mulVec x ∈ P • L) → ∃ z ∈ P, ((z : 𝓞 K) : K) = N.trace := by
  intro K _ _ r L N P n hL hspan hP hN hNn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, P.zero_mem, by simp [Matrix.trace]⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  set m := n + 1 with hm
  have hNm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ P • L := fun x hx => by
    rw [hm, pow_succ, ← Matrix.mulVec_mulVec]
    exact hNn _ (hN x hx)
  have hLm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ L := fun x hx => Submodule.smul_le_right (hNm x hx)
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  let f : Module.End (𝓞 K) L :=
    ((Matrix.toLin' (N ^ m)).restrictScalars (𝓞 K)).restrict (fun x hx => by
      show Matrix.toLin' (N ^ m) x ∈ L
      rw [Matrix.toLin'_apply]
      exact hLm x hx)
  have hf : ∀ y : L, ((f y : L) : Fin r → K) = (N ^ m) *ᵥ (y : Fin r → K) := fun y => by
    show Matrix.toLin' (N ^ m) (y : Fin r → K) = _
    exact Matrix.toLin'_apply _ _
  have hpow : ∀ (i : ℕ) (y : L), (((f ^ i) y : L) : Fin r → K) = ((N ^ m) ^ i) *ᵥ (y : Fin r → K) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; rw [pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']
  have hrange : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_smul_top_iff, hf]
    exact hNm _ y.2
  obtain ⟨q, hqm, -, hqc, hq0⟩ := LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul (𝓞 K) f P hrange
  have hzero : aeval (N ^ m) q = 0 := by
    have hon : ∀ x ∈ L, (aeval (N ^ m) q) *ᵥ x = 0 := by
      intro x hx
      have := congrArg (fun g : Module.End (𝓞 K) L => ((g ⟨x, hx⟩ : L) : Fin r → K)) hq0
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
        Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply,
        Submodule.coe_zero] at this
      rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans this
      exact Matrix.smul_mulVec _ _ _
    have h1 : Matrix.toLin' (aeval (N ^ m) q) = 0 :=
      LinearMap.ext_on hspan (fun x hx => by simpa using hon x hx)
    exact Matrix.toLin'.injective (h1.trans (map_zero _).symm)
  have hmpos : 0 < m := by omega
  set φ := expand (𝓞 K) m q with hφdef
  have hφm : φ.Monic := hqm.expand hmpos
  have hφ : aeval N (φ.map (algebraMap (𝓞 K) K)) = 0 := by
    rw [aeval_map_algebraMap, hφdef, expand_aeval, hzero]
  have hdvd := charpoly_dvd_pow_card_of_aeval_eq_zero N _ hφ
  rw [← Polynomial.map_pow] at hdvd
  obtain ⟨χ, hχ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hφm.pow r) hdvd
  rw [(Matrix.charpoly_monic N).leadingCoeff, C_1, mul_one] at hχ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hχm : χ.Monic := by
    have := Matrix.charpoly_monic N
    rw [← hχ] at this
    exact Polynomial.monic_of_injective hinj this
  have hχdvd : χ ∣ φ ^ r := (Polynomial.map_dvd_map _ hinj hχm).1 (hχ ▸ hdvd)
  have hχdeg : χ.natDegree = r := by
    rw [← natDegree_map_eq_of_injective hinj, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hqπ : q.map (Ideal.Quotient.mk P) = X ^ q.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy k q.natDegree with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_self (by omega) (hqc k)
    · simp [hqm.coeff_natDegree]
    · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]
  have hφπ : φ.map (Ideal.Quotient.mk P) = X ^ (m * q.natDegree) := by
    rw [hφdef, map_expand, hqπ, map_pow, expand_X, ← pow_mul]
  have hdvdπ : χ.map (Ideal.Quotient.mk P) ∣ X ^ (m * q.natDegree * r) := by
    rw [pow_mul, ← hφπ, ← Polynomial.map_pow]
    exact Polynomial.map_dvd _ hχdvd
  haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X _).1 hdvdπ
  have hχπ : χ.map (Ideal.Quotient.mk P) = X ^ i :=
    eq_of_monic_of_associated (hχm.map _) (monic_X_pow i) hi
  have hir : i = r := by
    have := congrArg natDegree hχπ
    rw [hχm.natDegree_map, natDegree_X_pow, hχdeg] at this
    exact this.symm
  have hcoeff : χ.coeff (r - 1) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun p => p.coeff (r - 1)) hχπ
    simp only [coeff_map, coeff_X_pow, hir] at this
    rw [this, if_neg (by omega)]
  refine ⟨-χ.coeff (r - 1), P.neg_mem hcoeff, ?_⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hχ, coeff_map]
  show algebraMap (𝓞 K) K (-χ.coeff (r - 1)) = _
  rw [map_neg]

end GlobalTheory
