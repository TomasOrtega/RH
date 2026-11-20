import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerOrder

/- English proof (translation)
Set `e : (Fin d → Fin n) → (Fin d →₀ ℕ)` to `fun a => Finsupp.equivFunOnFinite.symm fun i => a i`. Set `v : (Fin d → Fin n) → A` to `fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)`. Establish `hmono : ∀ m : Fin d →₀ ℕ, MvPolynomial.aeval (R` using `K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by`. Introduce `m`. Distinguish the cases in `hm : ∀ i, m i < n`.

Use `Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩` and prove the remaining obligations. Establish `: e (fun i => ⟨m i, hm i⟩) = m`. Use extensionality with `i`. Simplify using `[e]`. Simplify using `only [v, this]`.

Use `push_neg at hm`. Take `⟨i, hi⟩` from `hm`. Establish `h0 : MvPolynomial.aeval (R` using `K) x (MvPolynomial.monomial m 1) = 0 := by`. Rewrite using `[MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]`. Distinguish the cases in `hmi : m i = 0`.

Establish `hn : n = 0` using `by omega`. Substitute `hn` using the available equality. Establish `h10 : (1 : A) = 0` using `by simpa using hpow i`. Rewrite using `[← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]`. Apply `Finset.prod_eq_zero (i := i) (by simpa using hmi)` to reduce the goal to its premises.

Take `⟨r, hr⟩` from `Nat.exists_eq_add_of_le hi`. Rewrite using `[hr, pow_add, hpow i, zero_mul]`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `htop : Submodule.span K (Set.range v) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Take `⟨P, rfl⟩` from `hsurj y`. Rewrite using `[P.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations.

Establish `: MvPolynomial.monomial m (MvPolynomial.coeff m P) = MvPolynomial.coeff m P • MvPolynomial.monomial m (1 : K)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul]`. Conclude with `Submodule.smul_mem _ _ (hmono m)`. Establish `h1` using `finrank_range_le_card (R := K) v`.

Rewrite `h1` using `[Set.finrank, htop, finrank_top]`. Simplify using `using h1`.
-/
theorem finrank_le_pow_of_aeval_surjective {n d : ℕ} {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (x : Fin d → A) (hsurj : Function.Surjective (MvPolynomial.aeval (R := K) x))
    (hpow : ∀ i, x i ^ n = 0) :
    Module.finrank K A ≤ n ^ d := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  let v : (Fin d → Fin n) → A := fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by
    intro m
    by_cases hm : ∀ i, m i < n
    · refine Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩
      have : e (fun i => ⟨m i, hm i⟩) = m := by
        ext i; simp [e]
      simp only [v, this]
    · push_neg at hm
      obtain ⟨i, hi⟩ := hm
      have h0 : MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) = 0 := by
        rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
        by_cases hmi : m i = 0
        · have hn : n = 0 := by omega
          subst hn
          have h10 : (1 : A) = 0 := by simpa using hpow i
          rw [← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]
        · apply Finset.prod_eq_zero (i := i) (by simpa using hmi)
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hi
          rw [hr, pow_add, hpow i, zero_mul]
      rw [h0]; exact Submodule.zero_mem _
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨P, rfl⟩ := hsurj y
    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : MvPolynomial.monomial m (MvPolynomial.coeff m P) =
        MvPolynomial.coeff m P • MvPolynomial.monomial m (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have h1 := finrank_range_le_card (R := K) v
  rw [Set.finrank, htop, finrank_top] at h1
  simpa using h1

/- English proof (translation)
Use `haveI := isHopfIdeal p K H`. Use `set J := frobKerIdeal p K H with hJ`. Set `π` to `Ideal.Quotient.mkₐ K J`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mkₐ_surjective K J`. Establish `hε : (counitAlgHom K (H ⧸ J)).comp π = counitAlgHom K H` using `rfl`.

Establish `hbij : Function.Bijective (AugCot.map π hε)`. Use `⟨?_, AugCot.map_surjective π hε hπ⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨z, rfl⟩` from `(AugCot.exact_kerMap_map π hε hπ y).1 hy`.

Rewrite using `[AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2), Ideal.toCotangent_eq_zero]`. Conclude with `le_sq p K H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)`. Rewrite using `[(LinearEquiv.ofBijective _ hbij).finrank_eq]`. Use `set ε := counitAlgHom K (H ⧸ J) with hεdef`. Set `b` to `Module.finBasis K (AugCot ε)`.

Use `choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)`. Establish `hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i`. Introduce `l`. Simplify using `[map_sum, hx]`. Establish `hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε`.

Introduce `l`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (x i).2`. Establish `hpow : ∀ f ∈ RingHom.ker ε, f ^ p = 0`.

Introduce `f hf`. Take `⟨a, rfl⟩` from `hπ f`. Rewrite using `[← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := K) hf)`. Establish `: IsNoetherianRing (H ⧸ J)` using `isNoetherian_of_tower K inferInstance`.

Establish `hnil : IsNilpotent (RingHom.ker ε)`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `f hf`. Conclude with `⟨p, hpow f hf⟩`. Establish `hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K, y - ∑ i, l i • (x i : H ⧸ J) ∈ RingHom.ker ε ^ 2`.

Introduce `y hy`. Use `⟨b.repr (AugCot.d ε y), ?_⟩` and prove the remaining obligations. Establish `h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0`. Rewrite using `[map_sub, hsum, b.sum_repr, sub_self]`. Rewrite `h1` using `[AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero]`. Then use the resulting hypothesis.

Conclude with `finrank_le_pow_of_aeval_surjective (fun i => (x i : H ⧸ J)) (GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil _ (fun i => (x i).2) hspan) (fun i => hpow _ (x i).2)`.
-/
theorem finrank_le_pow_finrank_cot (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  haveI := isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π := Ideal.Quotient.mkₐ K J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective K J
  have hε : (counitAlgHom K (H ⧸ J)).comp π = counitAlgHom K H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p K H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom K (H ⧸ J) with hεdef
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hpow : ∀ f ∈ RingHom.ker ε, f ^ p = 0 := by
    intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := K) hf)
  have : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      y - ∑ i, l i • (x i : H ⧸ J) ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  exact finrank_le_pow_of_aeval_surjective (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil _ (fun i => (x i).2) hspan)
    (fun i => hpow _ (x i).2)

end GlobalTheory.PDiv.FrobKerOrder
