import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff

noncomputable section

namespace GlobalTheory.NormalDescent

open Polynomial TensorProduct

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Set `T : Submonoid B` to `p.primeCompl.map φ ⊔ Submonoid.powers b`. Establish `hdisj : Disjoint ((p.map φ : Ideal B) : Set B) (T : Set B)`. Rewrite using `[Set.disjoint_left]`.

Introduce `x hxJ hxT`. Take `⟨y, hy, z, hz, rfl⟩` from `Submonoid.mem_sup.mp hxT`. Take `⟨s, hs, rfl⟩` from `Submonoid.mem_map.mp hy`. Take `⟨n, rfl⟩` from `(Submonoid.mem_powers_iff _ _).mp hz`. Conclude with `hne s (Ideal.mem_primeCompl_iff.mp hs) n hxJ`.

Take `⟨Q, hQ, hJQ, hQT⟩` from `Ideal.exists_le_prime_disjoint (S := T) (disjoint := hdisj)`. Establish `hcomap : Q.comap φ = p`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Assume the negation of the conclusion as `hap`.

Conclude with `Set.disjoint_left.mp hQT (Ideal.mem_comap.mp ha) (Submonoid.mem_sup_left (Submonoid.mem_map_of_mem φ (Ideal.mem_primeCompl_iff.mpr hap)))`. Conclude with `Ideal.map_le_iff_le_comap.mp hJQ`. Conclude with `Set.disjoint_left.mp hQT (h Q hQ hcomap) (Submonoid.mem_sup_right (Submonoid.mem_powers b))`.
-/
theorem exists_mul_pow_mem_map (φ : A →+* B) (p : Ideal A) [p.IsPrime] (b : B)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∈ Q) :
    ∃ s ∉ p, ∃ n : ℕ, φ s * b ^ n ∈ p.map φ := by
  by_contra hne
  push Not at hne
  let T : Submonoid B := p.primeCompl.map φ ⊔ Submonoid.powers b
  have hdisj : Disjoint ((p.map φ : Ideal B) : Set B) (T : Set B) := by
    rw [Set.disjoint_left]
    intro x hxJ hxT
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_sup.mp hxT
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    exact hne s (Ideal.mem_primeCompl_iff.mp hs) n hxJ
  obtain ⟨Q, hQ, hJQ, hQT⟩ := Ideal.exists_le_prime_disjoint (S := T) (disjoint := hdisj)
  have hcomap : Q.comap φ = p := by
    apply le_antisymm
    · intro a ha
      by_contra hap
      exact Set.disjoint_left.mp hQT (Ideal.mem_comap.mp ha)
        (Submonoid.mem_sup_left (Submonoid.mem_map_of_mem φ (Ideal.mem_primeCompl_iff.mpr hap)))
    · exact Ideal.map_le_iff_le_comap.mp hJQ
  exact Set.disjoint_left.mp hQT (h Q hQ hcomap) (Submonoid.mem_sup_right (Submonoid.mem_powers b))

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite A B := hφ`. Establish `hrange : LinearMap.range (Algebra.lmul A B u) ≤ p • (⊤ : Submodule A B)`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]`.

Conclude with `Ideal.mul_mem_right _ _ hu`. Take `⟨g, hgm, -, hgc, hg0⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (f := Algebra.lmul A B u) (I := p) (hI := hrange)`. Use `⟨g, hgm, fun i hi => Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hgc i), ?_⟩` and prove the remaining obligations. Establish `e2` using `Polynomial.aeval_algHom_apply (Algebra.lmul A B) u g`. Rewrite `e2` using `[hg0]`.

Establish `e3` using `congrArg (fun F : Module.End A B => F 1) e2`. Establish `e4 : aeval u g = 0` using `by simpa using e3.symm`. Rewrite `e4` using `[aeval_def]`. Conclude with `e4`.
-/
theorem exists_monic_coeff_mem (φ : A →+* B) (hφ : φ.Finite) (p : Ideal A) (u : B) (hu : u ∈ p.map φ) :
    ∃ g : A[X], g.Monic ∧ (∀ i < g.natDegree, g.coeff i ∈ p) ∧ eval₂ φ u g = 0 := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  have hrange : LinearMap.range (Algebra.lmul A B u) ≤ p • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact Ideal.mul_mem_right _ _ hu
  obtain ⟨g, hgm, -, hgc, hg0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := Algebra.lmul A B u) (I := p) (hI := hrange)
  refine ⟨g, hgm, fun i hi => Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hgc i), ?_⟩
  have e2 := Polynomial.aeval_algHom_apply (Algebra.lmul A B) u g
  rw [hg0] at e2
  have e3 := congrArg (fun F : Module.End A B => F 1) e2
  have e4 : aeval u g = 0 := by simpa using e3.symm
  rw [aeval_def] at e4
  exact e4

/- English proof (translation)
Establish `key` using `hw`. Rewrite `key` using `[aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul]`. Establish `hsum : (∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i) ∈ P`. Use `P.sum_mem fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Conclude with `P.mul_mem_right _ (hc i (Finset.mem_range.mp hi))`. Establish `hpow : w ^ g.natDegree ∈ P`. Establish `e : w ^ g.natDegree = -(∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i)`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `key`.

Rewrite using `[e]`. Conclude with `P.neg_mem hsum`. Conclude with `hP.mem_of_pow_mem _ hpow`.
-/
theorem mem_of_aeval_eq_zero {R : Type} [CommRing R] [Algebra A R] (P : Ideal R) [hP : P.IsPrime] (g : A[X])
    (hg : g.Monic) (hc : ∀ i < g.natDegree, algebraMap A R (g.coeff i) ∈ P) (w : R) (hw : aeval w g = 0) :
    w ∈ P := by
  have key := hw
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul] at key
  have hsum : (∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i) ∈ P := by
    refine P.sum_mem fun i hi => ?_
    rw [Algebra.smul_def]
    exact P.mul_mem_right _ (hc i (Finset.mem_range.mp hi))
  have hpow : w ^ g.natDegree ∈ P := by
    have e : w ^ g.natDegree = -(∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact key
    rw [e]
    exact P.neg_mem hsum
  exact hP.mem_of_pow_mem _ hpow

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_multiset_prod, Multiset.map_map]`. Establish `hX : ∀ a ∈ s, ((Polynomial.map (Ideal.Quotient.mk P)) ∘ fun a => X - C a) a = X`. Introduce `a ha`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hs a ha)]`. Rewrite using `[Multiset.map_congr rfl hX, Multiset.map_const', Multiset.prod_replicate, coeff_X_pow, if_neg hi.ne]`.
-/
theorem coeff_prod_X_sub_C_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] (s : Multiset R)
    (hs : ∀ a ∈ s, a ∈ P) (i : ℕ) (hi : i < Multiset.card s) :
    ((s.map fun a => X - C a).prod).coeff i ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_multiset_prod,
    Multiset.map_map]
  have hX : ∀ a ∈ s, ((Polynomial.map (Ideal.Quotient.mk P)) ∘ fun a => X - C a) a = X := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hs a ha)]
  rw [Multiset.map_congr rfl hX, Multiset.map_const', Multiset.prod_replicate, coeff_X_pow,
    if_neg hi.ne]

end Algebra

section Spectral

variable {A B : Type} [CommRing A] [CommRing B]

/- English proof (translation)
Set `` to `φ.toAlgebra`. Establish `: Module.Finite A B` using `hφ`. Establish `hb : aeval b h = 0`. Rewrite using `[aeval_def]`. Conclude with `hh`.

Establish `h1 : aeval ((1 : K) ⊗ₜ[A] b) h = 0`. Establish `e` using `Polynomial.aeval_algHom_apply (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) b h`. Rewrite `e` using `[hb, map_zero]`. Conclude with `e`. Establish `hK : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K)) = 0`.

Rewrite using `[Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, h1, map_zero]`. Establish `hΩ : aeval ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω) ((h.map (algebraMap A K)).map (algebraMap K Ω)) = 0`. Establish `e` using `Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K Ω (K ⊗[A] B)) (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K))`. Rewrite `e` using `[hK, map_zero, ← Polynomial.aeval_map_algebraMap Ω]`. Conclude with `e`.

Establish `hroot : ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω).charpoly.IsRoot μ`. Rewrite using `[LinearMap.charpoly_baseChange]`. Conclude with `hμ`. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot).exists_hasEigenvector`. Establish `e` using `Module.End.aeval_apply_of_hasEigenvector (p := (h.map (algebraMap A K)).map (algebraMap K Ω)) hv`.

Rewrite `e` using `[hΩ, LinearMap.zero_apply, eq_comm, smul_eq_zero]`. Break down `e with e | e` into its components or cases. Rewrite `e` using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.eval_map_algebraMap]`. Then use the resulting hypothesis. Conclude with `absurd e hv.2`.
-/
theorem aeval_eq_zero_of_isRoot (φ : A →+* B) (hφ : φ.Finite) (K Ω : Type) [Field K] [Algebra A K] [Field Ω]
    [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω] (b : B) (h : A[X]) (hh : eval₂ φ b h = 0) (μ : Ω)
    (hμ : ((charK φ hφ K b).map (algebraMap K Ω)).IsRoot μ) :
    aeval μ h = 0 := by
  let := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : aeval b h = 0 := by
    rw [aeval_def]
    exact hh
  have h1 : aeval ((1 : K) ⊗ₜ[A] b) h = 0 := by
    have e := Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) b h
    rw [hb, map_zero] at e
    exact e
  have hK : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, h1, map_zero]
  have hΩ : aeval ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω)
      ((h.map (algebraMap A K)).map (algebraMap K Ω)) = 0 := by
    have e := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K Ω (K ⊗[A] B))
      (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K))
    rw [hK, map_zero, ← Polynomial.aeval_map_algebraMap Ω] at e
    exact e
  have hroot : ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω).charpoly.IsRoot μ := by
    rw [LinearMap.charpoly_baseChange]
    exact hμ
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot).exists_hasEigenvector
  have e := Module.End.aeval_apply_of_hasEigenvector
    (p := (h.map (algebraMap A K)).map (algebraMap K Ω)) hv
  rw [hΩ, LinearMap.zero_apply, eq_comm, smul_eq_zero] at e
  rcases e with e | e
  · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.eval_map_algebraMap] at e
  · exact absurd e hv.2

end Spectral

section Main

variable {A B : Type} [CommRing A] [IsDomain A] [CommRing B]

/- English proof (translation)
Use `set K := FractionRing A with hKdef`. Use `set χ := charK φ hφ K b with hχdef`. Establish `hχm : χ.Monic` using `charK_monic φ hφ K b`. Distinguish the cases in `hkN : χ.natDegree < k`. Establish `h0 : algebraMap A K a = 0`.

Rewrite using `[ha, coeff_reverse, revAt_eq_self_of_lt hkN]`. Conclude with `coeff_eq_zero_of_natDegree_lt hkN`. Establish `ha0 : a = 0` using `IsFractionRing.injective A K (h0.trans (map_zero _).symm)`. Rewrite using `[ha0]`. Conclude with `p.zero_mem`.

Use `push Not at hkN`. Take `⟨s, hs, n, hsn⟩` from `exists_mul_pow_mem_map φ p b h`. Take `⟨g, hgm, hgc, hg0⟩` from `exists_monic_coeff_mem φ hφ p _ hsn`. Establish `hbint : ∃ m : A[X], m.Monic ∧ eval₂ φ b m = 0`. Use `letI := φ.toAlgebra`.

Use `haveI : Module.Finite A B := hφ`. Conclude with `Algebra.IsIntegral.isIntegral (R := A) b`. Take `⟨m, hmm, hm0⟩` from `hbint`. Establish `hinj : Function.Injective (algebraMap A (AlgebraicClosure K))`. Rewrite using `[IsScalarTower.algebraMap_eq A K (AlgebraicClosure K), RingHom.coe_comp]`.

Conclude with `(algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective A K)`. Take `⟨P, -, hP, hPp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure A (AlgebraicClosure K)) p ⊥ (by`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`. Establish `hx0 : x = 0` using `hinj (by`.

Rewrite using `[IsScalarTower.algebraMap_apply A (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K), hx, map_zero, map_zero])`. Rewrite using `[hx0]`. Conclude with `p.zero_mem)`. Establish `hint : ∀ μ ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots, μ ∈ integralClosure A (AlgebraicClosure K)`. Introduce `μ hμ`.

Establish `e` using `aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b m hm0 μ (mem_roots'.mp hμ).2`. Conclude with `(mem_integralClosure_iff A (AlgebraicClosure K)).mpr ⟨m, hmm, by rwa [aeval_def] at e⟩`. Establish `hmemP : ∀ c : integralClosure A (AlgebraicClosure K), (χ.map (algebraMap K (AlgebraicClosure K))).IsRoot (c : AlgebraicClosure K) → c ∈ P`. Introduce `c hc`. Establish `e1 : eval₂ φ b (g.comp (C s * X ^ n)) = 0`.

Rewrite using `[eval₂_comp]`. Simplify using `using hg0`. Establish `e2` using `aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b _ e1 (c : AlgebraicClosure K) hc`. Rewrite `e2` using `[aeval_comp]`. Simplify using `only [map_mul, aeval_C, map_pow, aeval_X] at e2`.

Establish `e3 : aeval (algebraMap A (integralClosure A (AlgebraicClosure K)) s * c ^ n) g = 0`. Apply `Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.aeval_subalgebra_coe]`. Simplify using `using e2`. Establish `hw` using `mem_of_aeval_eq_zero P g hgm (fun i hi => by rw [← Ideal.mem_comap, hPp]; exact hgc i hi) _ e3`.

Break down `hP.mem_or_mem hw with h1 | h1` into its components or cases. Establish `h2 : s ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K)))` using `h1`. Rewrite `h2` using `[hPp]`. Conclude with `(hs h2).elim`. Conclude with `hP.mem_of_pow_mem n h1`.

Take `⟨t, ht⟩ : ∃ t : Multiset (integralClosure A (AlgebraicClosure K)), t.map Subtype.val = (χ.map (algebraMap K (AlgebraicClosure K))).roots` from `⟨(χ.map (algebraMap K (AlgebraicClosure K))).roots.attach.map fun x => ⟨x.1, hint x.1 x.2⟩, by simp [Multiset.map_map]⟩`. Establish `hsplit : (χ.map (algebraMap K (AlgebraicClosure K))).Splits` using `IsAlgClosed.splits _`. Establish `hprod : χ.map (algebraMap K (AlgebraicClosure K)) = ((t.map fun c => X - C c).prod).map (algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K))` using `by conv_lhs => rw [hsplit.eq_prod_roots_of_monic (hχm.map _), ← ht]`. Rewrite using `[Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `congr 1`.

Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `c _`. Simplify using the standard rewrite rules. Establish `hcard : Multiset.card t = χ.natDegree`. Rewrite using `[← Multiset.card_map Subtype.val t, ht, ← hsplit.natDegree_eq_card_roots, natDegree_map]`.

Establish `hi : χ.natDegree - k < Multiset.card t` using `by omega`. Establish `hc` using `coeff_prod_X_sub_C_mem P t (fun c hct => hmemP c (by`. Establish `hmem : (c : AlgebraicClosure K) ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots`. Rewrite using `[← ht]`. Conclude with `Multiset.mem_map_of_mem _ hct`.

Conclude with `(mem_roots'.mp hmem).2)) _ hi`. Establish `hval : algebraMap A (AlgebraicClosure K) a = algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K) ((t.map fun c => X - C c).prod.coeff (χ.natDegree - k))`. Rewrite using `[IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), ha, coeff_reverse, revAt_le hkN, ← Polynomial.coeff_map, hprod, Polynomial.coeff_map]`. Establish `hAR : algebraMap A (integralClosure A (AlgebraicClosure K)) a = (t.map fun c => X - C c).prod.coeff (χ.natDegree - k)`. Apply `Subtype.val_injective` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K) (algebraMap A (integralClosure A (AlgebraicClosure K)) a) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply, hval]`. Both sides reduce to the same expression. Establish `hmemA : a ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K)))`. Rewrite using `[Ideal.mem_comap, hAR]`.

Conclude with `hc`. Rewrite `hmemA` using `[hPp]`. Then use the resulting hypothesis.
-/
theorem mem_of_forall_mem_prime (φ : A →+* B) (hφ : φ.Finite) (b : B) (p : Ideal A) [p.IsPrime]
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∈ Q) (k : ℕ) (hk : 1 ≤ k) (a : A)
    (ha : algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) : a ∈ p := by
  classical
  set K := FractionRing A with hKdef
  set χ := charK φ hφ K b with hχdef
  have hχm : χ.Monic := charK_monic φ hφ K b
  by_cases hkN : χ.natDegree < k
  · have h0 : algebraMap A K a = 0 := by
      rw [ha, coeff_reverse, revAt_eq_self_of_lt hkN]
      exact coeff_eq_zero_of_natDegree_lt hkN
    have ha0 : a = 0 := IsFractionRing.injective A K (h0.trans (map_zero _).symm)
    rw [ha0]
    exact p.zero_mem
  push Not at hkN
  obtain ⟨s, hs, n, hsn⟩ := exists_mul_pow_mem_map φ p b h
  obtain ⟨g, hgm, hgc, hg0⟩ := exists_monic_coeff_mem φ hφ p _ hsn
  have hbint : ∃ m : A[X], m.Monic ∧ eval₂ φ b m = 0 := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    exact Algebra.IsIntegral.isIntegral (R := A) b
  obtain ⟨m, hmm, hm0⟩ := hbint
  have hinj : Function.Injective (algebraMap A (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq A K (AlgebraicClosure K), RingHom.coe_comp]
    exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective A K)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := integralClosure A (AlgebraicClosure K)) p ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by
        rw [IsScalarTower.algebraMap_apply A (integralClosure A (AlgebraicClosure K))
          (AlgebraicClosure K), hx, map_zero, map_zero])
      rw [hx0]
      exact p.zero_mem)
  have hint : ∀ μ ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots,
      μ ∈ integralClosure A (AlgebraicClosure K) := by
    intro μ hμ
    have e := aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b m hm0 μ (mem_roots'.mp hμ).2
    exact (mem_integralClosure_iff A (AlgebraicClosure K)).mpr ⟨m, hmm, by rwa [aeval_def] at e⟩
  have hmemP : ∀ c : integralClosure A (AlgebraicClosure K),
      (χ.map (algebraMap K (AlgebraicClosure K))).IsRoot (c : AlgebraicClosure K) → c ∈ P := by
    intro c hc
    have e1 : eval₂ φ b (g.comp (C s * X ^ n)) = 0 := by
      rw [eval₂_comp]
      simpa using hg0
    have e2 := aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b _ e1 (c : AlgebraicClosure K) hc
    rw [aeval_comp] at e2
    simp only [map_mul, aeval_C, map_pow, aeval_X] at e2
    have e3 : aeval (algebraMap A (integralClosure A (AlgebraicClosure K)) s * c ^ n) g = 0 := by
      apply Subtype.val_injective
      rw [Polynomial.aeval_subalgebra_coe]
      simpa using e2
    have hw := mem_of_aeval_eq_zero P g hgm
      (fun i hi => by rw [← Ideal.mem_comap, hPp]; exact hgc i hi) _ e3
    rcases hP.mem_or_mem hw with h1 | h1
    · have h2 : s ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K))) := h1
      rw [hPp] at h2
      exact (hs h2).elim
    · exact hP.mem_of_pow_mem n h1
  obtain ⟨t, ht⟩ : ∃ t : Multiset (integralClosure A (AlgebraicClosure K)),
      t.map Subtype.val = (χ.map (algebraMap K (AlgebraicClosure K))).roots :=
    ⟨(χ.map (algebraMap K (AlgebraicClosure K))).roots.attach.map fun x => ⟨x.1, hint x.1 x.2⟩,
      by simp [Multiset.map_map]⟩
  have hsplit : (χ.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hprod : χ.map (algebraMap K (AlgebraicClosure K)) =
      ((t.map fun c => X - C c).prod).map (algebraMap (integralClosure A (AlgebraicClosure K))
        (AlgebraicClosure K)) := by
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic (hχm.map _), ← ht]
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro c _
    simp
  have hcard : Multiset.card t = χ.natDegree := by
    rw [← Multiset.card_map Subtype.val t, ht, ← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hi : χ.natDegree - k < Multiset.card t := by omega
  have hc := coeff_prod_X_sub_C_mem P t (fun c hct => hmemP c (by
      have hmem : (c : AlgebraicClosure K) ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots := by
        rw [← ht]
        exact Multiset.mem_map_of_mem _ hct
      exact (mem_roots'.mp hmem).2)) _ hi
  have hval : algebraMap A (AlgebraicClosure K) a =
      algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K)
        ((t.map fun c => X - C c).prod.coeff (χ.natDegree - k)) := by
    rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), ha, coeff_reverse, revAt_le hkN,
      ← Polynomial.coeff_map, hprod, Polynomial.coeff_map]
  have hAR : algebraMap A (integralClosure A (AlgebraicClosure K)) a =
      (t.map fun c => X - C c).prod.coeff (χ.natDegree - k) := by
    apply Subtype.val_injective
    change algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K)
      (algebraMap A (integralClosure A (AlgebraicClosure K)) a) = _
    rw [← IsScalarTower.algebraMap_apply, hval]
    rfl
  have hmemA : a ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K))) := by
    rw [Ideal.mem_comap, hAR]
    exact hc
  rwa [hPp] at hmemA

end Main

section Main

variable {A B : Type} [CommRing A] [IsDomain A] [CommRing B]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `h` to reduce the goal to its premises. Distinguish the cases in `hex : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k`. Conclude with `mem_of_forall_mem_prime φ hφ b p hne k hk _ (algebraMap_normCoeff φ hφ b k hex)`.

Rewrite using `[normCoeff, dif_neg hex]`. Conclude with `p.zero_mem`.
-/
theorem exists_prime_comap_eq_notMem (φ : A →+* B) (hφ : φ.Finite) (b : B) (p : Ideal A) [p.IsPrime] (k : ℕ)
    (hk : 1 ≤ k) (h : normCoeff φ hφ b k ∉ p) : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = p ∧ b ∉ Q := by
  by_contra hne
  push Not at hne
  apply h
  by_cases hex : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k
  · exact mem_of_forall_mem_prime φ hφ b p hne k hk _ (algebraMap_normCoeff φ hφ b k hex)
  · rw [normCoeff, dif_neg hex]
    exact p.zero_mem

end Main

section Geometry

open AlgebraicGeometry CategoryTheory

/- English proof (translation)
Introduce `X Y f _ V hV _ _ τ x k hxV hk hx`. Establish `hU : IsAffineOpen (f ⁻¹ᵁ V)` using `hV.preimage f`. Use `set px := hV.primeIdealOf ⟨x, hxV⟩ with hpx`. Establish `hfx : hV.fromSpec px = x` using `hV.fromSpec_primeIdealOf ⟨x, hxV⟩`. Establish `hnot : normCoeff (f.app V).hom (f.finite_app V hV) τ k ∉ px.asIdeal`.

Establish `h1 : hV.fromSpec px ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)`. Rewrite using `[hfx]`. Conclude with `hx`. Establish `h2 : px ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)` using `h1`. Rewrite `h2` using `[hV.fromSpec_preimage_basicOpen]`.

Conclude with `(PrimeSpectrum.mem_basicOpen _ _).mp h2`. Take `⟨Q, hQ, hQp, hτQ⟩` from `exists_prime_comap_eq_notMem (f.app V).hom (f.finite_app V hV) τ px.asIdeal k hk hnot`. Set `q : Spec Γ(Y, f ⁻¹ᵁ V)` to `(⟨Q, hQ⟩ : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V))`. Use `⟨hU.fromSpec q, ?_, ?_⟩` and prove the remaining obligations. Establish `h3 : q ∈ PrimeSpectrum.basicOpen τ` using `(PrimeSpectrum.mem_basicOpen _ _).mpr hτQ`.

Rewrite `h3` using `[← hU.fromSpec_preimage_basicOpen]`. Conclude with `h3`. Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl`. Establish `e2 : f (hU.fromSpec q) = hV.fromSpec (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) q)`. Rewrite using `[← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]`.

Rewrite using `[e2, Scheme.Hom.appLE_eq_app, Spec.map_apply]`. Establish `hq : PrimeSpectrum.comap (f.app V).hom q = px` using `PrimeSpectrum.ext hQp`. Rewrite using `[hq, hfx]`.
-/
theorem exists_mem_basicOpen_of_mem_basicOpen_normCoeff : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V))
    (x : X) (k : ℕ), x ∈ V → 1 ≤ k →
    x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) → ∃ y ∈ Y.basicOpen τ, f y = x := by
  intro X Y f _ V hV _ _ τ x k hxV hk hx
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  set px := hV.primeIdealOf ⟨x, hxV⟩ with hpx
  have hfx : hV.fromSpec px = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hnot : normCoeff (f.app V).hom (f.finite_app V hV) τ k ∉ px.asIdeal := by
    have h1 : hV.fromSpec px ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
      rw [hfx]
      exact hx
    have h2 : px ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := h1
    rw [hV.fromSpec_preimage_basicOpen] at h2
    exact (PrimeSpectrum.mem_basicOpen _ _).mp h2
  obtain ⟨Q, hQ, hQp, hτQ⟩ :=
    exists_prime_comap_eq_notMem (f.app V).hom (f.finite_app V hV) τ px.asIdeal k hk hnot
  let q : Spec Γ(Y, f ⁻¹ᵁ V) := (⟨Q, hQ⟩ : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V))
  refine ⟨hU.fromSpec q, ?_, ?_⟩
  · have h3 : q ∈ PrimeSpectrum.basicOpen τ := (PrimeSpectrum.mem_basicOpen _ _).mpr hτQ
    rw [← hU.fromSpec_preimage_basicOpen] at h3
    exact h3
  · have e := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
    have e2 : f (hU.fromSpec q) = hV.fromSpec (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) q) := by
      rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]
    rw [e2, Scheme.Hom.appLE_eq_app, Spec.map_apply]
    have hq : PrimeSpectrum.comap (f.app V).hom q = px := PrimeSpectrum.ext hQp
    rw [hq, hfx]

end Geometry

end GlobalTheory.NormalDescent
