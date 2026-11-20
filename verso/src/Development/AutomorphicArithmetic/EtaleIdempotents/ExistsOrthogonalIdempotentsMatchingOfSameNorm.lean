import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PIdemCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchPart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatching
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGaussLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLinFactor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPermMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => exact ⟨RingHom.id _, fun x => by simp⟩`. Consider the case `succ a ih`. Take `⟨φ, hφ⟩` from `ih`. Use `⟨A.frob.comp φ, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, hφ, pow_succ l a, pow_mul]`. Both sides reduce to the same expression.
-/
private theorem powHom_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) :
    ∃ φ : A.A →+* A.A, ∀ x, φ x = x ^ l ^ a := by
  induction a with
  | zero => exact ⟨RingHom.id _, fun x => by simp⟩
  | succ a ih =>
    obtain ⟨φ, hφ⟩ := ih
    refine ⟨A.frob.comp φ, fun x => ?_⟩
    rw [RingHom.comp_apply, hφ, pow_succ l a, pow_mul]
    rfl

/- English proof (translation)
Proceed by induction on `a generalizing y with`. Consider the case `zero => exact ⟨y, by simp⟩`. Consider the case `succ a ih`. Take `⟨z, hz⟩` from `(A.perf.bijective_frobenius).2 y`. Take `⟨w, hw⟩` from `ih z`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ l a, pow_mul, hw]`. Conclude with `hz`.
-/
private theorem root_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) (y : A.A) :
    ∃ w : A.A, w ^ l ^ a = y := by
  induction a generalizing y with
  | zero => exact ⟨y, by simp⟩
  | succ a ih =>
    obtain ⟨z, hz⟩ := (A.perf.bijective_frobenius).2 y
    obtain ⟨w, hw⟩ := ih z
    refine ⟨w, ?_⟩
    rw [pow_succ l a, pow_mul, hw]
    exact hz

/- English proof (translation)
Introduce `l _ A hA a ι I I' _ _ _ _ _ N hI hI' hN c c' h`. Establish `hq : 0 < l ^ a` using `pow_pos (Fact.out : l.Prime).pos a`. Take `⟨φ, hφ⟩` from `powHom_exists A a`. Take `⟨w, hw⟩` from `root_exists A a A.pi`. Establish `hwn : w ∈ nonZeroDivisors A.A`.

Establish `h1 : w ^ (l ^ a - 1) * w ∈ nonZeroDivisors A.A`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq, hw]`. Conclude with `A.tf`. Conclude with `(mul_mem_nonZeroDivisors.1 h1).2`. Establish `hv : ValLike w`.

Introduce and unpack `f g ⟨m, hm⟩`. Take `⟨e, he, h1, h2⟩` from `hA.2 f g ⟨m, by`. Rewrite using `[← hw, ← pow_mul, mul_comm, pow_mul]`. Conclude with `Ideal.pow_mem_of_mem _ hm _ hq⟩`. Conclude with `⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩`.

Use `choose u hu using fun i k => Ideal.Quotient.mk_surjective (c i k)`. Use `choose u' hu' using fun i k => Ideal.Quotient.mk_surjective (c' i k)`. Establish `hdvd : w ^ (N + 1) ^ N ∣ A.pi`. Rewrite using `[← hw]`. Conclude with `pow_dvd_pow w hN`.

Establish `hle : Ideal.span {A.pi} ≤ Ideal.span {w ^ (N + 1) ^ N}` using `Ideal.span_singleton_le_span_singleton.2 hdvd`. Establish `hsn : SameNorm (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u)) (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u'))`. Establish `h2` using `(snBasic_of (Qb A) ι).1 (A.A ⧸ Ideal.span {w ^ (N + 1) ^ N}) (Ideal.Quotient.factor hle) _ _ h`. Establish `e1 : ∀ {J : Type} [Fintype J] (v : J → ι → A.A) (d : J → ι → Qb A), (∀ i k, Ideal.Quotient.mk _ (v i k) = d i k) → (Finset.univ.val.map d).map (fun x k => Ideal.Quotient.factor hle (x k)) = redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map v)`. Introduce `J _ v d hd`.

Rewrite using `[redMod, Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, ← hd i k]`. Conclude with `Ideal.Quotient.factor_mk hle _`.

Rewrite using `[← e1 u c hu, ← e1 u' c' hu']`. Conclude with `h2`. Establish `MV : MatchingVal` using `matchVal_of idemCover_of valLocal_of (matchPart_of snBasic_of (matching_of snBasic_of (matchStep_of gaussLin_of snBasic_of linFactor_of)) permMap_of)`. Take `⟨e, hce, he⟩` from `MV A.A w hwn hv ι I I' N hI hI' u u' hsn`. Use `⟨e, hce, fun σ i k => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht⟩` from `he σ i k`. Establish `hid : e σ ^ l ^ a = e σ`. Use `(hce.idem σ).pow_succ_eq (l ^ a - 1)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hq]`. Then use the resulting hypothesis. Establish `key : e σ * (u i k ^ l ^ a - u' (σ i) k ^ l ^ a) = A.pi * t ^ l ^ a`.

Establish `h3` using `congrArg φ ht`. Rewrite `h3` using `[map_mul, map_sub, map_mul, hφ, hφ, hφ, hφ, hφ, hid, hw]`. Conclude with `h3`. Rewrite using `[← hu i k, ← hu' (σ i) k, ← map_pow, ← map_pow, ← map_mul, ← map_mul]`. Use `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨t ^ l ^ a, ?_⟩)` and prove the remaining obligations.

Rewrite using `[← mul_sub, key]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.exists_orthogonalIdempotents_matching_of_sameNorm :
    ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ (a : ℕ) {ι I I' : Type} [Fintype ι] [Fintype I] [Fintype I']
        [DecidableEq I] [DecidableEq I'] (N : ℕ), Fintype.card I = N → Fintype.card I' = N →
        (N + 1) ^ N ≤ l ^ a → ∀ (c : I → ι → Qb A) (c' : I' → ι → Qb A),
        SameNorm (Finset.univ.val.map c) (Finset.univ.val.map c') →
        ∃ e : (I ≃ I') → A.A, CompleteOrthogonalIdempotents e ∧ ∀ σ i k,
          (Ideal.Quotient.mk _ (e σ) : Qb A) * c i k ^ l ^ a = Ideal.Quotient.mk _ (e σ) * c' (σ i) k ^ l ^ a := by
  intro l _ A hA a ι I I' _ _ _ _ _ N hI hI' hN c c' h
  have hq : 0 < l ^ a := pow_pos (Fact.out : l.Prime).pos a
  obtain ⟨φ, hφ⟩ := powHom_exists A a
  obtain ⟨w, hw⟩ := root_exists A a A.pi
  have hwn : w ∈ nonZeroDivisors A.A := by
    have h1 : w ^ (l ^ a - 1) * w ∈ nonZeroDivisors A.A := by
      rw [← pow_succ, Nat.sub_add_cancel hq, hw]
      exact A.tf
    exact (mul_mem_nonZeroDivisors.1 h1).2
  have hv : ValLike w := by
    rintro f g ⟨m, hm⟩
    obtain ⟨e, he, h1, h2⟩ := hA.2 f g ⟨m, by
      rw [← hw, ← pow_mul, mul_comm, pow_mul]
      exact Ideal.pow_mem_of_mem _ hm _ hq⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩
  choose u hu using fun i k => Ideal.Quotient.mk_surjective (c i k)
  choose u' hu' using fun i k => Ideal.Quotient.mk_surjective (c' i k)
  have hdvd : w ^ (N + 1) ^ N ∣ A.pi := by
    rw [← hw]
    exact pow_dvd_pow w hN
  have hle : Ideal.span {A.pi} ≤ Ideal.span {w ^ (N + 1) ^ N} :=
    Ideal.span_singleton_le_span_singleton.2 hdvd
  have hsn : SameNorm (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u))
      (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u')) := by
    have h2 := (snBasic_of (Qb A) ι).1 (A.A ⧸ Ideal.span {w ^ (N + 1) ^ N}) (Ideal.Quotient.factor hle) _ _ h
    have e1 : ∀ {J : Type} [Fintype J] (v : J → ι → A.A) (d : J → ι → Qb A),
        (∀ i k, Ideal.Quotient.mk _ (v i k) = d i k) →
        (Finset.univ.val.map d).map (fun x k => Ideal.Quotient.factor hle (x k)) =
          redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map v) := by
      intro J _ v d hd
      rw [redMod, Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      funext k
      simp only [Function.comp_apply, ← hd i k]
      exact Ideal.Quotient.factor_mk hle _
    rw [← e1 u c hu, ← e1 u' c' hu']
    exact h2
  have MV : MatchingVal := matchVal_of idemCover_of valLocal_of
    (matchPart_of snBasic_of (matching_of snBasic_of (matchStep_of gaussLin_of snBasic_of linFactor_of)) permMap_of)
  obtain ⟨e, hce, he⟩ := MV A.A w hwn hv ι I I' N hI hI' u u' hsn
  refine ⟨e, hce, fun σ i k => ?_⟩
  obtain ⟨t, ht⟩ := he σ i k
  have hid : e σ ^ l ^ a = e σ := by
    have := (hce.idem σ).pow_succ_eq (l ^ a - 1)
    rwa [Nat.sub_add_cancel hq] at this
  have key : e σ * (u i k ^ l ^ a - u' (σ i) k ^ l ^ a) = A.pi * t ^ l ^ a := by
    have h3 := congrArg φ ht
    rw [map_mul, map_sub, map_mul, hφ, hφ, hφ, hφ, hφ, hid, hw] at h3
    exact h3
  rw [← hu i k, ← hu' (σ i) k, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨t ^ l ^ a, ?_⟩)
  rw [← mul_sub, key]
  rfl
