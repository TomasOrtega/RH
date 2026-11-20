import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingKrullDimQuotientMvPolynomialEqNat

namespace GlobalTheory

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Forms

variable {σ ι R : Type*} [CommRing R]

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [coeff_map, coeff_homogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_homogeneousComponent_eq {R' : Type*} [CommRing R'] (φ : R →+* R') (n : ℕ)
    (p : MvPolynomial σ R) :
    map φ (homogeneousComponent n p) = homogeneousComponent n (map φ p) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨p, rfl⟩` from `map_surjective φ hφ q`. Conclude with `⟨homogeneousComponent n p, homogeneousComponent_isHomogeneous _ _, by`. Rewrite using `[map_homogeneousComponent_eq, homogeneousComponent_eq_self hq]⟩`.
-/
theorem exists_isHomogeneous_map_eq {R' : Type*} [CommRing R'] {φ : R →+* R'}
    (hφ : Function.Surjective φ) {n : ℕ} {q : MvPolynomial σ R'} (hq : q.IsHomogeneous n) :
    ∃ p : MvPolynomial σ R, p.IsHomogeneous n ∧ map φ p = q := by
  obtain ⟨p, rfl⟩ := map_surjective φ hφ q
  exact ⟨homogeneousComponent n p, homogeneousComponent_isHomogeneous _ _, by
    rw [map_homogeneousComponent_eq, homogeneousComponent_eq_self hq]⟩

/- English proof (translation)
Introduce `n q hq`. Take `⟨p, hp, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ (map_surjective φ hφ)).mp hq`. Establish `h1 : ((DirectSum.decompose (homogeneousSubmodule σ R') (map φ p) n : _) : MvPolynomial σ R') = homogeneousComponent n (map φ p)` using `decomposition.decompose'_apply _ _`. Rewrite using `[h1, ← map_homogeneousComponent_eq]`. Conclude with `Ideal.mem_map_of_mem _ (homogeneousComponent_mem_of_mem hI hp n)`.
-/
theorem isHomogeneous_map_of_surjective {R' : Type*} [CommRing R'] {φ : R →+* R'}
    (hφ : Function.Surjective φ) {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    (I.map (map φ)).IsHomogeneous (homogeneousSubmodule σ R') := by
  intro n q hq
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (map_surjective φ hφ)).mp hq
  have h1 : ((DirectSum.decompose (homogeneousSubmodule σ R') (map φ p) n : _) :
      MvPolynomial σ R') = homogeneousComponent n (map φ p) := decomposition.decompose'_apply _ _
  rw [h1, ← map_homogeneousComponent_eq]
  exact Ideal.mem_map_of_mem _ (homogeneousComponent_mem_of_mem hI hp n)

/- English proof (translation)
Rewrite using `[p.as_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `h1 : monomial m (coeff m p) = coeff m p • monomial m (1 : R)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1]`.

Use `Submodule.smul_mem_smul (hJ m) (hQ m ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `(mem_support_iff.mp hm) (hp.coeff_eq_zero hne)`.
-/
theorem mem_smul_of_isHomogeneous_of_coeff_mem {J : Ideal R} {Q : Submodule R (MvPolynomial σ R)}
    {n : ℕ} (hQ : ∀ m : σ →₀ ℕ, m.degree = n → monomial m (1 : R) ∈ Q) {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (hJ : ∀ m, p.coeff m ∈ J) : p ∈ J • Q := by
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have h1 : monomial m (coeff m p) = coeff m p • monomial m (1 : R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1]
  refine Submodule.smul_mem_smul (hJ m) (hQ m ?_)
  by_contra hne
  exact (mem_support_iff.mp hm) (hp.coeff_eq_zero hne)

variable [Fintype ι]

def formCombinations (I : Ideal (MvPolynomial σ R)) (F : ι → MvPolynomial σ R) (n : ℕ) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∃ G : ι → MvPolynomial σ R, (∀ i, (G i).IsHomogeneous n) ∧
    p - ∑ i, F i * G i ∈ I}
  zero_mem' := ⟨0, fun _ => isHomogeneous_zero _ _ _, by simp⟩
  add_mem' := by
    rintro p q ⟨G, hG, hp⟩ ⟨G', hG', hq⟩
    refine ⟨G + G', fun i => (hG i).add (hG' i), ?_⟩
    convert I.add_mem hp hq using 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  smul_mem' := by
    rintro c p ⟨G, hG, hp⟩
    refine ⟨fun i => C c * G i, fun i => by simpa using (isHomogeneous_C σ c).mul (hG i), ?_⟩
    convert I.mul_mem_left (C c) hp using 1
    simp only [smul_eq_C_mul, mul_sub, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hd`. Establish `hp' : p ∈ homogeneousSubmodule σ R d₀ * homogeneousSubmodule σ R c`. Rewrite using `[← homogeneousSubmodule_one_pow R d₀, ← homogeneousSubmodule_one_pow R c, ← pow_add, homogeneousSubmodule_one_pow]` and apply the resulting hypothesis. Use `clear hp`. Proceed by induction on `hp' using Submodule.mul_induction_on' with`.

Consider the case `mem_mul_mem x hx y hy`. Take `⟨G, hG, hπ⟩` from `h x hx`. Use `⟨fun i => G i * y, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(hG i).mul hy` as an intermediate fact. Rewrite `this` using `[show d₀ - e + c = d₀ + c - e by omega]`. Then use the resulting hypothesis.

Use `I.mul_mem_right y hπ using 1` and compare the differences between its conclusion and the goal. Simplify using `only [sub_mul, Finset.sum_mul, mul_assoc, smul_mul_assoc]`. Consider the case `add x _ y _ hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem smul_mem_formCombinations_of_le {I : Ideal (MvPolynomial σ R)}
    {F : ι → MvPolynomial σ R} {a : R} {e d₀ : ℕ} (he : e ≤ d₀)
    (h : ∀ p : MvPolynomial σ R, p.IsHomogeneous d₀ → a • p ∈ formCombinations I F (d₀ - e))
    {d : ℕ} (hd : d₀ ≤ d) (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    a • p ∈ formCombinations I F (d - e) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hp' : p ∈ homogeneousSubmodule σ R d₀ * homogeneousSubmodule σ R c := by
    rwa [← homogeneousSubmodule_one_pow R d₀, ← homogeneousSubmodule_one_pow R c, ← pow_add,
      homogeneousSubmodule_one_pow]
  clear hp
  induction hp' using Submodule.mul_induction_on' with
  | mem_mul_mem x hx y hy =>
    obtain ⟨G, hG, hπ⟩ := h x hx
    refine ⟨fun i => G i * y, fun i => ?_, ?_⟩
    · have := (hG i).mul hy
      rwa [show d₀ - e + c = d₀ + c - e by omega] at this
    · convert I.mul_mem_right y hπ using 1
      simp only [sub_mul, Finset.sum_mul, mul_assoc, smul_mul_assoc]
  | add x _ y _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

/- English proof (translation)
Establish `hs : Function.Surjective (Ideal.Quotient.mk J)` using `Ideal.Quotient.mk_surjective`. Establish `key : homogeneousSubmodule σ R (e + n) ≤ formCombinations I F n ⊔ J • homogeneousSubmodule σ R (e + n)`. Introduce `p hp`. Establish `hp' : p.IsHomogeneous (e + n)` using `hp`. Take `⟨g, hg, hgI⟩` from `h _ (hp'.map (Ideal.Quotient.mk J))`.

Use `choose G hG hGg using fun i => exists_isHomogeneous_map_eq hs (hg i)`. Take `⟨u, hu, hueq⟩` from `(Ideal.mem_map_iff_of_surjective _ (map_surjective _ hs)).mp hgI`. Use `set r := p - ∑ i, F i * G i with hr`. Establish `hrh : r.IsHomogeneous (e + n)` using `hp'.sub (IsHomogeneous.sum _ _ _ fun i _ => (hF i).mul (hG i))`. Establish `h0 : map (Ideal.Quotient.mk J) (r - u) = 0`.

Rewrite using `[map_sub, hueq, hr, map_sub, map_sum]`. Simplify using `only [map_mul, hGg, sub_self]`. Establish `h1 : r - homogeneousComponent (e + n) u ∈ J • homogeneousSubmodule σ R (e + n)`. Use `mem_smul_of_isHomogeneous_of_coeff_mem (n := e + n) (fun m hm => isHomogeneous_monomial _ hm) (hrh.sub (homogeneousComponent_isHomogeneous _ _)) fun m => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, ← homogeneousComponent_eq_self hrh, ← map_sub, map_homogeneousComponent_eq, h0]`.

Simplify using the standard rewrite rules. Establish `h2 : p - (r - homogeneousComponent (e + n) u) ∈ formCombinations I F n`. Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Use `homogeneousComponent_mem_of_mem hI hu (e + n) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hr]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `Submodule.add_mem_sup h2 h1`. Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨a, ha, hle⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (homogeneousSubmodule_fg σ R (e + n)) le_rfl key`. Conclude with `⟨a, ha, fun p hp => hle (Submodule.smul_mem_pointwise_smul p a _ hp)⟩`.
-/
theorem exists_smul_mem_formCombinations [Finite σ] {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) (J : Ideal R)
    {F : ι → MvPolynomial σ R} {e n : ℕ} (hF : ∀ i, (F i).IsHomogeneous e)
    (h : ∀ q : MvPolynomial σ (R ⧸ J), q.IsHomogeneous (e + n) →
      q ∈ formCombinations (I.map (map (Ideal.Quotient.mk J)))
        (fun i => map (Ideal.Quotient.mk J) (F i)) n) :
    ∃ a : R, a - 1 ∈ J ∧ ∀ p : MvPolynomial σ R, p.IsHomogeneous (e + n) →
      a • p ∈ formCombinations I F n := by
  have hs : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have key : homogeneousSubmodule σ R (e + n) ≤
      formCombinations I F n ⊔ J • homogeneousSubmodule σ R (e + n) := by
    intro p hp
    have hp' : p.IsHomogeneous (e + n) := hp
    obtain ⟨g, hg, hgI⟩ := h _ (hp'.map (Ideal.Quotient.mk J))
    choose G hG hGg using fun i => exists_isHomogeneous_map_eq hs (hg i)
    obtain ⟨u, hu, hueq⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (map_surjective _ hs)).mp hgI
    set r := p - ∑ i, F i * G i with hr
    have hrh : r.IsHomogeneous (e + n) :=
      hp'.sub (IsHomogeneous.sum _ _ _ fun i _ => (hF i).mul (hG i))
    have h0 : map (Ideal.Quotient.mk J) (r - u) = 0 := by
      rw [map_sub, hueq, hr, map_sub, map_sum]
      simp only [map_mul, hGg, sub_self]
    have h1 : r - homogeneousComponent (e + n) u ∈ J • homogeneousSubmodule σ R (e + n) := by
      refine mem_smul_of_isHomogeneous_of_coeff_mem (n := e + n)
        (fun m hm => isHomogeneous_monomial _ hm)
        (hrh.sub (homogeneousComponent_isHomogeneous _ _)) fun m => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map,
        ← homogeneousComponent_eq_self hrh, ← map_sub, map_homogeneousComponent_eq, h0]
      simp
    have h2 : p - (r - homogeneousComponent (e + n) u) ∈ formCombinations I F n := by
      refine ⟨G, hG, ?_⟩
      convert homogeneousComponent_mem_of_mem hI hu (e + n) using 1
      rw [hr]; ring
    have h3 := Submodule.add_mem_sup h2 h1
    rwa [sub_add_cancel] at h3
  obtain ⟨a, ha, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (homogeneousSubmodule_fg σ R (e + n)) le_rfl key
  exact ⟨a, ha, fun p hp => hle (Submodule.smul_mem_pointwise_smul p a _ hp)⟩

/- English proof (translation)
Use `finite_aeval_of_forms_eq_sum π' hπ' _ he hed fun d hd p hp => ?_` and prove the remaining obligations. Establish `h1 : p ∈ (⊤ : Ideal R') • formCombinations (RingHom.ker π') (fun i => map (algebraMap R R') (F i)) (d - e)`. Use `mem_smul_of_isHomogeneous_of_coeff_mem (fun m hm => ?_) hp fun _ => Submodule.mem_top` and prove the remaining obligations. Take `⟨G, hG, hGI⟩` from `h d hd _ (isHomogeneous_monomial (1 : R) hm)`. Rewrite using `[← Submodule.smul_mem_iff_of_isUnit _ ha]`.

Use `⟨fun i => map (algebraMap R R') (G i), fun i => (hG i).map _, ?_⟩` and prove the remaining obligations. Establish `h2` using `hI _ hGI`. Rewrite using `[RingHom.mem_ker, ← h2, smul_eq_C_mul, smul_eq_C_mul]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[Submodule.top_smul]`.

Take `⟨G, hG, hGI⟩` from `h1`. Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Rewrite `hGI` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Simplify using `[hGI]`.
-/
theorem finite_aeval_of_smul_mem_formCombinations [Finite σ] {I : Ideal (MvPolynomial σ R)}
    {F : ι → MvPolynomial σ R} {a : R} {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      a • p ∈ formCombinations I F (d - e))
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S']
    (ha : IsUnit (algebraMap R R' a)) (π' : MvPolynomial σ R' →ₐ[R'] S')
    (hπ' : Function.Surjective π') (hI : ∀ p ∈ I, π' (map (algebraMap R R') p) = 0) :
    (aeval (fun i => π' (map (algebraMap R R') (F i))) : MvPolynomial ι R' →ₐ[R'] S').Finite := by
  refine finite_aeval_of_forms_eq_sum π' hπ' _ he hed fun d hd p hp => ?_
  have h1 : p ∈ (⊤ : Ideal R') • formCombinations (RingHom.ker π')
      (fun i => map (algebraMap R R') (F i)) (d - e) := by
    refine mem_smul_of_isHomogeneous_of_coeff_mem (fun m hm => ?_) hp fun _ => Submodule.mem_top
    obtain ⟨G, hG, hGI⟩ := h d hd _ (isHomogeneous_monomial (1 : R) hm)
    rw [← Submodule.smul_mem_iff_of_isUnit _ ha]
    refine ⟨fun i => map (algebraMap R R') (G i), fun i => (hG i).map _, ?_⟩
    have h2 := hI _ hGI
    rw [RingHom.mem_ker, ← h2, smul_eq_C_mul, smul_eq_C_mul]
    simp
  rw [Submodule.top_smul] at h1
  obtain ⟨G, hG, hGI⟩ := h1
  refine ⟨G, hG, ?_⟩
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hGI
  simp [hGI]

end Forms

section Independence

/- English proof (translation)
Set `K` to `FractionRing o`. Take `⟨j, hj⟩` from `support_nonempty.mpr hG`. Take `⟨t, ht, m, hm, hmJ⟩` from `Ideal.exist_integer_multiples_notMem hJ G.support (fun m => algebraMap o K (G.coeff m)) hj (by simpa using mem_support_iff.mp hj)`. Take `⟨u, b, hb, rfl⟩` from `IsFractionRing.div_surjective o t`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hb0' : algebraMap o K b ≠ 0` using `by simpa using hb0`. Use `choose! c hc using ht`. Establish `hcoeff : ∀ m, (∑ m ∈ G.support, monomial m (c m)).coeff m = if m ∈ G.support then c m else 0`. Introduce `m`. Simplify using `[coeff_sum, coeff_monomial]`.

Use `⟨b, u, ∑ m ∈ G.support, monomial m (c m), hb0, ?_, m, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[coeff_C_mul, coeff_C_mul, hcoeff]`. Use `split_ifs with h`. Apply `IsFractionRing.injective o K` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, hc m h, ← mul_assoc, mul_div_cancel₀ _ hb0']`. Rewrite using `[notMem_support_iff.mp h, mul_zero, mul_zero]`. Rewrite using `[hcoeff, if_pos hm]`. Introduce `h`. Conclude with `hmJ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨c m, h, hc m hm⟩)`.
-/
theorem exists_C_mul_eq_C_mul_coeff_notMem {ι o : Type*} [CommRing o] [IsDedekindDomain o]
    {J : Ideal o} (hJ : J ≠ ⊤) {G : MvPolynomial ι o} (hG : G ≠ 0) :
    ∃ (b u : o) (G' : MvPolynomial ι o), b ≠ 0 ∧ C b * G' = C u * G ∧ ∃ m, G'.coeff m ∉ J := by
  classical
  let K := FractionRing o
  obtain ⟨j, hj⟩ := support_nonempty.mpr hG
  obtain ⟨t, ht, m, hm, hmJ⟩ := Ideal.exist_integer_multiples_notMem hJ G.support
    (fun m => algebraMap o K (G.coeff m)) hj
    (by simpa using mem_support_iff.mp hj)
  obtain ⟨u, b, hb, rfl⟩ := IsFractionRing.div_surjective o t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb0' : algebraMap o K b ≠ 0 := by simpa using hb0
  choose! c hc using ht
  have hcoeff : ∀ m, (∑ m ∈ G.support, monomial m (c m)).coeff m =
      if m ∈ G.support then c m else 0 := by
    intro m
    simp [coeff_sum, coeff_monomial]
  refine ⟨b, u, ∑ m ∈ G.support, monomial m (c m), hb0, ?_, m, ?_⟩
  · ext m
    rw [coeff_C_mul, coeff_C_mul, hcoeff]
    split_ifs with h
    · apply IsFractionRing.injective o K
      rw [map_mul, map_mul, hc m h, ← mul_assoc, mul_div_cancel₀ _ hb0']
    · rw [notMem_support_iff.mp h, mul_zero, mul_zero]
  · rw [hcoeff, if_pos hm]
    intro h
    exact hmJ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨c m, h, hc m hm⟩)

/- English proof (translation)
Rewrite `hf`, the goal using `[algebraicIndependent_iff]`. Introduce `G hG`. Assume the negation of the conclusion as `hne`. Take `⟨b, u, G', hb, hbu, m, hm⟩` from `exists_C_mul_eq_C_mul_coeff_notMem hJ hne`. Establish `h1 : aeval f G' = 0`.

Establish `h2` using `congrArg (aeval f : MvPolynomial ι o →ₐ[o] S) hbu`. Rewrite `h2` using `[map_mul, map_mul, hG, mul_zero, aeval_C, ← Algebra.smul_def]`. Conclude with `(smul_eq_zero.mp h2).resolve_left hb`. Establish `h3 : (aeval (fun i => ψ (f i)) : MvPolynomial ι (o ⧸ J) →ₐ[o ⧸ J] T).toRingHom.comp (map (Ideal.Quotient.mk J)) = ψ.comp (aeval f : MvPolynomial ι o →ₐ[o] S).toRingHom`. Apply the tactic sequence `ext r <;> simp [hψ]`.

Establish `h4` using `hf (map (Ideal.Quotient.mk J) G') (by`. Use `RingHom.congr_fun h3 G'` as an intermediate fact. Simplify `this)` using `[h1]`. Apply `hm` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h4, coeff_zero]`.
-/
theorem algebraicIndependent_of_quotient {ι o S T : Type*} [CommRing o] [IsDedekindDomain o]
    [CommRing S] [Algebra o S] [Module.IsTorsionFree o S] {J : Ideal o} (hJ : J ≠ ⊤)
    [CommRing T] [Algebra (o ⧸ J) T] (ψ : S →+* T)
    (hψ : ∀ r : o, ψ (algebraMap o S r) = algebraMap (o ⧸ J) T (Ideal.Quotient.mk J r))
    {f : ι → S} (hf : AlgebraicIndependent (o ⧸ J) (fun i => ψ (f i))) :
    AlgebraicIndependent o f := by
  rw [algebraicIndependent_iff] at hf ⊢
  intro G hG
  by_contra hne
  obtain ⟨b, u, G', hb, hbu, m, hm⟩ := exists_C_mul_eq_C_mul_coeff_notMem hJ hne
  have h1 : aeval f G' = 0 := by
    have h2 := congrArg (aeval f : MvPolynomial ι o →ₐ[o] S) hbu
    rw [map_mul, map_mul, hG, mul_zero, aeval_C, ← Algebra.smul_def] at h2
    exact (smul_eq_zero.mp h2).resolve_left hb
  have h3 : (aeval (fun i => ψ (f i)) : MvPolynomial ι (o ⧸ J) →ₐ[o ⧸ J] T).toRingHom.comp
      (map (Ideal.Quotient.mk J)) = ψ.comp (aeval f : MvPolynomial ι o →ₐ[o] S).toRingHom := by
    ext r <;> simp [hψ]
  have h4 := hf (map (Ideal.Quotient.mk J) G') (by
    have := RingHom.congr_fun h3 G'
    simpa [h1] using this)
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h4, coeff_zero]

end Independence

section Main

variable {σ : Type*} {o : Type*} [CommRing o]

/- English proof (translation)
Establish `hs : Function.Surjective (map (σ` using `σ) (Ideal.Quotient.mk J)) := map_surjective _ Ideal.Quotient.mk_surjective`. Establish `h1 : J.map (algebraMap o (MvPolynomial σ o ⧸ I)) = (J.map (C : o →+* MvPolynomial σ o)).map (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.map_map]`. Both sides reduce to the same expression. Establish `h2 : RingHom.ker ((Ideal.Quotient.mk (I.map (map (Ideal.Quotient.mk J)))).comp (map (σ` using `σ) (Ideal.Quotient.mk J))) = I ⊔ J.map (C : o →+* MvPolynomial σ o) := by`.

Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker]`. Conclude with `⟨(Ideal.quotEquivOfEq h1).trans <| (DoubleQuot.quotQuotEquivQuotSup I _).trans <| (Ideal.quotEquivOfEq h2.symm).trans <| RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hs)⟩`.
-/
theorem nonempty_quotient_map_algebraMap_ringEquiv (I : Ideal (MvPolynomial σ o)) (J : Ideal o) :
    Nonempty (((MvPolynomial σ o ⧸ I) ⧸ J.map (algebraMap o (MvPolynomial σ o ⧸ I))) ≃+*
      (MvPolynomial σ (o ⧸ J) ⧸ I.map (map (Ideal.Quotient.mk J)))) := by
  have hs : Function.Surjective (map (σ := σ) (Ideal.Quotient.mk J)) :=
    map_surjective _ Ideal.Quotient.mk_surjective
  have h1 : J.map (algebraMap o (MvPolynomial σ o ⧸ I)) =
      (J.map (C : o →+* MvPolynomial σ o)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_map]; rfl
  have h2 : RingHom.ker ((Ideal.Quotient.mk (I.map (map (Ideal.Quotient.mk J)))).comp
      (map (σ := σ) (Ideal.Quotient.mk J))) = I ⊔ J.map (C : o →+* MvPolynomial σ o) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hs,
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker]
  exact ⟨(Ideal.quotEquivOfEq h1).trans <| (DoubleQuot.quotQuotEquivQuotSup I _).trans <|
    (Ideal.quotEquivOfEq h2.symm).trans <|
      RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hs)⟩

/- English proof (translation)
Use `haveI := Ideal.Quotient.nontrivial_iff.mpr hI'`. Establish `h0 : ∀ p ∈ I, constantCoeff p = 0`. Introduce `p hp`. Establish `h1` using `homogeneousComponent_mem_of_mem hI hp 0`. Rewrite `h1` using `[homogeneousComponent_zero, ← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `h2 : coeff 0 p • (1 : MvPolynomial σ o ⧸ I) = 0`. Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `h1`. Conclude with `(smul_eq_zero.mp h2).resolve_right one_ne_zero`. Introduce `h`.

Apply `hJ` to reduce the goal to its premises. Establish `h3` using `congrArg (Ideal.map (Ideal.Quotient.lift I constantCoeff h0)) h`. Rewrite `h3` using `[Ideal.map_map, Ideal.map_top]`. Establish `h4 : (Ideal.Quotient.lift I constantCoeff h0).comp (algebraMap o (MvPolynomial σ o ⧸ I)) = RingHom.id o`. Use extensionality with `r`.

Conclude with `constantCoeff_C σ r`. Rewrite `h3` using `[h4, Ideal.map_id]`. Then use the resulting hypothesis.
-/
theorem map_algebraMap_quotient_ne_top [IsDomain o] (I : Ideal (MvPolynomial σ o))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ o))
    [Module.IsTorsionFree o (MvPolynomial σ o ⧸ I)] (hI' : I ≠ ⊤) {J : Ideal o} (hJ : J ≠ ⊤) :
    J.map (algebraMap o (MvPolynomial σ o ⧸ I)) ≠ ⊤ := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI'
  have h0 : ∀ p ∈ I, constantCoeff p = 0 := by
    intro p hp
    have h1 := homogeneousComponent_mem_of_mem hI hp 0
    rw [homogeneousComponent_zero, ← Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : coeff 0 p • (1 : MvPolynomial σ o ⧸ I) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]; exact h1
    exact (smul_eq_zero.mp h2).resolve_right one_ne_zero
  intro h
  apply hJ
  have h3 := congrArg (Ideal.map (Ideal.Quotient.lift I constantCoeff h0)) h
  rw [Ideal.map_map, Ideal.map_top] at h3
  have h4 : (Ideal.Quotient.lift I constantCoeff h0).comp
      (algebraMap o (MvPolynomial σ o ⧸ I)) = RingHom.id o := by
    ext r
    exact constantCoeff_C σ r
  rwa [h4, Ideal.map_id] at h3

variable [Finite σ] [IsDedekindDomain o]

/- English proof (translation)
Use `letI : Field (o ⧸ lam) := Ideal.Quotient.field lam`. Establish `hs : Function.Surjective (Ideal.Quotient.mk lam)` using `Ideal.Quotient.mk_surjective`. Take `⟨φ⟩` from `nonempty_quotient_map_algebraMap_ringEquiv I lam`. Establish `hIb : I.map (map (Ideal.Quotient.mk lam)) ≠ ⊤` using `by haveI := Ideal.Quotient.nontrivial_iff.mpr hlam`. Conclude with `Ideal.Quotient.nontrivial_iff.mp φ.injective.nontrivial`.

Take `⟨δ, hdim⟩` from `exists_ringKrullDim_quotient_mvPolynomial_eq_nat hIb`. Take `⟨e, d₀, f, he, hed, hf, hind, hgen, -⟩` from `exists_forms_algebraicIndependent_finite (isHomogeneous_map_of_surjective hs hI) hdim`. Use `choose F hF hFf using fun i => exists_isHomogeneous_map_eq hs (hf i)`. Take `rfl : f = fun i => map (Ideal.Quotient.mk lam) (F i)` from `funext fun i => (hFf i).symm`. Take `⟨n, rfl⟩` from `Nat.exists_eq_add_of_le hed`.

Take `⟨a, ha, hgen'⟩` from `exists_smul_mem_formCombinations hI lam (n := n) hF fun q hq => by`. Use `hgen _ le_rfl q hq` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel_left]`. Then use the resulting hypothesis. Use `⟨δ, e, e + n, a, F, (ringKrullDim_eq_of_ringEquiv φ).trans hdim, ha, he, hed, hF, ?_, fun d hd p hp => smul_mem_formCombinations_of_le hed ?_ hd p hp⟩` and prove the remaining obligations. Conclude with `algebraicIndependent_of_quotient (J := lam) (Ideal.IsMaximal.ne_top inferInstance) (Ideal.quotientMap _ (map (Ideal.Quotient.mk lam)) Ideal.le_comap_map) (fun r => by`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (map _ (C r)) = Ideal.Quotient.mk _ (C _)`. Rewrite using `[map_C]) hind`. Rewrite using `[Nat.add_sub_cancel_left]` and apply the resulting hypothesis.
-/
theorem exists_forms_algebraicIndependent_smul_sub_sum_mem (I : Ideal (MvPolynomial σ o))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ o))
    [Module.IsTorsionFree o (MvPolynomial σ o ⧸ I)] (lam : Ideal o) [lam.IsMaximal]
    (hlam : lam.map (algebraMap o (MvPolynomial σ o ⧸ I)) ≠ ⊤) :
    ∃ (δ e d₀ : ℕ) (a : o) (F : Fin δ → MvPolynomial σ o),
      ringKrullDim ((MvPolynomial σ o ⧸ I) ⧸ lam.map (algebraMap o (MvPolynomial σ o ⧸ I))) = δ ∧
      a - 1 ∈ lam ∧ 1 ≤ e ∧ e ≤ d₀ ∧ (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent o (fun i => Ideal.Quotient.mk I (F i)) ∧
      ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ o, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ o,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ a • p - ∑ i, F i * G i ∈ I := by
  letI : Field (o ⧸ lam) := Ideal.Quotient.field lam
  have hs : Function.Surjective (Ideal.Quotient.mk lam) := Ideal.Quotient.mk_surjective
  obtain ⟨φ⟩ := nonempty_quotient_map_algebraMap_ringEquiv I lam
  have hIb : I.map (map (Ideal.Quotient.mk lam)) ≠ ⊤ := by
    haveI := Ideal.Quotient.nontrivial_iff.mpr hlam
    exact Ideal.Quotient.nontrivial_iff.mp φ.injective.nontrivial
  obtain ⟨δ, hdim⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hIb
  obtain ⟨e, d₀, f, he, hed, hf, hind, hgen, -⟩ :=
    exists_forms_algebraicIndependent_finite (isHomogeneous_map_of_surjective hs hI) hdim
  choose F hF hFf using fun i => exists_isHomogeneous_map_eq hs (hf i)
  obtain rfl : f = fun i => map (Ideal.Quotient.mk lam) (F i) := funext fun i => (hFf i).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hed
  obtain ⟨a, ha, hgen'⟩ := exists_smul_mem_formCombinations hI lam (n := n) hF fun q hq => by
    have := hgen _ le_rfl q hq
    rwa [Nat.add_sub_cancel_left] at this
  refine ⟨δ, e, e + n, a, F, (ringKrullDim_eq_of_ringEquiv φ).trans hdim, ha, he, hed, hF, ?_,
    fun d hd p hp => smul_mem_formCombinations_of_le hed ?_ hd p hp⟩
  · exact algebraicIndependent_of_quotient (J := lam) (Ideal.IsMaximal.ne_top inferInstance)
      (Ideal.quotientMap _ (map (Ideal.Quotient.mk lam)) Ideal.le_comap_map)
      (fun r => by
        change Ideal.Quotient.mk _ (map _ (C r)) = Ideal.Quotient.mk _ (C _)
        rw [map_C]) hind
  · rwa [Nat.add_sub_cancel_left]

/- English proof (translation)
Establish `h1 : Module.IsTorsionFree ℤ (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ)))` using `Function.Injective.moduleIsTorsionFree _ (AlgEquiv.quotientBot ℤ (MvPolynomial (Fin 2) ℤ)).injective (fun c x => map_smul _ c x)`. Establish `h2 : (Ideal.span {(2 : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible`. Conclude with `⟨Ideal.IsHomogeneous.bot _, h1, h2, map_algebraMap_quotient_ne_top _ (Ideal.IsHomogeneous.bot _) bot_ne_top h2.ne_top⟩`.
-/
example : (⊥ : Ideal (MvPolynomial (Fin 2) ℤ)).IsHomogeneous (homogeneousSubmodule (Fin 2) ℤ) ∧
    Module.IsTorsionFree ℤ (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ))) ∧
    (Ideal.span {(2 : ℤ)}).IsMaximal ∧
    (Ideal.span {(2 : ℤ)}).map
      (algebraMap ℤ (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ)))) ≠ ⊤ := by
  have h1 : Module.IsTorsionFree ℤ
      (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ))) :=
    Function.Injective.moduleIsTorsionFree _
      (AlgEquiv.quotientBot ℤ (MvPolynomial (Fin 2) ℤ)).injective (fun c x => map_smul _ c x)
  have h2 : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact ⟨Ideal.IsHomogeneous.bot _, h1, h2,
    map_algebraMap_quotient_ne_top _ (Ideal.IsHomogeneous.bot _) bot_ne_top h2.ne_top⟩

end Main

end GlobalTheory
