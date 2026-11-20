import ReciprocityTheory.AnalyticForms.RegularLocalRings.SegreIdealIsHomogeneous

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[eval₂_eq, eval₂_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i ∈ d.support, d i = n`. Establish `h` using `hf (mem_support_iff.1 hd)`. Simplify `h` using `[Finsupp.weight_apply, Finsupp.sum]`.

Rewrite using `[Finset.prod_congr rfl (fun i _ => mul_pow (y i) t (d i)), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_mul_const_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (y : σ → S) (t : S) {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) :
    eval₂ g (fun i => y i * t) f = eval₂ g y f * t ^ n := by
  rw [eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hf (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl (fun i _ => mul_pow (y i) t (d i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `d hd`. Establish `h` using `hf d (mem_support_iff.2 hd)`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Pi.one_apply, smul_eq_mul, mul_one]`. Rewrite using `[Fintype.sum_sigma]`.

Conclude with `Finset.sum_congr rfl fun k _ => h k`.
-/
theorem isHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) : f.IsHomogeneous (∑ k, a k) := by
  intro d hd
  have h := hf d (mem_support_iff.2 hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun k _ => h k

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj)]`.
-/
theorem prod_update_eq {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p : (k : K) → ι k) (k : K) (v : ι k) :
    ∏ j, x ⟨j, Function.update p k v j⟩ = x ⟨k, v⟩ * ∏ j ∈ Finset.univ.erase k, x ⟨j, p j⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/- English proof (translation)
Repeatedly rewrite using `[prod_update_eq x p]`. Rewrite using `[Finset.prod_mul_distrib, mul_assoc]`. Use `congr 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul Finset.univ (fun j => x ⟨j, p j⟩) (Finset.mem_univ k)]`.

Rewrite using `[Finset.prod_const, Finset.card_univ]`.
-/
theorem prod_prod_update {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p p' : (k : K) → ι k) :
    (∏ k, ∏ j, x ⟨j, Function.update p k (p' k) j⟩) * ∏ j, x ⟨j, p j⟩ =
      (∏ k, x ⟨k, p' k⟩) * (∏ j, x ⟨j, p j⟩) ^ Fintype.card K := by
  simp_rw [prod_update_eq x p]
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul Finset.univ (fun j => x ⟨j, p j⟩)
    (Finset.mem_univ k)]
  rw [Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Simplify using `[segreMap]`.
-/
theorem segreMap_X (p : (k : K) → ι k) :
    segreMap (X p : MvPolynomial ((k : K) → ι k) ℂ) = ∏ k, X ⟨k, p k⟩ := by
  simp [segreMap]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub, h, sub_self]`. Conclude with `P.zero_mem`.
-/
theorem mk_eq_of_segreMap_eq (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    {φ ψ : MvPolynomial ((k : K) → ι k) ℂ} (h : segreMap φ = segreMap ψ) :
    Ideal.Quotient.mk (segreIdeal P) φ = Ideal.Quotient.mk (segreIdeal P) ψ := by
  rw [Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub, h, sub_self]
  exact P.zero_mem

/- English proof (translation)
Simplify using `only [segreW, ← map_prod, ← map_mul, ← map_pow]`. Apply `mk_eq_of_segreMap_eq` to reduce the goal to its premises. Simplify using `only [map_mul, map_prod, map_pow, segreMap_X]`. Conclude with `prod_prod_update (X : (Σ k, ι k) → MvPolynomial (Σ k, ι k) ℂ) p p'`.
-/
theorem segreW_prod_update [DecidableEq K] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (p p' : (k : K) → ι k) :
    (∏ k, segreW P (Function.update p k (p' k))) * segreW P p =
      segreW P p' * segreW P p ^ Fintype.card K := by
  simp only [segreW, ← map_prod, ← map_mul, ← map_pow]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, map_prod, map_pow, segreMap_X]
  exact prod_prod_update (X : (Σ k, ι k) → MvPolynomial (Σ k, ι k) ℂ) p p'

/- English proof (translation)
Take `⟨k, v⟩` from `q`. Simplify using `only [segreW, ← map_mul]`. Apply `mk_eq_of_segreMap_eq` to reduce the goal to its premises. Simplify using `only [map_mul, segreMap_X]`. Rewrite using `[prod_update_eq X p k v, prod_update_eq X p' k (p k), prod_update_eq X p' k v, ← Finset.mul_prod_erase Finset.univ (fun j => (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem segreW_exchange [DecidableEq K] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (p p' : (k : K) → ι k) (q : Σ k, ι k) :
    segreW P (Function.update p q.1 q.2) * segreW P (Function.update p' q.1 (p q.1)) =
      segreW P (Function.update p' q.1 q.2) * segreW P p := by
  obtain ⟨k, v⟩ := q
  simp only [segreW, ← map_mul]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, segreMap_X]
  rw [prod_update_eq X p k v, prod_update_eq X p' k (p k), prod_update_eq X p' k v,
    ← Finset.mul_prod_erase Finset.univ (fun j => (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (Finset.mem_univ k)]
  ring

/- English proof (translation)
Establish `h1 : segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) : MvPolynomial ((k : K) → ι k) ℂ)) f) = aeval (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) : MvPolynomial ((k : K) → ι k) ℂ)) f`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `hY : (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) : MvPolynomial ((k : K) → ι k) ℂ)) = fun q => X q * ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)`. Use function extensionality and compare the values at `q`. Rewrite using `[segreMap_X, prod_update_eq X p q.1 q.2]`.

Rewrite using `[h1, hY]`. Establish `key : ∀ m ∈ f.support, aeval (fun q : Σ k, ι k => X q * ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) (monomial m (f.coeff m)) = (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * monomial m (f.coeff m)`. Introduce `m hm`. Establish `hdeg` using `hf m hm`. Rewrite using `[aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]`.

Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finset.prod_mul_distrib]`. Establish `hc : ∏ q : (Σ k, ι k), (∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ m q = ∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hdeg k]`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [f.as_sum]`.

Rewrite using `[map_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl key`.
-/
theorem segreMap_aeval_update [DecidableEq K] (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ}
    {a : K → ℕ} (hf : IsMultiHomog f a) :
    segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by
  have h1 : segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      aeval (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hY : (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) =
      fun q => X q * ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ) := by
    funext q
    rw [segreMap_X, prod_update_eq X p q.1 q.2]
  rw [h1, hY]
  have key : ∀ m ∈ f.support,
      aeval (fun q : Σ k, ι k => X q *
          ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
        (monomial m (f.coeff m)) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) *
        monomial m (f.coeff m) := by
    intro m hm
    have hdeg := hf m hm
    rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    have hc : ∏ q : (Σ k, ι k),
        (∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ m q =
        ∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hdeg k]
    rw [hc]
    ring
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  conv_rhs => rw [f.as_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl key

abbrev invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.Away (segreW P p) :=
  Localization.mk 1 ⟨segreW P p, 1, pow_one _⟩

/- English proof (translation)
Rewrite using `[invW, Localization.mk_mul, mul_one, one_mul]`. Conclude with `Localization.mk_self (⟨segreW P p, 1, pow_one _⟩ : Submonoid.powers (segreW P p))`.
-/
theorem mk_one_mul_invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.mk (segreW P p) 1 * invW P p = 1 := by
  rw [invW, Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨segreW P p, 1, pow_one _⟩ : Submonoid.powers (segreW P p))

/- English proof (translation)
Rewrite using `[invW, Localization.mk_pow, Localization.mk_mul, one_pow, mul_one, one_mul]`. Use `congr 1`.
-/
theorem mk_pow_eq_mul_invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (a : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (n : ℕ) (h : segreW P p ^ n ∈ Submonoid.powers (segreW P p)) :
    (Localization.mk a ⟨segreW P p ^ n, h⟩ : Localization.Away (segreW P p)) =
      Localization.mk a 1 * invW P p ^ n := by
  rw [invW, Localization.mk_pow, Localization.mk_mul, one_pow, mul_one, one_mul]
  congr 1

/- English proof (translation)
Simplify using `only [Localization.mk_one_eq_algebraMap]`. Establish `h` using `MvPolynomial.eval₂_comp_left ((algebraMap (MvPolynomial τ ℂ ⧸ I) (Localization M)).comp (Ideal.Quotient.mk I)) (algebraMap ℂ (MvPolynomial τ ℂ)) Y f`. Rewrite `h` using `[RingHom.comp_apply]`. Rewrite using `[aeval_def, h]`. Use `congr 1`.
-/
theorem eval₂_mk_one {τ : Type} (I : Ideal (MvPolynomial τ ℂ)) (M : Submonoid (MvPolynomial τ ℂ ⧸ I))
    {σ : Type} (Y : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval₂ (algebraMap ℂ (Localization M)) (fun q => Localization.mk (Ideal.Quotient.mk I (Y q)) 1) f =
      Localization.mk (Ideal.Quotient.mk I (aeval Y f)) 1 := by
  simp only [Localization.mk_one_eq_algebraMap]
  have h := MvPolynomial.eval₂_comp_left
    ((algebraMap (MvPolynomial τ ℂ ⧸ I) (Localization M)).comp (Ideal.Quotient.mk I))
    (algebraMap ℂ (MvPolynomial τ ℂ)) Y f
  rw [RingHom.comp_apply] at h
  rw [aeval_def, h]
  congr 1

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_pow_inv_eq {R : Type*} [CommRing R] (Q W W' t : R) (c : ℕ) (E : Q * W = W' * W ^ c)
    (ht : W * t = 1) : Q * t ^ c = W' * t := by
  calc Q * t ^ c = Q * t ^ c * (W * t) := by rw [ht, mul_one]
    _ = (Q * W) * t ^ c * t := by ring
    _ = W' * (W * t) ^ c * t := by rw [E]; ring
    _ = W' * t := by rw [ht, one_pow, mul_one]

variable [Nonempty K]

/- English proof (translation)
Use `letI := segreGraded hP`. Introduce and unpack `⟨x, hx⟩`. Take `⟨q, hq, rfl⟩` from `Submodule.mem_map.1 hx`. Establish `hq' : q.IsHomogeneous 0` using `(mem_homogeneousSubmodule 0 q).1 hq`. Use `⟨q.coeff 0, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[SetLike.GradeZero.coe_algebraMap]`. Distinguish the cases in `h0 : q = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules.

Establish `hC : q = C (q.coeff 0)` using `totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0) show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q nth_rewrite 2 [hC]`. Conclude with `((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm`.
-/
theorem segreGrading_algebraMap_surjective {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Function.Surjective (algebraMap ℂ (segreGrading P 0)) := by
  letI := segreGraded hP
  rintro ⟨x, hx⟩
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hx
  have hq' : q.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 q).1 hq
  refine ⟨q.coeff 0, ?_⟩
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap]
  by_cases h0 : q = 0
  · subst h0
    simp
  · have hC : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0)
    show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q
    nth_rewrite 2 [hC]
    exact ((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm

/- English proof (translation)
Use `letI := segreGraded hP`. Use `haveI : Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) (Ideal.Quotient.mkₐ_surjective ℂ _)`. Use `haveI : IsScalarTower ℂ (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := IsScalarTower.of_algebraMap_eq fun c => by`. Rewrite using `[← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]`. Both sides reduce to the same expression.

Conclude with `Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) _`.
-/
theorem segreRing_finiteType {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Algebra.FiniteType (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := by
  letI := segreGraded hP
  haveI : Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P))
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  haveI : IsScalarTower ℂ (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]
      rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) _

section Proj

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/- English proof (translation)
Establish `hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι` using `by show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫ ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _`. Rewrite using `[Iso.hom_inv_id_assoc]`. Establish `hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)))`. Rewrite using `[← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]`. Establish `h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫ (Proj.basicOpen 𝒜 f).topIso.inv = (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop`.

Rewrite using `[Scheme.Opens.topIso_inv]`. Use `erw [Scheme.Hom.appLE_map]`. Establish `h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫ (Proj.basicOpen 𝒜 f).topIso.inv = ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫ (Proj.basicOpen 𝒜 f).topIso.inv`. Rewrite using `[h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]`. Establish `hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) = (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫ Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv` using `Proj.basicOpenToSpec_app_top 𝒜 f`.

Rewrite using `[hA]`. Rewrite using `[← Category.assoc, Scheme.ΓSpecIso_naturality]`. Simplify using `only [Category.assoc]`. Establish `h3` using `(cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2`. Rewrite using `[h3, Iso.inv_hom_id_assoc]`.
-/
theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by
  have hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
    rw [Iso.hom_inv_id_assoc]
  have hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]
  have h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by
    rw [Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.appLE_map]
  have h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]
    have hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫
          Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv :=
      Proj.basicOpenToSpec_app_top 𝒜 f
    rw [hA]
    rw [← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  have h3 := (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2
  rw [h3, Iso.inv_hom_id_assoc]

end Proj

end

end ReciprocityTheory.AnForm.R
