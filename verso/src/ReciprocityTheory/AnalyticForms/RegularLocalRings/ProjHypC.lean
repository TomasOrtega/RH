import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in
/- English proof (translation)
Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ q.1)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[chartUpd, Function.update_of_ne (Finset.ne_of_mem_erase hk)]`. Rewrite using `[chartUpd, Function.update_self]`.
-/
theorem prod_X_chartUpd (p : (k : K) → ι k) (q : Σ k, ι k) :
    (∏ k, (X ⟨k, chartUpd p q k⟩ : MvPolynomial (Σ k, ι k) ℂ)) =
      (∏ k ∈ Finset.univ.erase q.1, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) * X q := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ q.1)]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [chartUpd, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [chartUpd, Function.update_self]

open Classical in
/- English proof (translation)
Set `c : K → MvPolynomial (Σ k, ι k) ℂ` to `fun k => ∏ j ∈ Finset.univ.erase k, X ⟨j, p j⟩`. Set `φ` to `(segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).comp (rename (chartUpd p))`. Establish `hX : ∀ q, φ (X q) = c q.1 * X q`. Introduce `q`. Simplify using `only [φ, AlgHom.comp_apply, rename_X, segreMap, aeval_X]`.

Conclude with `prod_X_chartUpd p q`. Establish `hC : ∀ r : ℂ, φ (C r) = C r` using `fun r => by`. Simplify using `[φ, segreMap]`. Establish `key : ∀ m ∈ f.support, φ (monomial m (coeff m f)) = (∏ k, c k ^ a k) * monomial m (coeff m f)`. Introduce `m hm`.

Establish `hpow : (m.prod fun q e => c q.1 ^ e) = ∏ k, c k ^ a k`. Rewrite using `[Finsupp.prod, Finset.prod_subset (Finset.subset_univ m.support) (fun q _ hq => by rw [(by simpa using hq : m q = 0), pow_zero])]`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Rewrite using `[monomial_eq, map_mul, map_finsuppProd]`. Simplify using `only [map_pow, hX, hC, mul_pow]`. Rewrite using `[Finsupp.prod_mul, hpow]`. Expand and normalize the polynomial expressions, which then agree.

Use `show φ f = _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem segre_rename_chartUpd (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    segreMap (rename (chartUpd p) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by
  classical
  let c : K → MvPolynomial (Σ k, ι k) ℂ := fun k => ∏ j ∈ Finset.univ.erase k, X ⟨j, p j⟩
  let φ := (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).comp
    (rename (chartUpd p))
  have hX : ∀ q, φ (X q) = c q.1 * X q := by
    intro q
    simp only [φ, AlgHom.comp_apply, rename_X, segreMap, aeval_X]
    exact prod_X_chartUpd p q
  have hC : ∀ r : ℂ, φ (C r) = C r := fun r => by
    simp [φ, segreMap]
  have key : ∀ m ∈ f.support, φ (monomial m (coeff m f)) = (∏ k, c k ^ a k) * monomial m (coeff m f) := by
    intro m hm

    have hpow : (m.prod fun q e => c q.1 ^ e) = ∏ k, c k ^ a k := by
      rw [Finsupp.prod, Finset.prod_subset (Finset.subset_univ m.support)
        (fun q _ hq => by rw [(by simpa using hq : m q = 0), pow_zero])]
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
      rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
    rw [monomial_eq, map_mul, map_finsuppProd]
    simp only [map_pow, hX, hC, mul_pow]
    rw [Finsupp.prod_mul, hpow]
    ring
  show φ f = _
  calc φ f = φ (∑ m ∈ f.support, monomial m (coeff m f)) := by rw [← f.as_sum]
    _ = ∑ m ∈ f.support, φ (monomial m (coeff m f)) := map_sum _ _ _
    _ = ∑ m ∈ f.support, (∏ k, c k ^ a k) * monomial m (coeff m f) := Finset.sum_congr rfl key
    _ = (∏ k, c k ^ a k) * f := by rw [← Finset.mul_sum, ← f.as_sum]

open Classical in
/- English proof (translation)
Set `x : K → MvPolynomial (Σ k, ι k) ℂ` to `fun j => X ⟨j, p j⟩`. Set `c : K → MvPolynomial (Σ k, ι k) ℂ` to `fun k => ∏ j ∈ Finset.univ.erase k, x j`. Establish `hseg : ∀ v : (k : K) → ι k, segreMap (X v : MvPolynomial ((k : K) → ι k) ℂ) = ∏ k, (X ⟨k, v k⟩ : MvPolynomial (Σ k, ι k) ℂ)` using `fun v => by`. Simplify using `[segreMap]`. Establish `hne : (∏ j, x j) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero _`.

Establish `hn : Fintype.card K - 1 + 1 = Fintype.card K` using `Nat.sub_add_cancel Fintype.card_pos`. Establish `hcprod : (∏ k, c k) = (∏ j, x j) ^ (Fintype.card K - 1)`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[← pow_succ, hn, ← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul _ _ (Finset.mem_univ k)]`.

Rewrite using `[Finset.prod_const, Finset.card_univ]`. Rewrite using `[Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub]`. Establish `h1 : segreMap (∏ k, X (chartUpd p ⟨k, p' k⟩) : MvPolynomial ((k : K) → ι k) ℂ) = (∏ k, c k) * ∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ)`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hseg]`. Conclude with `prod_X_chartUpd p ⟨k, p' k⟩`. Establish `h2 : segreMap (X p' * X p ^ (Fintype.card K - 1) : MvPolynomial ((k : K) → ι k) ℂ) = (∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ)) * (∏ j, x j) ^ (Fintype.card K - 1)`. Rewrite using `[map_mul, map_pow, hseg, hseg]`. Rewrite using `[h1, h2, hcprod, mul_comm, sub_self]`.

Conclude with `P.zero_mem`.
-/
theorem mk_prod_chartUpd {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p p' : (k : K) → ι k) :
    Ideal.Quotient.mk (segreIdeal P) (∏ k, X (chartUpd p ⟨k, p' k⟩)) =
      Ideal.Quotient.mk (segreIdeal P) (X p' * X p ^ (Fintype.card K - 1)) := by
  classical
  let x : K → MvPolynomial (Σ k, ι k) ℂ := fun j => X ⟨j, p j⟩
  let c : K → MvPolynomial (Σ k, ι k) ℂ := fun k => ∏ j ∈ Finset.univ.erase k, x j
  have hseg : ∀ v : (k : K) → ι k, segreMap (X v : MvPolynomial ((k : K) → ι k) ℂ) =
      ∏ k, (X ⟨k, v k⟩ : MvPolynomial (Σ k, ι k) ℂ) := fun v => by
    simp [segreMap]
  have hne : (∏ j, x j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero _
  have hn : Fintype.card K - 1 + 1 = Fintype.card K := Nat.sub_add_cancel Fintype.card_pos

  have hcprod : (∏ k, c k) = (∏ j, x j) ^ (Fintype.card K - 1) := by
    apply mul_right_cancel₀ hne
    rw [← pow_succ, hn, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    rw [Finset.prod_const, Finset.card_univ]
  rw [Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub]
  have h1 : segreMap (∏ k, X (chartUpd p ⟨k, p' k⟩) : MvPolynomial ((k : K) → ι k) ℂ) =
      (∏ k, c k) * ∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hseg]
    exact prod_X_chartUpd p ⟨k, p' k⟩
  have h2 : segreMap (X p' * X p ^ (Fintype.card K - 1) : MvPolynomial ((k : K) → ι k) ℂ) =
      (∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ)) * (∏ j, x j) ^ (Fintype.card K - 1) := by
    rw [map_mul, map_pow, hseg, hseg]
  rw [h1, h2, hcprod, mul_comm, sub_self]
  exact P.zero_mem

section Dehom

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)

/- English proof (translation)
Simplify using `only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]`. Unfold `awayCoord`. Rewrite using `[HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']`. Use `congr 1`. Conclude with `Subtype.ext (pow_one _)`.
-/
theorem val_polyToAway_X (q : Σ k, ι k) :
    letI := segreGraded hP
    (polyToAway hP p (X q)).val = IsLocalization.mk' (Localization.Away (segreW P p))
      (segreW P (chartUpd p q)) (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  unfold awayCoord
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (pow_one _)

/- English proof (translation)
Simplify using `only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]`. Rewrite using `[← Localization.mk_one_eq_algebraMap]`. Use `first`. Consider the case `rfl`. Consider the case `(rw [← HomogeneousLocalization.algebraMap_apply]; rfl)`.

Consider the case `simp [HomogeneousLocalization.val_fromZeroRingHom, Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]`.
-/
theorem val_polyToAway_C (c : ℂ) :
    letI := segreGraded hP
    (polyToAway hP p (C c)).val =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) (C c)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
  rw [← Localization.mk_one_eq_algebraMap]
  first
  | rfl
  | (rw [← HomogeneousLocalization.algebraMap_apply]; rfl)
  | simp [HomogeneousLocalization.val_fromZeroRingHom, Localization.mk_one_eq_algebraMap,
      SetLike.GradeZero.coe_algebraMap, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]

/- English proof (translation)
Use `letI := segreGraded hP`. Set `W` to `algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p)) (segreW P p)`. Set `ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p)` to `(algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p)) (Localization.Away (segreW P p))).comp (polyToAway hP p)`. Set `τ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p)` to `(algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp ((Ideal.Quotient.mk (segreIdeal P)).comp (rename (chartUpd p)).toRingHom)`. Establish `hψ : ∀ g, ψ g = (polyToAway hP p g).val` using `fun g => HomogeneousLocalization.algebraMap_apply _`.

Establish `hX : ∀ q, ψ (X q) * W = τ (X q)`. Introduce `q`. Establish `hs` using `IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q)) (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))`. Rewrite using `[hψ, val_polyToAway_X hP p q]`. Use `hs.trans ?_` and prove the remaining obligations.

Simplify using `[τ]`. Establish `hC : ∀ r, ψ (C r) = τ (C r)` using `fun r => by`. Rewrite using `[hψ, val_polyToAway_C hP p r]`. Simplify using `[τ]`. Establish `key : ∀ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) = τ (monomial m (coeff m f))`.

Introduce `m hm`. Establish `hW : W ^ (∑ k, a k) = m.prod (fun _ e => W ^ e)`. Rewrite using `[Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun k _ => (hf m hm k).symm`.

Rewrite using `[hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc, ← Finsupp.prod_mul]`. Simplify using `only [map_pow, ← mul_pow, hX, hC]`. Use `show ψ f * W ^ (∑ k, a k) = τ f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_sum, ← f.as_sum]`.

Use `_ = ∑ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) := Finset.sum_mul _ _ _`. Use `_ = ∑ m ∈ f.support, τ (monomial m (coeff m f)) := Finset.sum_congr rfl key`. Use `_ = τ f := by rw [← map_sum, ← f.as_sum]`.
-/
theorem val_polyToAway_mul_pow {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    letI := segreGraded hP
    (polyToAway hP p f).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ (∑ k, a k) =
      algebraMap _ (Localization.Away (segreW P p))
        (Ideal.Quotient.mk (segreIdeal P) (rename (chartUpd p) f)) := by
  letI := segreGraded hP
  let W := algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))
    (segreW P p)
  let ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p))
      (Localization.Away (segreW P p))).comp (polyToAway hP p)
  let τ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp
      ((Ideal.Quotient.mk (segreIdeal P)).comp (rename (chartUpd p)).toRingHom)
  have hψ : ∀ g, ψ g = (polyToAway hP p g).val := fun g => HomogeneousLocalization.algebraMap_apply _
  have hX : ∀ q, ψ (X q) * W = τ (X q) := by
    intro q
    have hs := IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q))
      (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))
    rw [hψ, val_polyToAway_X hP p q]
    refine hs.trans ?_
    simp [τ]
  have hC : ∀ r, ψ (C r) = τ (C r) := fun r => by
    rw [hψ, val_polyToAway_C hP p r]
    simp [τ]
  have key : ∀ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) =
      τ (monomial m (coeff m f)) := by
    intro m hm

    have hW : W ^ (∑ k, a k) = m.prod (fun _ e => W ^ e) := by
      rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hf m hm k).symm
    rw [hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc,
      ← Finsupp.prod_mul]
    simp only [map_pow, ← mul_pow, hX, hC]
  show ψ f * W ^ (∑ k, a k) = τ f
  calc ψ f * W ^ (∑ k, a k) = (∑ m ∈ f.support, ψ (monomial m (coeff m f))) * W ^ (∑ k, a k) := by
        rw [← map_sum, ← f.as_sum]
    _ = ∑ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) := Finset.sum_mul _ _ _
    _ = ∑ m ∈ f.support, τ (monomial m (coeff m f)) := Finset.sum_congr rfl key
    _ = τ f := by rw [← map_sum, ← f.as_sum]

/- English proof (translation)
Use `letI := segreGraded hP`. Set `W` to `algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p)) (segreW P p)`. Set `ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p)` to `(algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p)) (Localization.Away (segreW P p))).comp (polyToAway hP p)`. Set `σ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p)` to `(algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp (Ideal.Quotient.mk (segreIdeal P))`. Set `ψ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p)` to `ψ.comp (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).toRingHom`.

Establish `hψ : ∀ g, ψ g = (polyToAway hP p g).val` using `fun g => HomogeneousLocalization.algebraMap_apply _`. Establish `hU : IsUnit W` using `IsLocalization.Away.algebraMap_isUnit _`. Establish `hn : Fintype.card K - 1 + 1 = Fintype.card K` using `Nat.sub_add_cancel Fintype.card_pos`. Establish `hXq : ∀ q : Σ k, ι k, ψ (X q) * W = σ' (X (chartUpd p q))`. Introduce `q`.

Establish `hs` using `IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q)) (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))`. Rewrite using `[hψ, val_polyToAway_X hP p q]`. Conclude with `hs`. Establish `hA : ∀ v : (k : K) → ι k, ψ' (X v) * W = σ' (X v)`. Introduce `v`.

Apply `(hU.pow (Fintype.card K - 1)).mul_right_cancel` to reduce the goal to its premises. Establish `e1 : ψ' (X v) * W * W ^ (Fintype.card K - 1) = ∏ k, (ψ (X ⟨k, v k⟩) * W)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc, ← pow_succ', hn]`. Simplify using `[ψ', segreMap, map_prod]`. Rewrite using `[e1, Finset.prod_congr rfl fun k _ => hXq ⟨k, v k⟩, ← map_prod]`.

Simplify using `only [σ', RingHom.comp_apply]`. Rewrite using `[mk_prod_chartUpd p v, map_mul, map_mul, map_pow, map_pow]`. Establish `hC : ∀ r, ψ' (C r) = σ' (C r)` using `fun r => by`. Establish `e : segreMap (C r : MvPolynomial ((k : K) → ι k) ℂ) = C r` using `by simp [segreMap]`. Use `show ψ (segreMap (C r)) = σ' (C r)`.

Rewrite using `[e, hψ, val_polyToAway_C hP p r]`. Both sides reduce to the same expression. Establish `key : ∀ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d = σ' (monomial m (coeff m g))`. Introduce `m hm`. Establish `hdeg : ∑ v ∈ m.support, m v = d`.

Establish `h1` using `hg (mem_support_iff.1 hm)`. Simplify `h1` using `[Finsupp.weight_apply, Finsupp.sum]`. Establish `hW : W ^ d = m.prod (fun _ e => W ^ e)`. Rewrite using `[Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]`. Rewrite using `[hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc, ← Finsupp.prod_mul]`.

Simplify using `only [map_pow, ← mul_pow, hA, hC]`. Use `show ψ' g * W ^ d = σ' g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_sum, ← g.as_sum]`. Use `_ = ∑ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d := Finset.sum_mul _ _ _`.

Use `_ = ∑ m ∈ g.support, σ' (monomial m (coeff m g)) := Finset.sum_congr rfl key`. Use `_ = σ' g := by rw [← map_sum, ← g.as_sum]`.
-/
theorem val_polyToAway_segre_mul_pow {g : MvPolynomial ((k : K) → ι k) ℂ} {d : ℕ}
    (hg : g.IsHomogeneous d) :
    letI := segreGraded hP
    (polyToAway hP p (segreMap g)).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ d =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) g) := by
  classical
  letI := segreGraded hP
  let W := algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))
    (segreW P p)
  let ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p))
      (Localization.Away (segreW P p))).comp (polyToAway hP p)
  let σ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp
      (Ideal.Quotient.mk (segreIdeal P))
  let ψ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p) :=
    ψ.comp (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).toRingHom
  have hψ : ∀ g, ψ g = (polyToAway hP p g).val := fun g => HomogeneousLocalization.algebraMap_apply _
  have hU : IsUnit W := IsLocalization.Away.algebraMap_isUnit _
  have hn : Fintype.card K - 1 + 1 = Fintype.card K := Nat.sub_add_cancel Fintype.card_pos

  have hXq : ∀ q : Σ k, ι k, ψ (X q) * W = σ' (X (chartUpd p q)) := by
    intro q
    have hs := IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q))
      (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))
    rw [hψ, val_polyToAway_X hP p q]
    exact hs
  have hA : ∀ v : (k : K) → ι k, ψ' (X v) * W = σ' (X v) := by
    intro v
    apply (hU.pow (Fintype.card K - 1)).mul_right_cancel
    have e1 : ψ' (X v) * W * W ^ (Fintype.card K - 1) = ∏ k, (ψ (X ⟨k, v k⟩) * W) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc, ← pow_succ', hn]
      simp [ψ', segreMap, map_prod]
    rw [e1, Finset.prod_congr rfl fun k _ => hXq ⟨k, v k⟩, ← map_prod]
    simp only [σ', RingHom.comp_apply]
    rw [mk_prod_chartUpd p v, map_mul, map_mul, map_pow, map_pow]
  have hC : ∀ r, ψ' (C r) = σ' (C r) := fun r => by
    have e : segreMap (C r : MvPolynomial ((k : K) → ι k) ℂ) = C r := by simp [segreMap]
    show ψ (segreMap (C r)) = σ' (C r)
    rw [e, hψ, val_polyToAway_C hP p r]
    rfl
  have key : ∀ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d = σ' (monomial m (coeff m g)) := by
    intro m hm
    have hdeg : ∑ v ∈ m.support, m v = d := by
      have h1 := hg (mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using h1
    have hW : W ^ d = m.prod (fun _ e => W ^ e) := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
    rw [hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc,
      ← Finsupp.prod_mul]
    simp only [map_pow, ← mul_pow, hA, hC]
  show ψ' g * W ^ d = σ' g
  calc ψ' g * W ^ d = (∑ m ∈ g.support, ψ' (monomial m (coeff m g))) * W ^ d := by
        rw [← map_sum, ← g.as_sum]
    _ = ∑ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d := Finset.sum_mul _ _ _
    _ = ∑ m ∈ g.support, σ' (monomial m (coeff m g)) := Finset.sum_congr rfl key
    _ = σ' g := by rw [← map_sum, ← g.as_sum]

/- English proof (translation)
Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Rewrite using `[HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]`. Simplify `h` using `[map_pow]`.
-/
theorem away_eq_mk_of_val {N : ℕ} (n : MvPolynomial ((k : K) → ι k) ℂ) (hn : n.IsHomogeneous N)
    (a : letI := segreGraded hP; HomogeneousLocalization.Away (segreGrading P) (segreW P p))
    (h : letI := segreGraded hP; a.val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ N =
      algebraMap _ _ (Ideal.Quotient.mk (segreIdeal P) n)) :
    letI := segreGraded hP
    a = HomogeneousLocalization.mk
      ({ deg := N
         num := ⟨Ideal.Quotient.mk _ n, n, (mem_homogeneousSubmodule N n).mpr hn, rfl⟩
         den := ⟨segreW P p ^ N, by simpa using SetLike.pow_mem_graded N (segreW_mem P p)⟩
         den_mem := ⟨N, rfl⟩ } :
        HomogeneousLocalization.NumDenSameDeg (segreGrading P) (Submonoid.powers (segreW P p))) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simpa [map_pow] using h

end Dehom

/- English proof (translation)
Rewrite using `[Scheme.evaluation_eq_zero_iff_notMem_basicOpen]`. Establish `e : x ∈ X.basicOpen s ↔ hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen s`. Rewrite using `[← hU.fromSpec_preimage_basicOpen]`. Express the relevant statement in the definitionally equal form `x ∈ X.basicOpen s ↔ hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen s`. Rewrite using `[show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x from hU.fromSpec_primeIdealOf ⟨x, hx⟩]`.

Rewrite using `[e, PrimeSpectrum.mem_basicOpen, not_not]`.
-/
theorem evaluation_eq_zero_iff_mem_primeIdealOf {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.evaluation U x hx s = 0 ↔ s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  have e : x ∈ X.basicOpen s ↔ hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen s := by
    rw [← hU.fromSpec_preimage_basicOpen]
    change x ∈ X.basicOpen s ↔ hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen s
    rw [show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x from hU.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [e, PrimeSpectrum.mem_basicOpen, not_not]

end

end ReciprocityTheory.AnForm.R
