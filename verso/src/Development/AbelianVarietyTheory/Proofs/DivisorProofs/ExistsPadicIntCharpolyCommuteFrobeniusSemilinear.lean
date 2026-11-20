import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.DieuCharpoly

open Polynomial

/- English proof (translation)
Establish `hp : 1 < p` using `(Fact.out : p.Prime).one_lt`. Establish `hroots` using `FiniteField.roots_X_pow_card_sub_X (ZMod p)`. Rewrite `hroots` using `[ZMod.card p]`. Establish `hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p` using `FiniteField.X_pow_card_sub_X_natDegree_eq _ hp`. Establish `hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree`.

Rewrite using `[hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]`. Establish `hmap` using `Polynomial.roots_map_of_injective_of_card_eq_natDegree ((ZMod.castHom (dvd_refl p) k)).injective hcard`. Establish `hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots`. Rewrite using `[Polynomial.mem_roots]`. Simplify using `[hc]`.

Simplify using `using FiniteField.X_pow_card_sub_X_ne_zero k hp`. Rewrite `hmem` using `[← hmap, hroots, Multiset.mem_map]`. Take `⟨a, -, ha⟩` from `hmem`. Conclude with `⟨a, ha⟩`.
-/
theorem mem_range_zmod_of_pow_eq_self (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (c : k) (hc : c ^ p = c) : c ∈ Set.range ((ZMod.castHom (dvd_refl p) k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card p] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    ((ZMod.castHom (dvd_refl p) k)).injective hcard
  have hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots := by
    rw [Polynomial.mem_roots]
    · simp [hc]
    · simpa using FiniteField.X_pow_card_sub_X_ne_zero k hp
  rw [← hmap, hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

/- English proof (translation)
Establish `hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n`. Introduce `n`. Establish `h` using `congrArg (fun z => z.coeff n) hx`. Simplify using `only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h`. Conclude with `mem_range_zmod_of_pow_eq_self p _ h`.

Use `choose a ha using hc`. Use `⟨WittVector.mk p a, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Simplify using `[WittVector.map_coeff, ha]`.
-/
theorem exists_map_eq_of_frobenius_eq (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ y : WittVector p (ZMod p), WittVector.map ((ZMod.castHom (dvd_refl p) k)) y = x := by
  have hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n := by
    intro n
    have h := congrArg (fun z => z.coeff n) hx
    simp only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h
    exact mem_range_zmod_of_pow_eq_self p _ h
  choose a ha using hc
  refine ⟨WittVector.mk p a, ?_⟩
  ext n
  simp [WittVector.map_coeff, ha]

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Establish `hI : Ideal.span {(p : WittVector p k)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `(WittVector.irreducible p).not_isUnit`.

Establish `h` using `Ideal.iInf_pow_eq_bot_of_isDomain _ hI`. Rewrite using `[← Ideal.mem_bot, ← h, Ideal.mem_iInf]`. Introduce `m`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)`. Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`.

Use `⟨f y - g y, ?_⟩` and prove the remaining obligations. Establish `h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m` using `by rw [hy]; ring`. Rewrite using `[h1]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] (f g : ℤ_[p] →+* WittVector p k) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  have hI : Ideal.span {(p : WittVector p k)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (WittVector.irreducible p).not_isUnit
  have h := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro m
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f y - g y, ?_⟩
  have h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m := by rw [hy]; ring
  rw [h1]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R N`. Set `U` to `LinearMap.toMatrix b b u`. Set `Φ : Matrix _ _ R` to `fun i j => b.repr (F (b j)) i`. Establish `hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j)`. Introduce `x i`.

Use `conv_lhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l`. Introduce `y i`.

Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b u y]`. Both sides reduce to the same expression. Establish `hcomm : U * Φ = Φ * U.map σ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun z => b.repr z i) (hu (b j))`.

Rewrite `h` using `[hurepr, hFrepr]`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `h.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]`. Establish `hdet : Φ.det ≠ 0`.

Introduce `h0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `choose w hw using fun j => hσ (v j)`. Set `x` to `b.repr.symm (Finsupp.equivFunOnFinite.symm w)`. Establish `hx : ∀ j, b.repr x j = w j` using `by simp [x]`.

Establish `hFx : F x = 0`. Apply `b.repr.injective` to reduce the goal to its premises. Use `Finsupp.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Use `congrFun hv i` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hx, hw]`. Establish `hx0 : x = 0` using `hF (by rw [hFx, map_zero])`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Rewrite using `[← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]`. Rewrite using `[← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]`. Establish `hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ = (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix`. Rewrite using `[Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul, (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]`.

Establish `hd` using `congrArg Matrix.det hm`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det]`. Establish `hC : Polynomial.C Φ.det ≠ 0` using `Polynomial.C_ne_zero.2 hdet`. Rewrite `hd` using `[mul_comm]`. Conclude with `(mul_left_cancel₀ hC hd).symm`.
-/
theorem charpoly_map_eq_of_commute_semilinear {R : Type} [CommRing R] [IsDomain R]
    (σ : R →+* R) (hσ : Function.Surjective σ) (N : Type) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N] (F : N →ₛₗ[σ] N) (u : N →ₗ[R] N)
    (hF : Function.Injective F) (hu : ∀ x, u (F x) = F (u x)) :
    u.charpoly.map σ = u.charpoly := by
  classical
  let b := Module.Free.chooseBasis R N
  let U := LinearMap.toMatrix b b u
  let Φ : Matrix _ _ R := fun i j => b.repr (F (b j)) i
  have hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j) := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, Finsupp.coe_finset_sum, Finset.sum_apply,
      map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l := by
    intro y i
    rw [← LinearMap.toMatrix_mulVec_repr b b u y]
    rfl
  have hcomm : U * Φ = Φ * U.map σ := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg (fun z => b.repr z i) (hu (b j))
    rw [hurepr, hFrepr] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]
  have hdet : Φ.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    choose w hw using fun j => hσ (v j)
    let x := b.repr.symm (Finsupp.equivFunOnFinite.symm w)
    have hx : ∀ j, b.repr x j = w j := by simp [x]
    have hFx : F x = 0 := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx, hw]
    have hx0 : x = 0 := hF (by rw [hFx, map_zero])
    apply hv0
    funext j
    rw [← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  rw [← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]
  have hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ =
      (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hd
  have hC : Polynomial.C Φ.det ≠ 0 := Polynomial.C_ne_zero.2 hdet
  rw [mul_comm] at hd
  exact (mul_left_cancel₀ hC hd).symm

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

/- English proof (translation)
Introduce `p _ k _ _ _ N _ _ _ _ F ψ u hF hu`. Establish `hfix` using `charpoly_map_eq_of_commute_semilinear _ (WittVector.frobenius_bijective p k).surjective N F u hF hu`. Establish `hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom` using `padicInt_ringHom_ext p _ _`. Establish `hl : u.charpoly ∈ Polynomial.lifts ψ`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Establish `h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n` using `by conv_rhs => rw [← hfix]`. Rewrite using `[Polynomial.coeff_map]`. Take `⟨y, hy⟩` from `exists_map_eq_of_frobenius_eq p _ h`. Use `⟨WittVector.equiv p y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, hy]`. Take `⟨P, hP, -, hPm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)`. Conclude with `⟨P, hPm, hP⟩`.
-/
theorem exists_monic_map_eq_charpoly : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N),
    Function.Injective F → (∀ x, u (F x) = F (u x)) →
      ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  intro p _ k _ _ _ N _ _ _ _ F ψ u hF hu
  have hfix := charpoly_map_eq_of_commute_semilinear _
    (WittVector.frobenius_bijective p k).surjective N F u hF hu
  have hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom := padicInt_ringHom_ext p _ _
  have hl : u.charpoly ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n := by
      conv_rhs => rw [← hfix]
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := exists_map_eq_of_frobenius_eq p _ h
    refine ⟨WittVector.equiv p y, ?_⟩
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hy]
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)
  exact ⟨P, hPm, hP⟩

end GlobalTheory.DieuCharpoly
