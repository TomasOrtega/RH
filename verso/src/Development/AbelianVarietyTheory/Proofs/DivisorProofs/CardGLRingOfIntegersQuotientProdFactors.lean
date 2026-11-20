import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.CardGLQuot

/- English proof (translation)
Use `haveI := Fintype.ofFinite κ`. Establish `hq1 : 1 ≤ Nat.card κ` using `Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'`. Establish `hq0 : (Nat.card κ : ℝ) ≠ 0` using `by positivity`. Establish `hIcc : Finset.Icc 1 n = Finset.Ioc 0 n`. Use extensionality with `i`.

Simplify using `only [Finset.mem_Icc, Finset.mem_Ioc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[glVol, hIcc]`. Rewrite using `[Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]`.

Rewrite using `[← Finset.prod_range_reflect]`. Establish `hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hIoc, Finset.prod_map, sq, pow_mul, show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun j hj => ?_)` and prove the remaining obligations.

Establish `hj' : j < n` using `Finset.mem_range.mp hj`. Establish `hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n` using `Nat.pow_le_pow_right hq1 (by omega)`. Simplify using `only [Function.Embedding.coeFn_mk]`. Rewrite using `[Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]`. Use `congr 1`.

Establish `hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]`.
-/
theorem card_GL_field_real (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) = (Nat.card κ : ℝ) ^ (n ^ 2) * glVol (Nat.card κ) n := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [glVol, hIcc]
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

open Classical in

/- English proof (translation)
Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Use `Nat.card_congr (Equiv.ofBijective (fun u => ⟨(u : Matrix (Fin n) (Fin n) S), u.isUnit⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `u v h`. Conclude with `Units.ext (congrArg Subtype.val h)`. Introduce and unpack `⟨A, hA⟩`.

Conclude with `⟨hA.unit, rfl⟩`.
-/
theorem card_GL_eq_card_isUnit (S : Type) [CommRing S] [Fintype S] (n : ℕ) :
    Nat.card (GL (Fin n) S) =
      (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) S => IsUnit A)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun u => ⟨(u : Matrix (Fin n) (Fin n) S), u.isUnit⟩) ⟨?_, ?_⟩)
  · intro u v h; exact Units.ext (congrArg Subtype.val h)
  · rintro ⟨A, hA⟩; exact ⟨hA.unit, rfl⟩

/- English proof (translation)
Use `haveI := Fintype.ofFinite R`. Use `haveI : Finite k := Finite.of_surjective π hπ`. Use `haveI := Fintype.ofFinite k`. Set `φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k` to `(π.mapMatrix).toAddMonoidHom`. Establish `hφ : ∀ A, φ A = A.map π` using `fun A => rfl`.

Establish `hsurj : Function.Surjective φ`. Introduce `B`. Use `⟨Matrix.of fun i j => (hπ (B i j)).choose, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `(hπ (B i j)).choose_spec`.

Establish `hunit : ∀ A, IsUnit A ↔ IsUnit (φ A)`. Introduce `A`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, hu, isUnit_iff_ne_zero, hφ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Use `set K := (Finset.univ.filter (fun A => φ A = 0)).card with hK`. Establish `hfib : ∀ B, (Finset.univ.filter (fun A => φ A = B)).card = K` using `fun B => AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj B) (hsurj 0)`.

Establish `h1 : (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) R => IsUnit A)).card = (Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B)).card * K`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B))]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul]`. Introduce `B hB`. Rewrite using `[← hfib B, Finset.filter_filter]`.

Use `congr 1`. Use `Finset.filter_congr (fun A _ => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`.

Use `⟨(hunit A).2 ?_, h⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `(Finset.mem_filter.1 hB).2`. Introduce `A hA`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢`.

Conclude with `(hunit A).1 hA`. Establish `h2 : Fintype.card (Matrix (Fin n) (Fin n) R) = Fintype.card (Matrix (Fin n) (Fin n) k) * K`. Rewrite using `[← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul, Finset.card_univ]`. Introduce `B _`.

Conclude with `hfib B`. Introduce `A _`. Conclude with `Finset.mem_coe.2 (Finset.mem_univ _)`. Establish `hcard : ∀ (S : Type) [Fintype S], (Fintype.card (Matrix (Fin n) (Fin n) S) : ℝ) = (Nat.card S : ℝ) ^ (n ^ 2)`. Introduce `S _`.

Rewrite using `[← Nat.card_eq_fintype_card, show Nat.card (Matrix (Fin n) (Fin n) S) = Nat.card (Fin n → Fin n → S) from rfl, Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, ← sq]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hR : (Nat.card R : ℝ) ^ (n ^ 2) = (Nat.card k : ℝ) ^ (n ^ 2) * K`. Rewrite using `[← hcard R, ← hcard k, h2, Nat.cast_mul]`.

Rewrite using `[card_GL_eq_card_isUnit, h1, Nat.cast_mul, ← card_GL_eq_card_isUnit, card_GL_field_real]`. Take the linear combination `(-(glVol (Nat.card k) n)) * hR`.
-/
theorem card_GL_of_residue {R k : Type} [CommRing R] [Finite R] [Field k] (π : R →+* k)
    (hπ : Function.Surjective π) (hu : ∀ x, IsUnit x ↔ π x ≠ 0) (n : ℕ) :
    (Nat.card (GL (Fin n) R) : ℝ) = (Nat.card R : ℝ) ^ (n ^ 2) * glVol (Nat.card k) n := by
  classical
  haveI := Fintype.ofFinite R
  haveI : Finite k := Finite.of_surjective π hπ
  haveI := Fintype.ofFinite k
  let φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k := (π.mapMatrix).toAddMonoidHom
  have hφ : ∀ A, φ A = A.map π := fun A => rfl
  have hsurj : Function.Surjective φ := by
    intro B
    refine ⟨Matrix.of fun i j => (hπ (B i j)).choose, ?_⟩
    ext i j
    exact (hπ (B i j)).choose_spec
  have hunit : ∀ A, IsUnit A ↔ IsUnit (φ A) := by
    intro A
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, hu, isUnit_iff_ne_zero, hφ,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  set K := (Finset.univ.filter (fun A => φ A = 0)).card with hK
  have hfib : ∀ B, (Finset.univ.filter (fun A => φ A = B)).card = K :=
    fun B => AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj B) (hsurj 0)
  have h1 : (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) R => IsUnit A)).card =
      (Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B)).card * K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
      (t := Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B))]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul]
      intro B hB
      rw [← hfib B, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr (fun A _ => ?_)
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hunit A).2 ?_, h⟩
        rw [h]; exact (Finset.mem_filter.1 hB).2
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact (hunit A).1 hA
  have h2 : Fintype.card (Matrix (Fin n) (Fin n) R) = Fintype.card (Matrix (Fin n) (Fin n) k) * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul, Finset.card_univ]
      intro B _
      exact hfib B
    · intro A _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  have hcard : ∀ (S : Type) [Fintype S],
      (Fintype.card (Matrix (Fin n) (Fin n) S) : ℝ) = (Nat.card S : ℝ) ^ (n ^ 2) := by
    intro S _
    rw [← Nat.card_eq_fintype_card, show Nat.card (Matrix (Fin n) (Fin n) S) = Nat.card (Fin n → Fin n → S) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, ← sq]
    push_cast; rfl
  have hR : (Nat.card R : ℝ) ^ (n ^ 2) = (Nat.card k : ℝ) ^ (n ^ 2) * K := by
    rw [← hcard R, ← hcard k, h2, Nat.cast_mul]
  rw [card_GL_eq_card_isUnit, h1, Nat.cast_mul, ← card_GL_eq_card_isUnit, card_GL_field_real]
  linear_combination (-(glVol (Nat.card k) n)) * hR

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h ha`. Establish `hU` using `h.map (Ideal.Quotient.factor (Ideal.pow_le_self hc))`.

Rewrite `hU` using `[Ideal.Quotient.factor_mk, (Ideal.Quotient.eq_zero_iff_mem).2 ha]`. Use `haveI := hw.isPrime`. Conclude with `not_isUnit_zero hU`. Introduce `ha`. Take `⟨y, i, hi, hyx⟩` from `hw.exists_inv ha`.

Establish `hnil : IsNilpotent (Ideal.Quotient.mk (w ^ c) i)` using `⟨c, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi c⟩`. Establish `hu : IsUnit (Ideal.Quotient.mk (w ^ c) (y * a))`. Use `hnil.isUnit_one_sub` as an intermediate fact. Rewrite `this` using `[← map_one (Ideal.Quotient.mk (w ^ c)), ← map_sub, show (1 : A) - i = y * a by rw [← hyx]; ring]`. Then use the resulting hypothesis. Rewrite `hu` using `[map_mul]`.

Conclude with `isUnit_of_mul_isUnit_right hu`.
-/
theorem isUnit_quot_pow_iff {A : Type} [CommRing A] {w : Ideal A} (hw : w.IsMaximal) {c : ℕ} (hc : c ≠ 0)
    (x : A ⧸ w ^ c) : IsUnit x ↔ Ideal.Quotient.factor (Ideal.pow_le_self hc) x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h ha
    have hU := h.map (Ideal.Quotient.factor (Ideal.pow_le_self hc))
    rw [Ideal.Quotient.factor_mk, (Ideal.Quotient.eq_zero_iff_mem).2 ha] at hU
    haveI := hw.isPrime
    exact not_isUnit_zero hU
  · intro ha
    obtain ⟨y, i, hi, hyx⟩ := hw.exists_inv ha
    have hnil : IsNilpotent (Ideal.Quotient.mk (w ^ c) i) :=
      ⟨c, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi c⟩
    have hu : IsUnit (Ideal.Quotient.mk (w ^ c) (y * a)) := by
      have := hnil.isUnit_one_sub
      rwa [← map_one (Ideal.Quotient.mk (w ^ c)), ← map_sub,
        show (1 : A) - i = y * a by rw [← hyx]; ring] at this
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem natCard_quot {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Set `e` to `IsDedekindDomain.quotientEquivPiFactors h𝔪`. Establish `h1 : Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) = Nat.card (∀ P : (factors 𝔪).toFinset, GL (Fin n) (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P))` using `Nat.card_congr ((Units.mapEquiv ((e.mapMatrix).trans Matrix.piRingEquiv).toMulEquiv).trans MulEquiv.piUnits).toEquiv`. Rewrite using `[h1, Nat.card_pi, Nat.cast_prod, ← factors_eq_normalizedFactors]`. Rewrite using `[← Finset.prod_coe_sort (factors 𝔪).toFinset (fun w => (Ideal.absNorm w : ℝ) ^ ((factors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n)]`. Use `Finset.prod_congr rfl (fun P _ => ?_)` and prove the remaining obligations.

Establish `hmem : (P : Ideal (𝓞 E)) ∈ factors 𝔪` using `Multiset.mem_toFinset.1 P.2`. Establish `hprime : Prime (P : Ideal (𝓞 E))` using `prime_of_factor _ hmem`. Establish `hbot : (P : Ideal (𝓞 E)) ≠ ⊥` using `hprime.ne_zero`. Establish `hmax : (P : Ideal (𝓞 E)).IsMaximal` using `((Ideal.isPrime_of_prime hprime)).isMaximal hbot`. Establish `hc : (factors 𝔪).count (P : Ideal (𝓞 E)) ≠ 0` using `(Multiset.count_pos.2 hmem).ne'`.

Use `letI : Field (𝓞 E ⧸ (P : Ideal (𝓞 E))) := Ideal.Quotient.field _`. Use `haveI : Finite (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P) := by`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[natCard_quot, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `pow_ne_zero _ hbot`.

Rewrite using `[card_GL_of_residue (Ideal.Quotient.factor (Ideal.pow_le_self hc)) (Ideal.Quotient.factor_surjective _) (isUnit_quot_pow_iff hmax hc) n, natCard_quot, natCard_quot, map_pow, Nat.cast_pow, ← pow_mul]`.
-/
theorem card_GL_quot (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥) (n : ℕ) :
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  classical
  let e := IsDedekindDomain.quotientEquivPiFactors h𝔪
  have h1 : Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) = Nat.card (∀ P : (factors 𝔪).toFinset,
      GL (Fin n) (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P)) :=
    Nat.card_congr ((Units.mapEquiv ((e.mapMatrix).trans Matrix.piRingEquiv).toMulEquiv).trans
      MulEquiv.piUnits).toEquiv
  rw [h1, Nat.card_pi, Nat.cast_prod, ← factors_eq_normalizedFactors]
  rw [← Finset.prod_coe_sort (factors 𝔪).toFinset (fun w => (Ideal.absNorm w : ℝ) ^ ((factors 𝔪).count w * n ^ 2) *
    glVol (Ideal.absNorm w : ℝ) n)]
  refine Finset.prod_congr rfl (fun P _ => ?_)
  have hmem : (P : Ideal (𝓞 E)) ∈ factors 𝔪 := Multiset.mem_toFinset.1 P.2
  have hprime : Prime (P : Ideal (𝓞 E)) := prime_of_factor _ hmem
  have hbot : (P : Ideal (𝓞 E)) ≠ ⊥ := hprime.ne_zero
  have hmax : (P : Ideal (𝓞 E)).IsMaximal :=
    ((Ideal.isPrime_of_prime hprime)).isMaximal hbot
  have hc : (factors 𝔪).count (P : Ideal (𝓞 E)) ≠ 0 := (Multiset.count_pos.2 hmem).ne'
  letI : Field (𝓞 E ⧸ (P : Ideal (𝓞 E))) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ (P : Ideal (𝓞 E)) ^ (factors 𝔪).count ↑P) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_quot, Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ hbot
  rw [card_GL_of_residue (Ideal.Quotient.factor (Ideal.pow_le_self hc)) (Ideal.Quotient.factor_surjective _)
    (isUnit_quot_pow_iff hmax hc) n, natCard_quot, natCard_quot, map_pow, Nat.cast_pow, ← pow_mul]

/- English proof (translation)
Introduce `E _ _ 𝔪 h𝔪 n` and use `card_GL_quot E 𝔪 h𝔪 n`.
-/
theorem card_GL_quot_prod : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n :=
  fun E _ _ 𝔪 h𝔪 n => card_GL_quot E 𝔪 h𝔪 n

end GlobalTheory.CardGLQuot
