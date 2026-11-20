import Formalism.SatakeDualWeyl.Statement

open Matrix NumberField ComplexConjugate

namespace Formalism.UG.P

section Den
variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hZ : ∀ x : ℤ, IsIntegral ℤ (x : E)` using `fun x => by`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := x))`. Establish `hQ : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i)`. Introduce `i`. Take `⟨⟨m, hm⟩, hint⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))`.

Use `⟨m, nonZeroDivisors.ne_zero hm, ?_⟩` and prove the remaining obligations. Simplify `hint` using `[Submonoid.smul_def, zsmul_eq_mul]`. Use `choose m hm0 hmi using hQ`. Establish `_` using `Fintype.ofFinite ι`. Use `⟨((∏ i, m i : ℤ) : E), ?_, hZ _, ?_⟩` and prove the remaining obligations.

Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hm0 i)` after adjusting the coercions. Introduce `i`. Rewrite using `[← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]`. Use `push_cast`. Rewrite using `[mul_comm ((m i : ℤ) : E), mul_assoc]`.

Use `IsIntegral.mul ?_ (hmi i)` and prove the remaining obligations. Conclude with `hZ (∏ j ∈ Finset.univ.erase i, m j)` after adjusting the coercions.
-/
theorem sf_den {ι : Type} [Finite ι] (f : ι → E) :
    ∃ d : E, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ i, IsIntegral ℤ (d * f i) := by
  classical
  have hZ : ∀ x : ℤ, IsIntegral ℤ (x : E) := fun x => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := x))
  have hQ : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using hQ
  have _ := Fintype.ofFinite ι
  refine ⟨((∏ i, m i : ℤ) : E), ?_, hZ _, ?_⟩
  · exact_mod_cast Finset.prod_ne_zero_iff.2 (fun i _ => hm0 i)
  · intro i
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast
    rw [mul_comm ((m i : ℤ) : E), mul_assoc]
    refine IsIntegral.mul ?_ (hmi i)
    exact_mod_cast hZ (∏ j ∈ Finset.univ.erase i, m j)

end Den

section CS
variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Unfold `hform`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sf_expand (A : Matrix n n ℂ) (a b : ℂ) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (a • v + b • u) (a • v + b • u) =
      conj a * a * hform (starRingEnd ℂ) A v v + conj a * b * hform (starRingEnd ℂ) A v u +
      conj b * a * hform (starRingEnd ℂ) A u v + conj b * b * hform (starRingEnd ℂ) A u u := by
  unfold hform
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_mul]
  ring

/- English proof (translation)
Unfold `hform`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, Complex.conj_conj, hA]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sf_conj (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    conj (hform (starRingEnd ℂ) A u v) = hform (starRingEnd ℂ) A v u := by
  unfold hform
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_conj, hA]
  ring

/- English proof (translation)
Rewrite using `[sf_expand]`. Establish `h1 : conj (hform (starRingEnd ℂ) A u u) = hform (starRingEnd ℂ) A u u` using `sf_conj A hA u u`. Establish `h2 : hform (starRingEnd ℂ) A v u = conj (hform (starRingEnd ℂ) A u v)` using `(sf_conj A hA u v).symm`. Rewrite using `[h2, map_neg, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sf_cs (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u)
      (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u) =
    hform (starRingEnd ℂ) A u u * (hform (starRingEnd ℂ) A u u * hform (starRingEnd ℂ) A v v
      - conj (hform (starRingEnd ℂ) A u v) * hform (starRingEnd ℂ) A u v) := by
  rw [sf_expand]
  have h1 : conj (hform (starRingEnd ℂ) A u u) = hform (starRingEnd ℂ) A u u := sf_conj A hA u u
  have h2 : hform (starRingEnd ℂ) A v u = conj (hform (starRingEnd ℂ) A u v) := (sf_conj A hA u v).symm
  rw [h2, map_neg, h1]
  ring

/- English proof (translation)
Unfold `hform`. Simplify using `only [map_sum, map_mul, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `RingHom.congr_fun hτ (x i)`. Simplify using `only [RingHom.comp_apply] at h1`.

Rewrite using `[h1]`.
-/
theorem sf_map {E : Type} [CommRing E] (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : τ.comp σ = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x y : n → E) :
    τ (hform σ J x y) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (x k)) (fun k => τ (y k)) := by
  unfold hform
  simp only [map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := RingHom.congr_fun hτ (x i)
  simp only [RingHom.comp_apply] at h1
  rw [h1]

/- English proof (translation)
Unfold `hform cT`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem sf_gram {A : Type} [CommRing A] (σ : A →+* A) (J M : Matrix n n A) (a b : n) :
    (cT σ M * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  unfold hform cT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Matrix.mulVec, dotProduct]`. Introduce `k _ hk`. Simplify using `[hk]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem sf_single {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix n n A) (i : n) (y : n → A) :
    hform σ J (Pi.single i 1) y = (J *ᵥ y) i := by
  unfold hform
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CS

section B
variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `hreal : ∀ a : F, conj (τ (algebraMap F E a)) = τ (algebraMap F E a)`. Introduce `a`. Establish `h1 : τ ((σ : E →+* E) (algebraMap F E a)) = conj (τ (algebraMap F E a))` using `RingHom.congr_fun hτ _`. Establish `h2 : (σ : E →+* E) (algebraMap F E a) = algebraMap F E a` using `σ.commutes a`. Rewrite `h1` using `[h2]`.

Conclude with `h1.symm`. Establish `him : ∀ a : F, (τ (algebraMap F E a)).im = 0` using `fun a => Complex.conj_eq_iff_im.1 (hreal a)`. Set `ι : F →+* ℝ` to `{ toFun := fun a => (τ (algebraMap F E a)).re map_one' := by simp map_mul' := fun a b => by simp [map_mul, Complex.mul_re, him a, him b] map_zero' := by simp map_add' := fun a b => by simp [map_add] }`. Establish `hval : ∀ a : F, τ (algebraMap F E a) = ((ι a : ℝ) : ℂ)` using `fun a => (Complex.conj_eq_iff_re.1 (hreal a)).symm`. Establish `h00 : τ (hform (σ : E →+* E) J 0 0) = ((0 : ℝ) : ℂ)`.

Unfold `hform`. Simplify using the standard rewrite rules. Break down `hdef ι with hpos | hneg` into its components or cases. Use `⟨1, by norm_num, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Use `⟨0, ?_, fun h => absurd hx h, by norm_num⟩` and prove the remaining obligations. Substitute `hx` using the available equality. Conclude with `h00`. Take `⟨a, ha, hpa⟩` from `hpos x hx`. Use `⟨ι a, ?_, fun _ => by linarith, by linarith⟩` and prove the remaining obligations.

Rewrite using `[← ha]`. Conclude with `hval a`. Use `⟨-1, by norm_num, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Use `⟨0, ?_, fun h => absurd hx h, by norm_num⟩` and prove the remaining obligations.

Substitute `hx` using the available equality. Conclude with `h00`. Take `⟨a, ha, hpa⟩` from `hneg x hx`. Use `⟨ι a, ?_, fun _ => by linarith, by linarith⟩` and prove the remaining obligations. Rewrite using `[← ha]`.

Conclude with `hval a`.
-/
theorem sf_sign {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) :
    ∃ s : ℝ, 0 < s * s ∧ ∀ x : n → E, ∃ t : ℝ, τ (hform (σ : E →+* E) J x x) = t ∧
      (x ≠ 0 → 0 < s * t) ∧ 0 ≤ s * t := by
  classical
  have hreal : ∀ a : F, conj (τ (algebraMap F E a)) = τ (algebraMap F E a) := by
    intro a
    have h1 : τ ((σ : E →+* E) (algebraMap F E a)) = conj (τ (algebraMap F E a)) :=
      RingHom.congr_fun hτ _
    have h2 : (σ : E →+* E) (algebraMap F E a) = algebraMap F E a := σ.commutes a
    rw [h2] at h1
    exact h1.symm
  have him : ∀ a : F, (τ (algebraMap F E a)).im = 0 := fun a => Complex.conj_eq_iff_im.1 (hreal a)
  let ι : F →+* ℝ :=
    { toFun := fun a => (τ (algebraMap F E a)).re
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, Complex.mul_re, him a, him b]
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hval : ∀ a : F, τ (algebraMap F E a) = ((ι a : ℝ) : ℂ) := fun a =>
    (Complex.conj_eq_iff_re.1 (hreal a)).symm
  have h00 : τ (hform (σ : E →+* E) J 0 0) = ((0 : ℝ) : ℂ) := by
    unfold hform
    simp
  rcases hdef ι with hpos | hneg
  · refine ⟨1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hpos x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a
  · refine ⟨-1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hneg x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a

/- English proof (translation)
Take `⟨s, hs, hsign⟩` from `sf_sign σ J τ hτ hdef`. Establish `hA : ∀ a b, conj ((J.map τ) b a) = (J.map τ) a b`. Introduce `a b`. Establish `h3 : τ ((σ : E →+* E) (J b a)) = conj (τ (J b a))` using `RingHom.congr_fun hτ _`. Establish `h4 : (σ : E →+* E) (J b a) = J a b`.

Establish `h1 : (cT (σ : E →+* E) J) a b = J a b` using `by rw [hH]`. Conclude with `h1`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[← h3, h4]`. Establish `hc : (J * g) i j = hform (σ : E →+* E) J (Pi.single i 1) (fun k => g k j)`.

Rewrite using `[sf_single]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hb : hform (σ : E →+* E) J (fun k => g k j) (fun k => g k j) = J j j`. Rewrite using `[← sf_gram, hg]`. Establish `ha : hform (σ : E →+* E) J (Pi.single i 1) (Pi.single i 1) = J i i`.

Rewrite using `[sf_single]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hau : τ (J i i) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k)) (fun k => τ ((Pi.single i 1 : n → E) k))`. Rewrite using `[← sf_map _ τ hτ, ha]`. Establish `hcu : τ ((J * g) i j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k)) (fun k => τ (g k j))`.

Rewrite using `[← sf_map _ τ hτ, hc]`. Establish `hbv : τ (J j j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (g k j)) (fun k => τ (g k j))`. Rewrite using `[← sf_map _ τ hτ, hb]`. Take `⟨tw, htw, -, htw0⟩` from `hsign ((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E))`. Take `⟨ta, hta, hta1, -⟩` from `hsign (Pi.single i 1 : n → E)`.

Take `⟨tb, htb, -, htb0⟩` from `hsign (fun k => g k j)`. Establish `hei : (Pi.single i 1 : n → E) ≠ 0`. Introduce `h`. Establish `h5` using `congr_fun h i`. Simplify using `at h5`.

Establish `hta'` using `hta1 hei`. Rewrite `hta` using `[ha]`. Rewrite `htb` using `[hb]`. Rewrite `htw` using `[sf_map _ τ hτ]`. Establish `hw : (fun k => τ (((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E)) k)) = τ (J i i) • (fun k => τ (g k j)) + (-τ ((J * g) i j)) • (fun k => τ ((Pi.single i 1 : n → E) k))`.

Use function extensionality and compare the values at `k`. Simplify using `[map_add, map_mul, map_neg]`. Rewrite `htw` using `[hw, hau, hcu, sf_cs _ hA, ← hau, ← hcu, ← hbv, hta, htb]`. Rewrite `htw` using `[← Complex.normSq_eq_conj_mul_self]`. Establish `key : ta * (ta * tb - Complex.normSq (τ ((J * g) i j))) = tw` using `by exact_mod_cast htw`.

Establish `hN : Complex.normSq (τ ((J * g) i j)) = ‖τ ((J * g) i j)‖ ^ 2` using `Complex.normSq_eq_norm_sq _`. Rewrite `key` using `[hN]`. Establish `h1 : ‖τ ((J * g) i j)‖ ^ 2 ≤ ta * tb`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `h6 : s * tw < 0`. Rewrite using `[← key]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ta * tb ≤ |ta| * |tb|`.

Rewrite using `[← abs_mul]`. Conclude with `le_abs_self _`. Rewrite using `[hta, htb]`. Apply the tactic sequence `have hn1 : ‖((ta : ℝ) : ℂ)‖ = |ta| := by first | simp | rw [Complex.norm_real, Real.norm_eq_abs]`. Apply the tactic sequence `have hn2 : ‖((tb : ℝ) : ℂ)‖ = |tb| := by first | simp | rw [Complex.norm_real, Real.norm_eq_abs]`.

Rewrite using `[hn1, hn2]`. Use polynomial arithmetic with `[abs_nonneg ta, abs_nonneg tb, norm_nonneg (τ ((J * g) i j))]`.
-/
theorem sf_bound {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) (g : Matrix n n E)
    (hg : cT (σ : E →+* E) g * J * g = J) (i j : n) :
    ‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖ := by
  classical
  obtain ⟨s, hs, hsign⟩ := sf_sign σ J τ hτ hdef
  have hA : ∀ a b, conj ((J.map τ) b a) = (J.map τ) a b := by
    intro a b
    have h3 : τ ((σ : E →+* E) (J b a)) = conj (τ (J b a)) := RingHom.congr_fun hτ _
    have h4 : (σ : E →+* E) (J b a) = J a b := by
      have h1 : (cT (σ : E →+* E) J) a b = J a b := by rw [hH]
      exact h1
    simp only [Matrix.map_apply]
    rw [← h3, h4]
  have hc : (J * g) i j = hform (σ : E →+* E) J (Pi.single i 1) (fun k => g k j) := by
    rw [sf_single]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hb : hform (σ : E →+* E) J (fun k => g k j) (fun k => g k j) = J j j := by
    rw [← sf_gram, hg]
  have ha : hform (σ : E →+* E) J (Pi.single i 1) (Pi.single i 1) = J i i := by
    rw [sf_single]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hau : τ (J i i) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    rw [← sf_map _ τ hτ, ha]
  have hcu : τ ((J * g) i j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ ((Pi.single i 1 : n → E) k))
      (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hc]
  have hbv : τ (J j j) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (g k j)) (fun k => τ (g k j)) := by
    rw [← sf_map _ τ hτ, hb]
  obtain ⟨tw, htw, -, htw0⟩ := hsign ((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E))
  obtain ⟨ta, hta, hta1, -⟩ := hsign (Pi.single i 1 : n → E)
  obtain ⟨tb, htb, -, htb0⟩ := hsign (fun k => g k j)
  have hei : (Pi.single i 1 : n → E) ≠ 0 := by
    intro h
    have h5 := congr_fun h i
    simp at h5
  have hta' := hta1 hei
  rw [ha] at hta
  rw [hb] at htb
  rw [sf_map _ τ hτ] at htw
  have hw : (fun k => τ (((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E)) k)) =
      τ (J i i) • (fun k => τ (g k j)) + (-τ ((J * g) i j)) • (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    funext k
    simp [map_add, map_mul, map_neg]
  rw [hw, hau, hcu, sf_cs _ hA, ← hau, ← hcu, ← hbv, hta, htb] at htw
  rw [← Complex.normSq_eq_conj_mul_self] at htw
  have key : ta * (ta * tb - Complex.normSq (τ ((J * g) i j))) = tw := by exact_mod_cast htw
  have hN : Complex.normSq (τ ((J * g) i j)) = ‖τ ((J * g) i j)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [hN] at key
  have h1 : ‖τ ((J * g) i j)‖ ^ 2 ≤ ta * tb := by
    by_contra hneg
    push_neg at hneg
    have h6 : s * tw < 0 := by
      rw [← key]
      nlinarith
    linarith
  have h3 : ta * tb ≤ |ta| * |tb| := by
    rw [← abs_mul]
    exact le_abs_self _
  rw [hta, htb]
  have hn1 : ‖((ta : ℝ) : ℂ)‖ = |ta| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖((tb : ℝ) : ℂ)‖ = |tb| := by
    first | simp | rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn1, hn2]
  nlinarith [abs_nonneg ta, abs_nonneg tb, norm_nonneg (τ ((J * g) i j))]

end B

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan`. Take `⟨dJ, hdJ0, -, hdJ⟩` from `sf_den (fun p : n × n => J p.1 p.2)`. Take `⟨S, hS⟩ : Λ.FG` from `Module.Finite.iff_fg.mp hfin`. Take `⟨dL, hdL0, -, hdL⟩` from `sf_den (fun p : S × n => (p.1 : n → E) p.2)`. Establish `hΛint : ∀ v ∈ Λ, ∀ k, IsIntegral ℤ (dL * v k)`.

Introduce `v hv`. Rewrite `hv` using `[← hS]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => intro k`. Conclude with `hdL (⟨x, hx⟩, k)`.

Consider the case `zero => intro k`. Simplify using `[isIntegral_zero]`. Consider the case `add x y _ _ hx hy => intro k`. Simplify `(hx k).add (hy k)` using `[mul_add]`. Consider the case `smul r x _ hx`.

Introduce `k`. Establish `: (r • x) k = (algebraMap (𝓞 E) E r) * x k`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Rewrite using `[this, mul_left_comm]`. Conclude with `(RingOfIntegers.isIntegral_coe r).mul (hx k)`.

Establish `hcol : ∀ j : n, ∃ c : E, c ≠ 0 ∧ c • (Pi.single j 1 : n → E) ∈ Λ`. Introduce `j`. Establish `hm : (Pi.single j 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E))`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨m, f, gg, hsum⟩` from `Submodule.mem_span_set'.mp hm`. Take `⟨d, hd0, -, hd⟩` from `sf_den f`. Use `⟨d, hd0, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsum, Finset.smul_sum]`. Use `Submodule.sum_mem _ (fun l _ => ?_)` and prove the remaining obligations.

Take `⟨r, hr⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hd l)`. Establish `: d • (f l • (gg l : n → E)) = r • (gg l : n → E)`. Rewrite using `[smul_smul, ← hr, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `Λ.smul_mem r (gg l).2`.

Use `choose c hc0 hcΛ using hcol`. Set `β : (E →+* ℂ) × n × n → ℝ` to `fun z => ‖z.1 (dJ * dL * c z.2.2)‖ * (‖z.1 (J z.2.1 z.2.1)‖ + ‖z.1 (J z.2.2 z.2.2)‖)`. Take `⟨B, hB⟩` from `(Set.finite_range β).bddAbove`. Use `set T : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} with hT`. Establish `hTfin : T.Finite` using `NumberField.Embeddings.finite_of_norm_le E ℂ B`.

Establish `hmem : ∀ g ∈ level (σ : E →+* E) J Λ, ∀ i j, dJ * dL * c j * ((J * (g : Matrix n n E)) i j) ∈ T`. Introduce `g hg i j`. Establish `hU : cT (σ : E →+* E) (g : Matrix n n E) * J * (g : Matrix n n E) = J` using `hg.1`. Establish `hstab : ∀ x : n → E, x ∈ Λ ↔ (g : Matrix n n E) *ᵥ x ∈ Λ` using `hg.2`. Establish `hgc : (g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E)) ∈ Λ` using `(hstab _).mp (hcΛ j)`.

Establish `hcoord : ∀ k, ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k = c j * (g : Matrix n n E) k j`. Introduce `k`. Simplify using `[Matrix.mulVec_smul]`. Use `⟨?_, fun φ => ?_⟩` and prove the remaining obligations. Establish `: dJ * dL * c j * ((J * (g : Matrix n n E)) i j) = ∑ k, (dJ * J i k) * (dL * ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k)`.

Simplify using `only [hcoord, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `IsIntegral.sum _ (fun k _ => (hdJ (i, k)).mul (hΛint _ hgc k))`.

Rewrite using `[map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `: Finite T` using `hTfin.to_subtype`. Establish `hJu : IsUnit J` using `(Matrix.isUnit_iff_isUnit_det J).mpr hdet`. Use `Finite.of_injective (fun g : level (σ : E →+* E) J Λ => fun i j => (⟨_, hmem g.1 g.2 i j⟩ : T)) ?_` and prove the remaining obligations.

Introduce `g g' hgg`. Establish `h1 : J * (g.1 : Matrix n n E) = J * (g'.1 : Matrix n n E)`. Use extensionality with `i j`. Use `congr_arg Subtype.val (congr_fun (congr_fun hgg i) j)` as an intermediate fact. Conclude with `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hdJ0 hdL0) (hc0 j)) this`.

Conclude with `Subtype.ext (Units.ext (hJu.mul_left_cancel h1))`.
-/
theorem UG_stabilizer_finite : Formalism.UG.StabFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan
  classical
  obtain ⟨dJ, hdJ0, -, hdJ⟩ := sf_den (fun p : n × n => J p.1 p.2)
  obtain ⟨S, hS⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨dL, hdL0, -, hdL⟩ := sf_den (fun p : S × n => (p.1 : n → E) p.2)
  have hΛint : ∀ v ∈ Λ, ∀ k, IsIntegral ℤ (dL * v k) := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem x hx => intro k; exact hdL (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (r • x) k = (algebraMap (𝓞 E) E r) * x k := by
        rw [Pi.smul_apply, Algebra.smul_def]
      rw [this, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hcol : ∀ j : n, ∃ c : E, c ≠ 0 ∧ c • (Pi.single j 1 : n → E) ∈ Λ := by
    intro j
    have hm : (Pi.single j 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; trivial
    obtain ⟨m, f, gg, hsum⟩ := Submodule.mem_span_set'.mp hm
    obtain ⟨d, hd0, -, hd⟩ := sf_den f
    refine ⟨d, hd0, ?_⟩
    rw [← hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun l _ => ?_)
    obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hd l)
    have : d • (f l • (gg l : n → E)) = r • (gg l : n → E) := by
      rw [smul_smul, ← hr, algebraMap_smul]
    rw [this]
    exact Λ.smul_mem r (gg l).2
  choose c hc0 hcΛ using hcol
  let β : (E →+* ℂ) × n × n → ℝ := fun z =>
    ‖z.1 (dJ * dL * c z.2.2)‖ * (‖z.1 (J z.2.1 z.2.1)‖ + ‖z.1 (J z.2.2 z.2.2)‖)
  obtain ⟨B, hB⟩ := (Set.finite_range β).bddAbove
  set T : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  have hmem : ∀ g ∈ level (σ : E →+* E) J Λ, ∀ i j,
      dJ * dL * c j * ((J * (g : Matrix n n E)) i j) ∈ T := by
    intro g hg i j
    have hU : cT (σ : E →+* E) (g : Matrix n n E) * J * (g : Matrix n n E) = J := hg.1
    have hstab : ∀ x : n → E, x ∈ Λ ↔ (g : Matrix n n E) *ᵥ x ∈ Λ := hg.2
    have hgc : (g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E)) ∈ Λ := (hstab _).mp (hcΛ j)
    have hcoord : ∀ k, ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k =
        c j * (g : Matrix n n E) k j := by
      intro k; simp [Matrix.mulVec_smul]
    refine ⟨?_, fun φ => ?_⟩
    · have : dJ * dL * c j * ((J * (g : Matrix n n E)) i j) =
          ∑ k, (dJ * J i k) * (dL * ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k) := by
        simp only [hcoord, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
      rw [this]
      exact IsIntegral.sum _ (fun k _ => (hdJ (i, k)).mul (hΛint _ hgc k))
    · rw [map_mul, norm_mul]
      calc ‖φ (dJ * dL * c j)‖ * ‖φ ((J * (g : Matrix n n E)) i j)‖
          ≤ ‖φ (dJ * dL * c j)‖ * (‖φ (J i i)‖ + ‖φ (J j j)‖) :=
            mul_le_mul_of_nonneg_left (sf_bound σ J φ (hτ φ) hH hdef.2 _ hU i j) (norm_nonneg _)
        _ = β (φ, i, j) := rfl
        _ ≤ B := hB ⟨(φ, i, j), rfl⟩
  have : Finite T := hTfin.to_subtype
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr hdet
  refine Finite.of_injective
    (fun g : level (σ : E →+* E) J Λ => fun i j => (⟨_, hmem g.1 g.2 i j⟩ : T)) ?_
  intro g g' hgg
  have h1 : J * (g.1 : Matrix n n E) = J * (g'.1 : Matrix n n E) := by
    ext i j
    have := congr_arg Subtype.val (congr_fun (congr_fun hgg i) j)
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hdJ0 hdL0) (hc0 j)) this
  exact Subtype.ext (Units.ext (hJu.mul_left_cancel h1))

end Formalism.UG.P
