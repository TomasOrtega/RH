import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section ValuationRepresentative
variable {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {e : B →ₐ[ℂ] ℂ}

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Take `⟨h1, rfl⟩` from `(hev _ _).1 h`. Take `⟨h2, rfl⟩` from `(hev _ _).1 h'`. Conclude with `(hev _ _).2 ⟨add_mem h1 h2, map_add ev ⟨v, h1⟩ ⟨w, h2⟩⟩`.
-/
private theorem val_add (hV : ValBasic) {v w : L} {a b : ℂ} (h : Val B e v a) (h' : Val B e w b) :
    Val B e (v + w) (a + b) := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨add_mem h1 h2, map_add ev ⟨v, h1⟩ ⟨w, h2⟩⟩

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Take `⟨h1, rfl⟩` from `(hev _ _).1 h`. Take `⟨h2, rfl⟩` from `(hev _ _).1 h'`. Conclude with `(hev _ _).2 ⟨sub_mem h1 h2, map_sub ev ⟨v, h1⟩ ⟨w, h2⟩⟩`.
-/
private theorem val_sub (hV : ValBasic) {v w : L} {a b : ℂ} (h : Val B e v a) (h' : Val B e w b) :
    Val B e (v - w) (a - b) := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨sub_mem h1 h2, map_sub ev ⟨v, h1⟩ ⟨w, h2⟩⟩

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Take `⟨h1, rfl⟩` from `(hev _ _).1 h`. Take `⟨h2, rfl⟩` from `(hev _ _).1 h'`. Conclude with `(hev _ _).2 ⟨mul_mem h1 h2, map_mul ev ⟨v, h1⟩ ⟨w, h2⟩⟩`.
-/
private theorem val_mul (hV : ValBasic) {v w : L} {a b : ℂ} (h : Val B e v a) (h' : Val B e w b) :
    Val B e (v * w) (a * b) := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨mul_mem h1 h2, map_mul ev ⟨v, h1⟩ ⟨w, h2⟩⟩

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Conclude with `(hev _ _).2 ⟨(loc B e).algebraMap_mem c, ev.commutes c⟩`.
-/
private theorem val_const (hV : ValBasic) (c : ℂ) : Val B e (algebraMap ℂ L c) c := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  exact (hev _ _).2 ⟨(loc B e).algebraMap_mem c, ev.commutes c⟩

/- English proof (translation)
Simplify using `using val_const (B := B) (e := e) hV 1`.
-/
private theorem val_one (hV : ValBasic) : Val B e 1 1 := by
  simpa using val_const (B := B) (e := e) hV 1

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Take `⟨h1, rfl⟩` from `(hev _ _).1 h`. Take `⟨h2, rfl⟩` from `(hev _ _).1 h'`. Both sides reduce to the same expression.
-/
private theorem val_unique (hV : ValBasic) {v : L} {a b : ℂ} (h : Val B e v a) (h' : Val B e v b) : a = b := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  rfl

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using val_one hV`. Consider the case `succ N ih => simpa [pow_succ] using val_mul hV ih h`.
-/
private theorem val_pow (hV : ValBasic) {v : L} {a : ℂ} (h : Val B e v a) (N : ℕ) : Val B e (v ^ N) (a ^ N) := by
  induction N with
  | zero => simpa using val_one hV
  | succ N ih => simpa [pow_succ] using val_mul hV ih h

/- English proof (translation)
The claim follows from `(hV L B e).2.2.1 ⟨b, hb⟩`.
-/
private theorem val_mem (hV : ValBasic) {b : L} (hb : b ∈ B) : Val B e b (e ⟨b, hb⟩) :=
  (hV L B e).2.2.1 ⟨b, hb⟩

/- English proof (translation)
Take `⟨hv0, hv⟩` from `(hV L B e).2.2.2 v c h hc`. Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Establish `h1 : Val B e v⁻¹ (ev ⟨v⁻¹, hv⟩)` using `(hev _ _).2 ⟨hv, rfl⟩`. Establish `h2` using `val_mul hV h h1`. Rewrite `h2` using `[mul_inv_cancel₀ hv0]`.

Establish `h3` using `val_unique hV h2 (val_one hV)`. Rewrite using `[← eq_inv_of_mul_eq_one_right h3]`. Conclude with `h1`.
-/
private theorem val_inv (hV : ValBasic) {v : L} {c : ℂ} (h : Val B e v c) (hc : c ≠ 0) : Val B e v⁻¹ c⁻¹ := by
  obtain ⟨hv0, hv⟩ := (hV L B e).2.2.2 v c h hc
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  have h1 : Val B e v⁻¹ (ev ⟨v⁻¹, hv⟩) := (hev _ _).2 ⟨hv, rfl⟩
  have h2 := val_mul hV h h1
  rw [mul_inv_cancel₀ hv0] at h2
  have h3 := val_unique hV h2 (val_one hV)
  rw [← eq_inv_of_mul_eq_one_right h3]
  exact h1

/- English proof (translation)
Take `⟨ev, hev⟩` from `(hV L B e).2.1`. Conclude with `((hev _ _).1 h).1`.
-/
private theorem val_loc (hV : ValBasic) {v : L} {c : ℂ} (h : Val B e v c) : v ∈ loc B e := by
  obtain ⟨ev, hev⟩ := (hV L B e).2.1
  exact ((hev _ _).1 h).1

end ValuationRepresentative

section Mono
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ}

/- English proof (translation)
Establish `hA : rA ℂ x J ≤ rA ℂ x J'` using `Algebra.adjoin_mono fun y ⟨i, hi, j, hy⟩ => ⟨i, h hi, j, hy⟩`. Introduce `y hy`. Establish `hy' : IsIntegral (rA ℂ x J) y` using `hy`. Conclude with `IsIntegral.map_of_comp_eq (Subalgebra.inclusion hA).toRingHom (RingHom.id K) (by ext; rfl) hy'`.
-/
private theorem rB_mono' (x : Fin (d + 1) → F) {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') :
    rB ℂ K x J ≤ rB ℂ K x J' := by
  have hA : rA ℂ x J ≤ rA ℂ x J' := Algebra.adjoin_mono fun y ⟨i, hi, j, hy⟩ => ⟨i, h hi, j, hy⟩
  intro y hy
  have hy' : IsIntegral (rA ℂ x J) y := hy
  exact IsIntegral.map_of_comp_eq (Subalgebra.inclusion hA).toRingHom (RingHom.id K) (by ext; rfl) hy'

/- English proof (translation)
Establish `hA : (rB ℂ K x J).map j2 ≤ (rB ℂ K x J').map j2` using `Subalgebra.map_mono (rB_mono' x h)`. Introduce `y hy`. Establish `hy' : IsIntegral ((rB ℂ K x J).map j2) y` using `hy`. Conclude with `IsIntegral.map_of_comp_eq (Subalgebra.inclusion hA).toRingHom (RingHom.id K') (by ext; rfl) hy'`.
-/
private theorem integralClosure_mono_subset (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') :
    R2 x j2 J ≤ R2 x j2 J' := by
  have hA : (rB ℂ K x J).map j2 ≤ (rB ℂ K x J').map j2 := Subalgebra.map_mono (rB_mono' x h)
  intro y hy
  have hy' : IsIntegral ((rB ℂ K x J).map j2) y := hy
  exact IsIntegral.map_of_comp_eq (Subalgebra.inclusion hA).toRingHom (RingHom.id K') (by ext; rfl) hy'

end Mono

section Main
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private abbrev Xv (a : Fin (d + 1)) : K' := algebraMap F K' (x a)

private abbrev Yv (a : Fin (d + 1)) : K' := j2 (algebraMap F K (x a))

/- English proof (translation)
The claim follows from `(map_ne_zero (algebraMap F K')).2 (x a).ne_zero`.
-/
private theorem Xv_ne (a : Fin (d + 1)) : (Xv (K' := K') x a) ≠ 0 :=
  (map_ne_zero (algebraMap F K')).2 (x a).ne_zero

/- English proof (translation)
The claim follows from `Units.ne_zero ((sysY x j2 d).Y a)`.
-/
private theorem Yv_ne (a : Fin (d + 1)) : Yv x j2 a ≠ 0 := Units.ne_zero ((sysY x j2 d).Y a)

/- English proof (translation)
Use `hG.memX I J hJ i hi a` as an intermediate fact. Rewrite `this` using `[Units.val_mul, Units.val_inv_eq_inv_val]`. Conclude with `this`.
-/
private theorem memX' (hG : (sysY x j2 d).Good) {I J : Finset (Fin (d + 1))} (hJ : J.Nonempty) {i : Fin (d + 1)}
    (hi : i ∈ I) (a : Fin (d + 1)) : Xv x a * (Xv x i)⁻¹ ∈ RY (xv x) j2 I J := by
  have := hG.memX I J hJ i hi a
  rw [Units.val_mul, Units.val_inv_eq_inv_val] at this
  exact this

/- English proof (translation)
Use `hG.memY I J hI j hj a` as an intermediate fact. Rewrite `this` using `[Units.val_mul, Units.val_inv_eq_inv_val]`. Conclude with `this`.
-/
private theorem memY' (hG : (sysY x j2 d).Good) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) {j : Fin (d + 1)}
    (hj : j ∈ J) (a : Fin (d + 1)) : Yv x j2 a * (Yv x j2 j)⁻¹ ∈ RY (xv x) j2 I J := by
  have := hG.memY I J hI j hj a
  rw [Units.val_mul, Units.val_inv_eq_inv_val] at this
  exact this

/- English proof (translation)
Use `show (sysY x j2 d).mu m * (((((sysY x j2 d).X i ^ 1 * (sysY x j2 d).Y j ^ 1)⁻¹ : K'ˣ)) : K') = _`. Rewrite using `[Units.val_inv_eq_inv_val, pow_one, pow_one, Units.val_mul]`. Both sides reduce to the same expression.
-/
private theorem r_inl {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (m : Mi d) :
    (sysY x j2 d).r (app n11 n) (gG x j2 z) i j (toLex (Sum.inl m)) =
      (Xv x (ofLex m).1 * Yv x j2 (ofLex m).2 - Xv x (ofLex m).2 * Yv x j2 (ofLex m).1) * (Xv x i * Yv x j2 j)⁻¹ := by
  show (sysY x j2 d).mu m * (((((sysY x j2 d).X i ^ 1 * (sysY x j2 d).Y j ^ 1)⁻¹ : K'ˣ)) : K') = _
  rw [Units.val_inv_eq_inv_val, pow_one, pow_one, Units.val_mul]
  rfl

/- English proof (translation)
Use `show gS j2 (z l) * (((((sysY x j2 d).X i ^ (n l).1 * (sysY x j2 d).Y j ^ (n l).2)⁻¹ : K'ˣ)) : K') = _`. Rewrite using `[Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression.
-/
private theorem r_inr {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (l : κ) :
    (sysY x j2 d).r (app n11 n) (gG x j2 z) i j (toLex (Sum.inr l)) =
      gS j2 (z l) * (Xv x i ^ (n l).1 * Yv x j2 j ^ (n l).2)⁻¹ := by
  show gS j2 (z l) * (((((sysY x j2 d).X i ^ (n l).1 * (sysY x j2 d).Y j ^ (n l).2)⁻¹ : K'ˣ)) : K') = _
  rw [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  rfl

/- English proof (translation)
Establish `hX : gS j2 (((sysZ K x 0).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = Xv x i` using `by show gS j2 ((algebraMap F K (x i)) ⊗ₜ 1) = _`. Simplify using `[gS, Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.algebraMap_apply F K K']`. Establish `hY : gS j2 (((sysZ K x 0).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = Yv x j2 i` using `by show gS j2 (1 ⊗ₜ (algebraMap F K (x i))) = _`. Simplify using `[gS, Algebra.TensorProduct.productMap_apply_tmul]`. Rewrite using `[map_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_pow, map_pow, hX, hY, map_sub]`.

Simplify using `[gS, Algebra.TensorProduct.productMap_apply_tmul]`.
-/
private theorem gS_gen (i : Fin (d + 1)) (N : ℕ) (b : K) :
    gS j2 ((((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)) =
      Xv x i ^ N * Yv x j2 i ^ N * (algebraMap K K' b - j2 b) := by
  have hX : gS j2 (((sysZ K x 0).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = Xv x i := by
    show gS j2 ((algebraMap F K (x i)) ⊗ₜ 1) = _
    simp [gS, Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.algebraMap_apply F K K']
  have hY : gS j2 (((sysZ K x 0).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = Yv x j2 i := by
    show gS j2 (1 ⊗ₜ (algebraMap F K (x i))) = _
    simp [gS, Algebra.TensorProduct.productMap_apply_tmul]
  rw [map_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_pow, map_pow, hX, hY,
    map_sub]
  simp [gS, Algebra.TensorProduct.productMap_apply_tmul]

/- English proof (translation)
Take `⟨hR1, hGood, hR3, hR4, hR5⟩` from `hR F K K' d x j2 hY.toY0`. Establish `hG` using `hGood d`. Establish `hIne : I.Nonempty` using `⟨i, hi⟩`. Establish `hJne : J.Nonempty` using `⟨j, hj⟩`. Establish `hα` using `val_mem (e := e) hV (memX' x j2 hG hJne hi j)`.

Establish `hβ` using `val_mem (e := e) hV (memY' x j2 hG hIne hj i)`. Generalize the expression as in `e ⟨_, memX' x j2 hG hJne hi j⟩ = α at hα`. Generalize the expression as in `e ⟨_, memY' x j2 hG hIne hj i⟩ = β at hβ`. Establish `hXi` using `Xv_ne (K' := K') x i`. Establish `hXj` using `Xv_ne (K' := K') x j`.

Establish `hYi` using `Yv_ne x j2 i`. Establish `hYj` using `Yv_ne x j2 j`. Establish `hab : α * β = 1`. Establish `hr` using `h (toLex (Sum.inl (toLex (i, j))))`. Rewrite `hr` using `[r_inl]`.

Establish `h1` using `val_sub hV (val_one (B := RY (xv x) j2 I J) (e := e) hV) hr`. Establish `heq : (1 : K') - (Xv x (ofLex (toLex (i, j))).1 * Yv x j2 (ofLex (toLex (i, j))).2 - Xv x (ofLex (toLex (i, j))).2 * Yv x j2 (ofLex (toLex (i, j))).1) * (Xv x i * Yv x j2 j)⁻¹ = Xv x j * (Xv x i)⁻¹ * (Yv x j2 i * (Yv x j2 j)⁻¹)`. Simplify using `only [ofLex_toLex]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[heq, sub_zero]`. Conclude with `val_unique hV (val_mul hV hα hβ) h1`. Establish `hβ0 : β ≠ 0` using `right_ne_zero_of_mul_eq_one hab`. Establish `hinv` using `val_inv hV hβ hβ0`. Establish `hηne : Yv x j2 i * (Yv x j2 j)⁻¹ ≠ 0` using `mul_ne_zero hYi (inv_ne_zero hYj)`.

Establish `hR2 : R2 (xv x) j2 {i} ≤ loc (RY (xv x) j2 I J) e`. Introduce `y hy`. Take `⟨N, hN⟩` from `hR5 {j} j (Finset.mem_singleton_self j) i y (integralClosure_mono_subset (xv x) j2 (by simp) hy)`. Establish `hyJ : y * j2 (algebraMap F K ((x i : F) / x j)) ^ N ∈ RY (xv x) j2 I J` using `(le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (integralClosure_mono_subset (xv x) j2 (Finset.singleton_subset_iff.2 hj) hN)`. Establish `hl` using `val_loc hV (val_mul hV (val_mem (e := e) hV hyJ) (val_pow hV hinv N))`.

Establish `heq : j2 (algebraMap F K ((x i : F) / x j)) = Yv x j2 i * (Yv x j2 j)⁻¹`. Simplify using `[div_eq_mul_inv]`. Rewrite `hl` using `[heq, mul_assoc, ← mul_pow, mul_inv_cancel₀ hηne, one_pow, mul_one]`. Conclude with `hl`. Establish `hgen : ∀ b ∈ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧ z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)}, ∃ c, Val (RY (xv x) j2 I J) e (algebraMap K K' b) c ∧ Val (RY (xv x) j2 I J) e (j2 b) c`.

Introduce and unpack `b ⟨hb, l, N, hl, hz⟩`. Establish `hbR : algebraMap K K' b ∈ RY (xv x) j2 I J` using `(le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rB_mono' (xv x) (Finset.singleton_subset_iff.2 hi) (hR4 {i} b hb).1)`. Establish `hr` using `h (toLex (Sum.inr l))`. Establish `hb1` using `val_mem (e := e) hV hbR`. Use `⟨_, hb1, ?_⟩` and prove the remaining obligations.

Rewrite using `[show (sysY x j2 d).r (app n11 n) (gG x j2 z) i j (toLex (Sum.inr l)) = (Yv x j2 i * (Yv x j2 j)⁻¹) ^ N * (algebraMap K K' b - j2 b) by`. Rewrite using `[r_inr, hl, hz, gS_gen]`. Simplify using `only [mul_pow, inv_pow]`. Use the proof step `field_simp] at hr`. Establish `h2` using `val_mul hV (val_pow hV hinv N) hr`.

Rewrite `h2` using `[← mul_assoc, ← mul_pow, inv_mul_cancel₀ hηne, one_pow, one_mul, mul_zero]`. Establish `h3` using `val_sub hV hb1 h2`. Rewrite `h3` using `[sub_sub_cancel, sub_zero]`. Conclude with `h3`. Establish `hall : ∀ b ∈ rB ℂ K (xv x) {i}, ∃ c, Val (RY (xv x) j2 I J) e (algebraMap K K' b) c ∧ Val (RY (xv x) j2 I J) e (j2 b) c`.

Introduce `b hb`. Establish `hb' : b ∈ (Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧ z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)})`. Rewrite using `[hZ.gen i]`. Conclude with `hb`. Use `clear hb`.

Proceed by induction on `hb' using Algebra.adjoin_induction with`. Consider the case `mem b hb => exact hgen b hb`. Consider the case `algebraMap c`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply]`.

Conclude with `val_const hV c`. Rewrite using `[AlgHom.commutes]`. Conclude with `val_const hV c`. Consider the case `add a b _ _ ha hb`. Take `⟨c, h1, h2⟩` from `ha`.

Take `⟨c', h1', h2'⟩` from `hb`. Conclude with `⟨c + c', by simpa using val_add hV h1 h1', by simpa using val_add hV h2 h2'⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨c, h1, h2⟩` from `ha`. Take `⟨c', h1', h2'⟩` from `hb`.

Conclude with `⟨c * c', by simpa using val_mul hV h1 h1', by simpa using val_mul hV h2 h2'⟩`. Take `⟨e0, hloc, hval⟩` from `hL F K K' d x j2 hY.toY0 I J i hi e`. Use `⟨e0, hloc, hval, fun b hb h1 => ?_⟩` and prove the remaining obligations. Take `⟨c, hc1, hc2⟩` from `hall b hb`. Establish `hc : e0 ⟨_, h1⟩ = c` using `val_unique hV (val_mem hV h1) ((hval _ _).1 hc1)`.

Rewrite using `[hc]`. Conclude with `(hval _ _).1 hc2`.
-/
private theorem core (hL : LocEq) (hV : ValBasic) (hR : RYBasic)
    {Fx : Finset (fib ℂ K' (xv x))} {A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ} (hY : Y1 x j2 Fx A)
    {κ : Type} [LinearOrder κ] [Fintype κ] {n : κ → ℕ × ℕ} {z : κ → K ⊗[ℂ] K} (hZ : ZF K x n z)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (e : RY (xv x) j2 I J →ₐ[ℂ] ℂ)
    (h : ∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) i j l) 0) :
    ∃ e0 : rB ℂ K' (xv x) {i} →ₐ[ℂ] ℂ, loc (RY (xv x) j2 I J) e = loc (rB ℂ K' (xv x) {i}) e0 ∧
      (∀ v c, Val (RY (xv x) j2 I J) e v c ↔ Val (rB ℂ K' (xv x) {i}) e0 v c) ∧
      IsFix (rB ℂ K' (xv x) {i}) e0 j2 (rB ℂ K (xv x) {i}) := by
  obtain ⟨hR1, hGood, hR3, hR4, hR5⟩ := hR F K K' d x j2 hY.toY0
  have hG := hGood d
  have hIne : I.Nonempty := ⟨i, hi⟩
  have hJne : J.Nonempty := ⟨j, hj⟩
  have hα := val_mem (e := e) hV (memX' x j2 hG hJne hi j)
  have hβ := val_mem (e := e) hV (memY' x j2 hG hIne hj i)
  generalize e ⟨_, memX' x j2 hG hJne hi j⟩ = α at hα
  generalize e ⟨_, memY' x j2 hG hIne hj i⟩ = β at hβ
  have hXi := Xv_ne (K' := K') x i
  have hXj := Xv_ne (K' := K') x j
  have hYi := Yv_ne x j2 i
  have hYj := Yv_ne x j2 j
  have hab : α * β = 1 := by
    have hr := h (toLex (Sum.inl (toLex (i, j))))
    rw [r_inl] at hr
    have h1 := val_sub hV (val_one (B := RY (xv x) j2 I J) (e := e) hV) hr
    have heq : (1 : K') - (Xv x (ofLex (toLex (i, j))).1 * Yv x j2 (ofLex (toLex (i, j))).2 -
        Xv x (ofLex (toLex (i, j))).2 * Yv x j2 (ofLex (toLex (i, j))).1) * (Xv x i * Yv x j2 j)⁻¹ =
        Xv x j * (Xv x i)⁻¹ * (Yv x j2 i * (Yv x j2 j)⁻¹) := by
      simp only [ofLex_toLex]
      field_simp
      ring
    rw [heq, sub_zero] at h1
    exact val_unique hV (val_mul hV hα hβ) h1
  have hβ0 : β ≠ 0 := right_ne_zero_of_mul_eq_one hab
  have hinv := val_inv hV hβ hβ0
  have hηne : Yv x j2 i * (Yv x j2 j)⁻¹ ≠ 0 := mul_ne_zero hYi (inv_ne_zero hYj)
  have hR2 : R2 (xv x) j2 {i} ≤ loc (RY (xv x) j2 I J) e := by
    intro y hy
    obtain ⟨N, hN⟩ := hR5 {j} j (Finset.mem_singleton_self j) i y (integralClosure_mono_subset (xv x) j2 (by simp) hy)
    have hyJ : y * j2 (algebraMap F K ((x i : F) / x j)) ^ N ∈ RY (xv x) j2 I J :=
      (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (integralClosure_mono_subset (xv x) j2 (Finset.singleton_subset_iff.2 hj) hN)
    have hl := val_loc hV (val_mul hV (val_mem (e := e) hV hyJ) (val_pow hV hinv N))
    have heq : j2 (algebraMap F K ((x i : F) / x j)) = Yv x j2 i * (Yv x j2 j)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [heq, mul_assoc, ← mul_pow, mul_inv_cancel₀ hηne, one_pow, mul_one] at hl
    exact hl
  have hgen : ∀ b ∈ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
      z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)},
      ∃ c, Val (RY (xv x) j2 I J) e (algebraMap K K' b) c ∧ Val (RY (xv x) j2 I J) e (j2 b) c := by
    rintro b ⟨hb, l, N, hl, hz⟩
    have hbR : algebraMap K K' b ∈ RY (xv x) j2 I J :=
      (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J)
        (rB_mono' (xv x) (Finset.singleton_subset_iff.2 hi) (hR4 {i} b hb).1)
    have hr := h (toLex (Sum.inr l))
    have hb1 := val_mem (e := e) hV hbR
    refine ⟨_, hb1, ?_⟩
    rw [show (sysY x j2 d).r (app n11 n) (gG x j2 z) i j (toLex (Sum.inr l)) =
      (Yv x j2 i * (Yv x j2 j)⁻¹) ^ N * (algebraMap K K' b - j2 b) by
        rw [r_inr, hl, hz, gS_gen]
        simp only [mul_pow, inv_pow]
        field_simp] at hr
    have h2 := val_mul hV (val_pow hV hinv N) hr
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hηne, one_pow, one_mul, mul_zero] at h2
    have h3 := val_sub hV hb1 h2
    rw [sub_sub_cancel, sub_zero] at h3
    exact h3
  have hall : ∀ b ∈ rB ℂ K (xv x) {i},
      ∃ c, Val (RY (xv x) j2 I J) e (algebraMap K K' b) c ∧ Val (RY (xv x) j2 I J) e (j2 b) c := by
    intro b hb
    have hb' : b ∈ (Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
      z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)}) := by
      rw [hZ.gen i]; exact hb
    clear hb
    induction hb' using Algebra.adjoin_induction with
    | mem b hb => exact hgen b hb
    | algebraMap c =>
      refine ⟨c, ?_, ?_⟩
      · rw [← IsScalarTower.algebraMap_apply]; exact val_const hV c
      · rw [AlgHom.commutes]; exact val_const hV c
    | add a b _ _ ha hb =>
      obtain ⟨c, h1, h2⟩ := ha
      obtain ⟨c', h1', h2'⟩ := hb
      exact ⟨c + c', by simpa using val_add hV h1 h1', by simpa using val_add hV h2 h2'⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, h1, h2⟩ := ha
      obtain ⟨c', h1', h2'⟩ := hb
      exact ⟨c * c', by simpa using val_mul hV h1 h1', by simpa using val_mul hV h2 h2'⟩
  obtain ⟨e0, hloc, hval⟩ := hL F K K' d x j2 hY.toY0 I J i hi e
  refine ⟨e0, hloc, hval, fun b hb h1 => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hall b hb
  have hc : e0 ⟨_, h1⟩ = c := val_unique hV (val_mem hV h1) ((hval _ _).1 hc1)
  rw [hc]
  exact (hval _ _).1 hc2

end Main

/- English proof (translation)
Introduce `hL hV hR _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ I J i hi j hj e h`. Take `⟨e0, hloc, hval, hfix⟩` from `core x j2 hL hV hR hY hZ hi hj e h`. Choose the witnesses or unpack the hypotheses as in `rfl : i = 0 := by`. Assume the negation of the conclusion as `h0`. Conclude with `hY.off i h0 e0 hfix`.

Take `⟨hR1, hGood, hR3, hR4, hR5⟩` from `hR F K K' d x j2 hY.toY0`. Establish `hG` using `hGood d`. Establish `hIne : I.Nonempty` using `⟨0, hi⟩`. Establish `hJne : J.Nonempty` using `⟨j, hj⟩`. Establish `ht` using `hY.orig e0 hfix`.

Establish `hI : I = {0}`. Use `Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Take `⟨m, rfl⟩` from `Fin.exists_succ_eq.2 h0`. Establish `h1 : Val (rB ℂ K' (xv x) {0}) e0 (algebraMap F K' ((x m.succ : F) / x 0)) 0`.

Use `val_mem (e := e0) hV (tco_mem ℂ K' (xv x) m)` as an intermediate fact. Rewrite `this` using `[ht m]`. Then use the resulting hypothesis. Establish `h2` using `(hval _ _).2 h1`. Establish `hm` using `memX' x j2 hG hJne ha 0`. Establish `hv` using `val_mul hV h2 (val_mem (e := e) hV hm)`.

Establish `heq : algebraMap F K' ((x m.succ : F) / x 0) * (Xv x 0 * (Xv x m.succ)⁻¹) = 1`. Establish `h3` using `Xv_ne (K' := K') x 0`. Establish `h4` using `Xv_ne (K' := K') x m.succ`. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hv` using `[heq, zero_mul]`. Conclude with `zero_ne_one (val_unique hV hv (val_one hV))`. Establish `hJ : J = {0}`. Use `Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hJne, fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Take `⟨m, rfl⟩` from `Fin.exists_succ_eq.2 h0`. Establish `hb` using `tco_mem ℂ K (xv x) m`. Establish `hb1` using `(hR4 {0} _ hb).1`. Establish `h1` using `hfix _ hb hb1`. Establish `h0e : e0 ⟨_, hb1⟩ = 0`.

Rewrite using `[← ht m]`. Conclude with `congrArg e0 (Subtype.ext (IsScalarTower.algebraMap_apply F K K' _).symm)`. Rewrite `h1` using `[h0e]`. Establish `h2` using `(hval _ _).2 h1`. Establish `hm` using `memY' x j2 hG hIne ha 0`.

Establish `hv` using `val_mul hV h2 (val_mem (e := e) hV hm)`. Establish `heq : j2 (algebraMap F K ((xv x m.succ) / xv x 0)) * (Yv x j2 0 * (Yv x j2 m.succ)⁻¹) = 1`. Establish `h3` using `Yv_ne x j2 0`. Establish `h4` using `Yv_ne x j2 m.succ`. Rewrite using `[map_div₀, map_div₀]`.

Clear the denominators using the available nonvanishing facts. Rewrite `hv` using `[heq, zero_mul]`. Conclude with `zero_ne_one (val_unique hV hv (val_one hV))`. Conclude with `⟨hJ, ⟨e0, ht⟩, (hY.fx _).2 hfix, hI, hloc, hval⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.ptG_of :
    LocEq → ValBasic → RYBasic → PtT → PtG := by
  intro hL hV hR _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ I J i hi j hj e h
  obtain ⟨e0, hloc, hval, hfix⟩ := core x j2 hL hV hR hY hZ hi hj e h
  obtain rfl : i = 0 := by
    by_contra h0
    exact hY.off i h0 e0 hfix
  obtain ⟨hR1, hGood, hR3, hR4, hR5⟩ := hR F K K' d x j2 hY.toY0
  have hG := hGood d
  have hIne : I.Nonempty := ⟨0, hi⟩
  have hJne : J.Nonempty := ⟨j, hj⟩
  have ht := hY.orig e0 hfix
  have hI : I = {0} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun a ha => ?_⟩
    by_contra h0
    obtain ⟨m, rfl⟩ := Fin.exists_succ_eq.2 h0
    have h1 : Val (rB ℂ K' (xv x) {0}) e0 (algebraMap F K' ((x m.succ : F) / x 0)) 0 := by
      have := val_mem (e := e0) hV (tco_mem ℂ K' (xv x) m)
      rwa [ht m] at this
    have h2 := (hval _ _).2 h1
    have hm := memX' x j2 hG hJne ha 0
    have hv := val_mul hV h2 (val_mem (e := e) hV hm)
    have heq : algebraMap F K' ((x m.succ : F) / x 0) * (Xv x 0 * (Xv x m.succ)⁻¹) = 1 := by
      have h3 := Xv_ne (K' := K') x 0
      have h4 := Xv_ne (K' := K') x m.succ
      rw [map_div₀]
      field_simp
    rw [heq, zero_mul] at hv
    exact zero_ne_one (val_unique hV hv (val_one hV))
  have hJ : J = {0} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hJne, fun a ha => ?_⟩
    by_contra h0
    obtain ⟨m, rfl⟩ := Fin.exists_succ_eq.2 h0
    have hb := tco_mem ℂ K (xv x) m
    have hb1 := (hR4 {0} _ hb).1
    have h1 := hfix _ hb hb1
    have h0e : e0 ⟨_, hb1⟩ = 0 := by
      rw [← ht m]
      exact congrArg e0 (Subtype.ext (IsScalarTower.algebraMap_apply F K K' _).symm)
    rw [h0e] at h1
    have h2 := (hval _ _).2 h1
    have hm := memY' x j2 hG hIne ha 0
    have hv := val_mul hV h2 (val_mem (e := e) hV hm)
    have heq : j2 (algebraMap F K ((xv x m.succ) / xv x 0)) * (Yv x j2 0 * (Yv x j2 m.succ)⁻¹) = 1 := by
      have h3 := Yv_ne x j2 0
      have h4 := Yv_ne x j2 m.succ
      rw [map_div₀, map_div₀]
      field_simp
    rw [heq, zero_mul] at hv
    exact zero_ne_one (val_unique hV hv (val_one hV))
  exact ⟨hJ, ⟨e0, ht⟩, (hY.fx _).2 hfix, hI, hloc, hval⟩
