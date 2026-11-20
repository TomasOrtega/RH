import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def Cg (p : ℕ) (f g : PowerSeries ℂ) : Prop :=
  CoeffIn (Rm p) g ∧ ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ f = g + PowerSeries.C (1 - zetaC p) * w

/- English proof (translation)
Introduce `n`. Rewrite using `[PowerSeries.coeff_C]`. Use `split_ifs`. Conclude with `hc`. Conclude with `R.zero_mem`.
-/
theorem CoeffIn.ksC {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) : CoeffIn R (PowerSeries.C c) := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

/- English proof (translation)
Introduce `n`. Rewrite using `[map_zero]`. Conclude with `R.zero_mem`.
-/
theorem CoeffIn.ksZero (R : Subring ℂ) : CoeffIn R 0 := by
  intro n
  rw [map_zero]
  exact R.zero_mem

/- English proof (translation)
Introduce `n`. Rewrite using `[map_neg]`. Conclude with `R.neg_mem (hf n)`.
-/
theorem CoeffIn.ksNeg {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) : CoeffIn R (-f) := by
  intro n
  rw [map_neg]
  exact R.neg_mem (hf n)

/- English proof (translation)
Conclude with `(Rm p).sub_mem (Rm p).one_mem (zetaC_mem p)`.
-/
theorem ks_one_sub_zetaC_mem (p : ℕ) : 1 - zetaC p ∈ Rm p := by
  exact (Rm p).sub_mem (Rm p).one_mem (zetaC_mem p)

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h`. Conclude with `hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw)`.
-/
theorem Cg.left {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : CoeffIn (Rm p) f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw)

/- English proof (translation)
Conclude with `⟨hf, 0, CoeffIn.ksZero _, by simp⟩`.
-/
theorem Cg.refl {p : ℕ} {f : PowerSeries ℂ} (hf : CoeffIn (Rm p) f) : Cg p f f := by
  exact ⟨hf, 0, CoeffIn.ksZero _, by simp⟩

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h`. Conclude with `⟨hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw), -w, hw.ksNeg, by ring⟩`.
-/
theorem Cg.symm {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : Cg p g f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact ⟨hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw), -w, hw.ksNeg, by ring⟩

/- English proof (translation)
Take `⟨hg, w₁, hw₁, rfl⟩` from `h1`. Take `⟨hh, w₂, hw₂, rfl⟩` from `h2`. Conclude with `⟨hh, w₂ + w₁, hw₂.add hw₁, by ring⟩`.
-/
theorem Cg.trans {p : ℕ} {f g h : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p g h) : Cg p f h := by
  obtain ⟨hg, w₁, hw₁, rfl⟩ := h1
  obtain ⟨hh, w₂, hw₂, rfl⟩ := h2
  exact ⟨hh, w₂ + w₁, hw₂.add hw₁, by ring⟩

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h1`. Take `⟨hg', w', hw', rfl⟩` from `h2`. Establish `hε` using `CoeffIn.ksC (ks_one_sub_zetaC_mem p)`. Use `⟨hg.mul hg', w * g' + g * w' + PowerSeries.C (1 - zetaC p) * w * w', ?_, by ring⟩` and prove the remaining obligations. Conclude with `((hw.mul hg').add (hg.mul hw')).add ((hε.mul hw).mul hw')`.
-/
theorem Cg.mul {p : ℕ} {f g f' g' : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f * f') (g * g') := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  obtain ⟨hg', w', hw', rfl⟩ := h2
  have hε := CoeffIn.ksC (ks_one_sub_zetaC_mem p)
  refine ⟨hg.mul hg', w * g' + g * w' + PowerSeries.C (1 - zetaC p) * w * w', ?_, by ring⟩
  exact ((hw.mul hg').add (hg.mul hw')).add ((hε.mul hw).mul hw')

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h1`. Take `⟨hg', w', hw', rfl⟩` from `h2`. Conclude with `⟨hg.sub hg', w - w', hw.sub hw', by ring⟩`.
-/
theorem Cg.sub {p : ℕ} {f g f' g' : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f - f') (g - g') := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  obtain ⟨hg', w', hw', rfl⟩ := h2
  exact ⟨hg.sub hg', w - w', hw.sub hw', by ring⟩

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h1`. Conclude with `⟨hg.ksNeg, -w, hw.ksNeg, by ring⟩`.
-/
theorem Cg.neg {p : ℕ} {f g : PowerSeries ℂ} (h1 : Cg p f g) : Cg p (-f) (-g) := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  exact ⟨hg.ksNeg, -w, hw.ksNeg, by ring⟩

/- English proof (translation)
Take `⟨hg, w, hw, rfl⟩` from `h1`. Conclude with `⟨hg.xp k, ReciprocityTheory.ChartRestriction.L1.xp k w, hw.xp k, by rw [xp_add, xp_C_mul]⟩`.
-/
theorem Cg.xp {p : ℕ} {f g : PowerSeries ℂ} (h1 : Cg p f g) (k : ℕ) : Cg p (xp k f) (xp k g) := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  exact ⟨hg.xp k, ReciprocityTheory.ChartRestriction.L1.xp k w, hw.xp k, by rw [xp_add, xp_C_mul]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `Cg.refl (CoeffIn.one _)`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).mul (ih fun t ht => h t (Finset.mem_insert_of_mem ht))`.
-/
theorem Cg.prod {p : ℕ} {α : Type*} (s : Finset α) (f g : α → PowerSeries ℂ)
    (h : ∀ t ∈ s, Cg p (f t) (g t)) : Cg p (∏ t ∈ s, f t) (∏ t ∈ s, g t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Cg.refl (CoeffIn.one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

/- English proof (translation)
Take `⟨r, hr, hpr⟩` from `p_mem_span hp`. Use `⟨CoeffIn.map_int _ G, PowerSeries.C r * W.map (Int.castRingHom ℂ), (CoeffIn.ksC hr).mul (CoeffIn.map_int _ W), ?_⟩` and prove the remaining obligations. Rewrite using `[h, map_add, map_mul, PowerSeries.map_C]`. Establish `hc : (Int.castRingHom ℂ) (p : ℤ) = (1 - zetaC p) * r`. Rewrite using `[eq_intCast, Int.cast_natCast, hpr]`.

Rewrite using `[hc, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Cg.of_int {p : ℕ} (hp : p.Prime) {F G W : PowerSeries ℤ} (h : F = G + PowerSeries.C (p : ℤ) * W) :
    Cg p (F.map (Int.castRingHom ℂ)) (G.map (Int.castRingHom ℂ)) := by
  obtain ⟨r, hr, hpr⟩ := p_mem_span hp
  refine ⟨CoeffIn.map_int _ G, PowerSeries.C r * W.map (Int.castRingHom ℂ),
    (CoeffIn.ksC hr).mul (CoeffIn.map_int _ W), ?_⟩
  rw [h, map_add, map_mul, PowerSeries.map_C]
  have hc : (Int.castRingHom ℂ) (p : ℤ) = (1 - zetaC p) * r := by
    rw [eq_intCast, Int.cast_natCast, hpr]
  rw [hc, map_mul]
  ring

/- English proof (translation)
The claim follows from `CoeffIn.map_int R aZ`.
-/
theorem ks_coeffIn_aC (R : Subring ℂ) : CoeffIn R aC := CoeffIn.map_int R aZ

/- English proof (translation)
The claim follows from `CoeffIn.map_int R dZ`.
-/
theorem ks_coeffIn_dC (R : Subring ℂ) : CoeffIn R dC := CoeffIn.map_int R dZ

/- English proof (translation)
Take `⟨g, hg⟩` from `xp_congr hp F`. Establish `h` using `Cg.of_int hp hg`. Rewrite `h` using `[← xp_map, map_pow]`. Then use the resulting hypothesis.
-/
theorem Cg.xp_map_int {p : ℕ} (hp : p.Prime) (F : PowerSeries ℤ) :
    Cg p (ReciprocityTheory.ChartRestriction.L1.xp p (F.map (Int.castRingHom ℂ))) (F.map (Int.castRingHom ℂ) ^ p) := by
  obtain ⟨g, hg⟩ := xp_congr hp F
  have h := Cg.of_int hp hg
  rwa [← xp_map, map_pow] at h

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_xp]`. Simplify using the standard rewrite rules.
-/
theorem ks_xp_one {R : Type*} [CommRing R] (f : PowerSeries R) : xp 1 f = f := by
  ext n
  rw [coeff_xp]
  simp

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_xp, coeff_xp, coeff_xp]`. Establish `hk0 : 0 < k` using `Nat.pos_of_ne_zero hk`. Distinguish the cases in `h1 : k ∣ n`. Take `⟨m, rfl⟩` from `h1`.

Rewrite using `[if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m hk0]`. Distinguish the cases in `h2 : k ∣ m`. Take `⟨j, rfl⟩` from `h2`. Rewrite using `[if_pos (dvd_mul_right k j), if_pos ⟨j, by ring⟩, Nat.mul_div_cancel_left j hk0, show k * (k * j) = k ^ 2 * j by ring, Nat.mul_div_cancel_left j (by positivity)]`. Rewrite using `[if_neg h2, if_neg]`.

Introduce and unpack `⟨j, hj⟩`. Conclude with `h2 ⟨j, Nat.eq_of_mul_eq_mul_left hk0 (by rw [hj]; ring)⟩`. Rewrite using `[if_neg h1, if_neg]`. Conclude with `fun h => h1 (dvd_trans (dvd_pow_self k two_ne_zero) h)`.
-/
theorem ks_xp_xp {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    xp (k ^ 2) f = xp k (xp k f) := by
  ext n
  rw [coeff_xp, coeff_xp, coeff_xp]
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  by_cases h1 : k ∣ n
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m hk0]
    by_cases h2 : k ∣ m
    · obtain ⟨j, rfl⟩ := h2
      rw [if_pos (dvd_mul_right k j), if_pos ⟨j, by ring⟩, Nat.mul_div_cancel_left j hk0,
        show k * (k * j) = k ^ 2 * j by ring, Nat.mul_div_cancel_left j (by positivity)]
    · rw [if_neg h2, if_neg]
      rintro ⟨j, hj⟩
      exact h2 ⟨j, Nat.eq_of_mul_eq_mul_left hk0 (by rw [hj]; ring)⟩
  · rw [if_neg h1, if_neg]
    exact fun h => h1 (dvd_trans (dvd_pow_self k two_ne_zero) h)

/- English proof (translation)
Use extensionality with `⟨a, b, e⟩`. Rewrite using `[mem_Tm hp.pos, Finset.mem_insert, Finset.mem_image]`. Simplify using `only [Finset.mem_range, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hae, hbe⟩`.

Establish `ha : a ∣ p` using `⟨e, hae.symm⟩`. Break down `hp.eq_one_or_self_of_dvd a ha with rfl | rfl` into its components or cases. Use `right`. Conclude with `⟨b, by omega, rfl, rfl, by omega⟩`. Use `left`.

Establish `he : e = 1` using `Nat.eq_of_mul_eq_mul_left hp.pos (hae.trans (mul_one a).symm)`. Substitute `he` using the available equality. Conclude with `⟨rfl, by omega, rfl⟩`. Introduce and unpack `(⟨rfl, rfl, rfl⟩ | ⟨c, hc, rfl, rfl, rfl⟩)`. Conclude with `⟨mul_one _, Nat.zero_lt_one⟩`.

Conclude with `⟨one_mul _, hc⟩`.
-/
theorem Tm_prime {p : ℕ} (hp : p.Prime) :
    Tm p = insert (p, 0, 1) ((Finset.range p).image fun b => (1, b, p)) := by
  ext ⟨a, b, e⟩
  rw [mem_Tm hp.pos, Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨hae, hbe⟩
    have ha : a ∣ p := ⟨e, hae.symm⟩
    rcases hp.eq_one_or_self_of_dvd a ha with rfl | rfl
    · right
      exact ⟨b, by omega, rfl, rfl, by omega⟩
    · left
      have he : e = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (hae.trans (mul_one a).symm)
      subst he
      exact ⟨rfl, by omega, rfl⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨c, hc, rfl, rfl, rfl⟩)
    · exact ⟨mul_one _, Nat.zero_lt_one⟩
    · exact ⟨one_mul _, hc⟩

/- English proof (translation)
Introduce `h`. Take `⟨b, _, hb⟩` from `Finset.mem_image.mp h`. Simplify using `only [Prod.mk.injEq] at hb`. Conclude with `hp.one_lt.ne hb.1`.
-/
theorem Tm_prime_notMem {p : ℕ} (hp : p.Prime) :
    ((p, 0, 1) : ℕ × ℕ × ℕ) ∉ (Finset.range p).image fun b => ((1, b, p) : ℕ × ℕ × ℕ) := by
  intro h
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
  simp only [Prod.mk.injEq] at hb
  exact hp.one_lt.ne hb.1

/- English proof (translation)
Introduce `b b' h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `h.2.1`.
-/
theorem Tm_prime_inj (p : ℕ) : Function.Injective fun b : ℕ => ((1, b, p) : ℕ × ℕ × ℕ) := by
  intro b b' h
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/- English proof (translation)
Rewrite using `[Tm_prime hp, Finset.card_insert_of_notMem (Tm_prime_notMem hp), Finset.card_image_of_injective _ (Tm_prime_inj p), Finset.card_range]`.
-/
theorem card_Tm_prime {p : ℕ} (hp : p.Prime) : (Tm p).card = p + 1 := by
  rw [Tm_prime hp, Finset.card_insert_of_notMem (Tm_prime_notMem hp),
    Finset.card_image_of_injective _ (Tm_prime_inj p), Finset.card_range]

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `hsub : ∀ f : PowerSeries ℂ, sub1 (zetaC ((p, 0, 1) : ℕ × ℕ × ℕ).2.2 ^ ((p, 0, 1) : ℕ × ℕ × ℕ).2.1) (((p, 0, 1) : ℕ × ℕ × ℕ).1 ^ 2) f = xp p (xp p f)`. Introduce `f`. Simplify using `only [sub1, pow_zero, PowerSeries.rescale_one, RingHom.id_apply]`. Conclude with `ks_xp_xp hp0 f`.

Establish `hfac : facSer p (p, 0, 1) = xp p (aC * xp p dC - xp p aC * dC)`. Rewrite using `[facSer, hsub, hsub, xp_sub, xp_mul hp0, xp_mul hp0]`. Rewrite using `[hfac]`. Establish `hd : Cg p (xp p dC) (dC ^ p)` using `Cg.xp_map_int hp dZ`. Establish `ha : Cg p (xp p aC) (aC ^ p)` using `Cg.xp_map_int hp aZ`.

Conclude with `(((Cg.refl (ks_coeffIn_aC _)).mul hd).sub (ha.mul (Cg.refl (ks_coeffIn_dC _)))).xp p`.
-/
theorem facSer_Cg_a {p : ℕ} (hp : p.Prime) :
    Cg p (facSer p (p, 0, 1)) (xp p (aC * dC ^ p - aC ^ p * dC)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hsub : ∀ f : PowerSeries ℂ,
      sub1 (zetaC ((p, 0, 1) : ℕ × ℕ × ℕ).2.2 ^ ((p, 0, 1) : ℕ × ℕ × ℕ).2.1)
        (((p, 0, 1) : ℕ × ℕ × ℕ).1 ^ 2) f = xp p (xp p f) := by
    intro f
    simp only [sub1, pow_zero, PowerSeries.rescale_one, RingHom.id_apply]
    exact ks_xp_xp hp0 f
  have hfac : facSer p (p, 0, 1) = xp p (aC * xp p dC - xp p aC * dC) := by
    rw [facSer, hsub, hsub, xp_sub, xp_mul hp0, xp_mul hp0]
  rw [hfac]
  have hd : Cg p (xp p dC) (dC ^ p) := Cg.xp_map_int hp dZ
  have ha : Cg p (xp p aC) (aC ^ p) := Cg.xp_map_int hp aZ
  exact (((Cg.refl (ks_coeffIn_aC _)).mul hd).sub (ha.mul (Cg.refl (ks_coeffIn_dC _)))).xp p

/- English proof (translation)
Assemble the required witnesses or components as `⟨CoeffIn.map_int _ F, rescale_congr hp b F⟩`.
-/
theorem Cg.rescale_map_int {p : ℕ} (hp : 0 < p) (b : ℕ) (F : PowerSeries ℤ) :
    Cg p (PowerSeries.rescale (zetaC p ^ b) (F.map (Int.castRingHom ℂ))) (F.map (Int.castRingHom ℂ)) := ⟨CoeffIn.map_int _ F, rescale_congr hp b F⟩

/- English proof (translation)
Establish `hsub : ∀ f : PowerSeries ℂ, sub1 (zetaC ((1, b, p) : ℕ × ℕ × ℕ).2.2 ^ ((1, b, p) : ℕ × ℕ × ℕ).2.1) (((1, b, p) : ℕ × ℕ × ℕ).1 ^ 2) f = PowerSeries.rescale (zetaC p ^ b) f`. Introduce `f`. Simplify using `only [sub1, one_pow]`. Conclude with `ks_xp_one _`. Rewrite using `[facSer, hsub, hsub]`.

Establish `hd : Cg p (PowerSeries.rescale (zetaC p ^ b) dC) dC` using `Cg.rescale_map_int hp.pos b dZ`. Establish `ha : Cg p (PowerSeries.rescale (zetaC p ^ b) aC) aC` using `Cg.rescale_map_int hp.pos b aZ`. Conclude with `((Cg.refl ((ks_coeffIn_aC _).xp p)).mul hd).sub (ha.mul (Cg.refl ((ks_coeffIn_dC _).xp p)))`.
-/
theorem facSer_Cg_b {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Cg p (facSer p (1, b, p)) (xp p aC * dC - aC * xp p dC) := by
  have hsub : ∀ f : PowerSeries ℂ,
      sub1 (zetaC ((1, b, p) : ℕ × ℕ × ℕ).2.2 ^ ((1, b, p) : ℕ × ℕ × ℕ).2.1)
        (((1, b, p) : ℕ × ℕ × ℕ).1 ^ 2) f = PowerSeries.rescale (zetaC p ^ b) f := by
    intro f
    simp only [sub1, one_pow]
    exact ks_xp_one _
  rw [facSer, hsub, hsub]
  have hd : Cg p (PowerSeries.rescale (zetaC p ^ b) dC) dC := Cg.rescale_map_int hp.pos b dZ
  have ha : Cg p (PowerSeries.rescale (zetaC p ^ b) aC) aC := Cg.rescale_map_int hp.pos b aZ
  exact ((Cg.refl ((ks_coeffIn_aC _).xp p)).mul hd).sub (ha.mul (Cg.refl ((ks_coeffIn_dC _).xp p)))

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `haR : CoeffIn (Rm p) aC` using `ks_coeffIn_aC _`. Establish `hdR : CoeffIn (Rm p) dC` using `ks_coeffIn_dC _`. Take `⟨w, hw⟩` from `sub_pow_congr hp (xp p aZ * dZ) (aZ * xp p dZ)`. Establish `h1` using `Cg.of_int hp hw`.

Simplify using `only [map_pow, map_sub, map_mul, ← xp_map] at h1`. Establish `ha : Cg p (xp p aC) (aC ^ p)` using `Cg.xp_map_int hp aZ`. Establish `hd : Cg p (xp p dC) (dC ^ p)` using `Cg.xp_map_int hp dZ`. Establish `h2 : Cg p ((xp p aC * dC) ^ p - (aC * xp p dC) ^ p) (xp p (aC ^ p * dC) - xp p (aC * dC ^ p))`. Rewrite using `[mul_pow, mul_pow, xp_mul hp0, xp_mul hp0, xp_pow hp0, xp_pow hp0]`.

Conclude with `((Cg.refl ((haR.xp p).pow p)).mul hd.symm).sub (ha.symm.mul (Cg.refl ((hdR.xp p).pow p)))`. Establish `h3 : xp p (aC ^ p * dC) - xp p (aC * dC ^ p) = - xp p (aC * dC ^ p - aC ^ p * dC)`. Rewrite using `[xp_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h3]`.

Conclude with `h1.trans h2`.
-/
theorem pow_Cg {p : ℕ} (hp : p.Prime) :
    Cg p ((xp p aC * dC - aC * xp p dC) ^ p) (- xp p (aC * dC ^ p - aC ^ p * dC)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have haR : CoeffIn (Rm p) aC := ks_coeffIn_aC _
  have hdR : CoeffIn (Rm p) dC := ks_coeffIn_dC _
  obtain ⟨w, hw⟩ := sub_pow_congr hp (xp p aZ * dZ) (aZ * xp p dZ)
  have h1 := Cg.of_int hp hw
  simp only [map_pow, map_sub, map_mul, ← xp_map] at h1
  have ha : Cg p (xp p aC) (aC ^ p) := Cg.xp_map_int hp aZ
  have hd : Cg p (xp p dC) (dC ^ p) := Cg.xp_map_int hp dZ
  have h2 : Cg p ((xp p aC * dC) ^ p - (aC * xp p dC) ^ p)
      (xp p (aC ^ p * dC) - xp p (aC * dC ^ p)) := by
    rw [mul_pow, mul_pow, xp_mul hp0, xp_mul hp0, xp_pow hp0, xp_pow hp0]
    exact ((Cg.refl ((haR.xp p).pow p)).mul hd.symm).sub (ha.symm.mul (Cg.refl ((hdR.xp p).pow p)))
  have h3 : xp p (aC ^ p * dC) - xp p (aC * dC ^ p) = - xp p (aC * dC ^ p - aC ^ p * dC) := by
    rw [xp_sub]
    ring
  rw [← h3]
  exact h1.trans h2

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `hprod : prodSer p = facSer p (p, 0, 1) * ∏ b ∈ Finset.range p, facSer p (1, b, p)`. Rewrite using `[prodSer, Tm_prime hp, Finset.prod_insert (Tm_prime_notMem hp), Finset.prod_image (fun b _ b' _ h => Tm_prime_inj p h)]`. Establish `hB : Cg p (∏ b ∈ Finset.range p, facSer p (1, b, p)) (∏ _b ∈ Finset.range p, (xp p aC * dC - aC * xp p dC))` using `Cg.prod _ _ _ fun b _ => facSer_Cg_b hp b`. Rewrite `hB` using `[Finset.prod_const, Finset.card_range]`.

Establish `hC` using `(facSer_Cg_a hp).mul (hB.trans (pow_Cg hp))`. Rewrite `hC` using `[← hprod]`. Take `⟨-, w, hw, hwe⟩` from `hC`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[hwe, xp_pow hp0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kronSer {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) = PowerSeries.C (1 - zetaC p) * w := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hprod : prodSer p = facSer p (p, 0, 1) * ∏ b ∈ Finset.range p, facSer p (1, b, p) := by
    rw [prodSer, Tm_prime hp, Finset.prod_insert (Tm_prime_notMem hp),
      Finset.prod_image (fun b _ b' _ h => Tm_prime_inj p h)]
  have hB : Cg p (∏ b ∈ Finset.range p, facSer p (1, b, p))
      (∏ _b ∈ Finset.range p, (xp p aC * dC - aC * xp p dC)) :=
    Cg.prod _ _ _ fun b _ => facSer_Cg_b hp b
  rw [Finset.prod_const, Finset.card_range] at hB
  have hC := (facSer_Cg_a hp).mul (hB.trans (pow_Cg hp))
  rw [← hprod] at hC
  obtain ⟨-, w, hw, hwe⟩ := hC
  refine ⟨w, hw, ?_⟩
  rw [hwe, xp_pow hp0]
  ring

end ReciprocityTheory.ChartRestriction.L1
