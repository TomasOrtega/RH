import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpoly

open Matrix Polynomial

namespace GlobalTheory.IsoIdem

/- English proof (translation)
Take `⟨q, rfl⟩` from `GlobalTheory.CommSep.eq_aeval_of_commute_of_separable A hs y hy`. Break down `k with _ | k` into its components or cases. Rewrite `hk` using `[pow_zero]`. Conclude with `eq_zero_of_zero_eq_one hk.symm _`. Establish `hsq : Squarefree (minpoly E A)` using `Squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly A) hs.squarefree`.

Establish `h1 : minpoly E A ∣ q ^ (k + 1)` using `minpoly.dvd E A (by rw [map_pow]; exact hk)`. Establish `h2 : minpoly E A ∣ q` using `(hsq.dvd_pow_iff_dvd (by omega)).1 h1`. Conclude with `minpoly.dvd_iff.1 h2`.
-/
theorem eq_zero_of_pow_eq_zero {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) (k : ℕ)
    (hk : y ^ k = 0) : y = 0 := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CommSep.eq_aeval_of_commute_of_separable A hs y hy
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm _
  have hsq : Squarefree (minpoly E A) :=
    Squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly A) hs.squarefree
  have h1 : minpoly E A ∣ q ^ (k + 1) := minpoly.dvd E A (by rw [map_pow]; exact hk)
  have h2 : minpoly E A ∣ q := (hsq.dvd_pow_iff_dvd (by omega)).1 h1
  exact minpoly.dvd_iff.1 h2

/- English proof (translation)
Set `S` to `Subalgebra.centralizer E ({A} : Set (Matrix (Fin r) (Fin r) E))`. Establish `hmem : ∀ a : Matrix (Fin r) (Fin r) E, a ∈ S ↔ a * A = A * a`. Introduce `a`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Simplify using `[eq_comm]`.

Use `letI : CommRing S := { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (GlobalTheory.CommSep.commute_of_commute_separable E r A hs a b ((hmem a).1 a.2) ((hmem b).1 b.2)) }`. Use `haveI : IsArtinianRing S := IsArtinianRing.of_finite E S`. Take `⟨n, w, hw⟩` from `IsArtinian.exists_pow_succ_smul_dvd (R := S) (M := S) ⟨z, (hmem z).2 hz⟩ 1`. Use `⟨n, w, (hmem w).1 w.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hw` as an intermediate fact.

Simplify using `using this`.
-/
theorem exists_pow_mul_eq {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (z : Matrix (Fin r) (Fin r) E) (hz : z * A = A * z) :
    ∃ n : ℕ, ∃ w : Matrix (Fin r) (Fin r) E, w * A = A * w ∧ z ^ (n + 1) * w = z ^ n := by
  let S := Subalgebra.centralizer E ({A} : Set (Matrix (Fin r) (Fin r) E))
  have hmem : ∀ a : Matrix (Fin r) (Fin r) E, a ∈ S ↔ a * A = A * a := by
    intro a; rw [Subalgebra.mem_centralizer_iff]; simp [eq_comm]
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun a b => Subtype.ext (GlobalTheory.CommSep.commute_of_commute_separable E r A hs a b
      ((hmem a).1 a.2) ((hmem b).1 b.2)) }
  haveI : IsArtinianRing S := IsArtinianRing.of_finite E S
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := S) (M := S) ⟨z, (hmem z).2 hz⟩ 1
  refine ⟨n, w, (hmem w).1 w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa using this

/- English proof (translation)
Establish `hA' : star A = A` using `hA`. Use `congrArg star hy` as an intermediate fact. Rewrite `this` using `[star_mul, star_mul, hA']`. Conclude with `this.symm`.
-/
theorem star_mul_comm {E : Type} [Field E] [StarRing E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hA : A.IsHermitian) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) :
    star y * A = A * star y := by
  have hA' : star A = A := hA
  have := congrArg star hy
  rw [star_mul, star_mul, hA'] at this
  exact this.symm

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_succ' w j, show m + (j + 1) = j + (m + 1) by omega, pow_add]`. Simplify using `only [mul_assoc]`. Use `_ = z ^ (m + j) * w ^ j := by rw [h, ← pow_add, show j + m = m + j by omega]`. Use `_ = z ^ m := ih`.
-/
theorem pow_add_mul_pow {R : Type} [Ring R] (z w : R) (m : ℕ) (h : z ^ (m + 1) * w = z ^ m) :
    ∀ j : ℕ, z ^ (m + j) * w ^ j = z ^ m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc z ^ (m + (j + 1)) * w ^ (j + 1) = z ^ j * (z ^ (m + 1) * w) * w ^ j := by
          rw [pow_succ' w j, show m + (j + 1) = j + (m + 1) by omega, pow_add]
          simp only [mul_assoc]
      _ = z ^ (m + j) * w ^ j := by rw [h, ← pow_add, show j + m = m + j by omega]
      _ = z ^ m := ih

/- English proof (translation)
Introduce `E _ _ r A hA hs`. Establish `comm : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → a * b = b * a` using `GlobalTheory.CommSep.commute_of_commute_separable E r A hs`. Establish `cstar` using `star_mul_comm A hA`. Establish `cmul : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → (a * b) * A = A * (a * b)`. Introduce `a b ha hb`.

Rewrite using `[mul_assoc, hb, ← mul_assoc, ha, mul_assoc]`. Establish `cadd : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → (a + b) * A = A * (a + b)`. Introduce `a b ha hb`. Rewrite using `[add_mul, mul_add, ha, hb]`. Establish `csub : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → (a - b) * A = A * (a - b)`.

Introduce `a b ha hb`. Rewrite using `[sub_mul, mul_sub, ha, hb]`. Establish `cone : (1 : Matrix (Fin r) (Fin r) E) * A = A * 1` using `by simp`. Establish `cpow : ∀ a : Matrix (Fin r) (Fin r) E, a * A = A * a → ∀ k : ℕ, a ^ k * A = A * a ^ k`. Introduce `a ha k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `cmul _ _ ih ha`. Set `S : Set (Matrix (Fin r) (Fin r) E)` to `{f | f * A = A * f ∧ f * f = f ∧ f * star f = 0}`.

Take `⟨f, ⟨hfC, hff, hfs⟩, hmax⟩` from `(measure fun f : Matrix (Fin r) (Fin r) E => r - f.rank).wf.has_min S ⟨0, by simp [S]⟩`. Use `⟨f, hfC, hff, hfs, ?_⟩` and prove the remaining obligations. Introduce `y hy hiso`. Assume the negation of the conclusion as `hz`. Use `set e := 1 - f - star f with he`.

Use `set z := y * e with hzdef`. Establish `hfsC` using `cstar f hfC`. Establish `heC : e * A = A * e` using `csub _ _ (csub _ _ cone hfC) hfsC`. Establish `hzC : z * A = A * z` using `cmul _ _ hy heC`. Establish `hsf : star f * f = 0` using `by rw [← comm f (star f) hfC hfsC]; exact hfs`.

Establish `hsfsf : star f * star f = star f` using `by rw [← star_mul, hff]`. Establish `hfe : f * e = 0` using `by rw [he, mul_sub, mul_sub, mul_one, hff, hfs]; abel`. Establish `hsfe : star f * e = 0` using `by rw [he, mul_sub, mul_sub, mul_one, hsf, hsfsf]; abel`. Establish `hef : e * star f = 0` using `by rw [← comm _ _ hfsC heC]; exact hsfe`. Establish `hee : e * e = e`.

Combine the equalities or inequalities in the displayed calculation. Establish `hestar : star e = e`. Rewrite using `[he, star_sub, star_sub, star_one, star_star, sub_right_comm]`. Establish `hze : z * e = z` using `by rw [hzdef, mul_assoc, hee]`. Take `⟨n, w, hwC, hw⟩` from `exists_pow_mul_eq A hs z hzC`.

Establish `hw' : z ^ (n + 1 + 1) * w = z ^ (n + 1)`. Rewrite using `[pow_succ' z (n + 1), mul_assoc, hw, ← pow_succ']`. Establish `key` using `pow_add_mul_pow z w (n + 1) hw' (n + 1)`. Establish `hzw : Commute z w` using `comm _ _ hzC hwC`. Use `set g := z ^ (n + 1) * w ^ (n + 1) with hg`.

Establish `hgC : g * A = A * g` using `cmul _ _ (cpow _ hzC _) (cpow _ hwC _)`. Establish `hgz : g * z ^ (n + 1) = z ^ (n + 1)`. Rewrite using `[hg, mul_assoc, ((hzw.pow_pow (n + 1) (n + 1)).symm).eq, ← mul_assoc, ← pow_add, key]`. Establish `hgg : g * g = g` using `by conv_lhs => rw [hg]`. Rewrite using `[← mul_assoc, hgz]`.

Establish `hg0 : g ≠ 0`. Introduce `h0`. Rewrite `hgz` using `[h0, zero_mul]`. Conclude with `hz (eq_zero_of_pow_eq_zero A hs z hzC _ hgz.symm)`. Use `set a := z ^ n * w ^ (n + 1) with ha`.

Establish `haC : a * A = A * a` using `cmul _ _ (cpow _ hzC _) (cpow _ hwC _)`. Establish `hgza : g = z * a` using `by rw [hg, ha, pow_succ', mul_assoc]`. Establish `hgs : g * star g = 0`. Establish `hb : (a * star a) * A = A * (a * star a)` using `cmul _ _ haC (cstar _ haC)`. Rewrite using `[hgza, star_mul, mul_assoc, ← mul_assoc a, comm _ _ hb (cstar _ hzC), ← mul_assoc]`.

Rewrite using `[show z * star z = 0 from hiso, zero_mul]`. Establish `hge : g * e = g`. Rewrite using `[hgza, mul_assoc, comm a e haC heC, ← mul_assoc, hze]`. Establish `hfz : f * z = 0`. Rewrite using `[hzdef, ← mul_assoc, comm f y hfC hy, mul_assoc, hfe, mul_zero]`.

Establish `hfg : f * g = 0` using `by rw [hgza, ← mul_assoc, hfz, zero_mul]`. Establish `hgf : g * f = 0` using `by rw [comm g f hgC hfC]; exact hfg`. Establish `hfsg : f * star g = 0`. Rewrite using `[← hge, star_mul, hestar, ← mul_assoc, hfe, zero_mul]`. Establish `hgsf : g * star f = 0` using `by rw [← hge, mul_assoc, hef, mul_zero]`.

Establish `hf'S : f + g ∈ S`. Use `⟨cadd _ _ hfC hgC, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, mul_add, mul_add, hff, hfg, hgf, hgg]`. Normalize the expressions using the abelian group laws. Rewrite using `[star_add, add_mul, mul_add, mul_add, hfs, hfsg, hgsf, hgs]`.

Normalize the expressions using the abelian group laws. Establish `hrank : f.rank < (f + g).rank`. Unfold `Matrix.rank`. Apply `Submodule.finrank_lt_finrank_of_lt` to reduce the goal to its premises. Rewrite using `[SetLike.lt_iff_le_and_exists]`.

Prove the components needed by the constructor for the conclusion. Establish `h1 : (f + g) * f = f` using `by rw [add_mul, hff, hgf, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : Fin r → E, g *ᵥ v ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Simplify using `only [not_exists, not_not] at hall`. Apply `hg0` to reduce the goal to its premises. Use extensionality with `i j`. Use `congrFun (hall (Pi.single j 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single]`.

Use `⟨g *ᵥ v, ⟨g *ᵥ v, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hfg, hgg, zero_add]`. Introduce and unpack `⟨u, hu⟩`. Rewrite `hu` using `[Matrix.mulVecLin_apply]`. Apply `hv` to reduce the goal to its premises.

Establish `hgv : g *ᵥ v = g *ᵥ (g *ᵥ v)` using `by rw [Matrix.mulVec_mulVec, hgg]`. Rewrite using `[hgv, ← hu, Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]`. Establish `hle : (f + g).rank ≤ r`. Simplify using `using Matrix.rank_le_card_width (f + g)`. Conclude with `hmax (f + g) hf'S (show r - (f + g).rank < r - f.rank by omega)`.
-/
theorem isoIdem : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E),
    A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧
      f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y →
        y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  intro E _ _ r A hA hs
  have comm : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → a * b = b * a :=
    GlobalTheory.CommSep.commute_of_commute_separable E r A hs
  have cstar := star_mul_comm A hA
  have cmul : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a * b) * A = A * (a * b) := by
    intro a b ha hb; rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have cadd : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a + b) * A = A * (a + b) := by
    intro a b ha hb; rw [add_mul, mul_add, ha, hb]
  have csub : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a - b) * A = A * (a - b) := by
    intro a b ha hb; rw [sub_mul, mul_sub, ha, hb]
  have cone : (1 : Matrix (Fin r) (Fin r) E) * A = A * 1 := by simp
  have cpow : ∀ a : Matrix (Fin r) (Fin r) E, a * A = A * a → ∀ k : ℕ, a ^ k * A = A * a ^ k := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact cmul _ _ ih ha
  let S : Set (Matrix (Fin r) (Fin r) E) := {f | f * A = A * f ∧ f * f = f ∧ f * star f = 0}
  obtain ⟨f, ⟨hfC, hff, hfs⟩, hmax⟩ :=
    (measure fun f : Matrix (Fin r) (Fin r) E => r - f.rank).wf.has_min S ⟨0, by simp [S]⟩
  refine ⟨f, hfC, hff, hfs, ?_⟩
  intro y hy hiso
  by_contra hz
  set e := 1 - f - star f with he
  set z := y * e with hzdef
  have hfsC := cstar f hfC
  have heC : e * A = A * e := csub _ _ (csub _ _ cone hfC) hfsC
  have hzC : z * A = A * z := cmul _ _ hy heC
  have hsf : star f * f = 0 := by rw [← comm f (star f) hfC hfsC]; exact hfs
  have hsfsf : star f * star f = star f := by rw [← star_mul, hff]
  have hfe : f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hff, hfs]; abel
  have hsfe : star f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hsf, hsfsf]; abel
  have hef : e * star f = 0 := by rw [← comm _ _ hfsC heC]; exact hsfe
  have hee : e * e = e := by
    calc e * e = (1 - f - star f) * e := by rw [← he]
      _ = e := by rw [sub_mul, sub_mul, one_mul, hfe, hsfe, sub_zero, sub_zero]
  have hestar : star e = e := by
    rw [he, star_sub, star_sub, star_one, star_star, sub_right_comm]
  have hze : z * e = z := by rw [hzdef, mul_assoc, hee]
  obtain ⟨n, w, hwC, hw⟩ := exists_pow_mul_eq A hs z hzC
  have hw' : z ^ (n + 1 + 1) * w = z ^ (n + 1) := by
    rw [pow_succ' z (n + 1), mul_assoc, hw, ← pow_succ']
  have key := pow_add_mul_pow z w (n + 1) hw' (n + 1)
  have hzw : Commute z w := comm _ _ hzC hwC
  set g := z ^ (n + 1) * w ^ (n + 1) with hg
  have hgC : g * A = A * g := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgz : g * z ^ (n + 1) = z ^ (n + 1) := by
    rw [hg, mul_assoc, ((hzw.pow_pow (n + 1) (n + 1)).symm).eq, ← mul_assoc, ← pow_add, key]
  have hgg : g * g = g := by
    conv_lhs => rw [hg]
    rw [← mul_assoc, hgz]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgz
    exact hz (eq_zero_of_pow_eq_zero A hs z hzC _ hgz.symm)
  set a := z ^ n * w ^ (n + 1) with ha
  have haC : a * A = A * a := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgza : g = z * a := by rw [hg, ha, pow_succ', mul_assoc]
  have hgs : g * star g = 0 := by
    have hb : (a * star a) * A = A * (a * star a) := cmul _ _ haC (cstar _ haC)
    rw [hgza, star_mul, mul_assoc, ← mul_assoc a, comm _ _ hb (cstar _ hzC), ← mul_assoc]
    rw [show z * star z = 0 from hiso, zero_mul]
  have hge : g * e = g := by
    rw [hgza, mul_assoc, comm a e haC heC, ← mul_assoc, hze]
  have hfz : f * z = 0 := by
    rw [hzdef, ← mul_assoc, comm f y hfC hy, mul_assoc, hfe, mul_zero]
  have hfg : f * g = 0 := by rw [hgza, ← mul_assoc, hfz, zero_mul]
  have hgf : g * f = 0 := by rw [comm g f hgC hfC]; exact hfg
  have hfsg : f * star g = 0 := by
    rw [← hge, star_mul, hestar, ← mul_assoc, hfe, zero_mul]
  have hgsf : g * star f = 0 := by rw [← hge, mul_assoc, hef, mul_zero]
  have hf'S : f + g ∈ S := by
    refine ⟨cadd _ _ hfC hgC, ?_, ?_⟩
    · rw [add_mul, mul_add, mul_add, hff, hfg, hgf, hgg]; abel
    · rw [star_add, add_mul, mul_add, mul_add, hfs, hfsg, hgsf, hgs]; abel
  have hrank : f.rank < (f + g).rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · have h1 : (f + g) * f = f := by rw [add_mul, hff, hgf, add_zero]
      calc LinearMap.range f.mulVecLin = LinearMap.range ((f + g) * f).mulVecLin := by rw [h1]
        _ ≤ _ := by rw [Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · obtain ⟨v, hv⟩ : ∃ v : Fin r → E, g *ᵥ v ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hg0
        ext i j
        have := congrFun (hall (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      refine ⟨g *ᵥ v, ⟨g *ᵥ v, ?_⟩, ?_⟩
      · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hfg, hgg, zero_add]
      · rintro ⟨u, hu⟩
        rw [Matrix.mulVecLin_apply] at hu
        apply hv
        have hgv : g *ᵥ v = g *ᵥ (g *ᵥ v) := by rw [Matrix.mulVec_mulVec, hgg]
        rw [hgv, ← hu, Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  have hle : (f + g).rank ≤ r := by
    simpa using Matrix.rank_le_card_width (f + g)
  exact hmax (f + g) hf'S (show r - (f + g).rank < r - f.rank by omega)

end GlobalTheory.IsoIdem
