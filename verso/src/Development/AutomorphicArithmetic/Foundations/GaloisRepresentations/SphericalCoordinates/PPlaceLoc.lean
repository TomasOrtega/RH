import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

/- English proof (translation)
Simplify using `only [formB, map_add, LinearMap.add_apply]`.
-/
private theorem formB_add_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β (a + b) c = formB L β a c + formB L β b c := by
  simp only [formB, map_add, LinearMap.add_apply]

/- English proof (translation)
Simplify using `only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`.
-/
private theorem formB_nsmul_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β (n • a) c = n * formB L β a c := by
  simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

/- English proof (translation)
Simplify using `only [formB, map_add]`.
-/
private theorem formB_add_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β a (b + c) = formB L β a b + formB L β a c := by
  simp only [formB, map_add]

/- English proof (translation)
Simplify using `only [formB, map_nsmul, nsmul_eq_mul]`.
-/
private theorem formB_nsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_nsmul, nsmul_eq_mul]

/- English proof (translation)
Simplify using `only [formB, map_zsmul, zsmul_eq_mul]`.
-/
private theorem formB_zsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℤ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_zsmul, zsmul_eq_mul]

/- English proof (translation)
Establish `h1 : (n : ℤ) * q.num = z * q.den`. Establish `h2 : (q.num : ℚ) = q * q.den` using `(Rat.mul_den_eq_num q).symm`. Establish `h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[h2, ← _root_.mul_assoc, h]`.

Conclude with `h3` after adjusting the coercions. Establish `h3 : (q.den : ℤ) ∣ n * q.num` using `⟨z, by rw [h1]; ring⟩`. Establish `h4 : IsCoprime (q.den : ℤ) q.num`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]`. Conclude with `q.reduced`.

Conclude with `Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)`.
-/
private theorem den_dvd_of_mul_eq_int (q : ℚ) (n : ℕ) (z : ℤ) (h : (n : ℚ) * q = z) : q.den ∣ n := by
  have h1 : (n : ℤ) * q.num = z * q.den := by
    have h2 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h2, ← _root_.mul_assoc, h]
    exact_mod_cast h3
  have h3 : (q.den : ℤ) ∣ n * q.num := ⟨z, by rw [h1]; ring⟩
  have h4 : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)

/- English proof (translation)
Introduce `p _ D G L β D' j hP hH`. Take `⟨-, hact, hspan, s0, hs0, hform⟩` from `hP`. Take `⟨E₁, hE, e, he, hperf⟩` from `hH`. Establish `hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u')`. Introduce `u u'`.

Establish `h` using `hform u u'`. Rewrite `h` using `[hE]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨S, hS⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)`. Establish `hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `u _`. Establish `hu : u ∈ Submodule.span ℤ (S : Set D'.La)` using `hS ▸ Submodule.mem_top`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx => exact AddSubgroup.subset_closure hx`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)`. Consider the case `smul a x _ hx => exact zsmul_mem (hx trivial) a`.

Establish `hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range`. Rewrite using `[Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]`. Set `M : AddSubgroup (VQ D)` to `{ carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u} add_mem' := by`. Introduce and unpack `a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩`. Use `⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]`. Use the proof step `zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨m, u, hm, hu⟩`. Conclude with `⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }`.

Establish `hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u` using `fun w => Iff.rfl`. Use `⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩` and prove the remaining obligations. Introduce and unpack `c w ⟨m, u, hm, h⟩`. Conclude with `⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩`. Rewrite using `[eq_top_iff]`.

Introduce `w _`. Take `⟨m, u, hm, h⟩` from `hspan w`. Establish `hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D))` using `hcl ▸ ⟨u, rfl⟩`. Establish `hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))` using `(AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2 Submodule.subset_span hu`. Establish `hw : w = (m : ℚ)⁻¹ • j u`.

Rewrite using `[← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]`. Rewrite using `[hw]`. Conclude with `Submodule.smul_mem _ _ hu'`. Introduce `w`. Rewrite using `[hcl]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, u, hm, h⟩`. Conclude with `⟨m, hm, ⟨u, h.symm⟩⟩`. Introduce and unpack `⟨m, hm, u, h⟩`. Conclude with `⟨m, u, hm, h.symm⟩`.

Introduce `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩`. Establish `key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ)`. Rewrite using `[hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')`. Introduce `h`. Establish `hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p` using `fun x => h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩`.

Set `m : ℕ` to `∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den`. Establish `hm : m.Coprime p` using `Nat.Coprime.prod_left fun x _ => hden x`. Establish `hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u))`. Introduce `u`. Establish `hu : u ∈ Submodule.span ℤ (S : Set D'.La)` using `hS ▸ Submodule.mem_top`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨r, hr⟩` from `Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx`. Use `⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩` and prove the remaining obligations. Establish `h2` using `Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))`.

Express the relevant statement in the definitionally equal form `(((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _`. Rewrite using `[hr]`. Use `push_cast`. Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `h0 : formB L β w (j 0) = 0`. Use `formB_nsmul_right L β 0 w (0 : VQ D)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, formB_add_right]`. Use `push_cast`. Rewrite using `[ha, hb]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul a x _ hx`. Take `⟨b, hb⟩` from `hx`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, formB_zsmul_right]`. Use `push_cast`.

Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Use `choose c hc using hint`. Set `f : D'.La →ₗ[ℤ] ℤ` to `AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by`. Establish `h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ)`.

Use `push_cast`. Rewrite using `[hc, hc, hc, map_add, formB_add_right]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h3))` after adjusting the coercions. Take `⟨x, hx⟩` from `hperf f`.

Take `⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w` from `⟨(e * m) • w - j x, sub_add_cancel _ _⟩`. Establish `hs : s0 / 2 ≠ 0` using `by positivity`. Establish `hzero : ∀ u, formB L β z (j u) = 0`. Introduce `u`. Establish `h1 : E₁ x u = e • c u`.

Use `LinearMap.congr_fun hx u` as an intermediate fact. Simplify `this` using `[f]`. Establish `h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u)))`. Rewrite using `[h1, ← hc]`. Use `push_cast`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[hE1]`. Establish `h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u)`. Rewrite using `[hz, formB_nsmul_left]`. Rewrite `h3` using `[formB_add_left]`.

Establish `h4 : s0 / 2 * formB L β z (j u) = 0`. Establish `h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) = s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u))` using `by rw [h3]`. Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mul_eq_zero.1 h4).resolve_left hs`.

Take `⟨k, u₁, hk, hu₁⟩` from `hspan z`. Establish `hEF : ∀ u, D'.EF u₁ u = 0`. Introduce `u`. Establish `h1` using `hform u₁ u`. Rewrite `h1` using `[← hu₁, formB_nsmul_left, hzero u]`.

Simplify using `using h1`. Establish `hu₀ : u₁ = 0` using `D'.nondeg _ hEF`. Establish `hz0 : z = 0`. Rewrite `hu₁` using `[hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ]`. Conclude with `(smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)`.

Use `⟨e * m, x, he.mul_left hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, hz0, zero_add]`.
-/
theorem placeLoc_of : PlaceLoc := by
  intro p _ D G L β D' j hP hH
  obtain ⟨-, hact, hspan, s0, hs0, hform⟩ := hP
  obtain ⟨E₁, hE, e, he, hperf⟩ := hH
  have hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u') := by
    intro u u'
    have h := hform u u'
    rw [hE] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    push_cast at h
    linarith
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)
  have hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | smul a x _ hx => exact zsmul_mem (hx trivial) a
  have hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range := by
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]
  let M : AddSubgroup (VQ D) :=
    { carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u}
      add_mem' := by
        rintro a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩
        refine ⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩
        rw [map_add, map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]
      zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩
      neg_mem' := by
        rintro a ⟨m, u, hm, hu⟩
        exact ⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }
  have hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u := fun w => Iff.rfl
  refine ⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩
  · rintro c w ⟨m, u, hm, h⟩
    exact ⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm, h⟩ := hspan w
    have hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) := hcl ▸ ⟨u, rfl⟩
    have hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D)) :=
      (AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2
        Submodule.subset_span hu
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hu'
  · intro w
    rw [hcl]
    constructor
    · rintro ⟨m, u, hm, h⟩
      exact ⟨m, hm, ⟨u, h.symm⟩⟩
    · rintro ⟨m, hm, u, h⟩
      exact ⟨m, u, hm, h.symm⟩
  · intro w
    constructor
    · rintro ⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩
      have key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ) := by
        rw [hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]
        push_cast
        ring
      exact Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')
    · intro h
      have hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p := fun x =>
        h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩
      let m : ℕ := ∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den
      have hm : m.Coprime p := Nat.Coprime.prod_left fun x _ => hden x
      have hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u)) := by
        intro u
        have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx
          refine ⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩
          have h2 := Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))
          change (((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _
          rw [hr]
          push_cast
          rw [← h2]
          ring
        | zero =>
          refine ⟨0, ?_⟩
          have h0 : formB L β w (j 0) = 0 := by
            have := formB_nsmul_right L β 0 w (0 : VQ D)
            simpa using this
          rw [h0]
          simp
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          rw [map_add, formB_add_right]
          push_cast
          rw [ha, hb]
          ring
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          refine ⟨a * b, ?_⟩
          rw [map_zsmul, formB_zsmul_right]
          push_cast
          rw [hb]
          ring
      choose c hc using hint
      let f : D'.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by
        have h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ) := by
          push_cast
          rw [hc, hc, hc, map_add, formB_add_right]
          ring
        exact_mod_cast h3))
      obtain ⟨x, hx⟩ := hperf f
      obtain ⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w := ⟨(e * m) • w - j x, sub_add_cancel _ _⟩
      have hs : s0 / 2 ≠ 0 := by positivity
      have hzero : ∀ u, formB L β z (j u) = 0 := by
        intro u
        have h1 : E₁ x u = e • c u := by
          have := LinearMap.congr_fun hx u
          simpa [f] using this
        have h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u))) := by
          rw [h1, ← hc]
          push_cast
          simp
        rw [hE1] at h2
        have h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u) := by
          rw [hz, formB_nsmul_left]
        rw [formB_add_left] at h3
        have h4 : s0 / 2 * formB L β z (j u) = 0 := by
          have h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) =
              s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u)) := by rw [h3]
          push_cast at h5
          linarith
        exact (mul_eq_zero.1 h4).resolve_left hs
      obtain ⟨k, u₁, hk, hu₁⟩ := hspan z
      have hEF : ∀ u, D'.EF u₁ u = 0 := by
        intro u
        have h1 := hform u₁ u
        rw [← hu₁, formB_nsmul_left, hzero u] at h1
        simpa using h1
      have hu₀ : u₁ = 0 := D'.nondeg _ hEF
      have hz0 : z = 0 := by
        rw [hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hu₁
        exact (smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)
      refine ⟨e * m, x, he.mul_left hm, ?_⟩
      rw [← hz, hz0, zero_add]

end UpperTheory.Gal.W2
