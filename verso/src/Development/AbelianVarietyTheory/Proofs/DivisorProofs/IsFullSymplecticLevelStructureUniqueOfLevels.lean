import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel

set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

namespace GlobalTheory.FullLevel.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Apply `D.unimod.1` to reduce the goal to its premises. Use extensionality with `w`. Establish `h1` using `congrArg (fun t => D.EF t w) h`. Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hn) h1`.
-/
theorem nsmul_cancel {n : ℕ} (hn : n ≠ 0) {x y : D.La} (h : n • x = n • y) : x = y := by
  apply D.unimod.1
  ext w
  have h1 := congrArg (fun t => D.EF t w) h
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (by exact_mod_cast hn) h1

/- English proof (translation)
Establish `hM' : (M : ℤ) ≠ 0` using `by exact_mod_cast hM`. Use `choose f hf using h`. Set `φ : D.La →ₗ[ℤ] ℤ` to `{ toFun := f map_add' := fun a b => by`. Apply `mul_left_cancel₀ hM'` to reduce the goal to its premises. Rewrite using `[mul_add, ← hf, ← hf, ← hf, map_add]`.

Use the proof step `map_smul' := fun c a => by`. Apply `mul_left_cancel₀ hM'` to reduce the goal to its premises. Rewrite using `[← hf, map_smul, hf]`. Simplify using `only [smul_eq_mul, RingHom.id_apply]`. Use `ring }`.

Take `⟨u, hu⟩` from `D.unimod.2 φ`. Use `⟨u, D.unimod.1 ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Rewrite using `[map_nsmul, LinearMap.smul_apply, hu, hf, nsmul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem mem_of_dvd {M : ℕ} (hM : M ≠ 0) {x : D.La} (h : ∀ y, (M : ℤ) ∣ D.EF x y) : ∃ u, x = M • u := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  choose f hf using h
  let φ : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a b => by
        apply mul_left_cancel₀ hM'
        rw [mul_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := fun c a => by
        apply mul_left_cancel₀ hM'
        rw [← hf, map_smul, hf]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  obtain ⟨u, hu⟩ := D.unimod.2 φ
  refine ⟨u, D.unimod.1 ?_⟩
  ext w
  rw [map_nsmul, LinearMap.smul_apply, hu, hf, nsmul_eq_mul]
  rfl

/- English proof (translation)
Establish `hg : Nat.gcd M A ≠ 0` using `fun h => hM (Nat.eq_zero_of_gcd_eq_zero_left h)`. Use `⟨Nat.gcdA M A • v + Nat.gcdB M A • u, nsmul_cancel hg ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_nsmul', Nat.gcd_mul_lcm, ← natCast_zsmul x, Nat.gcd_eq_gcd_ab, add_zsmul, smul_add]`. Use `congr 1`. Rewrite using `[hv, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_lcm {M A : ℕ} (hM : M ≠ 0) {x u v : D.La} (hu : x = M • u) (hv : x = A • v) :
    ∃ w, x = Nat.lcm M A • w := by
  have hg : Nat.gcd M A ≠ 0 := fun h => hM (Nat.eq_zero_of_gcd_eq_zero_left h)
  refine ⟨Nat.gcdA M A • v + Nat.gcdB M A • u, nsmul_cancel hg ?_⟩
  rw [← mul_nsmul', Nat.gcd_mul_lcm, ← natCast_zsmul x, Nat.gcd_eq_gcd_ab, add_zsmul, smul_add]
  congr 1
  · rw [hv, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · rw [hu, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}

/- English proof (translation)
The claim follows from `(h.2.2.1 0).2 ⟨0, by simp⟩`.
-/
theorem ev_zero (h : IsSympLevel D act e N z ev) : ev 0 = 1 := (h.2.2.1 0).2 ⟨0, by simp⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [ev_zero h]`. Consider the case `succ n ih => rw [succ_nsmul, h.1, ih, pow_succ]`.
-/
theorem ev_nsmul (h : IsSympLevel D act e N z ev) (n : ℕ) (a : D.La) : ev (n • a) = ev a ^ n := by
  induction n with
  | zero => simp [ev_zero h]
  | succ n ih => rw [succ_nsmul, h.1, ih, pow_succ]

/- English proof (translation)
Rewrite using `[← h.2.2.1]`. Establish `h1 : ev x = ev (x - y) * ev y` using `by rw [← h.1, sub_add_cancel]`. Rewrite using `[h1]`. Conclude with `mul_eq_right`.
-/
theorem ev_eq_iff (h : IsSympLevel D act e N z ev) (x y : D.La) : ev x = ev y ↔ ∃ b, x - y = N • b := by
  rw [← h.2.2.1]
  have h1 : ev x = ev (x - y) * ev y := by rw [← h.1, sub_add_cancel]
  rw [h1]
  exact mul_eq_right

/- English proof (translation)
Take `⟨m, hm⟩` from `hA`. Establish `hA0 : 0 < A` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm; omega`. Establish `hd : N / A = m` using `by rw [hm, Nat.mul_div_cancel_left _ hA0]`. Rewrite `hxy` using `[hd, ← ev_nsmul h, ← ev_nsmul h, ev_eq_iff h]`.

Take `⟨b, hb⟩` from `hxy`. Use `⟨b, nsmul_cancel hm0 ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, hb, hm, smul_smul, mul_comm]`.
-/
theorem ev_pow_eq (h : IsSympLevel D act e N z ev) (hN : 0 < N) {A : ℕ} (hA : A ∣ N) {x y : D.La}
    (hxy : ev x ^ (N / A) = ev y ^ (N / A)) : ∃ b, x - y = A • b := by
  obtain ⟨m, hm⟩ := hA
  have hA0 : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hd : N / A = m := by rw [hm, Nat.mul_div_cancel_left _ hA0]
  rw [hd, ← ev_nsmul h, ← ev_nsmul h, ev_eq_iff h] at hxy
  obtain ⟨b, hb⟩ := hxy
  refine ⟨b, nsmul_cancel hm0 ?_⟩
  rw [smul_sub, hb, hm, smul_smul, mul_comm]

end GlobalTheory.FullLevel.Uniq

namespace GlobalTheory.FullLevel

open Uniq

/- English proof (translation)
Establish `hM'` using `M'_pos l`. Establish `hM : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `hex : ∀ a, ∃ x, ev x = ev' a` using `fun a => (h.2.2.2.1 _).1 ((h'.2.2.2.1 _).2 ⟨a, rfl⟩)`. Use `choose g hg using hex`. Establish `h1 : ∀ a, ∃ b, g a - a = l.A • b` using `fun a => ev_pow_eq h hM' (A_dvd_M' l) (by rw [hg, hi'.1, hi.1])`.

Establish `h2 : ∀ c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∀ a : D.La, ∃ b, g (c • a) - c • a = l.M • b`. Introduce `c hc a`. Establish `hmem : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul hc Submodule.mem_top`. Conclude with `ev_pow_eq h hM' (M_dvd_M' l) (by rw [hg, hi'.2 _ hmem, hi.2 _ hmem])`. Establish `h3 : ∀ a b, (l.M : ℤ) ∣ D.EF (g a) (g b) - D.EF a b`.

Introduce `a b`. Establish `e1` using `h.2.2.2.2 (g a) (g b)`. Rewrite `e1` using `[hg, hg]`. Establish `e2` using `he _ _ _ _ e1 (h'.2.2.2.2 a b)`. Establish `e3 : z ^ (D.EF (g a) (g b) - D.EF a b) = 1` using `by rw [zpow_sub, e2, mul_inv_cancel]`.

Conclude with `(Int.natCast_dvd_natCast.2 (M_dvd_M' l)).trans ((hz.zpow_eq_one_iff_dvd _).1 e3)`. Take `⟨n, hn, m, hm, hnm⟩` from `Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)`. Use function extensionality and compare the values at `a`. Establish `h4 : ∃ u, m • (g a - a) = l.M • u`. Take `⟨b, hb⟩` from `h2 m hm a`.

Take `⟨c, hc⟩` from `(ev_eq_iff h (m • g a) (g (m • a))).1 (by rw [h.2.1, hg, hg, h'.2.1])`. Take `⟨t, ht⟩` from `M_dvd_M' l`. Use `⟨t • c + b, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, smul_smul, ← ht, ← hc, ← hb, smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `h5 : ∃ u, n • (g a - a) = l.M • u`. Use `mem_of_dvd hM fun y => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `h2 (H.bar n) (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn) y`. Establish `h6` using `h3 a (H.bar n • y)`. Rewrite `hb` using `[sub_eq_iff_eq_add]`.

Rewrite `h6` using `[hb, map_add, map_nsmul, nsmul_eq_mul, add_sub_assoc, dvd_add_right (dvd_mul_right _ _)]`. Rewrite using `[D.adj, map_sub, LinearMap.sub_apply]`. Conclude with `h6`. Take `⟨u, hu⟩` from `h4`. Take `⟨v, hv⟩` from `h5`.

Take `⟨b, hb⟩` from `h1 a`. Establish `h7 : g a - a = l.M • (v + u)` using `by rw [smul_add, ← hu, ← hv, ← add_smul, hnm, one_smul]`. Rewrite using `[← hg]`. Conclude with `((ev_eq_iff h _ _).2 (mem_lcm hM h7 hb)).symm`.
-/
theorem isSympLevel_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H)
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c')
    {z : kˣ} (hz : IsPrimitiveRoot z l.M') {etaA eta ev ev' : D.La → Q}
    (h : IsSympLevel D act e l.M' z ev) (hi : Induces l etaA eta ev)
    (h' : IsSympLevel D act e l.M' z ev') (hi' : Induces l etaA eta ev') : ev = ev' := by
  have hM' := M'_pos l
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hex : ∀ a, ∃ x, ev x = ev' a := fun a =>
    (h.2.2.2.1 _).1 ((h'.2.2.2.1 _).2 ⟨a, rfl⟩)
  choose g hg using hex
  have h1 : ∀ a, ∃ b, g a - a = l.A • b := fun a =>
    ev_pow_eq h hM' (A_dvd_M' l) (by rw [hg, hi'.1, hi.1])
  have h2 : ∀ c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∀ a : D.La, ∃ b, g (c • a) - c • a = l.M • b := by
    intro c hc a
    have hmem : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul hc Submodule.mem_top
    exact ev_pow_eq h hM' (M_dvd_M' l) (by rw [hg, hi'.2 _ hmem, hi.2 _ hmem])
  have h3 : ∀ a b, (l.M : ℤ) ∣ D.EF (g a) (g b) - D.EF a b := by
    intro a b
    have e1 := h.2.2.2.2 (g a) (g b)
    rw [hg, hg] at e1
    have e2 := he _ _ _ _ e1 (h'.2.2.2.2 a b)
    have e3 : z ^ (D.EF (g a) (g b) - D.EF a b) = 1 := by rw [zpow_sub, e2, mul_inv_cancel]
    exact (Int.natCast_dvd_natCast.2 (M_dvd_M' l)).trans ((hz.zpow_eq_one_iff_dvd _).1 e3)
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  funext a
  have h4 : ∃ u, m • (g a - a) = l.M • u := by
    obtain ⟨b, hb⟩ := h2 m hm a
    obtain ⟨c, hc⟩ := (ev_eq_iff h (m • g a) (g (m • a))).1 (by rw [h.2.1, hg, hg, h'.2.1])
    obtain ⟨t, ht⟩ := M_dvd_M' l
    refine ⟨t • c + b, ?_⟩
    rw [smul_add, smul_smul, ← ht, ← hc, ← hb, smul_sub]
    abel
  have h5 : ∃ u, n • (g a - a) = l.M • u := by
    refine mem_of_dvd hM fun y => ?_
    obtain ⟨b, hb⟩ := h2 (H.bar n) (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn) y
    have h6 := h3 a (H.bar n • y)
    rw [sub_eq_iff_eq_add] at hb
    rw [hb, map_add, map_nsmul, nsmul_eq_mul, add_sub_assoc, dvd_add_right (dvd_mul_right _ _)] at h6
    rw [D.adj, map_sub, LinearMap.sub_apply]
    exact h6
  obtain ⟨u, hu⟩ := h4
  obtain ⟨v, hv⟩ := h5
  obtain ⟨b, hb⟩ := h1 a
  have h7 : g a - a = l.M • (v + u) := by rw [smul_add, ← hu, ← hv, ← add_smul, hnm, one_smul]
  rw [← hg]
  exact ((ev_eq_iff h _ _).2 (mem_lcm hM h7 hb)).symm

end GlobalTheory.FullLevel
