import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Set `f : Multiplicative D.La →* Q` to `MonoidHom.mk' (fun y => J.ev n (Multiplicative.toAdd y)) (fun a b => J.add n _ _)`. Establish `h` using `map_zpow f (Multiplicative.ofAdd x) m`. Rewrite `h` using `[← ofAdd_zsmul]`. Conclude with `h`.
-/
theorem ev_zsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (J : TateIso D k Q act e) (n : ℕ) (m : ℤ) (x : D.La) :
    J.ev n (m • x) = J.ev n x ^ m := by
  let f : Multiplicative D.La →* Q :=
    MonoidHom.mk' (fun y => J.ev n (Multiplicative.toAdd y)) (fun a b => J.add n _ _)
  have h := map_zpow f (Multiplicative.ofAdd x) m
  rw [← ofAdd_zsmul] at h
  exact h

/- English proof (translation)
Establish `h : y * x ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)` using `Ideal.mul_mem_mul hy hx`. Rewrite `h` using `[l.prod, Ideal.mem_span_singleton']`. Take `⟨r, hr⟩` from `h`. Conclude with `⟨r, by rw [mul_comm, ← hr]⟩`.
-/
theorem mul_mem_M (l : Level H) {x y : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (hy : y ∈ l.Mb) :
    ∃ r : 𝓞 E, x * y = r * (l.M : 𝓞 E) := by
  have h : y * x ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hy hx
  rw [l.prod, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by rw [mul_comm, ← hr]⟩

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun b => ∃ c : D.La, x • b = l.M • c) hb ?_ ?_` and prove the remaining obligations. Introduce `y hy t _`. Take `⟨r, hr⟩` from `mul_mem_M l hx hy`. Use `⟨r • t, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_smul, hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`.

Introduce and unpack `b1 b2 ⟨c1, hc1⟩ ⟨c2, hc2⟩`. Conclude with `⟨c1 + c2, by rw [smul_add, hc1, hc2, smul_add]⟩`.
-/
theorem smul_mem_M {D : Datum H} (l : Level H) {x : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    {b : D.La} (hb : b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c : D.La, x • b = l.M • c := by
  refine Submodule.smul_induction_on (p := fun b => ∃ c : D.La, x • b = l.M • c) hb ?_ ?_
  · intro y hy t _
    obtain ⟨r, hr⟩ := mul_mem_M l hx hy
    refine ⟨r • t, ?_⟩
    rw [← mul_smul, hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  · rintro b1 b2 ⟨c1, hc1⟩ ⟨c2, hc2⟩
    exact ⟨c1 + c2, by rw [smul_add, hc1, hc2, smul_add]⟩

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun a => (l.M : ℤ) ∣ D.EF a c) ha ?_ ?_` and prove the remaining obligations. Introduce `y hy t _ show (l.M : ℤ) ∣ D.EF (y • t) c`. Rewrite using `[D.adj]`. Establish `hy' : H.bar y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)` using `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hy`. Take `⟨c', hc'⟩` from `smul_mem_M l hy' hc`.

Rewrite using `[hc', map_nsmul, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`. Introduce `x y hx hy show (l.M : ℤ) ∣ D.EF (x + y) c`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `dvd_add hx hy`.
-/
theorem dvd_EF (D : Datum H) (l : Level H) {a c : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (hc : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : (l.M : ℤ) ∣ D.EF a c := by
  refine Submodule.smul_induction_on (p := fun a => (l.M : ℤ) ∣ D.EF a c) ha ?_ ?_
  · intro y hy t _
    show (l.M : ℤ) ∣ D.EF (y • t) c
    rw [D.adj]
    have hy' : H.bar y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hy
    obtain ⟨c', hc'⟩ := smul_mem_M l hy' hc
    rw [hc', map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro x y hx hy
    show (l.M : ℤ) ∣ D.EF (x + y) c
    rw [map_add, LinearMap.add_apply]
    exact dvd_add hx hy

end GlobalTheory.LowDat.Uniq

namespace GlobalTheory.LowDat

open GlobalTheory.LowDat.Uniq in

/- English proof (translation)
Introduce `E _ _ _ H D l k _ Q _ act e huniq J J' hζ hA hM`. Establish `hM0 : 0 < l.M` using `by have := l.three_le; omega`. Establish `hA0` using `l.A_pos`. Take `⟨j, hj⟩` from `Nat.gcd_dvd_left l.M l.A`. Take `⟨kk, hkk⟩` from `Nat.gcd_dvd_right l.M l.A`.

Establish `hgl : Nat.gcd l.M l.A * l.M' = l.M * l.A` using `Nat.gcd_mul_lcm _ _`. Establish `hg0 : 0 < Nat.gcd l.M l.A` using `Nat.gcd_pos_of_pos_left _ hM0`. Establish `hcop0` using `Nat.coprime_div_gcd_div_gcd (m := l.M) (n := l.A) hg0`. Generalize the expression as in `Nat.gcd l.M l.A = G at hj hkk hgl hg0 hcop0`. Establish `hMk : l.M' = l.M * kk` using `Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hkk]; ring)`.

Establish `hAj : l.M' = l.A * j` using `Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hj]; ring)`. Establish `hj0 : 0 < j`. Break down `Nat.eq_zero_or_pos j with h | h` into its components or cases. Rewrite `hj` using `[h, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hk0 : 0 < kk`. Break down `Nat.eq_zero_or_pos kk with h | h` into its components or cases. Rewrite `hkk` using `[h, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hcop : Nat.Coprime j kk`. Establish `e1 : l.M / G = j` using `by rw [hj]; exact Nat.mul_div_cancel_left j hg0`. Establish `e2 : l.A / G = kk` using `by rw [hkk]; exact Nat.mul_div_cancel_left kk hg0`. Rewrite `hcop0` using `[e1, e2]`.

Conclude with `hcop0`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.mpr hcop`. Establish `hζM : J.ζ l.M = J'.ζ l.M`. Rewrite using `[← J.ζ_pow l.M kk hM0 hk0, ← J'.ζ_pow l.M kk hM0 hk0, ← hMk, hζ]`. Establish `h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)` using `by rw [l.coprime]; trivial`.

Take `⟨f, hf, g2, hg2, hfg⟩` from `Submodule.mem_sup.mp h1`. Establish `decomp : ∀ x : D.La, x = f • x + g2 • x` using `fun x => by rw [← add_smul, hfg, one_smul]`. Establish `key : ∀ b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M b = J'.ev l.M b`. Introduce `b hb`. Establish `hord : (J'.ev l.M b) ^ l.M = 1` using `(J'.onto l.M hM0 _).mpr ⟨b, rfl⟩`.

Take `⟨b', hb'⟩` from `(J.onto l.M hM0 _).mp hord`. Establish `h2 : J.ev l.M (g2 • b') = 1`. Rewrite using `[J.lin, hb', ← J'.lin]`. Take `⟨c, hc⟩` from `smul_mem_M (D := D) l hg2 hb`. Rewrite using `[hc]`.

Conclude with `(J'.ker l.M hM0 _).mpr ⟨c, rfl⟩`. Establish `hb'' : J.ev l.M (f • b') = J'.ev l.M b`. Establish `h` using `J.add l.M (f • b') (g2 • b')`. Rewrite `h` using `[← decomp b', h2, _root_.mul_one]`. Rewrite using `[← hb', h]`.

Establish `hf' : f • b' ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul hf Submodule.mem_top`. Use `set c := b - f • b' with hcdef`. Establish `hcm : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.sub_mem _ hb hf'`. Establish `hdiv : ∀ a, (l.M : ℤ) ∣ D.EF a c`. Introduce `a`.

Rewrite using `[decomp a, map_add, LinearMap.add_apply]`. Use `dvd_add (dvd_EF D l (Submodule.smul_mem_smul hf Submodule.mem_top) hcm) ?_` and prove the remaining obligations. Establish `hga : g2 • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul hg2 Submodule.mem_top`. Establish `i1` using `J.isom l.M hM0 (g2 • a) (f • b')`. Establish `i2` using `J'.isom l.M hM0 (g2 • a) b`.

Rewrite `i1` using `[hM _ hga, hb'', hζM]`. Establish `heq` using `huniq l.M hM0 _ _ _ _ i1 i2`. Rewrite using `[← (J'.ζ_prim l.M hM0).zpow_eq_one_iff_dvd, hcdef, map_sub, zpow_sub, heq, mul_inv_cancel]`. Establish `hdiv' : ∀ a, (l.M : ℤ) ∣ D.EF c a` using `fun a => by`. Establish `h` using `D.alt (a + c)`.

Simplify using `only [map_add, LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h`. Establish `h' : D.EF c a = - D.EF a c` using `by linarith`. Rewrite using `[h']`. Conclude with `(hdiv a).neg_right`. Use `choose q hq using hdiv'`.

Establish `hMne : (l.M : ℤ) ≠ 0` using `by exact_mod_cast hM0.ne'`. Set `φ : D.La →ₗ[ℤ] ℤ` to `{ toFun := q map_add' := fun x y => by`. Apply `mul_left_cancel₀ hMne` to reduce the goal to its premises. Rewrite using `[← hq, mul_add, ← hq, ← hq, map_add]`. Use the proof step `map_smul' := fun m x => by`.

Apply `mul_left_cancel₀ hMne` to reduce the goal to its premises. Rewrite using `[← hq, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hq, map_zsmul, smul_eq_mul] }`. Take `⟨c0, hc0⟩` from `D.unimod.2 φ`. Establish `hc : c = l.M • c0`. Apply `D.unimod.1` to reduce the goal to its premises.

Use extensionality with `a`. Rewrite using `[map_nsmul, LinearMap.smul_apply, hc0, nsmul_eq_mul]`. Conclude with `hq a`. Establish `hJc : J.ev l.M c = 1` using `(J.ker l.M hM0 _).mpr ⟨c0, hc⟩`. Establish `hbc : b = f • b' + c` using `by rw [hcdef]; abel`.

Rewrite using `[hbc, J.add, hJc, _root_.mul_one, hb'', ← hbc]`. Establish `hall : ∀ a, J.ev l.M a = J'.ev l.M a`. Introduce `a`. Rewrite using `[decomp a, J.add, J'.add, key _ (Submodule.smul_mem_smul hf Submodule.mem_top), hM _ (Submodule.smul_mem_smul hg2 Submodule.mem_top)]`. Establish `expand : ∀ (K : TateIso D k Q act e) (a : D.La), K.ev l.M' a = K.ev l.A (u • a) * K.ev l.M (v • a)`.

Introduce `K a`. Establish `ha : a = (j : ℤ) • (u • a) + (kk : ℤ) • (v • a)`. Rewrite using `[smul_smul, smul_smul, ← add_smul, mul_comm (j : ℤ), mul_comm (kk : ℤ), huv, one_smul]`. Use `conv_lhs => rw [ha]`. Rewrite using `[K.add, ev_zsmul K l.M' (j : ℤ) (u • a), ev_zsmul K l.M' (kk : ℤ) (v • a), zpow_natCast, zpow_natCast]`.

Use `congr 1`. Establish `h` using `K.tower l.A j hA0 hj0 (u • a)`. Rewrite `h` using `[← hAj]`. Conclude with `h`. Establish `h` using `K.tower l.M kk hM0 hk0 (v • a)`.

Rewrite `h` using `[← hMk]`. Conclude with `h`. Introduce `a`. Rewrite using `[expand J, expand J', hA, hall]`.
-/
theorem tateIso_ev_lcm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
    (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
    (∀ a, J.ev l.A a = J'.ev l.A a) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
    ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  intro E _ _ _ H D l k _ Q _ act e huniq J J' hζ hA hM
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hA0 := l.A_pos

  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left l.M l.A
  obtain ⟨kk, hkk⟩ := Nat.gcd_dvd_right l.M l.A
  have hgl : Nat.gcd l.M l.A * l.M' = l.M * l.A := Nat.gcd_mul_lcm _ _
  have hg0 : 0 < Nat.gcd l.M l.A := Nat.gcd_pos_of_pos_left _ hM0
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := l.M) (n := l.A) hg0
  generalize Nat.gcd l.M l.A = G at hj hkk hgl hg0 hcop0
  have hMk : l.M' = l.M * kk := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hkk]; ring)
  have hAj : l.M' = l.A * j := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hj]; ring)
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj; omega
    · exact h
  have hk0 : 0 < kk := by
    rcases Nat.eq_zero_or_pos kk with h | h
    · rw [h, mul_zero] at hkk; omega
    · exact h
  have hcop : Nat.Coprime j kk := by
    have e1 : l.M / G = j := by rw [hj]; exact Nat.mul_div_cancel_left j hg0
    have e2 : l.A / G = kk := by rw [hkk]; exact Nat.mul_div_cancel_left kk hg0
    rw [e1, e2] at hcop0; exact hcop0
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop

  have hζM : J.ζ l.M = J'.ζ l.M := by
    rw [← J.ζ_pow l.M kk hM0 hk0, ← J'.ζ_pow l.M kk hM0 hk0, ← hMk, hζ]

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨f, hf, g2, hg2, hfg⟩ := Submodule.mem_sup.mp h1
  have decomp : ∀ x : D.La, x = f • x + g2 • x := fun x => by rw [← add_smul, hfg, one_smul]

  have key : ∀ b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M b = J'.ev l.M b := by
    intro b hb
    have hord : (J'.ev l.M b) ^ l.M = 1 := (J'.onto l.M hM0 _).mpr ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := (J.onto l.M hM0 _).mp hord
    have h2 : J.ev l.M (g2 • b') = 1 := by
      rw [J.lin, hb', ← J'.lin]
      obtain ⟨c, hc⟩ := smul_mem_M (D := D) l hg2 hb
      rw [hc]; exact (J'.ker l.M hM0 _).mpr ⟨c, rfl⟩
    have hb'' : J.ev l.M (f • b') = J'.ev l.M b := by
      have h := J.add l.M (f • b') (g2 • b')
      rw [← decomp b', h2, _root_.mul_one] at h
      rw [← hb', h]
    have hf' : f • b' ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hf Submodule.mem_top
    set c := b - f • b' with hcdef
    have hcm : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.sub_mem _ hb hf'
    have hdiv : ∀ a, (l.M : ℤ) ∣ D.EF a c := by
      intro a
      rw [decomp a, map_add, LinearMap.add_apply]
      refine dvd_add (dvd_EF D l (Submodule.smul_mem_smul hf Submodule.mem_top) hcm) ?_
      have hga : g2 • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
        Submodule.smul_mem_smul hg2 Submodule.mem_top
      have i1 := J.isom l.M hM0 (g2 • a) (f • b')
      have i2 := J'.isom l.M hM0 (g2 • a) b
      rw [hM _ hga, hb'', hζM] at i1
      have heq := huniq l.M hM0 _ _ _ _ i1 i2
      rw [← (J'.ζ_prim l.M hM0).zpow_eq_one_iff_dvd, hcdef, map_sub, zpow_sub, heq, mul_inv_cancel]
    have hdiv' : ∀ a, (l.M : ℤ) ∣ D.EF c a := fun a => by
      have h := D.alt (a + c)
      simp only [map_add, LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h
      have h' : D.EF c a = - D.EF a c := by linarith
      rw [h']; exact (hdiv a).neg_right
    choose q hq using hdiv'
    have hMne : (l.M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
    let φ : D.La →ₗ[ℤ] ℤ :=
      { toFun := q
        map_add' := fun x y => by
          apply mul_left_cancel₀ hMne
          rw [← hq, mul_add, ← hq, ← hq, map_add]
        map_smul' := fun m x => by
          apply mul_left_cancel₀ hMne
          rw [← hq, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hq, map_zsmul, smul_eq_mul] }
    obtain ⟨c0, hc0⟩ := D.unimod.2 φ
    have hc : c = l.M • c0 := by
      apply D.unimod.1
      ext a
      rw [map_nsmul, LinearMap.smul_apply, hc0, nsmul_eq_mul]
      exact hq a
    have hJc : J.ev l.M c = 1 := (J.ker l.M hM0 _).mpr ⟨c0, hc⟩
    have hbc : b = f • b' + c := by rw [hcdef]; abel
    rw [hbc, J.add, hJc, _root_.mul_one, hb'', ← hbc]
  have hall : ∀ a, J.ev l.M a = J'.ev l.M a := by
    intro a
    rw [decomp a, J.add, J'.add, key _ (Submodule.smul_mem_smul hf Submodule.mem_top),
      hM _ (Submodule.smul_mem_smul hg2 Submodule.mem_top)]

  have expand : ∀ (K : TateIso D k Q act e) (a : D.La),
      K.ev l.M' a = K.ev l.A (u • a) * K.ev l.M (v • a) := by
    intro K a
    have ha : a = (j : ℤ) • (u • a) + (kk : ℤ) • (v • a) := by
      rw [smul_smul, smul_smul, ← add_smul, mul_comm (j : ℤ), mul_comm (kk : ℤ), huv, one_smul]
    conv_lhs => rw [ha]
    rw [K.add, ev_zsmul K l.M' (j : ℤ) (u • a), ev_zsmul K l.M' (kk : ℤ) (v • a), zpow_natCast, zpow_natCast]
    congr 1
    · have h := K.tower l.A j hA0 hj0 (u • a); rw [← hAj] at h; exact h
    · have h := K.tower l.M kk hM0 hk0 (v • a); rw [← hMk] at h; exact h
  intro a
  rw [expand J, expand J', hA, hall]

end GlobalTheory.LowDat
