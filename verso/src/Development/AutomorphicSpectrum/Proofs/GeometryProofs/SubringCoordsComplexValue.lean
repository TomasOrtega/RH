import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RegVal

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

/- English proof (translation)
Take `⟨V, hpV, t, rfl⟩` from `X.presheaf.exists_germ_eq s`. Take `⟨d, hdV, hpd⟩` from `hU.exists_basicOpen_le (V := V) ⟨p, hpV⟩ hp`. Use `hU.isLocalization_basicOpen d` as an intermediate fact. Take `⟨m, n, e⟩` from `IsLocalization.Away.surj (S := Γ(X, X.basicOpen d)) d (X.presheaf.map (homOfLE hdV).op t)`. Use `⟨n, d, m, (X.mem_basicOpen d p hp).1 hpd, ?_⟩` and prove the remaining obligations.

Establish `e'` using `congrArg (X.presheaf.germ (X.basicOpen d) p hpd) e`. Rewrite `e'` using `[map_mul, map_pow]`. Establish `h0 : ∀ f : Γ(X, U), X.presheaf.germ (X.basicOpen d) p hpd (algebraMap Γ(X, U) Γ(X, X.basicOpen d) f) = X.presheaf.germ U p hp f` using `fun f => X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le d)) p hpd f`. Rewrite `e'` using `[h0, h0, TopCat.Presheaf.germ_res_apply]`. Conclude with `e'`.
-/
theorem germ_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ (n d : Γ(X, U)) (m : ℕ), IsUnit (X.presheaf.germ U p hp d) ∧
      s * X.presheaf.germ U p hp d ^ m = X.presheaf.germ U p hp n := by
  obtain ⟨V, hpV, t, rfl⟩ := X.presheaf.exists_germ_eq s
  obtain ⟨d, hdV, hpd⟩ := hU.exists_basicOpen_le (V := V) ⟨p, hpV⟩ hp
  have := hU.isLocalization_basicOpen d
  obtain ⟨m, n, e⟩ := IsLocalization.Away.surj (S := Γ(X, X.basicOpen d)) d
    (X.presheaf.map (homOfLE hdV).op t)
  refine ⟨n, d, m, (X.mem_basicOpen d p hp).1 hpd, ?_⟩
  have e' := congrArg (X.presheaf.germ (X.basicOpen d) p hpd) e
  rw [map_mul, map_pow] at e'
  have h0 : ∀ f : Γ(X, U), X.presheaf.germ (X.basicOpen d) p hpd (algebraMap Γ(X, U) Γ(X, X.basicOpen d) f) =
      X.presheaf.germ U p hp f := fun f =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le d)) p hpd f
  rw [h0, h0, TopCat.Presheaf.germ_res_apply] at e'
  exact e'

/- English proof (translation)
Establish `e` using `congr($(X.presheaf.germ_stalkSpecializes hq h) f)`. Simplify using `only [CommRingCat.comp_apply] at e`. Simplify using `only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom e`.
-/
theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} {q : X} (hq : q ∈ U) (h : genPt ξ ⤳ q)
    (f : Γ(X, U)) :
    genMap ξ ⟨q, h⟩ (X.presheaf.germ U q hq f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (h.mem_open U.isOpen hq) f) := by
  have e := congr($(X.presheaf.germ_stalkSpecializes hq h) f)
  simp only [CommRingCat.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom e

/- English proof (translation)
Take `⟨h, x, rfl, rfl⟩` from `h`. Take `⟨_, y, rfl, rfl⟩` from `h'`. Conclude with `⟨h, x + y, map_add _ _ _, map_add _ _ _⟩`.
-/
theorem add_val {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x + y, map_add _ _ _, map_add _ _ _⟩

def QV (i : Ω →+* Ω') (W : Subring Ω') (φ : W →+* ℂ) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (n : Ω) : Prop :=
  ∃ h : i n ∈ W, ValAt ξ z n (φ ⟨i n, h⟩)

variable {i : Ω →+* Ω'} {W : Subring Ω'} {φ : W →+* ℂ} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

/- English proof (translation)
Take `⟨h1, v1⟩` from `ha`. Take `⟨h2, v2⟩` from `hb`. Establish `hm : i (a + b) ∈ W` using `by rw [map_add]; exact W.add_mem h1 h2`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Establish `e : (⟨i (a + b), hm⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩` using `Subtype.ext (by simp)`.

Rewrite using `[e, map_add]`. Conclude with `add_val v1 v2`.
-/
theorem QV.add {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a + b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a + b) ∈ W := by rw [map_add]; exact W.add_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a + b), hm⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_add]
  exact add_val v1 v2

/- English proof (translation)
Take `⟨h1, v1⟩` from `ha`. Take `⟨h2, v2⟩` from `hb`. Establish `hm : i (a * b) ∈ W` using `by rw [map_mul]; exact W.mul_mem h1 h2`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Establish `e : (⟨i (a * b), hm⟩ : W) = ⟨_, h1⟩ * ⟨_, h2⟩` using `Subtype.ext (by simp)`.

Rewrite using `[e, map_mul]`. Conclude with `CxVal.mul v1 v2`.
-/
theorem QV.mul {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a * b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a * b) ∈ W := by rw [map_mul]; exact W.mul_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a * b), hm⟩ : W) = ⟨_, h1⟩ * ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_mul]
  exact CxVal.mul v1 v2

/- English proof (translation)
Establish `hm : i (n : Ω) ∈ W` using `by rw [map_intCast]; exact intCast_mem W n`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Establish `e : (⟨i (n : Ω), hm⟩ : W) = (n : W)` using `Subtype.ext (by simp)`. Rewrite using `[e, map_intCast]`. Conclude with `⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩`.
-/
theorem QV.int (hz : genPt ξ ⤳ centre z) (n : ℤ) : QV i W φ ξ z (n : Ω) := by
  have hm : i (n : Ω) ∈ W := by rw [map_intCast]; exact intCast_mem W n
  refine ⟨hm, ?_⟩
  have e : (⟨i (n : Ω), hm⟩ : W) = (n : W) := Subtype.ext (by simp)
  rw [e, map_intCast]
  exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using QV.int (i := i) (W := W) (φ := φ) hz 1`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.prod_insert hk]`. Conclude with `(h k (Finset.mem_insert_self k s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))`.
-/
theorem QV.prod {ι : Type} (hz : genPt ξ ⤳ centre z) (s : Finset ι) (f : ι → Ω)
    (h : ∀ k ∈ s, QV i W φ ξ z (f k)) : QV i W φ ξ z (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using QV.int (i := i) (W := W) (φ := φ) hz 1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    exact (h k (Finset.mem_insert_self k s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `algebraMap n => simpa using QV.int (i := i) (W := W) (φ := φ) hz n`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `mul x y _ _ hx hy => exact hx.mul hy`.
-/
theorem QV.adjoin (hz : genPt ξ ⤳ centre z) {S : Set Ω} (hS : ∀ n ∈ S, QV i W φ ξ z n) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ S) : QV i W φ ξ z a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap n => simpa using QV.int (i := i) (W := W) (φ := φ) hz n
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/- English proof (translation)
Rewrite using `[← e, map_mul, map_pow]`.
-/
theorem val_frac {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {s g n : S} {m : ℕ} (e : s * g ^ m = n) :
    f s * f g ^ m = f n := by
  rw [← e, map_mul, map_pow]

/- English proof (translation)
Take `⟨u, hu⟩` from `hU ⟨_, hd⟩ (by rw [vd']; exact hvd)`. Establish `h1 : ((u : W) : Ω') = i dd` using `by rw [hu]`. Establish `h2 : (((u⁻¹ : Wˣ) : W) : Ω') * i dd = 1`. Rewrite using `[← h1]`. Conclude with `congrArg Subtype.val u.inv_mul`.

Establish `hia : i a = i nn * (((u⁻¹ : Wˣ) : W) : Ω') ^ m`. Rewrite using `[← e, map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (i dd), h2, one_pow, mul_one]`. Establish `hm : i a ∈ W`. Rewrite using `[hia]`. Conclude with `W.mul_mem hn (W.pow_mem (SetLike.coe_mem _) m)`.

Use `⟨hm, ?_⟩` and prove the remaining obligations. Establish `e2 : (⟨i a, hm⟩ : W) = ⟨_, hn⟩ * ((u⁻¹ : Wˣ) : W) ^ m` using `Subtype.ext (by simpa using hia)`. Establish `h3 : φ ((u⁻¹ : Wˣ) : W) * vd = 1`. Rewrite using `[← vd', ← hu, ← map_mul, u.inv_mul, map_one]`. Rewrite using `[e2, map_mul, map_pow, vn', ← e', mul_assoc, ← mul_pow, mul_comm vd, h3, one_pow, mul_one]`.
-/
theorem frac_mem (hU : ∀ a : W, φ a ≠ 0 → IsUnit a) {a nn dd : Ω} {m : ℕ} {r vn vd : ℂ}
    (hn : i nn ∈ W) (hd : i dd ∈ W) (vn' : φ ⟨_, hn⟩ = vn) (vd' : φ ⟨_, hd⟩ = vd) (hvd : vd ≠ 0)
    (e : a * dd ^ m = nn) (e' : r * vd ^ m = vn) : ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  obtain ⟨u, hu⟩ := hU ⟨_, hd⟩ (by rw [vd']; exact hvd)
  have h1 : ((u : W) : Ω') = i dd := by rw [hu]
  have h2 : (((u⁻¹ : Wˣ) : W) : Ω') * i dd = 1 := by
    rw [← h1]
    exact congrArg Subtype.val u.inv_mul
  have hia : i a = i nn * (((u⁻¹ : Wˣ) : W) : Ω') ^ m := by
    rw [← e, map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (i dd), h2, one_pow, mul_one]
  have hm : i a ∈ W := by
    rw [hia]
    exact W.mul_mem hn (W.pow_mem (SetLike.coe_mem _) m)
  refine ⟨hm, ?_⟩
  have e2 : (⟨i a, hm⟩ : W) = ⟨_, hn⟩ * ((u⁻¹ : Wˣ) : W) ^ m := Subtype.ext (by simpa using hia)
  have h3 : φ ((u⁻¹ : Wˣ) : W) * vd = 1 := by
    rw [← vd', ← hu, ← map_mul, u.inv_mul, map_one]
  rw [e2, map_mul, map_pow, vn', ← e', mul_assoc, ← mul_pow, mul_comm vd, h3, one_pow, mul_one]

/- English proof (translation)
Introduce `X Ω Ω' _ _ i ξ K _ J y z w W φ tie hw hU hyp a r har`. Take `⟨hz, s, hsa, hsr⟩` from `har`. Use `choose c hc using hw.1`. Establish `hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0` using `fun k => (hc k).ne_zero`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hw.2 k (c k) (hc k)).1`.

Establish `hxc : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hy k`. Establish `ratio : ∀ (k : K) (e : J k), QV i W φ ξ z (y ⟨k, e⟩ / y ⟨k, c k⟩)` using `fun k e => by`. Take `⟨h, v⟩` from `hyp k (c k) e (hc0 k)`. Take `⟨t, ht, ht'⟩` from `(hw.2 k (c k) (hc k)).2 e`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_right_cancel₀ (hc0 k) (v.trans ht')]` and apply the resulting hypothesis. Establish `gen : ∀ c' : (k : K) → J k, QV i W φ ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩)` using `fun c' => by`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `QV.prod hz _ _ fun k _ => ratio k (c' k)`. Establish `hin : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩`.

Use `⟨hxc, fun c' => ?_⟩` and prove the remaining obligations. Take `⟨_, _, s', hs', _⟩` from `gen c'`. Conclude with `⟨s', hs'⟩`. Take `⟨U, hUa, hUm⟩` from `tie.affine c hxc`. Establish `hpU : centre z ∈ U` using `(hUm _).2 ⟨hz, hin⟩`.

Take `⟨n, d, m, hd, e⟩` from `germ_frac hUa hpU s`. Establish `hgU : genPt ξ ∈ U` using `hz.mem_open U.isOpen hpU`. Establish `hQ : ∀ f : Γ(X, U), QV i W φ ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f))` using `fun f => by`. Use `QV.adjoin hz (S := Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ?_ ((tie.ring c hxc _).2 fun q hq => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `gen j`. Establish `hqU : q.1 ∈ U` using `(hUm _).2 ⟨q.2, hq⟩`. Conclude with `⟨X.presheaf.germ U q.1 hqU f, genMap_germ ξ hqU q.2 f⟩`. Establish `hval : ∀ f : Γ(X, U), ∃ h : i ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) ∈ W, φ ⟨_, h⟩ = (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hpU f)` using `fun f => by`. Take `⟨h, v⟩` from `hQ f`.

Conclude with `⟨h, CxVal.unique v ⟨hz, _, genMap_germ ξ hpU hz f, rfl⟩⟩`. Take `⟨hn, vn⟩` from `hval n`. Take `⟨hd', vd⟩` from `hval d`. Use `frac_mem (m := m) hU hn hd' vn vd (hd.map (Scheme.stalkClosedPointTo z).hom).ne_zero ?_ ?_` and prove the remaining obligations. Establish `e1` using `congrArg (genMap ξ ⟨centre z, hz⟩) e`.

Rewrite `e1` using `[map_mul, map_pow, hsa, genMap_germ ξ hpU hz, genMap_germ ξ hpU hz]`. Conclude with `e1`. Rewrite using `[← hsr]`. Conclude with `val_frac (Scheme.stalkClosedPointTo z).hom e`.
-/
theorem contains_localRing : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w →
    (∀ a : W, φ a ≠ 0 → IsUnit a) →
    (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 →
      ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) →
    ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  intro X Ω Ω' _ _ i ξ K _ J y z w W φ tie hw hU hyp a r har
  obtain ⟨hz, s, hsa, hsr⟩ := har
  choose c hc using hw.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have ratio : ∀ (k : K) (e : J k), QV i W φ ξ z (y ⟨k, e⟩ / y ⟨k, c k⟩) := fun k e => by
    obtain ⟨h, v⟩ := hyp k (c k) e (hc0 k)
    obtain ⟨t, ht, ht'⟩ := (hw.2 k (c k) (hc k)).2 e
    refine ⟨h, ?_⟩
    rwa [mul_right_cancel₀ (hc0 k) (v.trans ht')]
  have gen : ∀ c' : (k : K) → J k, QV i W φ ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) := fun c' => by
    rw [← Finset.prod_div_distrib]
    exact QV.prod hz _ _ fun k _ => ratio k (c' k)
  have hin : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
    refine ⟨hxc, fun c' => ?_⟩
    obtain ⟨_, _, s', hs', _⟩ := gen c'
    exact ⟨s', hs'⟩
  obtain ⟨U, hUa, hUm⟩ := tie.affine c hxc
  have hpU : centre z ∈ U := (hUm _).2 ⟨hz, hin⟩
  obtain ⟨n, d, m, hd, e⟩ := germ_frac hUa hpU s
  have hgU : genPt ξ ∈ U := hz.mem_open U.isOpen hpU
  have hQ : ∀ f : Γ(X, U), QV i W φ ξ z
      ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) := fun f => by
    refine QV.adjoin hz (S := Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ?_ ((tie.ring c hxc _).2 fun q hq => ?_)
    · rintro _ ⟨j, rfl⟩
      exact gen j
    · have hqU : q.1 ∈ U := (hUm _).2 ⟨q.2, hq⟩
      exact ⟨X.presheaf.germ U q.1 hqU f, genMap_germ ξ hqU q.2 f⟩
  have hval : ∀ f : Γ(X, U), ∃ h : i ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) ∈ W,
      φ ⟨_, h⟩ = (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hpU f) := fun f => by
    obtain ⟨h, v⟩ := hQ f
    exact ⟨h, CxVal.unique v ⟨hz, _, genMap_germ ξ hpU hz f, rfl⟩⟩
  obtain ⟨hn, vn⟩ := hval n
  obtain ⟨hd', vd⟩ := hval d
  refine frac_mem (m := m) hU hn hd' vn vd (hd.map (Scheme.stalkClosedPointTo z).hom).ne_zero ?_ ?_
  · have e1 := congrArg (genMap ξ ⟨centre z, hz⟩) e
    rw [map_mul, map_pow, hsa, genMap_germ ξ hpU hz, genMap_germ ξ hpU hz] at e1
    exact e1
  · rw [← hsr]
    exact val_frac (Scheme.stalkClosedPointTo z).hom e

end GlobalTheory.CompanionTheory.Ar.RegVal
