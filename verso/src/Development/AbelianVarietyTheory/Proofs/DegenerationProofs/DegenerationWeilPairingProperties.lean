import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.WpPairing

variable {O : Type} [CommRing O] (N : NumD O)

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, _root_.GlobalTheory.Ex.NumD.Gt.s_zero]`. Consider the case `succ n ih`. Establish `hm` using `g.mult (n • y) y`. Rewrite using `[succ_nsmul, pow_succ, ← ih]`.

Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul]`. Rewrite using `[← N.c_nsmul, ← mul_assoc, mul_right_comm, hm]`. Conclude with `mul_right_comm _ _ _`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, _root_.GlobalTheory.Ex.NumD.Gt.s_zero]
  | succ n ih =>
    have hm := g.mult (n • y) y
    rw [succ_nsmul, pow_succ, ← ih]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul]
    rw [← N.c_nsmul, ← mul_assoc, mul_right_comm, hm]
    exact mul_right_comm _ _ _

/- English proof (translation)
Establish `e` using `N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b`. Rewrite `e` using `[N.cub.face, mul_one, one_mul, N.QT_pow_b]`. Express the relevant statement in the definitionally equal form `(p.1.2 * p'.1.2).s p''.1.1.toAdd * cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _`. Rewrite using `[NumD.Gt.mul_s, NumD.tk, NumD.tk]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Use `replace e := congrArg Additive.ofMul e`. Simplify using `only [ofMul_mul, ofMul_div] at e ⊢`. Take the linear combination `(norm := abel) e`.
-/
theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have e := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b] at e
  change (p.1.2 * p'.1.2).s p''.1.1.toAdd * cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  rw [NumD.Gt.mul_s, NumD.tk, NumD.tk]
  apply Additive.ofMul.injective
  replace e := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_div] at e ⊢
  linear_combination (norm := abel) e

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, hθ.face]`. Consider the case `succ n ih`. Establish `c1` using `hθ.coc (b ^ n * b' ^ n) b b' m`. Establish `c2` using `hθ.coc (b ^ n * b) (b' ^ n) b' m`.

Establish `c3` using `hθ.coc (b ^ n) (b' ^ n) b m`. Establish `c4` using `hθ.coc (b ^ n) b (b' ^ n) m`. Rewrite `c2` using `[mul_right_comm (b ^ n) b (b' ^ n)]`. Rewrite `c4` using `[mul_comm b (b' ^ n), hθ.s01 b (b' ^ n) m]`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul, mul_pow, pow_succ] at ih ⊢`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `ih'` using `congrArg Additive.ofMul ih`. Establish `c1'` using `congrArg Additive.ofMul c1`. Establish `c2'` using `congrArg Additive.ofMul c2`. Establish `c3'` using `congrArg Additive.ofMul c3`.

Establish `c4'` using `congrArg Additive.ofMul c4`. Simplify using `only [ofMul_mul, ofMul_pow] at ih' c1' c2' c3' c4' ⊢`. Take the linear combination `(norm := abel) ih' + c2' + c3' - c1' - c4'`.
-/
private lemma cubN_one_mul_mul_pow_eq {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
    (hθ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub θ) (n : ℕ) (b b' m : A) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 (b * b') m * θ b b' m ^ n =
      θ (b ^ n) (b' ^ n) m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b' m := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, hθ.face]
  | succ n ih =>
    have c1 := hθ.coc (b ^ n * b' ^ n) b b' m
    have c2 := hθ.coc (b ^ n * b) (b' ^ n) b' m
    have c3 := hθ.coc (b ^ n) (b' ^ n) b m
    have c4 := hθ.coc (b ^ n) b (b' ^ n) m
    rw [mul_right_comm (b ^ n) b (b' ^ n)] at c2
    rw [mul_comm b (b' ^ n), hθ.s01 b (b' ^ n) m] at c4
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul, mul_pow, pow_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c1' := congrArg Additive.ofMul c1
    have c2' := congrArg Additive.ofMul c2
    have c3' := congrArg Additive.ofMul c3
    have c4' := congrArg Additive.ofMul c4
    simp only [ofMul_mul, ofMul_pow] at ih' c1' c2' c3' c4' ⊢
    linear_combination (norm := abel) ih' + c2' + c3' - c1' - c4'

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Establish `hθ` using `N.cub`. Use `set g := (p : Multiplicative N.X × N.Gt).2 with hg`. Use `set g' := (p' : Multiplicative N.X × N.Gt).2 with hg'`. Use `set h := (p'' : Multiplicative N.X × N.Gt).2 with hh`. Use `set x := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hx`.

Use `set x' := Multiplicative.toAdd (p' : Multiplicative N.X × N.Gt).1 with hx'`. Use `set y := Multiplicative.toAdd (p'' : Multiplicative N.X × N.Gt).1 with hy`. Establish `bp` using `N.QT_pow_b p`. Establish `bp'` using `N.QT_pow_b p'`. Establish `bq` using `N.QT_pow_b p''`.

Rewrite `bp` using `[← hg, ← hx]`. Rewrite `bp'` using `[← hg', ← hx']`. Rewrite `bq` using `[← hh, ← hy]`. Establish `e1 : N.tk (p * p') p'' = g.s y * g'.s y / N.θ (N.c y) g.b g'.b * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b (g.b * g'.b)`. Simplify using `only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul, _root_.GlobalTheory.Ex.NumD.Gt.mul_s, _root_.GlobalTheory.Ex.NumD.Gt.mul_b]`.

Both sides reduce to the same expression. Establish `e2 : N.tk p'' (p * p') = h.s (x + x') * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 (g.b * g'.b) h.b`. Simplify using `only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul, Prod.fst_mul, toAdd_mul, _root_.GlobalTheory.Ex.NumD.Gt.mul_b]`. Both sides reduce to the same expression. Establish `e3 : N.tk p p'' = g.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g.b` using `rfl`.

Establish `e4 : N.tk p' p'' = g'.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g'.b` using `rfl`. Establish `e5 : N.tk p'' p = h.s x * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g.b h.b` using `rfl`. Establish `e6 : N.tk p'' p' = h.s x' * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g'.b h.b` using `rfl`. Establish `hm` using `h.mult x x'`. Establish `hadd` using `hθ.N_add k 1 h.b g.b g'.b`.

Establish `hmid` using `cubN_one_mul_mul_pow_eq hθ k g.b g'.b h.b`. Establish `hsym : N.θ h.b g.b g'.b = N.θ g.b g'.b h.b`. Rewrite using `[hθ.s01, hθ.s12]`. Rewrite `hadd` using `[hθ.face, one_mul, hsym]`. Rewrite `hm` using `[← bp, ← bp']`.

Rewrite `e1` using `[← bq]`. Simplify using `only [_root_.GlobalTheory.Ex.NumD.wp]`. Rewrite using `[e1, e2, e3, e4, e5, e6]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `hm'` using `congrArg Additive.ofMul hm`.

Establish `hadd'` using `congrArg Additive.ofMul hadd`. Establish `hmid'` using `congrArg Additive.ofMul hmid`. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at hm' hadd' hmid' ⊢`. Take the linear combination `(norm := abel) hadd' - hmid' - hm'`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_left {k : ℕ} (p p' p'' : N.QT k) : N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' := by
  have hθ := N.cub
  set g := (p : Multiplicative N.X × N.Gt).2 with hg
  set g' := (p' : Multiplicative N.X × N.Gt).2 with hg'
  set h := (p'' : Multiplicative N.X × N.Gt).2 with hh
  set x := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hx
  set x' := Multiplicative.toAdd (p' : Multiplicative N.X × N.Gt).1 with hx'
  set y := Multiplicative.toAdd (p'' : Multiplicative N.X × N.Gt).1 with hy
  have bp := N.QT_pow_b p
  have bp' := N.QT_pow_b p'
  have bq := N.QT_pow_b p''
  rw [← hg, ← hx] at bp
  rw [← hg', ← hx'] at bp'
  rw [← hh, ← hy] at bq
  have e1 : N.tk (p * p') p'' = g.s y * g'.s y /
      N.θ (N.c y) g.b g'.b *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b
        (g.b * g'.b) := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_s,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e2 : N.tk p'' (p * p') = h.s (x + x') *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 (g.b * g'.b)
        h.b := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul, Prod.fst_mul,
      toAdd_mul, _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e3 : N.tk p p'' =
      g.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g.b := rfl
  have e4 : N.tk p' p'' =
      g'.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g'.b := rfl
  have e5 : N.tk p'' p =
      h.s x * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g.b h.b := rfl
  have e6 : N.tk p'' p' =
      h.s x' * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g'.b h.b := rfl
  have hm := h.mult x x'
  have hadd := hθ.N_add k 1 h.b g.b g'.b
  have hmid := cubN_one_mul_mul_pow_eq hθ k g.b g'.b
    h.b
  have hsym : N.θ h.b g.b g'.b =
      N.θ g.b g'.b h.b := by
    rw [hθ.s01, hθ.s12]
  rw [hθ.face, one_mul, hsym] at hadd
  rw [← bp, ← bp'] at hm
  rw [← bq] at e1
  simp only [_root_.GlobalTheory.Ex.NumD.wp]
  rw [e1, e2, e3, e4, e5, e6]
  apply Additive.ofMul.injective
  have hm' := congrArg Additive.ofMul hm
  have hadd' := congrArg Additive.ofMul hadd
  have hmid' := congrArg Additive.ofMul hmid
  simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at hm' hadd' hmid' ⊢
  linear_combination (norm := abel) hadd' - hmid' - hm'

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Rewrite using `[N.wp_swap (p' * p'') p, _root_.GlobalTheory.Ex.WpPairing.wp_mul_left, mul_inv, ← N.wp_swap p' p, ← N.wp_swap p'' p]`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_right {k : ℕ} (p p' p'' : N.QT k) : N.wp p (p' * p'') = N.wp p p' * N.wp p p'' := by
  rw [N.wp_swap (p' * p'') p, _root_.GlobalTheory.Ex.WpPairing.wp_mul_left, mul_inv, ← N.wp_swap p' p, ← N.wp_swap p'' p]

noncomputable def wpHom {k : ℕ} (q : N.QT k) : N.QT k →* Oˣ :=
  MonoidHom.mk' (fun p => N.wp p q) fun p p' => wp_mul_left N p p' q

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
The claim follows from `map_pow (_root_.GlobalTheory.Ex.WpPairing.wpHom N q) p n`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_pow_left {k : ℕ} (p q : N.QT k) (n : ℕ) : N.wp (p ^ n) q = N.wp p q ^ n :=
  map_pow (_root_.GlobalTheory.Ex.WpPairing.wpHom N q) p n

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Establish `hq` using `N.mem_QT.mp q.2`. Establish `h1` using `_root_.GlobalTheory.Ex.WpPairing.s_nsmul N (q : Multiplicative N.X × N.Gt).2 k z`. Establish `h2` using `_root_.GlobalTheory.Ex.NumD.Gt.pow_s (q : Multiplicative N.X × N.Gt).2 k z`. Rewrite `h2` using `[hq, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.τ_symm]`. Simplify using `only [_root_.GlobalTheory.Ex.NumD.wp, _root_.GlobalTheory.Ex.NumD.tk, _root_.GlobalTheory.Ex.NumD.qTriv, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.io_b, toAdd_ofAdd, div_eq_one]`.

Rewrite using `[h1, h2]`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_qTriv {k : ℕ} (z : N.X) (q : N.QT k) : N.wp (N.qTriv k z) q = 1 := by
  have hq := N.mem_QT.mp q.2
  have h1 := _root_.GlobalTheory.Ex.WpPairing.s_nsmul N
    (q : Multiplicative N.X × N.Gt).2 k z
  have h2 := _root_.GlobalTheory.Ex.NumD.Gt.pow_s
    (q : Multiplicative N.X × N.Gt).2 k z
  rw [hq, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.τ_symm] at h2
  simp only [_root_.GlobalTheory.Ex.NumD.wp, _root_.GlobalTheory.Ex.NumD.tk,
    _root_.GlobalTheory.Ex.NumD.qTriv, _root_.GlobalTheory.Ex.NumD.io_s,
    _root_.GlobalTheory.Ex.NumD.io_b, toAdd_ofAdd, div_eq_one]
  rw [h1, h2]

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Take `⟨z, rfl⟩` from `(N.qEq_iff p p').mp h`. Rewrite using `[_root_.GlobalTheory.Ex.WpPairing.wp_mul_left, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv, mul_one]`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_congr_left {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (q : N.QT k) : N.wp p q = N.wp p' q := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff p p').mp h
  rw [_root_.GlobalTheory.Ex.WpPairing.wp_mul_left, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv, mul_one]

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

/- English proof (translation)
Introduce `O _ N k p p' p''`. Use `⟨_root_.GlobalTheory.Ex.WpPairing.wp_mul_left N p p' p'', N.wp_self p, ?_, ?_, fun h => _root_.GlobalTheory.Ex.WpPairing.wp_congr_left N h p'', ?_, fun h1 h2 => N.wp_of_eq_zero p p' (by simp [h1]) (by simp [h2])⟩` and prove the remaining obligations. Rewrite using `[N.wp_swap p p', mul_inv_cancel]`. Establish `hp : p ^ k = N.qTriv k (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [SubgroupClass.coe_pow, _root_.GlobalTheory.Ex.NumD.qTriv]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `using N.mem_QT.mp p.2`. Rewrite using `[← _root_.GlobalTheory.Ex.WpPairing.wp_pow_left, hp, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv]`.

Introduce `h1 hb`. Take `⟨t, ht⟩` from `(N.exists_tor_iff _).mpr hb`. Establish `hk` using `N.mem_QT.mp p.2`. Rewrite `hk` using `[h1, toAdd_one, N.io_zero]`. Establish `htk : t ^ k = 1` using `N.tor_injective (by rw [N.tor_pow, ht, N.tor_one, hk])`.

Establish `hp : p = N.qTor t htk`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [_root_.GlobalTheory.Ex.NumD.qTor]`. Conclude with `Prod.ext h1 ht.symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hp]`. Use `_ = t (p' : Multiplicative N.X × N.Gt).1 := N.wp_qTor t htk p'`. Use `_ = _ := by rw [← ht, N.torus_generator_apply, ofAdd_toAdd]`.
-/
theorem _root_.GlobalTheory.Ex.WpPairing.wp_pairing : ∀ (O : Type) [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  intro O _ N k p p' p''
  refine ⟨_root_.GlobalTheory.Ex.WpPairing.wp_mul_left N p p' p'', N.wp_self p, ?_, ?_,
    fun h => _root_.GlobalTheory.Ex.WpPairing.wp_congr_left N h p'', ?_,
    fun h1 h2 => N.wp_of_eq_zero p p' (by simp [h1]) (by simp [h2])⟩
  · rw [N.wp_swap p p', mul_inv_cancel]
  · have hp : p ^ k = N.qTriv k
        (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, _root_.GlobalTheory.Ex.NumD.qTriv]
      refine Prod.ext ?_ ?_
      · simp
      · simpa using N.mem_QT.mp p.2
    rw [← _root_.GlobalTheory.Ex.WpPairing.wp_pow_left, hp, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv]
  · intro h1 hb
    obtain ⟨t, ht⟩ := (N.exists_tor_iff _).mpr hb
    have hk := N.mem_QT.mp p.2
    rw [h1, toAdd_one, N.io_zero] at hk
    have htk : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one, hk])
    have hp : p = N.qTor t htk := by
      apply Subtype.ext
      simp only [_root_.GlobalTheory.Ex.NumD.qTor]
      exact Prod.ext h1 ht.symm
    calc N.wp p p' =
          N.wp (N.qTor t htk) p' := by
          rw [← hp]
      _ = t (p' : Multiplicative N.X × N.Gt).1 := N.wp_qTor t htk p'
      _ = _ := by rw [← ht, N.torus_generator_apply, ofAdd_toAdd]

end GlobalTheory.Ex.WpPairing
