import Development.WeilBound.CoreStatements.HodgeTatePoints.CbFrob

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {d : ℕ}

def Lz (j : Fin d) (f : PS R 2 d) : PS R 1 d := ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) f)

/- English proof (translation)
Rewrite using `[← cc_pderiv, Lz, d2 (by zz) (by zz)]`. Simplify using `[dpt, ccev (show ZZ (![pt R d 0, 0] : Fin 2 → Pt R 1 d) by zz), cc_pderiv, coeff_pderiv, bil]`.
-/
theorem coeff_Lz (f : PS R 2 d) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), i) 1) (Lz j f) = bil f 1 1 i j := by
  rw [← cc_pderiv, Lz, d2 (by zz) (by zz)]
  simp [dpt, ccev (show ZZ (![pt R d 0, 0] : Fin 2 → Pt R 1 d) by zz), cc_pderiv, coeff_pderiv, bil]

/- English proof (translation)
Establish `hb : ZZ (n` using `1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)`. Simplify using `only [Lz, dmul, eva hb, evm hb]`.
-/
theorem Lz_mul (j : Fin d) (f g : PS R 2 d) : Lz j (f * g) =
    Lz j f * ev (n := 1) ![pt R d 0, 0] g + ev (n := 1) ![pt R d 0, 0] f * Lz j g := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  simp only [Lz, dmul, eva hb, evm hb]

/- English proof (translation)
Establish `hb : ZZ (n` using `1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)`. Establish `hφ' : ZZ ![φ]` using `ZZ_cons hφ ZZ_nil`. Establish `h01 : ((0 : Fin 2) = 1) ↔ False` using `by decide`. Simplify using `only [Lz]`. Rewrite using `[d2 (Z_comp1 hφ (Z_pt 0)) (Z_pt 1)]`.

Simplify using `only [dcomp_ne (show (0 : Fin 2) ≠ 1 by decide), dpt, mul_zero, Finset.sum_const_zero, zero_add, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[ev2 hb (Z_comp1 hφ (Z_pt 0)) (Z_pt 1), ev2 hφ' (Z_pt 0) Z_zero, ep_comp1 φ hb (Z_pt 0), ep_pt hb, ep_pt hb, ep_pt hφ', ep_zero hφ']`. Simplify using `[germCompOne_identityPoint_left]`.
-/
theorem Lz_fst {φ : Pt R 1 d} (hφ : Z φ) (j : Fin d) (f : PS R 2 d) :
    Lz j (ev (n := 2) ![comp1 φ (pt R d 0), pt R d 1] f) = ev ![φ] (Lz j f) := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  have hφ' : ZZ ![φ] := ZZ_cons hφ ZZ_nil
  have h01 : ((0 : Fin 2) = 1) ↔ False := by decide
  simp only [Lz]
  rw [d2 (Z_comp1 hφ (Z_pt 0)) (Z_pt 1)]
  simp only [dcomp_ne (show (0 : Fin 2) ≠ 1 by decide), dpt, mul_zero, Finset.sum_const_zero,
    zero_add, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev2 hb (Z_comp1 hφ (Z_pt 0)) (Z_pt 1), ev2 hφ' (Z_pt 0) Z_zero, ep_comp1 φ hb (Z_pt 0),
    ep_pt hb, ep_pt hb, ep_pt hφ', ep_zero hφ']
  simp [germCompOne_identityPoint_left]

/- English proof (translation)
Establish `hb : ZZ (n` using `1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)`. Establish `h01 : ((0 : Fin 2) = 1) ↔ False` using `by decide`. Simplify using `only [Lz]`. Rewrite using `[d2 (Z_pt 0) (Z_comp1 hψ (Z_pt 1))]`. Simplify using `only [dpt, dcomp_eq, Prod.mk.injEq, h01, false_and, if_false, mul_zero, Finset.sum_const_zero, zero_add, evsum hb, evm hb]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[ev2 hb (Z_pt 0) (Z_comp1 hψ (Z_pt 1)), ev1 hb (Z_pt 1), ep_comp1 ψ hb (Z_pt 1)]`. Simplify using `only [ep_pt hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germComp1_zero_of_noConstantCoeff hψ, ev_at_zero, cc_pderiv, lin]`.
-/
theorem Lz_snd {ψ : Pt R 1 d} (hψ : Z ψ) (j : Fin d) (f : PS R 2 d) :
    Lz j (ev (n := 2) ![pt R d 0, comp1 ψ (pt R d 1)] f) = ∑ c, Lz c f * C (lin ψ 1 c j) := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  have h01 : ((0 : Fin 2) = 1) ↔ False := by decide
  simp only [Lz]
  rw [d2 (Z_pt 0) (Z_comp1 hψ (Z_pt 1))]
  simp only [dpt, dcomp_eq, Prod.mk.injEq, h01, false_and, if_false, mul_zero,
    Finset.sum_const_zero, zero_add, evsum hb, evm hb]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ev2 hb (Z_pt 0) (Z_comp1 hψ (Z_pt 1)), ev1 hb (Z_pt 1), ep_comp1 ψ hb (Z_pt 1)]
  simp only [ep_pt hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germComp1_zero_of_noConstantCoeff hψ,
    ev_at_zero, cc_pderiv, lin]

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/- English proof (translation)
Establish `hψ : Z (fun i => MvPowerSeries.map (frobenius R p) (φ i))`. Introduce `i`. Simplify using `[hφ i]`. Establish `hφ' : ZZ ![φ]` using `ZZ_cons hφ ZZ_nil`. Establish `hq : ZZ (n` using `1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil`.

Rewrite using `[ev1 hφ' (Z_ptPow p 0), ev1 hq hψ, ep_ptPow p hφ']`. Use `congr 1`. Use function extensionality and compare the values at `k i`. Simplify using `only [ep, Matrix.cons_val_fin_one]`. Rewrite using `[frob_subst R p d 1 (φ i)]`.

Use `congr 1`. Use function extensionality and compare the values at `k'`. Rewrite using `[Fin.fin_one_eq_zero k']`. Both sides reduce to the same expression.
-/
theorem ev_ev_pow {φ : Pt R 1 d} (hφ : Z φ) (f : PS R 1 d) :
    ev ![φ] (ev (n := 1) ![ptPow R d p 0] f) =
      ev (n := 1) ![ptPow R d p 0] (ev ![fun i => MvPowerSeries.map (frobenius R p) (φ i)] f) := by
  have hψ : Z (fun i => MvPowerSeries.map (frobenius R p) (φ i)) := by
    intro i
    simp [hφ i]
  have hφ' : ZZ ![φ] := ZZ_cons hφ ZZ_nil
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  rw [ev1 hφ' (Z_ptPow p 0), ev1 hq hψ, ep_ptPow p hφ']
  congr 1
  funext k i
  simp only [ep, Matrix.cons_val_fin_one]
  rw [frob_subst R p d 1 (φ i)]
  congr 1
  funext k'
  rw [Fin.fin_one_eq_zero k']
  rfl

end

/- English proof (translation)
Establish `hψ : Z (fun i => MvPowerSeries.map (frobenius R p) (φ i))`. Introduce `i`. Simplify using `[hφ i]`. Rewrite using `[ev_ev_pow p hφ, coeff_ev_pow_one, coeff_lin_ev hψ]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `[lin, coeff_map, frobenius_def]`.
-/
private theorem coeff_single_prime_ev_of_Z {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP R p]
    {φ : Pt R 1 d} (hφ : Z φ) (F : PS R 1 d) (i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), i) p) (ev ![φ] (ev (n := 1) ![ptPow R d p 0] F)) =
      ∑ c, coeff (Finsupp.single ((0 : Fin 1), c) 1) F * lin φ 1 c i ^ p := by
  have hψ : Z (fun i => MvPowerSeries.map (frobenius R p) (φ i)) := by
    intro i
    simp [hφ i]
  rw [ev_ev_pow p hφ, coeff_ev_pow_one, coeff_lin_ev hψ]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [lin, coeff_map, frobenius_def]

/- English proof (translation)
Establish `key : ∀ c, ∃ g : PS R 1 d, B.A.act (p : O) c = ev ![ptPow R d p 0] g` using `fun c => (series_in_p R p d).1 _ (fun j => d_act_p p B.A c j)`. Use `choose h hh using key`. Establish `hq : ZZ (n` using `1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil`. Use `⟨h, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`.

Rewrite using `[← ccev hq (h c), ← hh c]`. Conclude with `B.A.const _ c`. Use function extensionality and compare the values at `c`. Conclude with `hh c`. Introduce `c i show coeff _ (h c) = coeff _ (B.A.act (p : O) c)`.

Rewrite using `[hh c, coeff_ev_pow_one]`.
-/
private theorem exists_act_prime_eq_comp1_ptPow {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP R p]
    {O : Type} [CommRing O] [StarRing O] (B : FB R d O) :
    ∃ h : Pt R 1 d, Z h ∧ B.A.act (p : O) = comp1 h (ptPow R d p 0) ∧
      ∀ c i, lin h 1 c i = hw B p c i := by
  have key : ∀ c, ∃ g : PS R 1 d, B.A.act (p : O) c = ev ![ptPow R d p 0] g := fun c =>
    (series_in_p R p d).1 _ (fun j => d_act_p p B.A c j)
  choose h hh using key
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  refine ⟨h, ?_, ?_, ?_⟩
  · intro c
    rw [← ccev hq (h c), ← hh c]
    exact B.A.const _ c
  · funext c
    exact hh c
  · intro c i
    show coeff _ (h c) = coeff _ (B.A.act (p : O) c)
    rw [hh c, coeff_ev_pow_one]

/- English proof (translation)
Establish `hq : ZZ (n` using `1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil`. Rewrite using `[ev1 hq hh, ep_one]`.
-/
private theorem ev_comp1_ptPow_eq_ev {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime]
    (h : Pt R 1 d) (hh : Z h) (F : PS R 1 d) :
    ev ![comp1 h (ptPow R d p 0)] F = ev (n := 1) ![ptPow R d p 0] (ev ![h] F) := by
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  rw [ev1 hq hh, ep_one]

/- English proof (translation)
Establish `hb : ZZ (n` using `1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)`. Establish `hq : ZZ (n` using `1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil`. Establish `hp0 : ∀ c, pderiv R ((1 : Fin 2), j) (ptPow R d p (0 : Fin 2) c) = 0` using `fun c => d_pow_p p _ (X ((0 : Fin 2), c))`. Simplify using `only [Lz]`. Rewrite using `[d2 (Z_ptPow p 0) (Z_pt 1)]`.

Simplify using `only [hp0, dpt, mul_zero, Finset.sum_const_zero, zero_add, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[ev2 hb (Z_ptPow p 0) (Z_pt 1), ev2 hq (Z_pt 0) Z_zero, ep_ptPow p hb, ep_pt hb, ep_pt hq, ep_zero hq]`. Use `congr 1`.
-/
private theorem Lz_ev_ptPow_pt {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP R p]
    (g : PS R 2 d) (j : Fin d) :
    Lz j (ev ![ptPow R d p 0, pt R d 1] g) = ev (n := 1) ![ptPow R d p 0] (Lz j g) := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  have hp0 : ∀ c, pderiv R ((1 : Fin 2), j) (ptPow R d p (0 : Fin 2) c) = 0 := fun c =>
    d_pow_p p _ (X ((0 : Fin 2), c))
  simp only [Lz]
  rw [d2 (Z_ptPow p 0) (Z_pt 1)]
  simp only [hp0, dpt, mul_zero, Finset.sum_const_zero, zero_add, Prod.mk.injEq, true_and,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev2 hb (Z_ptPow p 0) (Z_pt 1), ev2 hq (Z_pt 0) Z_zero, ep_ptPow p hb, ep_pt hb, ep_pt hq,
    ep_zero hq]
  congr 1

/- English proof (translation)
Establish `hxy : ZZ ![x, y]` using `ZZ_cons hx (ZZ_cons hy ZZ_nil)`. Establish `e` using `congrArg (ev ![x, y]) B.cocycleLeft_zero_thd`. Rewrite `e` using `[ev3 hxy (Z_pt 0) (Z_pt 1) Z_zero, ep_pt hxy, ep_pt hxy, ep_zero hxy]`. Simplify `e` using `[ev_one]`.
-/
private theorem ev_ph1_zero_eq_one {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) {x y : Pt R n d} (hx : Z x) (hy : Z y) : ev ![x, y, 0] B.ph1 = 1 := by
  have hxy : ZZ ![x, y] := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have e := congrArg (ev ![x, y]) B.cocycleLeft_zero_thd
  rw [ev3 hxy (Z_pt 0) (Z_pt 1) Z_zero, ep_pt hxy, ep_pt hxy, ep_zero hxy] at e
  simpa [ev_one] using e

/- English proof (translation)
Rewrite using `[first_power_eq_prod_at B hx Z_zero]`. Conclude with `Finset.prod_eq_one fun j _ => ev_ph1_zero_eq_one B (Z_comp1 (Z_act B.A _) hx) hx`.
-/
private theorem ev_pow1_zero_eq_one {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) {x : Pt R n d} (hx : Z x) (k : ℕ) : ev ![x, 0] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B hx Z_zero]
  exact Finset.prod_eq_one fun j _ => ev_ph1_zero_eq_one B (Z_comp1 (Z_act B.A _) hx) hx

/- English proof (translation)
Establish `hx' : ZZ ![x]` using `ZZ_cons hx ZZ_nil`. Establish `e` using `congrArg (ev ![x]) (B.adjoint_zero_snd a)`. Rewrite `e` using `[ev2 hx' (Z_pt 0) Z_zero, ep_pt hx', ep_zero hx']`. Simplify `e` using `[ev_one]`.
-/
private theorem ev_zero_ad_eq_one {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) {x : Pt R n d} (hx : Z x) (a : O) : ev ![x, 0] (B.ad a) = 1 := by
  have hx' : ZZ ![x] := ZZ_cons hx ZZ_nil
  have e := congrArg (ev ![x]) (B.adjoint_zero_snd a)
  rw [ev2 hx' (Z_pt 0) Z_zero, ep_pt hx', ep_zero hx'] at e
  simpa [ev_one] using e

/- English proof (translation)
Establish `hb : ZZ (n` using `1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)`. Establish `e` using `congrArg (Lz j) (first_power_adjoint R d O B a p)`. Rewrite `e` using `[Lz_mul, Lz_mul, Lz_fst (Z_act B.A a), Lz_fst (Z_act B.A (p : O)), Lz_snd (Z_act B.A (star a))]`. Establish `e1 : ev (n` using `1) ![pt R d 0, 0] (ev ![comp1 (B.A.act (p : O)) (pt R d 0), pt R d 1] (B.ad a)) = 1 := by`. Rewrite using `[ev2 hb (Z_comp1 (Z_act _ _) (Z_pt 0)) (Z_pt 1), ep_comp1 _ hb (Z_pt 0), ep_pt hb, ep_pt hb]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]`. Conclude with `ev_zero_ad_eq_one B (Z_act _ _) a`. Establish `e2 : ev (n` using `1) ![pt R d 0, 0] (ev ![comp1 (B.A.act a) (pt R d 0), pt R d 1] (pow1 B p)) = 1 := by`. Rewrite using `[ev2 hb (Z_comp1 (Z_act _ _) (Z_pt 0)) (Z_pt 1), ep_comp1 _ hb (Z_pt 0), ep_pt hb, ep_pt hb]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]`.

Conclude with `ev_pow1_zero_eq_one B (Z_act _ _) p`. Establish `e3 : Lz j (B.ad a ^ p) = 0`. Simplify using `only [Lz, d_pow_p, evz hb]`. Establish `e4 : ev (n` using `1) ![pt R d 0, 0] (B.ad a ^ p) = 1 := by`. Rewrite using `[evpow hb, B.adjoint_zero_snd, one_pow]`.

Rewrite `e` using `[e1, e2, e3, e4]`. Simplify using `using e`.
-/
private theorem ev_act_Lz_pow1_add_ev_act_prime_Lz_ad {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP R p]
    {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (a : O) (j : Fin d) :
    ev ![B.A.act a] (Lz j (pow1 B p)) + ev ![B.A.act (p : O)] (Lz j (B.ad a)) =
      ∑ c, Lz c (pow1 B p) * C (lin (B.A.act (star a)) 1 c j) := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  have e := congrArg (Lz j) (first_power_adjoint R d O B a p)
  rw [Lz_mul, Lz_mul, Lz_fst (Z_act B.A a), Lz_fst (Z_act B.A (p : O)),
    Lz_snd (Z_act B.A (star a))] at e
  have e1 : ev (n := 1) ![pt R d 0, 0]
      (ev ![comp1 (B.A.act (p : O)) (pt R d 0), pt R d 1] (B.ad a)) = 1 := by
    rw [ev2 hb (Z_comp1 (Z_act _ _) (Z_pt 0)) (Z_pt 1), ep_comp1 _ hb (Z_pt 0), ep_pt hb, ep_pt hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]
    exact ev_zero_ad_eq_one B (Z_act _ _) a
  have e2 : ev (n := 1) ![pt R d 0, 0]
      (ev ![comp1 (B.A.act a) (pt R d 0), pt R d 1] (pow1 B p)) = 1 := by
    rw [ev2 hb (Z_comp1 (Z_act _ _) (Z_pt 0)) (Z_pt 1), ep_comp1 _ hb (Z_pt 0), ep_pt hb, ep_pt hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]
    exact ev_pow1_zero_eq_one B (Z_act _ _) p
  have e3 : Lz j (B.ad a ^ p) = 0 := by
    simp only [Lz, d_pow_p, evz hb]
  have e4 : ev (n := 1) ![pt R d 0, 0] (B.ad a ^ p) = 1 := by
    rw [evpow hb, B.adjoint_zero_snd, one_pow]
  rw [e1, e2, e3, e4] at e
  simpa using e

/- English proof (translation)
Take `⟨g, -, hg, hgb⟩` from `first_power_char_p R p d O B`. Take `⟨h, hh, hχ, hhw⟩` from `exists_act_prime_eq_comp1_ptPow p B`. Establish `hLP : ∀ c, Lz c (pow1 B p) = ev (n` using `1) ![ptPow R d p 0] (Lz c g) := fun c => by`. Rewrite using `[hg, Lz_ev_ptPow_pt]`. Establish `e` using `congrArg (coeff (Finsupp.single ((0 : Fin 1), i) p)) (ev_act_Lz_pow1_add_ev_act_prime_Lz_ad p B a j)`.

Simplify using `only [hLP] at e`. Rewrite `e` using `[map_add, coeff_single_prime_ev_of_Z p (Z_act B.A a), hχ, ev_comp1_ptPow_eq_ev p h hh, coeff_ev_pow_one, coeff_lin_ev hh, map_sum]`. Simplify using `only [coeff_mul_C, coeff_ev_pow_one, coeff_Lz, hgb, hhw] at e`. Conclude with `e`.
-/
private theorem sum_am_mul_rho_pow_add_bil_ad_mul_hw {R : Type} [CommRing R] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP R p]
    {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (a : O) (i j : Fin d) :
    ∑ c, am B p c j * rho B a c i ^ p + ∑ c, bil (B.ad a) 1 1 c j * hw B p c i =
      ∑ c, am B p i c * rho B (star a) c j := by
  obtain ⟨g, -, hg, hgb⟩ := first_power_char_p R p d O B
  obtain ⟨h, hh, hχ, hhw⟩ := exists_act_prime_eq_comp1_ptPow p B
  have hLP : ∀ c, Lz c (pow1 B p) = ev (n := 1) ![ptPow R d p 0] (Lz c g) := fun c => by
    rw [hg, Lz_ev_ptPow_pt]
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) p)) (ev_act_Lz_pow1_add_ev_act_prime_Lz_ad p B a j)
  simp only [hLP] at e
  rw [map_add, coeff_single_prime_ev_of_Z p (Z_act B.A a), hχ, ev_comp1_ptPow_eq_ev p h hh, coeff_ev_pow_one,
    coeff_lin_ev hh, map_sum] at e
  simp only [coeff_mul_C, coeff_ev_pow_one, coeff_Lz, hgb, hhw] at e
  exact e

/- English proof (translation)
Introduce `R _ p _ _ d O _ _ B a u`. Take `⟨h, hh, hχ, hhw⟩` from `exists_act_prime_eq_comp1_ptPow p B`. Establish `m1 : hw B p * (rho B a).map (· ^ p) = rho B a * hw B p`. Use extensionality with `i k`. Establish `e` using `congrArg (fun F : Pt R 1 d => lin F p i k) (act_comm B.A a (p : O) (Z_pt (R := R) (d := d) (n := 1) 0))`.

Simplify using `only [germCompOne_identityPoint_left] at e`. Rewrite `e` using `[hχ]`. Establish `L : lin (comp1 (B.A.act a) (comp1 h (ptPow R d p 0))) p i k = ∑ c, rho B a i c * hw B p c k` using `by show coeff (Finsupp.single ((0 : Fin 1), k) p) (ev ![comp1 h (ptPow R d p 0)] (B.A.act a i)) = _`. Rewrite using `[ev_comp1_ptPow_eq_ev p h hh, coeff_ev_pow_one, coeff_lin_ev hh]`. Simplify using `only [hhw]`.

Both sides reduce to the same expression. Establish `Rr : lin (comp1 (comp1 h (ptPow R d p 0)) (B.A.act a)) p i k = ∑ c, hw B p i c * rho B a c k ^ p` using `by show coeff (Finsupp.single ((0 : Fin 1), k) p) (ev ![B.A.act a] (ev (n := 1) ![ptPow R d p 0] (h i))) = _`. Rewrite using `[coeff_single_prime_ev_of_Z p (Z_act B.A a)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← hhw]`.

Both sides reduce to the same expression. Rewrite `e` using `[L, Rr]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply]`. Conclude with `e.symm`. Establish `m2 : (am B p).transpose * (rho B a).map (· ^ p) = (rho B (star a)).transpose * (am B p).transpose - (bil (B.ad a) 1 1).transpose * hw B p`.

Use extensionality with `i k`. Establish `e` using `sum_am_mul_rho_pow_add_bil_ad_mul_hw p B a k i`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[eq_sub_iff_add_eq, e]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[alpha, rhoH, Matrix.mulVec_mulVec, m1]`. Simplify using `[alpha, rhoH, Matrix.mulVec_mulVec, m2, Matrix.sub_mulVec]`.
-/
theorem alpha_act : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) := by
  intro R _ p _ _ d O _ _ B a u
  obtain ⟨h, hh, hχ, hhw⟩ := exists_act_prime_eq_comp1_ptPow p B
  have m1 : hw B p * (rho B a).map (· ^ p) = rho B a * hw B p := by
    ext i k
    have e := congrArg (fun F : Pt R 1 d => lin F p i k)
      (act_comm B.A a (p : O) (Z_pt (R := R) (d := d) (n := 1) 0))
    simp only [germCompOne_identityPoint_left] at e
    rw [hχ] at e
    have L : lin (comp1 (B.A.act a) (comp1 h (ptPow R d p 0))) p i k =
        ∑ c, rho B a i c * hw B p c k := by
      show coeff (Finsupp.single ((0 : Fin 1), k) p) (ev ![comp1 h (ptPow R d p 0)] (B.A.act a i)) = _
      rw [ev_comp1_ptPow_eq_ev p h hh, coeff_ev_pow_one, coeff_lin_ev hh]
      simp only [hhw]
      rfl
    have Rr : lin (comp1 (comp1 h (ptPow R d p 0)) (B.A.act a)) p i k =
        ∑ c, hw B p i c * rho B a c k ^ p := by
      show coeff (Finsupp.single ((0 : Fin 1), k) p)
        (ev ![B.A.act a] (ev (n := 1) ![ptPow R d p 0] (h i))) = _
      rw [coeff_single_prime_ev_of_Z p (Z_act B.A a)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hhw]
      rfl
    rw [L, Rr] at e
    simp only [Matrix.mul_apply, Matrix.map_apply]
    exact e.symm
  have m2 : (am B p).transpose * (rho B a).map (· ^ p) =
      (rho B (star a)).transpose * (am B p).transpose - (bil (B.ad a) 1 1).transpose * hw B p := by
    ext i k
    have e := sum_am_mul_rho_pow_add_bil_ad_mul_hw p B a k i
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [eq_sub_iff_add_eq, e]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine Prod.ext ?_ ?_
  · simp [alpha, rhoH, Matrix.mulVec_mulVec, m1]
  · simp [alpha, rhoH, Matrix.mulVec_mulVec, m2, Matrix.sub_mulVec]

end PositivityTheory.HtPt.Cb
