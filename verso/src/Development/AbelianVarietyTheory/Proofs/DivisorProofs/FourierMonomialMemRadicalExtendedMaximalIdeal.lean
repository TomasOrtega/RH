import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.RadQ

section Forms

variable {s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {X : Type} [AddCommGroup X]

def polW (W : Matrix (Fin s) (Fin s) ℤ) (β : LinearMap.BilinForm ℤ X) (x y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * (β (x u) (y v) + β (y u) (x v))

/- English proof (translation)
Simplify using `only [qW, polW, Pi.add_apply, Pi.smul_apply, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qW_smul_add (β : LinearMap.BilinForm ℤ X) (a : ℤ) (x y : Fin s → X) :
    qW W β (a • x + y) = a ^ 2 * qW W β x + a * polW W β x y + qW W β y := by
  simp only [qW, polW, Pi.add_apply, Pi.smul_apply, map_add, map_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/- English proof (translation)
Establish `h` using `qW_smul_add (W := W) β a x 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[h]`. Simplify using `[qW, polW]`.
-/
theorem qW_smul (β : LinearMap.BilinForm ℤ X) (a : ℤ) (x : Fin s → X) :
    qW W β (a • x) = a ^ 2 * qW W β x := by
  have h := qW_smul_add (W := W) β a x 0
  rw [add_zero] at h
  rw [h]
  simp [qW, polW]

/- English proof (translation)
Establish `h : ∀ a : ℤ, 0 ≤ a * polW W β x y + qW W β y` using `fun a => by`. Use `qW_nonneg hW hs hβ (a • x + y)` as an intermediate fact. Rewrite `this` using `[qW_smul_add, hx, mul_zero, zero_add]`. Conclude with `this`. Establish `hy` using `qW_nonneg hW hs hβ y`.

Break down `lt_trichotomy (polW W β x y) 0 with hp | hp | hp` into its components or cases. Use `h (qW W β y + 1)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `hp`. Use `h (-(qW W β y + 1))` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem polW_eq_zero (hW : PosW W) {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a)
    (hβ : ∀ y, 0 ≤ β y y) {x : Fin s → X} (hx : qW W β x = 0) (y : Fin s → X) : polW W β x y = 0 := by
  have h : ∀ a : ℤ, 0 ≤ a * polW W β x y + qW W β y := fun a => by
    have := qW_nonneg hW hs hβ (a • x + y)
    rw [qW_smul_add, hx, mul_zero, zero_add] at this
    exact this
  have hy := qW_nonneg hW hs hβ y
  rcases lt_trichotomy (polW W β x y) 0 with hp | hp | hp
  · have := h (qW W β y + 1); nlinarith
  · exact hp
  · have := h (-(qW W β y + 1)); nlinarith

/- English proof (translation)
Use `qW_smul_add (W := W) β 1 x y` as an intermediate fact. Rewrite `this` using `[one_smul]`. Rewrite using `[this, hx, hy, polW_eq_zero hW hs hβ hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qW_add_eq_zero (hW : PosW W) {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a)
    (hβ : ∀ y, 0 ≤ β y y) {x y : Fin s → X} (hx : qW W β x = 0) (hy : qW W β y = 0) :
    qW W β (x + y) = 0 := by
  have := qW_smul_add (W := W) β 1 x y
  rw [one_smul] at this
  rw [this, hx, hy, polW_eq_zero hW hs hβ hx]
  ring

def nullSub (hW : PosW W) {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X)
    (hs : ∀ k a b, δ k a b = δ k b a) (hn : ∀ k y, 0 ≤ δ k y y) (I : Fin m → Prop) :
    AddSubgroup (Fin s → X) where
  carrier := {mu | ∀ k, I k → qW W (δ k) mu = 0}
  add_mem' := fun ha hb k hk => qW_add_eq_zero hW (hs k) (hn k) (ha k hk) (hb k hk)
  zero_mem' := fun k _ => by simp [qW]
  neg_mem' := fun {x} ha k hk => by
    show qW W (δ k) (-x) = 0
    rw [← neg_one_smul ℤ x, qW_smul, ha k hk, mul_zero]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, mu u ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hmu (funext h)`. Take `⟨k, hk⟩` from `hp _ hu`.

Take `⟨c, hc0, hc⟩` from `QWDom.qW_ge s W hW`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1 : δ k (mu u) (mu u) ≤ ∑ v, δ k (mu v) (mu v)` using `Finset.single_le_sum (f := fun v => δ k (mu v) (mu v)) (fun v _ => hn k _) (Finset.mem_univ u)`. Establish `h2` using `hc X (δ k) (hs k) (hn k) mu`. Establish `h3 : (0 : ℝ) < c * ((∑ v, δ k (mu v) (mu v) : ℤ) : ℝ)`.

Apply `mul_pos hc0` to reduce the goal to its premises. Conclude with `hk.trans_le h1` after adjusting the coercions. Conclude with `h3.trans_le h2` after adjusting the coercions.
-/
theorem exists_qW_pos (hW : PosW W) {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X)
    (hs : ∀ k a b, δ k a b = δ k b a) (hn : ∀ k y, 0 ≤ δ k y y) (hp : ∀ x, x ≠ 0 → ∃ k, 0 < δ k x x)
    {mu : Fin s → X} (hmu : mu ≠ 0) : ∃ k, 0 < qW W (δ k) mu := by
  obtain ⟨u, hu⟩ : ∃ u, mu u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hmu (funext h)
  obtain ⟨k, hk⟩ := hp _ hu
  obtain ⟨c, hc0, hc⟩ := QWDom.qW_ge s W hW
  refine ⟨k, ?_⟩
  have h1 : δ k (mu u) (mu u) ≤ ∑ v, δ k (mu v) (mu v) :=
    Finset.single_le_sum (f := fun v => δ k (mu v) (mu v)) (fun v _ => hn k _) (Finset.mem_univ u)
  have h2 := hc X (δ k) (hs k) (hn k) mu
  have h3 : (0 : ℝ) < c * ((∑ v, δ k (mu v) (mu v) : ℤ) : ℝ) := by
    apply mul_pos hc0
    exact_mod_cast hk.trans_le h1
  exact_mod_cast h3.trans_le h2

/- English proof (translation)
Unfold `mono`. Use `Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) ?_` and prove the remaining obligations. Conclude with `Ideal.pow_mem_of_mem _ hk _ (by omega)`.
-/
theorem mono_mem {V : Type} [CommRing V] {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X)
    (mu : Fin s → X) (P : Ideal V) (k : Fin m) (hk : t k ∈ P) (hq : 0 < qW W (δ k) mu) :
    mono W t δ mu ∈ P := by
  unfold mono
  refine Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) ?_
  exact Ideal.pow_mem_of_mem _ hk _ (by omega)

end Forms

section Val

open IsDiscreteValuationRing

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, addVal_mul, ih]`.
-/
theorem addVal_prod {J : Type*} (S : Finset J) (f : J → R) :
    addVal R (∏ i ∈ S, f i) = ∑ i ∈ S, addVal R (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, addVal_mul, ih]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Rewrite `hx` using `[(irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Use `(addVal_le_iff_dvd (a := ϖ ^ j) (b := x)).2 hx` as an intermediate fact. Rewrite `this` using `[addVal_pow, addVal_uniformizer hϖ, nsmul_eq_mul, _root_.mul_one]`. Then use the resulting hypothesis.
-/
theorem le_addVal_of_mem_pow (j : ℕ) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R ^ j) : (j : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [(irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  have := (addVal_le_iff_dvd (a := ϖ ^ j) (b := x)).2 hx
  rwa [addVal_pow, addVal_uniformizer hϖ, nsmul_eq_mul, _root_.mul_one] at this

/- English proof (translation)
Use `(addVal_le_iff_dvd (a := x) (b := 1)).2 hx.dvd` as an intermediate fact. Rewrite `this` using `[AddValuation.map_one]`. Conclude with `le_antisymm this zero_le`.
-/
theorem addVal_unit {x : R} (hx : IsUnit x) : addVal R x = 0 := by
  have := (addVal_le_iff_dvd (a := x) (b := 1)).2 hx.dvd
  rw [AddValuation.map_one] at this
  exact le_antisymm this zero_le

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Rewrite `hx` using `[(irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]`. Establish `h1` using `(addVal_le_iff_dvd (a := ϖ) (b := x)).2 hx`. Rewrite `h1` using `[addVal_uniformizer hϖ]`. Establish `htop : addVal R x ≠ ⊤` using `fun e => h0 (addVal_eq_top_iff.1 e)`.

Take `⟨r, hr⟩` from `ENat.ne_top_iff_exists.1 htop`. Use `⟨r, ?_, hr.symm⟩` and prove the remaining obligations. Rewrite `h1` using `[← hr]`. Conclude with `h1` after adjusting the coercions.
-/
theorem addVal_mem (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (h0 : x ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ addVal R x = r := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [(irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hx
  have h1 := (addVal_le_iff_dvd (a := ϖ) (b := x)).2 hx
  rw [addVal_uniformizer hϖ] at h1
  have htop : addVal R x ≠ ⊤ := fun e => h0 (addVal_eq_top_iff.1 e)
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 htop
  refine ⟨r, ?_, hr.symm⟩
  rw [← hr] at h1
  exact_mod_cast h1

end Val

end GlobalTheory.Poinc.RadQ

namespace GlobalTheory.Poinc.RadQ

open IsDiscreteValuationRing

/- English proof (translation)
Assume the negation of the conclusion as `hm`. Establish `hs : ∀ k a b, Φ.δ y k a b = Φ.δ y k b a` using `fun k => (Φ.bal y k).1`. Establish `hn : ∀ k x, 0 ≤ Φ.δ y k x x` using `Φ.nonneg y`. Establish `hW` using `Φ.posW`. Establish `hQ : ∀ k mu, 0 ≤ qW W (Φ.δ y k) mu` using `fun k mu => qW_nonneg hW (hs k) (hn k) mu`.

Set `H` to `nullSub hW (Φ.δ y) hs hn (fun k => φ (Φ.t y k) = 0)`. Establish `hmemH : ∀ mu, mu ∈ H ↔ ∀ k, φ (Φ.t y k) = 0 → qW W (Φ.δ y k) mu = 0` using `fun mu => Iff.rfl`. Establish `hφmono : ∀ mu, φ (mono W (Φ.t y) (Φ.δ y) mu) = ∏ k, φ (Φ.t y k) ^ (qW W (Φ.δ y k) mu).toNat`. Introduce `mu`. Simplify using `[mono, map_prod, map_pow]`.

Establish `hout : ∀ mu, mu ∉ H → φ (mono W (Φ.t y) (Φ.δ y) mu) = 0`. Introduce `mu hmu`. Rewrite `hmu` using `[hmemH]`. Use `push_neg at hmu`. Take `⟨k, hk, hk'⟩` from `hmu`.

Rewrite using `[hφmono]`. Apply `Finset.prod_eq_zero (Finset.mem_univ k)` to reduce the goal to its premises. Rewrite using `[hk]`. Apply `zero_pow` to reduce the goal to its premises. Use `hQ k mu` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hnuH : nu ∈ H`. Assume the negation of the conclusion as `h`. Conclude with `hm (hout nu h)`. Set `n : Fin (Φ.m y) → ℕ` to `fun k => (addVal R (φ (Φ.t y k))).toNat`.

Establish `hnk : ∀ k, φ (Φ.t y k) ≠ 0 → 1 ≤ n k ∧ addVal R (φ (Φ.t y k)) = n k`. Introduce `k hk`. Take `⟨r, hr1, hr⟩` from `addVal_mem (φ (Φ.t y k)) (map_nonunit φ _ (Φ.t_mem y k).1) hk`. Establish `: n k = r` using `by simp only [n, hr, ENat.toNat_coe]`. Conclude with `⟨this ▸ hr1, this ▸ hr⟩`.

Set `β : LinearMap.BilinForm ℤ (Φ.X y)` to `∑ k, (n k : ℤ) • Φ.δ y k`. Establish `hβlin : ∀ mu, qW W β mu = ∑ k, (n k : ℤ) * qW W (Φ.δ y k) mu`. Introduce `mu`. Simplify using `only [qW, β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hβs : ∀ a b, β a b = β b a`.

Introduce `a b`. Simplify using `only [β, LinearMap.sum_apply, LinearMap.smul_apply, hs _ a b]`. Establish `hβn : ∀ x, 0 ≤ β x x`. Introduce `x`. Simplify using `only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hn k x)`. Establish `hβ0 : ∀ mu, 0 ≤ qW W β mu` using `qW_nonneg hW hβs hβn`. Set `e : (Fin s → Φ.X y) → ℕ` to `fun mu => ∑ k, (qW W (Φ.δ y k) mu).toNat * n k`. Establish `he : ∀ mu, (e mu : ℤ) = qW W β mu`. Introduce `mu`.

Rewrite using `[hβlin]`. Simplify using `only [e, Nat.cast_sum, Nat.cast_mul, Int.toNat_of_nonneg (hQ _ mu)]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `hvmono : ∀ mu ∈ H, addVal R (φ (mono W (Φ.t y) (Φ.δ y) mu)) = (e mu : ℕ∞)`. Introduce `mu hmu`.

Establish `hk : ∀ k, addVal R (φ (Φ.t y k) ^ (qW W (Φ.δ y k) mu).toNat) = (((qW W (Φ.δ y k) mu).toNat * n k : ℕ) : ℕ∞)`. Introduce `k`. Distinguish the cases in `hk : φ (Φ.t y k) = 0`. Rewrite using `[(hmemH mu).1 hmu k hk]`. Simplify using the standard rewrite rules.

Rewrite using `[addVal_pow, (hnk k hk).2, nsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hφmono, addVal_prod]`. Simplify using `only [hk, e, Nat.cast_sum]`.

Establish `hβpos : ∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu`. Introduce `mu hmu h0`. Take `⟨k, hk⟩` from `exists_qW_pos hW (Φ.δ y) hs hn (Φ.pos y) h0`. Establish `hk0 : φ (Φ.t y k) ≠ 0` using `fun e' => by`. Use `(hmemH mu).1 hmu k e'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hβlin]`. Establish `h1 : (n k : ℤ) * qW W (Φ.δ y k) mu ≤ ∑ j, (n j : ℤ) * qW W (Φ.δ y j) mu` using `Finset.single_le_sum (f := fun j => (n j : ℤ) * qW W (Φ.δ y j) mu) (fun j _ => mul_nonneg (by positivity) (hQ j mu)) (Finset.mem_univ k)`. Establish `h2 : (1 : ℤ) ≤ n k` using `by exact_mod_cast (hnk k hk0).1`. Establish `h3 : (0 : ℤ) < (n k : ℤ) * qW W (Φ.δ y k) mu` using `mul_pos (by omega) hk`.

Use linear arithmetic over natural numbers and integers. Establish `hex : ∃ r : ℕ, ∃ mu ∈ H, mu ≠ 0 ∧ qW W β mu = r` using `⟨(qW W β nu).toNat, nu, hnuH, hnu, (Int.toNat_of_nonneg (hβ0 nu)).symm⟩`. Take `⟨mu₀, hmu₀H, hmu₀0, hmu₀eq⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu`. Introduce `mu hmu h0`.

Rewrite using `[hmu₀eq]`. Establish `h1` using `Nat.find_min' hex ⟨mu, hmu, h0, (Int.toNat_of_nonneg (hβ0 mu)).symm⟩`. Establish `h2` using `Int.toNat_of_nonneg (hβ0 mu)`. Use linear arithmetic over natural numbers and integers. Establish `hcong : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → ∃ w : Fin s → Φ.X y, mu = mu₀ + N₁ • w`.

Introduce `mu h`. Use `choose w hw using h`. Conclude with `⟨w, funext fun i => by simp [hw i]⟩`. Establish `hsat : ∀ w : Fin s → Φ.X y, N₁ • w ∈ H → w ∈ H`. Introduce `w hw`.

Use `(hmemH w).2 fun k hk => ?_` and prove the remaining obligations. Establish `h` using `(hmemH _).1 hw k hk`. Rewrite `h` using `[← natCast_zsmul, qW_smul]`. Establish `h3 : (N₁ : ℤ) ^ 2 ≠ 0` using `by positivity`. Conclude with `(mul_eq_zero.1 h).resolve_left h3`.

Establish `hbig : ∀ mu ∈ H, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → mu ≠ mu₀ → qW W β mu₀ < qW W β mu`. Introduce `mu hmu hc hne`. Take `⟨w, rfl⟩` from `hcong mu hc`. Establish `hw : w ∈ H` using `hsat w (by simpa using H.sub_mem hmu hmu₀H)`. Establish `hw0 : w ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hne`. Conclude with `GlobalTheory.T.least_vector_unique_in_class_mod s W hW (Φ.X y) β hβs hβn H hβpos mu₀ hmu₀H hmu₀0 hmin N₁ hN w hw hw0`. Establish `hz : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → mu ≠ 0`. Introduce and unpack `mu hc rfl`.

Establish `h1` using `hbig 0 H.zero_mem hc (Ne.symm hmu₀0)`. Establish `h2 : qW W β 0 = 0` using `by simp [qW]`. Establish `h3` using `hβ0 mu₀`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc⟩` from `Φ.u_unit y mu₀`.

Take `⟨h, hh⟩` from `hE y mu₀ c`. Establish `hmaxV : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → Φ.term y mu c ∈ IsLocalRing.maximalIdeal (Φ.V y)`. Introduce `mu hmu`. Take `⟨k, hk⟩` from `exists_qW_pos hW (Φ.δ y) hs hn (Φ.pos y) (hz mu hmu)`. Conclude with `Ideal.mul_mem_left _ _ (mono_mem _ _ _ _ k (Φ.t_mem y k).1 hk)`.

Establish `hevh : Φ.ev y h ∈ IsLocalRing.maximalIdeal (Φ.V y)`. Take `⟨S, hS1, -, hS3⟩` from `hh 1`. Rewrite `hS3` using `[pow_one, RingHom.id_apply]`. Use `Ideal.add_mem _ hS3 (Ideal.sum_mem _ fun mu hmu => hmaxV mu (hS1 mu hmu))` as an intermediate fact. Simplify using `using this`.

Establish `hhA : h ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hevh (hu.map _)`. Establish `hφh : φ (Φ.ev y h) = 0` using `hJ h hhA`.

Use `set q₀ := (qW W β mu₀).toNat with hq₀`. Establish `he₀ : e mu₀ = q₀`. Use `he mu₀` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨S, hS1, hS2, hS3⟩` from `hh (q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat)`.

Establish `hmu₀S : mu₀ ∈ S`. Assume the negation of the conclusion as `hno`. Establish `h1` using `hS2 mu₀ (fun w => ⟨0, by simp⟩) hno`. Establish `hnn : 0 ≤ ∑ i, qW W (Φ.δ y i) mu₀` using `Finset.sum_nonneg fun i _ => hQ i mu₀`. Move the coercions through the operations in `at h1`.

Use linear arithmetic over natural numbers and integers. Establish `hsum : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (∑ mu ∈ S, Φ.term y mu c))`. Establish `h1 : φ (Φ.ev y h - ∑ mu ∈ S, Φ.term y mu c) ∈ IsLocalRing.maximalIdeal R ^ (q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat)` using `GlobalTheory.map_maximalIdeal_pow_le φ _ (Ideal.mem_map_of_mem φ (by simpa using hS3))`. Rewrite `h1` using `[map_sub, hφh, zero_sub]`. Establish `h2` using `le_addVal_of_mem_pow _ _ h1`.

Rewrite `h2` using `[AddValuation.map_neg]`. Use `le_trans ?_ h2` and prove the remaining obligations. Conclude with `(by omega : q₀ + 1 ≤ q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat)` after adjusting the coercions. Establish `hrest : ∀ mu ∈ S.erase mu₀, ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (Φ.term y mu c))`. Introduce `mu hmu`.

Take `⟨hne, hmuS⟩` from `Finset.mem_erase.1 hmu`. Rewrite using `[VPre.term, map_mul, addVal_mul]`. Use `le_trans ?_ le_add_self` and prove the remaining obligations. Distinguish the cases in `hH : mu ∈ H`. Rewrite using `[hvmono mu hH]`.

Establish `h1` using `hbig mu hH (hS1 mu hmuS) hne`. Establish `h2` using `he mu`. Establish `h3` using `hβ0 mu₀`. Conclude with `(show q₀ + 1 ≤ e mu by omega)` after adjusting the coercions. Rewrite using `[hout mu hH]`.

Simplify using the standard rewrite rules. Establish `hrestsum : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (∑ mu ∈ S.erase mu₀, Φ.term y mu c))`. Rewrite using `[map_sum]`. Conclude with `AddValuation.map_le_sum _ fun mu hmu => hrest mu hmu`. Establish `hv₀ : addVal R (φ (Φ.term y mu₀ c)) = (q₀ : ℕ∞)`.

Rewrite using `[VPre.term, map_mul, addVal_mul, addVal_unit (hc.map φ), hvmono mu₀ hmu₀H, he₀, zero_add]`. Establish `hfinal : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (Φ.term y mu₀ c))`. Establish `hsplit` using `Finset.add_sum_erase S (fun mu => Φ.term y mu c) hmu₀S`. Establish `h1 : φ (Φ.term y mu₀ c) = φ (∑ mu ∈ S, Φ.term y mu c) - φ (∑ mu ∈ S.erase mu₀, Φ.term y mu c)`. Rewrite using `[← hsplit, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `le_trans (le_min hsum hrestsum) (AddValuation.map_sub _ _ _)`. Rewrite `hfinal` using `[hv₀]`. Establish `: q₀ + 1 ≤ q₀` using `by exact_mod_cast hfinal`.

Use linear arithmetic over natural numbers and integers.
-/
theorem map_mono_eq_zero {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type}
    [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ) (hN : 3 ≤ N₁) (hE : Φ.Exact N₁) (y : Φ.Y)
    (nu : Fin s → Φ.X y) (hnu : nu ≠ 0) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (φ : Φ.V y →+* R) [IsLocalHom φ] (hJ : ∀ a ∈ IsLocalRing.maximalIdeal A, φ (Φ.ev y a) = 0) :
    φ (mono W (Φ.t y) (Φ.δ y) nu) = 0 := by
  classical
  by_contra hm
  have hs : ∀ k a b, Φ.δ y k a b = Φ.δ y k b a := fun k => (Φ.bal y k).1
  have hn : ∀ k x, 0 ≤ Φ.δ y k x x := Φ.nonneg y
  have hW := Φ.posW
  have hQ : ∀ k mu, 0 ≤ qW W (Φ.δ y k) mu := fun k mu => qW_nonneg hW (hs k) (hn k) mu
  let H := nullSub hW (Φ.δ y) hs hn (fun k => φ (Φ.t y k) = 0)
  have hmemH : ∀ mu, mu ∈ H ↔ ∀ k, φ (Φ.t y k) = 0 → qW W (Φ.δ y k) mu = 0 := fun mu => Iff.rfl
  have hφmono : ∀ mu, φ (mono W (Φ.t y) (Φ.δ y) mu) = ∏ k, φ (Φ.t y k) ^ (qW W (Φ.δ y k) mu).toNat := by
    intro mu
    simp [mono, map_prod, map_pow]
  have hout : ∀ mu, mu ∉ H → φ (mono W (Φ.t y) (Φ.δ y) mu) = 0 := by
    intro mu hmu
    rw [hmemH] at hmu
    push_neg at hmu
    obtain ⟨k, hk, hk'⟩ := hmu
    rw [hφmono]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [hk]
    apply zero_pow
    have := hQ k mu
    omega
  have hnuH : nu ∈ H := by
    by_contra h
    exact hm (hout nu h)

  let n : Fin (Φ.m y) → ℕ := fun k => (addVal R (φ (Φ.t y k))).toNat
  have hnk : ∀ k, φ (Φ.t y k) ≠ 0 → 1 ≤ n k ∧ addVal R (φ (Φ.t y k)) = n k := by
    intro k hk
    obtain ⟨r, hr1, hr⟩ := addVal_mem (φ (Φ.t y k)) (map_nonunit φ _ (Φ.t_mem y k).1) hk
    have : n k = r := by simp only [n, hr, ENat.toNat_coe]
    exact ⟨this ▸ hr1, this ▸ hr⟩
  let β : LinearMap.BilinForm ℤ (Φ.X y) := ∑ k, (n k : ℤ) • Φ.δ y k
  have hβlin : ∀ mu, qW W β mu = ∑ k, (n k : ℤ) * qW W (Φ.δ y k) mu := by
    intro mu
    simp only [qW, β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hβs : ∀ a b, β a b = β b a := by
    intro a b
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, hs _ a b]
  have hβn : ∀ x, 0 ≤ β x x := by
    intro x
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hn k x)
  have hβ0 : ∀ mu, 0 ≤ qW W β mu := qW_nonneg hW hβs hβn
  let e : (Fin s → Φ.X y) → ℕ := fun mu => ∑ k, (qW W (Φ.δ y k) mu).toNat * n k
  have he : ∀ mu, (e mu : ℤ) = qW W β mu := by
    intro mu
    rw [hβlin]
    simp only [e, Nat.cast_sum, Nat.cast_mul, Int.toNat_of_nonneg (hQ _ mu)]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hvmono : ∀ mu ∈ H, addVal R (φ (mono W (Φ.t y) (Φ.δ y) mu)) = (e mu : ℕ∞) := by
    intro mu hmu
    have hk : ∀ k, addVal R (φ (Φ.t y k) ^ (qW W (Φ.δ y k) mu).toNat) =
        (((qW W (Φ.δ y k) mu).toNat * n k : ℕ) : ℕ∞) := by
      intro k
      by_cases hk : φ (Φ.t y k) = 0
      · rw [(hmemH mu).1 hmu k hk]
        simp
      · rw [addVal_pow, (hnk k hk).2, nsmul_eq_mul]
        push_cast
        rfl
    rw [hφmono, addVal_prod]
    simp only [hk, e, Nat.cast_sum]
  have hβpos : ∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu := by
    intro mu hmu h0
    obtain ⟨k, hk⟩ := exists_qW_pos hW (Φ.δ y) hs hn (Φ.pos y) h0
    have hk0 : φ (Φ.t y k) ≠ 0 := fun e' => by
      have := (hmemH mu).1 hmu k e'
      omega
    rw [hβlin]
    have h1 : (n k : ℤ) * qW W (Φ.δ y k) mu ≤ ∑ j, (n j : ℤ) * qW W (Φ.δ y j) mu :=
      Finset.single_le_sum (f := fun j => (n j : ℤ) * qW W (Φ.δ y j) mu)
        (fun j _ => mul_nonneg (by positivity) (hQ j mu)) (Finset.mem_univ k)
    have h2 : (1 : ℤ) ≤ n k := by exact_mod_cast (hnk k hk0).1
    have h3 : (0 : ℤ) < (n k : ℤ) * qW W (Φ.δ y k) mu := mul_pos (by omega) hk
    omega

  have hex : ∃ r : ℕ, ∃ mu ∈ H, mu ≠ 0 ∧ qW W β mu = r :=
    ⟨(qW W β nu).toNat, nu, hnuH, hnu, (Int.toNat_of_nonneg (hβ0 nu)).symm⟩
  obtain ⟨mu₀, hmu₀H, hmu₀0, hmu₀eq⟩ := Nat.find_spec hex
  have hmin : ∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu := by
    intro mu hmu h0
    rw [hmu₀eq]
    have h1 := Nat.find_min' hex ⟨mu, hmu, h0, (Int.toNat_of_nonneg (hβ0 mu)).symm⟩
    have h2 := Int.toNat_of_nonneg (hβ0 mu)
    omega
  have hcong : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) →
      ∃ w : Fin s → Φ.X y, mu = mu₀ + N₁ • w := by
    intro mu h
    choose w hw using h
    exact ⟨w, funext fun i => by simp [hw i]⟩
  have hsat : ∀ w : Fin s → Φ.X y, N₁ • w ∈ H → w ∈ H := by
    intro w hw
    refine (hmemH w).2 fun k hk => ?_
    have h := (hmemH _).1 hw k hk
    rw [← natCast_zsmul, qW_smul] at h
    have h3 : (N₁ : ℤ) ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left h3
  have hbig : ∀ mu ∈ H, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → mu ≠ mu₀ → qW W β mu₀ < qW W β mu := by
    intro mu hmu hc hne
    obtain ⟨w, rfl⟩ := hcong mu hc
    have hw : w ∈ H := hsat w (by simpa using H.sub_mem hmu hmu₀H)
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hne
    exact GlobalTheory.T.least_vector_unique_in_class_mod s W hW (Φ.X y) β hβs hβn H hβpos mu₀ hmu₀H hmu₀0 hmin N₁ hN w hw hw0
  have hz : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → mu ≠ 0 := by
    rintro mu hc rfl
    have h1 := hbig 0 H.zero_mem hc (Ne.symm hmu₀0)
    have h2 : qW W β 0 = 0 := by simp [qW]
    have h3 := hβ0 mu₀
    omega

  obtain ⟨c, hc⟩ := Φ.u_unit y mu₀
  obtain ⟨h, hh⟩ := hE y mu₀ c
  have hmaxV : ∀ mu : Fin s → Φ.X y, (∀ w, CongMod N₁ (mu w) (mu₀ w)) → Φ.term y mu c ∈ IsLocalRing.maximalIdeal (Φ.V y) := by
    intro mu hmu
    obtain ⟨k, hk⟩ := exists_qW_pos hW (Φ.δ y) hs hn (Φ.pos y) (hz mu hmu)
    exact Ideal.mul_mem_left _ _ (mono_mem _ _ _ _ k (Φ.t_mem y k).1 hk)
  have hevh : Φ.ev y h ∈ IsLocalRing.maximalIdeal (Φ.V y) := by
    obtain ⟨S, hS1, -, hS3⟩ := hh 1
    rw [pow_one, RingHom.id_apply] at hS3
    have := Ideal.add_mem _ hS3 (Ideal.sum_mem _ fun mu hmu => hmaxV mu (hS1 mu hmu))
    simpa using this
  have hhA : h ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hevh (hu.map _)
  have hφh : φ (Φ.ev y h) = 0 := hJ h hhA

  set q₀ := (qW W β mu₀).toNat with hq₀
  have he₀ : e mu₀ = q₀ := by
    have := he mu₀
    omega
  obtain ⟨S, hS1, hS2, hS3⟩ := hh (q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat)
  have hmu₀S : mu₀ ∈ S := by
    by_contra hno
    have h1 := hS2 mu₀ (fun w => ⟨0, by simp⟩) hno
    have hnn : 0 ≤ ∑ i, qW W (Φ.δ y i) mu₀ := Finset.sum_nonneg fun i _ => hQ i mu₀
    push_cast at h1
    omega
  have hsum : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (∑ mu ∈ S, Φ.term y mu c)) := by
    have h1 : φ (Φ.ev y h - ∑ mu ∈ S, Φ.term y mu c) ∈
        IsLocalRing.maximalIdeal R ^ (q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat) :=
      GlobalTheory.map_maximalIdeal_pow_le φ _ (Ideal.mem_map_of_mem φ (by simpa using hS3))
    rw [map_sub, hφh, zero_sub] at h1
    have h2 := le_addVal_of_mem_pow _ _ h1
    rw [AddValuation.map_neg] at h2
    refine le_trans ?_ h2
    exact_mod_cast (by omega : q₀ + 1 ≤ q₀ + 1 + (∑ i, qW W (Φ.δ y i) mu₀).toNat)
  have hrest : ∀ mu ∈ S.erase mu₀, ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (Φ.term y mu c)) := by
    intro mu hmu
    obtain ⟨hne, hmuS⟩ := Finset.mem_erase.1 hmu
    rw [VPre.term, map_mul, addVal_mul]
    refine le_trans ?_ le_add_self
    by_cases hH : mu ∈ H
    · rw [hvmono mu hH]
      have h1 := hbig mu hH (hS1 mu hmuS) hne
      have h2 := he mu
      have h3 := hβ0 mu₀
      exact_mod_cast (show q₀ + 1 ≤ e mu by omega)
    · rw [hout mu hH]
      simp
  have hrestsum : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (∑ mu ∈ S.erase mu₀, Φ.term y mu c)) := by
    rw [map_sum]
    exact AddValuation.map_le_sum _ fun mu hmu => hrest mu hmu
  have hv₀ : addVal R (φ (Φ.term y mu₀ c)) = (q₀ : ℕ∞) := by
    rw [VPre.term, map_mul, addVal_mul, addVal_unit (hc.map φ), hvmono mu₀ hmu₀H, he₀, zero_add]
  have hfinal : ((q₀ + 1 : ℕ) : ℕ∞) ≤ addVal R (φ (Φ.term y mu₀ c)) := by
    have hsplit := Finset.add_sum_erase S (fun mu => Φ.term y mu c) hmu₀S
    have h1 : φ (Φ.term y mu₀ c) =
        φ (∑ mu ∈ S, Φ.term y mu c) - φ (∑ mu ∈ S.erase mu₀, Φ.term y mu c) := by
      rw [← hsplit, map_add]
      ring
    rw [h1]
    exact le_trans (le_min hsum hrestsum) (AddValuation.map_sub _ _ _)
  rw [hv₀] at hfinal
  have : q₀ + 1 ≤ q₀ := by exact_mod_cast hfinal
  omega

/- English proof (translation)
Introduce `O _ bar q s W A _ _ Φ N₁ hN hE y nu hnu`. Assume the negation of the conclusion as `hno`. Rewrite `hno` using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Use `push_neg at hno`. Take `⟨p, ⟨hJp, hp⟩, hmp⟩` from `hno`.

Establish `hs : ∀ k a b, Φ.δ y k a b = Φ.δ y k b a` using `fun k => (Φ.bal y k).1`. Distinguish the cases in `hpm : p = IsLocalRing.maximalIdeal (Φ.V y)`. Substitute `hpm` using the available equality. Take `⟨k, hk⟩` from `exists_qW_pos Φ.posW (Φ.δ y) hs (Φ.nonneg y) (Φ.pos y) hnu`. Conclude with `hmp (mono_mem _ _ _ _ k (Φ.t_mem y k).1 hk)`.

Use `haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1`. Take `⟨R, _, _, _, _, φ, hker, hloc⟩` from `GlobalTheory.exists_complete_discreteValuationRing_ker_eq p hpm`. Apply `hmp` to reduce the goal to its premises. Rewrite using `[← hker, RingHom.mem_ker]`. Conclude with `map_mono_eq_zero Φ N₁ hN hE y nu hnu R φ fun a ha => by`.

Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `hJp (Ideal.mem_map_of_mem _ ha)`.
-/
theorem mono_mem_radical : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type)
    [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → ∀ (y : Φ.Y)
    (nu : Fin s → Φ.X y), nu ≠ 0 → mono W (Φ.t y) (Φ.δ y) nu ∈ ((IsLocalRing.maximalIdeal A).map (Φ.ev y)).radical := by
  intro O _ bar q s W A _ _ Φ N₁ hN hE y nu hnu
  by_contra hno
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf] at hno
  push_neg at hno
  obtain ⟨p, ⟨hJp, hp⟩, hmp⟩ := hno
  have hs : ∀ k a b, Φ.δ y k a b = Φ.δ y k b a := fun k => (Φ.bal y k).1
  by_cases hpm : p = IsLocalRing.maximalIdeal (Φ.V y)
  · subst hpm
    obtain ⟨k, hk⟩ := exists_qW_pos Φ.posW (Φ.δ y) hs (Φ.nonneg y) (Φ.pos y) hnu
    exact hmp (mono_mem _ _ _ _ k (Φ.t_mem y k).1 hk)
  · haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
    obtain ⟨R, _, _, _, _, φ, hker, hloc⟩ := GlobalTheory.exists_complete_discreteValuationRing_ker_eq p hpm
    apply hmp
    rw [← hker, RingHom.mem_ker]
    exact map_mono_eq_zero Φ N₁ hN hE y nu hnu R φ fun a ha => by
      rw [← RingHom.mem_ker, hker]
      exact hJp (Ideal.mem_map_of_mem _ ha)

end GlobalTheory.Poinc.RadQ
