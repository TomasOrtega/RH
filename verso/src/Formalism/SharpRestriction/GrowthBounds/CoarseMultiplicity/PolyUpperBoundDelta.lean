import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultiplicityAtIdentity
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Establish `h1 : 0 ≤ 15 - 15 / 4 * de - 17 * ε` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg hε h1]`.
-/
theorem poly_upper_bound_delta {de ε : ℝ} (hε : 0 ≤ ε) (h40 : 40 * ε ≤ de) (h6 : de < 1 / 6) :
    (1 - de / 2) * (1 - de / 4) ≤ (1 - de / 2 + 17 * ε) * (1 - de / 4 - ε) - ε := by
  have h1 : 0 ≤ 15 - 15 / 4 * de - 17 * ε := by linarith
  nlinarith [mul_nonneg hε h1]

/- English proof (translation)
Establish `h1 : 0 ≤ 5 / 4 - 11 / 8 * de` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h0) h0]`.
-/
theorem poly_lower_bound_delta {de : ℝ} (h0 : 0 ≤ de) (h6 : de < 1 / 6) : 1 ≤ (1 + 2 * de) * ((1 - de / 2) * (1 - de / 4)) := by
  have h1 : 0 ≤ 5 / 4 - 11 / 8 * de := by linarith
  nlinarith [mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h0) h0]

/- English proof (translation)
Establish `hAP : b' * (1 - d / 2 + 17 * ε) < A * P`. Establish `a : b' * be ≤ b' * (d / 2 - 18 * ε)` using `mul_le_mul_of_nonneg_left hbe hb.le`. Establish `e : b' * (1 - d / 2 + 17 * ε) = b' - b' * (d / 2 - 18 * ε) - ε * b'` using `by ring`. Establish `e' : b' * (1 - be) = b' - b' * be` using `by ring`. Rewrite using `[e]`.

Rewrite `hg` using `[e']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu0 : 0 ≤ 1 - d / 2 + 17 * ε` using `by linarith`. Establish `hv0 : 0 < 1 - d / 4 - ε` using `by linarith`. Establish `hpoly : 1 ≤ (1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε)`.

Establish `a1` using `poly_upper_bound_delta hε0 h40 hd6`. Establish `a2` using `poly_lower_bound_delta hd0 hd6`. Establish `: (1 + 2 * d) * ((1 - d / 2) * (1 - d / 4)) ≤ (1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε)` using `mul_le_mul_of_nonneg_left a1 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htlt : t < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε)`.

Establish `a1 : b' * 1 ≤ b' * ((1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε))` using `mul_le_mul_of_nonneg_left hpoly hb.le`. Establish `a2 : t * (1 + 2 * d) < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) * (1 + 2 * d)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `lt_of_mul_lt_mul_right a2 (by linarith)`. Establish `hPc : P * c < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε))`.

Establish `e : b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) = b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε)) - ε * b'` using `by ring`. Rewrite `htlt` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAP0 : 0 ≤ A * P` using `le_trans (mul_nonneg hb.le hu0) hAP.le`. Establish `hfin : P * (c + La * A / k) ≤ P * (A * (1 - d / 4))`.

Establish `a1 : P * (La * A / k) = La / k * (A * P)` using `by ring`. Establish `a2 : La / k * (A * P) ≤ ε * (A * P)` using `mul_le_mul_of_nonneg_right hLk hAP0`. Establish `a3 : b' * (1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) ≤ A * P * (1 - d / 4 - ε)` using `mul_le_mul_of_nonneg_right hAP.le hv0.le`. Establish `e2 : A * P * (1 - d / 4 - ε) + ε * (A * P) = P * (A * (1 - d / 4))` using `by ring`. Establish `e3 : b' * (1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) = b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε))` using `by ring`.

Rewrite using `[mul_add, a1, ← e2]`. Rewrite `a3` using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left hfin hP0`.
-/
theorem upper_real_bound {b' d ε t P c A La k g be : ℝ} (hb : 0 < b') (hP0 : 0 < P) (hε0 : 0 ≤ ε) (h40 : 40 * ε ≤ d)
    (hd0 : 0 ≤ d) (hd6 : d < 1 / 6) (htb : t * (1 + 2 * d) < b') (hcap : P * c ≤ t + ε * b')
    (hg : b' * (1 - be) ≤ g) (hbe : be ≤ d / 2 - 18 * ε) (hkP : k * P ≤ ε * b') (hlow : g - k * P < A * P)
    (hLk : La / k ≤ ε) : c + La * A / k ≤ A * (1 - d / 4) := by
  have hAP : b' * (1 - d / 2 + 17 * ε) < A * P := by
    have a : b' * be ≤ b' * (d / 2 - 18 * ε) := mul_le_mul_of_nonneg_left hbe hb.le
    have e : b' * (1 - d / 2 + 17 * ε) = b' - b' * (d / 2 - 18 * ε) - ε * b' := by ring
    have e' : b' * (1 - be) = b' - b' * be := by ring
    rw [e]
    rw [e'] at hg
    linarith
  have hu0 : 0 ≤ 1 - d / 2 + 17 * ε := by linarith
  have hv0 : 0 < 1 - d / 4 - ε := by linarith
  have hpoly : 1 ≤ (1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) := by
    have a1 := poly_upper_bound_delta hε0 h40 hd6
    have a2 := poly_lower_bound_delta hd0 hd6
    have : (1 + 2 * d) * ((1 - d / 2) * (1 - d / 4)) ≤
        (1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) :=
      mul_le_mul_of_nonneg_left a1 (by linarith)
    linarith
  have htlt : t < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) := by
    have a1 : b' * 1 ≤ b' * ((1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε)) :=
      mul_le_mul_of_nonneg_left hpoly hb.le
    have a2 : t * (1 + 2 * d) < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) * (1 + 2 * d) := by
      calc t * (1 + 2 * d) < b' := htb
        _ = b' * 1 := (mul_one _).symm
        _ ≤ b' * ((1 + 2 * d) * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε)) := a1
        _ = b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) * (1 + 2 * d) := by ring
    exact lt_of_mul_lt_mul_right a2 (by linarith)
  have hPc : P * c < b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε)) := by
    have e : b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) - ε) =
        b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε)) - ε * b' := by ring
    rw [e] at htlt
    linarith
  have hAP0 : 0 ≤ A * P := le_trans (mul_nonneg hb.le hu0) hAP.le
  have hfin : P * (c + La * A / k) ≤ P * (A * (1 - d / 4)) := by
    have a1 : P * (La * A / k) = La / k * (A * P) := by ring
    have a2 : La / k * (A * P) ≤ ε * (A * P) := mul_le_mul_of_nonneg_right hLk hAP0
    have a3 : b' * (1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) ≤ A * P * (1 - d / 4 - ε) :=
      mul_le_mul_of_nonneg_right hAP.le hv0.le
    have e2 : A * P * (1 - d / 4 - ε) + ε * (A * P) = P * (A * (1 - d / 4)) := by ring
    have e3 : b' * (1 - d / 2 + 17 * ε) * (1 - d / 4 - ε) = b' * ((1 - d / 2 + 17 * ε) * (1 - d / 4 - ε)) := by ring
    rw [mul_add, a1, ← e2]
    rw [e3] at a3
    linarith
  exact le_of_mul_le_mul_left hfin hP0

variable {s r : ℕ} {p : ℕ} {S : SegData s} {b' de be aS Q : ℝ}

/- English proof (translation)
Establish `hp5` using `H.p0`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Use `set x : ℝ := 1 / (p : ℝ) with hx`. Establish `hx0 : 0 ≤ x` using `by positivity`. Establish `hx5 : x ≤ 1 / 5`.

Rewrite using `[hx]`. Conclude with `one_div_le_one_div_of_le (by norm_num) hp5`. Establish `hx1 : x < 1` using `by linarith`. Establish `e1 : ∀ i : Fin s, 1 / (p : ℝ) ^ (S.G - S.d i) = x ^ (S.G - S.d i)` using `fun i => by rw [hx, one_div_pow]`. Establish `hinj : Set.InjOn (fun i : Fin s => S.G - S.d i) (Finset.univ : Finset (Fin s))`.

Introduce `i _ i' _ h`. Establish `a1` using `(H.dlt i).2`. Establish `a2` using `(H.dlt i').2`. Establish `: S.d i = S.d i'`. Simplify using `only at h`.

Use linear arithmetic over natural numbers and integers. Conclude with `H.dmono.injective this`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => pow_nonneg hx0 n` and prove the remaining obligations. Introduce `n hn`.

Take `⟨i, _, rfl⟩` from `Finset.mem_image.1 hn`. Establish `a1` using `(H.dlt i).1`. Establish `a2` using `(H.dlt i).2`. Conclude with `Finset.mem_Ico.2 ⟨by omega, by omega⟩`. Use `_ ≤ x ^ 1 / (1 - x) := geom_sum_Ico_le_of_lt_one hx0 hx1`.

Use `_ ≤ 5 / 4 / (p : ℝ) := by`. Rewrite using `[pow_one, div_le_iff₀ (by linarith)]`. Establish `: 5 / 4 / (p : ℝ) = 5 / 4 * x` using `by rw [hx]; ring`. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem SegHyp.geo (H : SegHyp p S b' de be aS Q) : ∑ i : Fin s, 1 / (p : ℝ) ^ (S.G - S.d i) ≤ 5 / 4 / (p : ℝ) := by
  classical
  have hp5 := H.p0
  have hp0 : (0 : ℝ) < p := by linarith
  set x : ℝ := 1 / (p : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx5 : x ≤ 1 / 5 := by
    rw [hx]
    exact one_div_le_one_div_of_le (by norm_num) hp5
  have hx1 : x < 1 := by linarith
  have e1 : ∀ i : Fin s, 1 / (p : ℝ) ^ (S.G - S.d i) = x ^ (S.G - S.d i) := fun i => by rw [hx, one_div_pow]
  have hinj : Set.InjOn (fun i : Fin s => S.G - S.d i) (Finset.univ : Finset (Fin s)) := by
    intro i _ i' _ h
    have a1 := (H.dlt i).2
    have a2 := (H.dlt i').2
    have : S.d i = S.d i' := by
      simp only at h
      omega
    exact H.dmono.injective this
  calc ∑ i : Fin s, 1 / (p : ℝ) ^ (S.G - S.d i) = ∑ i : Fin s, x ^ (S.G - S.d i) := Finset.sum_congr rfl fun i _ => e1 i
    _ = ∑ n ∈ (Finset.univ : Finset (Fin s)).image (fun i => S.G - S.d i), x ^ n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Ico 1 S.G, x ^ n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => pow_nonneg hx0 n
        intro n hn
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hn
        have a1 := (H.dlt i).1
        have a2 := (H.dlt i).2
        exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
    _ ≤ x ^ 1 / (1 - x) := geom_sum_Ico_le_of_lt_one hx0 hx1
    _ ≤ 5 / 4 / (p : ℝ) := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        have : 5 / 4 / (p : ℝ) = 5 / 4 * x := by rw [hx]; ring
        rw [this]
        nlinarith

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc}

/- English proof (translation)
Use `St.LaK` as an intermediate fact. Unfold `eps`. Combine the linear relations using `[this, (by ring : 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k)]`.
-/
theorem Std.forty_epsilon_le_delta (St : Std C0 Cde CE1 CE2 1 X) : 40 * eps X C0 ≤ X.de C0 Cde := by
  have := St.LaK
  unfold eps
  linarith [this, (by ring : 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k)]

/- English proof (translation)
Use `St.beLe` as an intermediate fact. Unfold `eps`. Combine the linear relations using `[this, (by ring : 18 * (X.N1 * X.La C0 / X.k) = 18 * X.N1 * X.La C0 / X.k)]`.
-/
theorem Std.be18 (St : Std C0 Cde CE1 CE2 1 X) :
    _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0 ≤ X.de C0 Cde / 2 - 18 * eps X C0 := by
  have := St.beLe
  unfold eps
  linarith [this, (by ring : 18 * (X.N1 * X.La C0 / X.k) = 18 * X.N1 * X.La C0 / X.k)]

/- English proof (translation)
Establish `hk0 : 0 < X.k` using `by linarith [St.k5]`. Establish `hLa0 : 0 ≤ X.La C0` using `by linarith [St.La1]`. Unfold `eps`. Use `div_le_div_of_nonneg_right ?_ hk0.le` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ X.N1` using `by exact_mod_cast St.N1pos`.

Use `mul_le_mul_of_nonneg_right h1 hLa0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Std.Laeps (St : Std C0 Cde CE1 CE2 1 X) : X.La C0 / X.k ≤ eps X C0 := by
  have hk0 : 0 < X.k := by linarith [St.k5]
  have hLa0 : 0 ≤ X.La C0 := by linarith [St.La1]
  unfold eps
  refine div_le_div_of_nonneg_right ?_ hk0.le
  have h1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have := mul_le_mul_of_nonneg_right h1 hLa0
  linarith

/- English proof (translation)
Establish `hk5` using `St.k5`. Establish `hk0 : 0 < X.k` using `by linarith`. Establish `hp0 : (0 : ℝ) < X.p` using `by linarith [St.p1]`. Establish `hpk : X.k ^ 2 ≤ (X.p : ℝ)`. Establish `h1` using `St.pk`.

Establish `h2` using `St.Y1`. Establish `h3 : (1 : ℝ) ≤ X.Y ^ 2` using `one_le_pow₀ h2`. Establish `: X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2` using `mul_le_mul_of_nonneg_left h3 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : 2 / (X.p : ℝ) ≤ 1 / X.k`.

Rewrite using `[div_le_div_iff₀ hp0 hk0]`. Establish `: 5 * X.k ≤ X.k ^ 2` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 2 * (X.b' / X.p) = 2 / (X.p : ℝ) * X.b'` using `by ring`. Rewrite using `[h2]`.

Conclude with `mul_le_mul_of_nonneg_right (h1.trans St.eps_ge) St.bpos.le`.
-/
theorem Std.twoP (St : Std C0 Cde CE1 CE2 1 X) : 2 * (X.b' / X.p) ≤ eps X C0 * X.b' := by
  have hk5 := St.k5
  have hk0 : 0 < X.k := by linarith
  have hp0 : (0 : ℝ) < X.p := by linarith [St.p1]
  have hpk : X.k ^ 2 ≤ (X.p : ℝ) := by
    have h1 := St.pk
    have h2 := St.Y1
    have h3 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ h2
    have : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h1 : 2 / (X.p : ℝ) ≤ 1 / X.k := by
    rw [div_le_div_iff₀ hp0 hk0]
    have : 5 * X.k ≤ X.k ^ 2 := by nlinarith
    linarith
  have h2 : 2 * (X.b' / X.p) = 2 / (X.p : ℝ) * X.b' := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right (h1.trans St.eps_ge) St.bpos.le

/- English proof (translation)
Establish `H` using `segHyp_of St j`. Establish `hb` using `St.bpos`. Take `⟨hP0, hpd0, hQj, hQ, hPQ⟩` from `St.levels j i`. Establish `hcb` using `coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i) (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2`. Establish `hcap` using `H.Pcap b i`.

Establish `hPe : (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) = ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ)` using `by push_cast; rfl`. Rewrite `hcap` using `[hPe]`. Establish `hpd : (0 : ℝ) < (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i)` using `hpd0`. Establish `hns : ¬ (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) < ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b'` using `fun hh => absurd ((H.sig i).2 hh) (not_lt.2 hi)`. Establish `hge` using `not_lt.1 hns`.

Establish `hab0 : 0 ≤ ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b'` using `div_nonneg (Nat.cast_nonneg _) hb.le`. Establish `hband` using `H.band _ (H.dodd i)`. Establish `hde0` using `H.de0`. Establish `hgt : ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * (1 + 2 * X.de C0 Cde) < (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i)`. Assume the negation of the conclusion as `hcon`.

Use `hband ⟨?_, not_lt.1 hcon⟩` and prove the remaining obligations. Establish `: ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * (1 - 2 * X.de C0 Cde) ≤ ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * 1` using `mul_le_mul_of_nonneg_left (by linarith) hab0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htb : ((X.seg C0 CE1 CE2 j).a : ℝ) / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) * (1 + 2 * X.de C0 Cde) < X.b'`. Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ hpd]`.

Rewrite `hgt` using `[div_mul_eq_mul_div, div_lt_iff₀ hb]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ)` using `(H.bT i).1`. Establish `hkP : ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ eps X C0 * X.b'`. Establish `h5` using `St.kQeps le_rfl`.

Establish `: ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ X.k * X.Q` using `mul_le_mul_of_nonneg_left (hPQ.trans hQ) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcap'` using `hcap.trans (add_le_add_right St.twoP _)`. Conclude with `upper_real_bound hb hP0 St.eps0 St.forty_epsilon_le_delta hde0 St.de6 htb hcap' hbT St.be18 hkP hcb.2 St.Laeps`.
-/
theorem kept_upper_level_bound (St : Std C0 Cde CE1 CE2 1 X) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hdig : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (i : Fin (segS X.TT j))
    (hi : (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ)) :
    (cap X.p (X.seg C0 CE1 CE2 j) b i : ℝ) +
        (X.seg C0 CE1 CE2 j).La * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) / ((X.m : ℝ) + 1) ≤
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) := by
  have H := segHyp_of St j
  have hb := St.bpos
  obtain ⟨hP0, hpd0, hQj, hQ, hPQ⟩ := St.levels j i
  have hcb := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
    (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2
  have hcap := H.Pcap b i
  have hPe : (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) =
      ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := by
    push_cast; rfl
  rw [hPe] at hcap
  have hpd : (0 : ℝ) < (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) := hpd0
  have hns : ¬ (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) < ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' := fun hh =>
    absurd ((H.sig i).2 hh) (not_lt.2 hi)
  have hge := not_lt.1 hns
  have hab0 : 0 ≤ ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' := div_nonneg (Nat.cast_nonneg _) hb.le
  have hband := H.band _ (H.dodd i)
  have hde0 := H.de0
  have hgt : ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * (1 + 2 * X.de C0 Cde) <
      (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) := by
    by_contra hcon
    refine hband ⟨?_, not_lt.1 hcon⟩
    have : ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * (1 - 2 * X.de C0 Cde) ≤ ((X.seg C0 CE1 CE2 j).a : ℝ) / X.b' * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hab0
    linarith
  have htb : ((X.seg C0 CE1 CE2 j).a : ℝ) / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).d i) * (1 + 2 * X.de C0 Cde) < X.b' := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpd]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hb] at hgt
    linarith
  have hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (H.bT i).1
  have hkP : ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ eps X C0 * X.b' := by
    have h5 := St.kQeps le_rfl
    have : ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤ X.k * X.Q :=
      mul_le_mul_of_nonneg_left (hPQ.trans hQ) (by positivity)
    linarith
  have hcap' := hcap.trans (add_le_add_right St.twoP _)
  exact upper_real_bound hb hP0 St.eps0 St.forty_epsilon_le_delta hde0 St.de6 htb hcap' hbT St.be18 hkP hcb.2 St.Laeps

/- English proof (translation)
Establish `H` using `segHyp_of St j`. Establish `hp5` using `H.p0`. Establish `hp0 : (0 : ℝ) < X.p` using `by linarith`. Establish `hb` using `St.bpos`. Establish `hk0 : 0 < X.k` using `by linarith [St.k5]`.

Establish `hLa0 : 0 ≤ X.La C0` using `by linarith [St.La1]`. Establish `ha0 : (0 : ℝ) ≤ (X.a : ℝ)` using `Nat.cast_nonneg _`. Establish `hgeo` using `H.geo`. Establish `hcapS` using `cap_le X.p (X.seg C0 CE1 CE2 j) b (segS X.TT j)`. Establish `hA0` using `base_exponent_le_a X.p (by have := St.p5; omega) (X.seg C0 CE1 CE2 j) H.errorNonneg`.

Establish `hA0' : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2`. Use `hA0.trans ?_` and prove the remaining obligations. Use `show (X.a : ℝ) / (X.p : ℝ) ^ (X.seg C0 CE1 CE2 j).G ≤ _`. Conclude with `div_le_div_of_nonneg_left ha0 (by positivity) (pow_le_pow_right₀ (by linarith) H.G2)`. Establish `hsumA : (∑ i : Fin (segS X.TT j), if (i : ℕ) < segS X.TT j then (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) else 0) ≤ 3 * X.b' / X.p`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos i.2]`. Establish `a1` using `coarseA_mul X.p (X.seg C0 CE1 CE2 j) b i`. Establish `a2` using `H.top_degree_le_two_b i`.

Establish `a3 : (0 : ℝ) < (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i)` using `by positivity`. Rewrite using `[mul_one_div, le_div_iff₀ a3]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 2 * X.b' * ∑ i : Fin (segS X.TT j), 1 / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) := by rw [Finset.mul_sum]`. Use `_ ≤ 2 * X.b' * (5 / 4 / (X.p : ℝ)) := mul_le_mul_of_nonneg_left hgeo (by linarith)`.

Use `_ ≤ 3 * X.b' / X.p := by`. Establish `: 2 * X.b' * (5 / 4 / (X.p : ℝ)) = 5 / 2 * X.b' / X.p` using `by ring`. Rewrite using `[this]`. Conclude with `div_le_div_of_nonneg_right (by linarith) hp0.le`. Establish `hsumP : (∑ i : Fin (segS X.TT j), 2 * ((X.seg C0 CE1 CE2 j).a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)) ≤ 4 * (X.a : ℝ) / X.p`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `SegData.P`. Use `push_cast`.

Rewrite using `[mul_one_div]`. Both sides reduce to the same expression. Use `_ ≤ 2 * (X.a : ℝ) * (5 / 4 / (X.p : ℝ)) := mul_le_mul_of_nonneg_left hgeo (by linarith)`. Use `_ ≤ 4 * (X.a : ℝ) / X.p := by`. Establish `: 2 * (X.a : ℝ) * (5 / 4 / (X.p : ℝ)) = 5 / 2 * (X.a : ℝ) / X.p` using `by ring`.

Rewrite using `[this]`. Conclude with `div_le_div_of_nonneg_right (by linarith) hp0.le`. Establish `hbP : ((X.seg C0 CE1 CE2 j).bPlus : ℝ) ≤ 2 * X.b'`. Establish `a1` using `H.bP`. Establish `a2` using `H.beLe`.

Establish `a3` using `H.de6`. Establish `a4 : X.b' * (1 + _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ X.b' * 2` using `mul_le_mul_of_nonneg_left (by linarith) hb.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcoef : 0 ≤ X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2` using `by positivity`. Unfold `Oplus localOrderCap`.

Establish `a1 : ((X.seg C0 CE1 CE2 j).La / ((X.m : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) * (∑ i : Fin (segS X.TT j), 2 * ((X.seg C0 CE1 CE2 j).a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)) ≤ (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p)` using `mul_le_mul_of_nonneg_left hsumP hcoef`. Establish `a2 : (X.seg C0 CE1 CE2 j).La * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1) ≤ 2 * X.La C0 * X.b' / X.k` using `by show X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k ≤ _`. Use `div_le_div_of_nonneg_right ?_ hk0.le` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left hbP hLa0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem extra_order_le_maximal (St : Std C0 Cde CE1 CE2 1 X) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Oplus X.p X.m (X.seg C0 CE1 CE2 j) b ≤ localOrderCap C0 X := by
  have H := segHyp_of St j
  have hp5 := H.p0
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hb := St.bpos
  have hk0 : 0 < X.k := by linarith [St.k5]
  have hLa0 : 0 ≤ X.La C0 := by linarith [St.La1]
  have ha0 : (0 : ℝ) ≤ (X.a : ℝ) := Nat.cast_nonneg _
  have hgeo := H.geo
  have hcapS := cap_le X.p (X.seg C0 CE1 CE2 j) b (segS X.TT j)
  have hA0 := base_exponent_le_a X.p (by have := St.p5; omega) (X.seg C0 CE1 CE2 j) H.errorNonneg
  have hA0' : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 := by
    refine hA0.trans ?_
    show (X.a : ℝ) / (X.p : ℝ) ^ (X.seg C0 CE1 CE2 j).G ≤ _
    exact div_le_div_of_nonneg_left ha0 (by positivity) (pow_le_pow_right₀ (by linarith) H.G2)
  have hsumA : (∑ i : Fin (segS X.TT j), if (i : ℕ) < segS X.TT j then
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) else 0) ≤ 3 * X.b' / X.p := by
    calc (∑ i : Fin (segS X.TT j), if (i : ℕ) < segS X.TT j then
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) else 0)
        ≤ ∑ i : Fin (segS X.TT j), 2 * X.b' *
            (1 / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [if_pos i.2]
          have a1 := coarseA_mul X.p (X.seg C0 CE1 CE2 j) b i
          have a2 := H.top_degree_le_two_b i
          have a3 : (0 : ℝ) < (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) := by positivity
          rw [mul_one_div, le_div_iff₀ a3]
          linarith
      _ = 2 * X.b' * ∑ i : Fin (segS X.TT j),
            1 / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) := by rw [Finset.mul_sum]
      _ ≤ 2 * X.b' * (5 / 4 / (X.p : ℝ)) := mul_le_mul_of_nonneg_left hgeo (by linarith)
      _ ≤ 3 * X.b' / X.p := by
          have : 2 * X.b' * (5 / 4 / (X.p : ℝ)) = 5 / 2 * X.b' / X.p := by ring
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hsumP : (∑ i : Fin (segS X.TT j), 2 * ((X.seg C0 CE1 CE2 j).a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)) ≤
      4 * (X.a : ℝ) / X.p := by
    calc (∑ i : Fin (segS X.TT j), 2 * ((X.seg C0 CE1 CE2 j).a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ))
        = 2 * (X.a : ℝ) * ∑ i : Fin (segS X.TT j),
            1 / (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold SegData.P
          push_cast
          rw [mul_one_div]
          rfl
      _ ≤ 2 * (X.a : ℝ) * (5 / 4 / (X.p : ℝ)) := mul_le_mul_of_nonneg_left hgeo (by linarith)
      _ ≤ 4 * (X.a : ℝ) / X.p := by
          have : 2 * (X.a : ℝ) * (5 / 4 / (X.p : ℝ)) = 5 / 2 * (X.a : ℝ) / X.p := by ring
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hbP : ((X.seg C0 CE1 CE2 j).bPlus : ℝ) ≤ 2 * X.b' := by
    have a1 := H.bP
    have a2 := H.beLe
    have a3 := H.de6
    have a4 : X.b' * (1 + _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ X.b' * 2 := mul_le_mul_of_nonneg_left (by linarith) hb.le
    linarith
  have hcoef : 0 ≤ X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2 := by positivity
  unfold Oplus localOrderCap
  have a1 : ((X.seg C0 CE1 CE2 j).La / ((X.m : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) *
      (∑ i : Fin (segS X.TT j), 2 * ((X.seg C0 CE1 CE2 j).a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)) ≤
      (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p) :=
    mul_le_mul_of_nonneg_left hsumP hcoef
  have a2 : (X.seg C0 CE1 CE2 j).La * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1) ≤
      2 * X.La C0 * X.b' / X.k := by
    show X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k ≤ _
    refine div_le_div_of_nonneg_right ?_ hk0.le
    have := mul_le_mul_of_nonneg_left hbP hLa0
    linarith
  linarith

/- English proof (translation)
Establish `hp5 : (5 : ℝ) ≤ X.p` using `by exact_mod_cast St.p5`. Establish `hp0 : (0 : ℝ) < X.p` using `by linarith`. Establish `hb` using `St.bpos`. Establish `hk0 : 0 < X.k` using `by linarith [St.k5]`. Establish `hLa0 : 0 ≤ X.La C0` using `by linarith [St.La1]`.

Establish `ha0 : (0 : ℝ) ≤ (X.a : ℝ)` using `Nat.cast_nonneg _`. Establish `hbp : X.b' ≤ (X.a : ℝ) / X.p`. Use `St.pab` as an intermediate fact. Rewrite `this` using `[lt_div_iff₀ hb]`. Rewrite using `[le_div_iff₀ hp0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLak : X.La C0 / X.k ≤ 1 / 4`. Rewrite using `[div_le_iff₀ hk0]`. Establish `a1` using `St.LaN`. Establish `a2` using `mul_le_mul_of_nonneg_right St.N2 hLa0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2` using `by nlinarith`. Establish `b1 : (X.a : ℝ) / (X.p : ℝ) ^ 2 ≤ (X.a : ℝ) / 25` using `div_le_div_of_nonneg_left ha0 (by norm_num) hp25`. Establish `b0 : (X.a : ℝ) / X.p ≤ (X.a : ℝ) / 5` using `div_le_div_of_nonneg_left ha0 (by norm_num) hp5`. Establish `b2 : 3 * X.b' / X.p ≤ 3 * (X.a : ℝ) / 25`.

Establish `c0 : X.b' ≤ (X.a : ℝ) / 5` using `hbp.trans b0`. Establish `c1 : 3 * X.b' / X.p ≤ 3 * X.b' / 5` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) hp5`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b3 : 4 / (X.p : ℝ) ^ 2 ≤ 4 / 25` using `div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp25`. Establish `b4 : (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p) ≤ (1 / 4 + 4 / 25) * (4 * ((X.a : ℝ) / 5))`.

Establish `c1 : 4 * (X.a : ℝ) / X.p = 4 * ((X.a : ℝ) / X.p)` using `by ring`. Rewrite using `[c1]`. Conclude with `mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)`. Establish `b5 : 2 * X.La C0 * X.b' / X.k ≤ 2 * (1 / 4) * ((X.a : ℝ) / 5)`. Establish `c1 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 / X.k) * X.b'` using `by ring`.

Rewrite using `[c1]`. Conclude with `mul_le_mul (by linarith) (hbp.trans b0) hb.le (by norm_num)`. Unfold `localOrderCap`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem maximal_order_le_a (St : Std C0 Cde CE1 CE2 1 X) : localOrderCap C0 X ≤ (X.a : ℝ) := by
  have hp5 : (5 : ℝ) ≤ X.p := by exact_mod_cast St.p5
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hb := St.bpos
  have hk0 : 0 < X.k := by linarith [St.k5]
  have hLa0 : 0 ≤ X.La C0 := by linarith [St.La1]
  have ha0 : (0 : ℝ) ≤ (X.a : ℝ) := Nat.cast_nonneg _
  have hbp : X.b' ≤ (X.a : ℝ) / X.p := by
    have := St.pab
    rw [lt_div_iff₀ hb] at this
    rw [le_div_iff₀ hp0]
    linarith
  have hLak : X.La C0 / X.k ≤ 1 / 4 := by
    rw [div_le_iff₀ hk0]
    have a1 := St.LaN
    have a2 := mul_le_mul_of_nonneg_right St.N2 hLa0
    linarith
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by nlinarith
  have b1 : (X.a : ℝ) / (X.p : ℝ) ^ 2 ≤ (X.a : ℝ) / 25 := div_le_div_of_nonneg_left ha0 (by norm_num) hp25
  have b0 : (X.a : ℝ) / X.p ≤ (X.a : ℝ) / 5 := div_le_div_of_nonneg_left ha0 (by norm_num) hp5
  have b2 : 3 * X.b' / X.p ≤ 3 * (X.a : ℝ) / 25 := by
    have c0 : X.b' ≤ (X.a : ℝ) / 5 := hbp.trans b0
    have c1 : 3 * X.b' / X.p ≤ 3 * X.b' / 5 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hp5
    linarith
  have b3 : 4 / (X.p : ℝ) ^ 2 ≤ 4 / 25 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp25
  have b4 : (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p) ≤ (1 / 4 + 4 / 25) * (4 * ((X.a : ℝ) / 5)) := by
    have c1 : 4 * (X.a : ℝ) / X.p = 4 * ((X.a : ℝ) / X.p) := by ring
    rw [c1]
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have b5 : 2 * X.La C0 * X.b' / X.k ≤ 2 * (1 / 4) * ((X.a : ℝ) / 5) := by
    have c1 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 / X.k) * X.b' := by ring
    rw [c1]
    exact mul_le_mul (by linarith) (hbp.trans b0) hb.le (by norm_num)
  unfold localOrderCap
  linarith

/- English proof (translation)
Take `⟨hdig, hU, hSt, hX⟩` from `hK`. Use `⟨hdig, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Take `⟨h1, h2, h3, h4⟩` from `hU i hi`. Use `⟨h1, ?_, h3, h4⟩` and prove the remaining obligations.

Rewrite using `[add_zero]`. Conclude with `h2.trans (kept_upper_level_bound St j b hdig i hi)`. Introduce `i hi`. Take `⟨h1, h2, h3, _, h5⟩` from `hSt i hi`. Use `⟨h1, h2, h3, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_zero]`. Conclude with `h5`. Establish `hoO : (b.oPlus : ℝ) ≤ localOrderCap C0 X` using `hX.trans (extra_order_le_maximal St j b)`. Use `⟨?_, by rw [add_zero]; exact hoO⟩` and prove the remaining obligations. Establish `haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ)` using `(St.winA _ (next_mem X.TT j).1).1`.

Conclude with `hoO.trans ((maximal_order_le_a St).trans haP)` after adjusting the coercions.
-/
theorem keptBL_of_std (St : Std C0 Cde CE1 CE2 1 X) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hK : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) : BLk C0 Cde CE1 CE2 X 0 j b := by
  obtain ⟨hdig, hU, hSt, hX⟩ := hK
  refine ⟨hdig, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hU i hi
    refine ⟨h1, ?_, h3, h4⟩
    rw [add_zero]
    exact h2.trans (kept_upper_level_bound St j b hdig i hi)
  · intro i hi
    obtain ⟨h1, h2, h3, _, h5⟩ := hSt i hi
    refine ⟨h1, h2, h3, ?_⟩
    rw [add_zero]
    exact h5
  · have hoO : (b.oPlus : ℝ) ≤ localOrderCap C0 X := hX.trans (extra_order_le_maximal St j b)
    refine ⟨?_, by rw [add_zero]; exact hoO⟩
    have haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := (St.winA _ (next_mem X.TT j).1).1
    exact_mod_cast hoO.trans ((maximal_order_le_a St).trans haP)

/- English proof (translation)
The claim follows from `TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc j b hK => keptBL_of_std (h.2 X hD hH hc) j b hK) thr_std`.
-/
theorem restKeptBL : RestKeptBL :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc j b hK => keptBL_of_std (h.2 X hD hH hc) j b hK) thr_std

end Formalism.MainNotions.ColumnSystems.Pf
