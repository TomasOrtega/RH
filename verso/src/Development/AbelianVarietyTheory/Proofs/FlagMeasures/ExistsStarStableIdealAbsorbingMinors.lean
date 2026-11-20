import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.Absorb

section Ideals

variable {K : Type} [Field K] [NumberField K]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.DegCnt.ipow, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]`.
-/
theorem _root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat (𝔡 : Ideal (𝓞 K)) (n : ℕ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∃ d ∈ 𝔡 ^ n, (d : K) = x := by
  rw [_root_.GlobalTheory.DegCnt.ipow, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_coeIdeal]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in

/- English proof (translation)
Establish `h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-n) ≠ 0` using `zpow_ne_zero _ (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero])`. Rewrite using `[_root_.GlobalTheory.DegCnt.ipow, _root_.GlobalTheory.DegCnt.ipow, FractionalIdeal.mem_coe, ← inv_inv ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n), ← zpow_neg, FractionalIdeal.mem_inv_iff h0]`. Use `forall₂_congr fun u _ => ?_` and prove the remaining obligations. Rewrite using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]`.
-/
theorem _root_.GlobalTheory.DegCnt.Absorb.mem_ipow_iff {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∀ u ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 (-n),
      x * u ∈ (1 : Submodule (𝓞 K) K) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-n) ≠ 0 :=
    zpow_ne_zero _ (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero])
  rw [_root_.GlobalTheory.DegCnt.ipow, _root_.GlobalTheory.DegCnt.ipow, FractionalIdeal.mem_coe,
    ← inv_inv ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n), ← zpow_neg, FractionalIdeal.mem_inv_iff h0]
  refine forall₂_congr fun u _ => ?_
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]

variable [StarRing K]

def sig (K : Type) [Field K] [StarRing K] : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)

omit [NumberField K] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_sig (x : 𝓞 K) : ((sig K x : 𝓞 K) : K) = star (x : K) := rfl

omit [NumberField K] in

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.mem_one.1 hx`. Conclude with `Submodule.mem_one.2 ⟨sig K y, rfl⟩`.
-/
theorem star_mem_one {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨sig K y, rfl⟩

/- English proof (translation)
Establish `hm : 𝔡.map (sig K : 𝓞 K →+* 𝓞 K) ≤ 𝔡`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Take `⟨y, hy, e⟩` from `hs x hx`. Establish `: y = sig K x` using `by ext; rw [e, coe_sig]`.

Rewrite using `[Ideal.mem_comap]`. Conclude with `this ▸ hy`. Establish `hn : ∀ n : ℕ, ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n`. Introduce `n x hx`. Take `⟨d, hd, rfl⟩` from `(mem_ipow_nat 𝔡 n x).1 hx`.

Use `(mem_ipow_nat 𝔡 n _).2 ⟨sig K d, ?_, rfl⟩` and prove the remaining obligations. Use `Ideal.mem_map_of_mem (sig K : 𝓞 K →+* 𝓞 K) hd` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm n this`. Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`.

Conclude with `hn m`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_ipow_iff h, neg_neg]`. Introduce `u hu`. Use `star_mem_one (hx _ (hn m u hu))` as an intermediate fact.

Rewrite `this` using `[star_mul', star_star]`. Then use the resulting hypothesis.
-/
theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) :
    ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  have hm : 𝔡.map (sig K : 𝓞 K →+* 𝓞 K) ≤ 𝔡 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, e⟩ := hs x hx
    have : y = sig K x := by ext; rw [e, coe_sig]
    rw [Ideal.mem_comap]
    exact this ▸ hy
  have hn : ∀ n : ℕ, ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
    intro n x hx
    obtain ⟨d, hd, rfl⟩ := (mem_ipow_nat 𝔡 n x).1 hx
    refine (mem_ipow_nat 𝔡 n _).2 ⟨sig K d, ?_, rfl⟩
    have := Ideal.mem_map_of_mem (sig K : 𝓞 K →+* 𝓞 K) hd
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hm n this
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact hn m
  · intro x hx
    rw [mem_ipow_iff h, neg_neg] at hx ⊢
    intro u hu
    have := star_mem_one (hx _ (hn m u hu))
    rwa [star_mul', star_star] at this

end Ideals

section Flags

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, rfl⟩` from `hx`. Establish `hc' : (c : ℕ) < a` using `hc`.

Establish `hca : (c : ℕ) < l` using `lt_trans hc' a.isLt`. Use `⟨fun b => if (b : ℕ) = c then 1 else 0, fun b hb => ?_, ?_⟩` and prove the remaining obligations. Establish `: (a : ℕ) ≤ b` using `hb`. Simplify using `only [ite_eq_right_iff]`. Introduce `h`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_single ⟨c, hca⟩]`. Simplify using `only [if_true, one_smul]`. Use `congr 1`. Introduce `b _ hb dsimp only`.

Rewrite using `[if_neg (fun h => hb (Fin.ext h)), zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m, hm, rfl⟩` from `hx`. Take `⟨n, hn, rfl⟩` from `hy`. Conclude with `⟨m + n, fun b hb => by simp [hm b hb, hn b hb], by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul c x _ hx`. Take `⟨m, hm, rfl⟩` from `hx`.

Conclude with `⟨c • m, fun b hb => by simp [hm b hb], by simp [Finset.smul_sum, smul_smul]⟩`.
-/
theorem _root_.GlobalTheory.DegCnt.Absorb.exists_coord (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) {l : ℕ} (hl : l ≤ r + 1) (a : Fin l)
    {y : V} (hy : y ∈ F.Xa a.val) :
    ∃ m : Fin l → K, (∀ b, a ≤ b → m b = 0) ∧ y = ∑ b, m b • F.e (Fin.castLE hl b) := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : (c : ℕ) < a := hc
    have hca : (c : ℕ) < l := lt_trans hc' a.isLt
    refine ⟨fun b => if (b : ℕ) = c then 1 else 0, fun b hb => ?_, ?_⟩
    · have : (a : ℕ) ≤ b := hb
      simp only [ite_eq_right_iff]
      intro h
      omega
    · rw [Finset.sum_eq_single ⟨c, hca⟩]
      · simp only [if_true, one_smul]
        congr 1
      · intro b _ hb
        dsimp only
        rw [if_neg (fun h => hb (Fin.ext h)), zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨n, hn, rfl⟩ := hy
    exact ⟨m + n, fun b hb => by simp [hm b hb, hn b hb],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul c x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨c • m, fun b hb => by simp [hm b hb], by simp [Finset.smul_sum, smul_smul]⟩

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hJ, ih]`.
-/
private theorem fractionalIdeal_zpow_sum_eq_prod (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (s : Finset ℕ)
    (f : ℕ → ℤ) : J ^ (∑ a ∈ s, f a) = ∏ a ∈ s, J ^ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hJ, ih]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases. Rewrite using `[hF.1 b]`. Both sides reduce to the same expression. Rewrite using `[hF.2]`. Simplify using `[_root_.GlobalTheory.DegCnt.ipow]`.
-/
private theorem lead_eq_ipow_of_isFrame (N : _root_.GlobalTheory.DegCnt.NF H r) {F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    {Λ : Submodule (𝓞 K) V} (hF : _root_.GlobalTheory.HermLat.IsFrame F Λ N.aa) (a : Fin (r + 1)) :
    _root_.GlobalTheory.HermLat.lead F Λ a = _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-((r : ℤ) - a)) := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
  · rw [hF.1 b]; rfl
  · rw [hF.2]; simp [_root_.GlobalTheory.DegCnt.ipow]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Establish `h1 : N.𝔡 ≤ N.𝔡.comap (_root_.GlobalTheory.DegCnt.Absorb.sig K : 𝓞 K →+* 𝓞 K)`. Introduce `x hx`. Take `⟨y, hy, hyx⟩` from `N.𝔡_star x hx`. Establish `: (_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) = y` using `by ext; exact hyx.symm`. Rewrite using `[Ideal.mem_comap]`.

Simplify `hy` using `[this]`. Establish `h2` using `(Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ k) hd`. Conclude with `⟨_, h2, rfl⟩`.
-/
private theorem exists_mem_pow_eq_star (N : _root_.GlobalTheory.DegCnt.NF H r) (k : ℕ) {d : 𝓞 K}
    (hd : d ∈ N.𝔡 ^ k) : ∃ d' ∈ N.𝔡 ^ k, (d' : K) = star (d : K) := by
  have h1 : N.𝔡 ≤ N.𝔡.comap (_root_.GlobalTheory.DegCnt.Absorb.sig K : 𝓞 K →+* 𝓞 K) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := N.𝔡_star x hx
    have : (_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) = y := by
      ext; exact hyx.symm
    rw [Ideal.mem_comap]
    simpa [this] using hy
  have h2 := (Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ k) hd
  exact ⟨_, h2, rfl⟩

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`. Rewrite `ht`, the goal using `[_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_iff N.𝔡_ne, neg_neg]`. Introduce `u hu`. Take `⟨d, hd, rfl⟩` from `(_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hu`. Take `⟨d', hd', hdd'⟩` from `exists_mem_pow_eq_star N k hd`.

Establish `h3` using `ht _ ((_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)`. Rewrite `h3` using `[hdd']`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h3`. Use `Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) = star (algebraMap (𝓞 K) K o)` using `rfl`.

Rewrite using `[e1, ho, star_mul, star_star, mul_comm]`.
-/
private theorem star_mem_ipow_neg_of_nonneg (N : _root_.GlobalTheory.DegCnt.NF H r) {n : ℤ}
    (hn : 0 ≤ n) {t : K} (ht : t ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-n)) :
    star t ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-n) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_iff N.𝔡_ne, neg_neg] at ht ⊢
  intro u hu
  obtain ⟨d, hd, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hu
  obtain ⟨d', hd', hdd'⟩ := exists_mem_pow_eq_star N k hd
  have h3 := ht _ ((_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)
  rw [hdd'] at h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 h3
  refine Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩
  have e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) =
      star (algebraMap (𝓞 K) K o) := rfl
  rw [e1, ho, star_mul, star_star, mul_comm]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on generalizing x with`. Consider the case `empty`. Introduce `u hu`. Rewrite `hu` using `[Finset.prod_empty, FractionalIdeal.mem_one_iff]`. Take `⟨o, rfl⟩` from `hu`.

Establish `h0` using `hx (fun _ => 0) (by simp)`. Rewrite `h0` using `[Finset.prod_empty, mul_one]`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `M.smul_mem o h0`. Consider the case `insert i s hi ih`.

Introduce `u hu`. Rewrite `hu` using `[Finset.prod_insert hi]`. Use `FractionalIdeal.mul_induction_on hu ?_ ?_` and prove the remaining obligations. Introduce `p hp q hq`. Rewrite using `[← mul_assoc]`.

Use `ih (x * p) (fun g hg => ?_) q hq` and prove the remaining obligations. Establish `hne : ∀ j ∈ s, j ≠ i` using `fun j hj hji => hi (hji ▸ hj)`. Establish `h1` using `hx (Function.update g i p) (by`. Introduce `j hj`. Break down `Finset.mem_insert.1 hj with rfl | hj` into its components or cases.

Simplify using `using hp`. Rewrite using `[Function.update_of_ne (hne j hj)]`. Conclude with `hg j hj)`. Rewrite `h1` using `[Finset.prod_insert hi, Function.update_self, Finset.prod_congr rfl (fun j hj => Function.update_of_ne (hne j hj) _ _), ← mul_assoc]`. Then use the resulting hypothesis. Introduce `y z hy hz`.

Rewrite using `[mul_add]`. Conclude with `M.add_mem hy hz`.
-/
private theorem mul_mem_of_forall_prod_mem {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K)
    (M : Submodule (𝓞 K) K) (x : K)
    (hx : ∀ g : ι → K, (∀ i ∈ s, g i ∈ I i) → x * ∏ i ∈ s, g i ∈ M) :
    ∀ u ∈ (∏ i ∈ s, I i), x * u ∈ M := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    intro u hu
    rw [Finset.prod_empty, FractionalIdeal.mem_one_iff] at hu
    obtain ⟨o, rfl⟩ := hu
    have h0 := hx (fun _ => 0) (by simp)
    rw [Finset.prod_empty, mul_one] at h0
    rw [mul_comm, ← Algebra.smul_def]
    exact M.smul_mem o h0
  | insert i s hi ih =>
    intro u hu
    rw [Finset.prod_insert hi] at hu
    refine FractionalIdeal.mul_induction_on hu ?_ ?_
    · intro p hp q hq
      rw [← mul_assoc]
      refine ih (x * p) (fun g hg => ?_) q hq
      have hne : ∀ j ∈ s, j ≠ i := fun j hj hji => hi (hji ▸ hj)
      have h1 := hx (Function.update g i p) (by
        intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simpa using hp
        · rw [Function.update_of_ne (hne j hj)]; exact hg j hj)
      rwa [Finset.prod_insert hi, Function.update_self,
        Finset.prod_congr rfl (fun j hj => Function.update_of_ne (hne j hj) _ _), ← mul_assoc] at h1
    · intro y z hy hz
      rw [mul_add]
      exact M.add_mem hy hz

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Establish `hx : ∀ a : Fin l, ∃ m : Fin l → K, (∀ b, a ≤ b → m b = 0) ∧ u a • F.e (Fin.castLE hl a) - ∑ b, m b • F.e (Fin.castLE hl b) ∈ Λ`. Introduce `a`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 (hu a)`. Take `⟨m, hm, rfl⟩` from `_root_.GlobalTheory.DegCnt.Absorb.exists_coord F hl a (by simpa using hz)`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations.

Establish `: u a • F.e (Fin.castLE hl a) = y + ∑ b, m b • F.e (Fin.castLE hl b)` using `hyz.symm`. Rewrite using `[this, add_sub_cancel_right]`. Conclude with `hy`. Use `choose m hm hmΛ using hx`. Use `⟨Matrix.of fun a b => (if a = b then u a else 0) - m a b, ?_, ?_⟩` and prove the remaining obligations.

Establish `hP : (Matrix.of fun a b => (if a = b then u a else 0) - m a b).BlockTriangular OrderDual.toDual`. Introduce `a b hab`. Establish `hab' : a < b` using `hab`. Simplify using `[hab'.ne, hm a b hab'.le]`. Rewrite using `[Matrix.det_of_lowerTriangular _ hP]`.

Conclude with `Finset.prod_congr rfl fun a _ => by simp [hm a a le_rfl]`. Introduce `a`. Use `hmΛ a using 1` and compare the differences between its conclusion and the goal. Simplify using `[sub_smul, Finset.sum_sub_distrib, ite_smul]`.
-/
private theorem exists_triangular_lattice_vectors (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (Λ : Submodule (𝓞 K) V)
    {l : ℕ} (hl : l ≤ r + 1) (u : Fin l → K)
    (hu : ∀ a, u a ∈ _root_.GlobalTheory.HermLat.lead F Λ (Fin.castLE hl a)) :
    ∃ P : Matrix (Fin l) (Fin l) K, P.det = ∏ a, u a ∧
      ∀ a, ∑ b, P a b • F.e (Fin.castLE hl b) ∈ Λ := by
  have hx : ∀ a : Fin l, ∃ m : Fin l → K, (∀ b, a ≤ b → m b = 0) ∧
      u a • F.e (Fin.castLE hl a) - ∑ b, m b • F.e (Fin.castLE hl b) ∈ Λ := by
    intro a
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hu a)
    obtain ⟨m, hm, rfl⟩ := _root_.GlobalTheory.DegCnt.Absorb.exists_coord F hl a (by simpa using hz)
    refine ⟨m, hm, ?_⟩
    have : u a • F.e (Fin.castLE hl a) = y + ∑ b, m b • F.e (Fin.castLE hl b) := hyz.symm
    rw [this, add_sub_cancel_right]
    exact hy
  choose m hm hmΛ using hx
  refine ⟨Matrix.of fun a b => (if a = b then u a else 0) - m a b, ?_, ?_⟩
  · have hP : (Matrix.of fun a b => (if a = b then u a else 0) - m a b).BlockTriangular
        OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      simp [hab'.ne, hm a b hab'.le]
    rw [Matrix.det_of_lowerTriangular _ hP]
    exact Finset.prod_congr rfl fun a _ => by simp [hm a a le_rfl]
  · intro a
    convert hmΛ a using 1
    simp [sub_smul, Finset.sum_sub_distrib, ite_smul]

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
/- English proof (translation)
Use `choose Y hY using fun i j => Submodule.mem_one.1 (hX i j)`. Establish `hXY : X = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of Y)`. Use extensionality with `i j`. Simplify using `[hY]`. Rewrite using `[hXY, ← RingHom.map_det]`.

Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`.
-/
private theorem det_mem_one_of_entries_mem_one {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n K)
    (hX : ∀ i j, X i j ∈ (1 : Submodule (𝓞 K) K)) : X.det ∈ (1 : Submodule (𝓞 K) K) := by
  choose Y hY using fun i j => Submodule.mem_one.1 (hX i j)
  have hXY : X = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of Y) := by
    ext i j; simp [hY]
  rw [hXY, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, _root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.of_apply, map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `[starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hermForm_combinations_eq_gram_mul {l : ℕ} (P Q : Matrix (Fin l) (Fin l) K) (F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
    (hl : l ≤ r + 1) (a c : Fin l) :
    H.B (∑ b, P a b • F.e (Fin.castLE hl b)) (∑ d, Q c d • F'.e (Fin.castLE hl d)) =
      (P * (_root_.Formalism.HermitianLatticeCounting.S6.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl) * (Q.map star).transpose) a c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
    _root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.of_apply, map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  simp [starRingEnd_apply]; ring

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Establish `hd` using `h.1.2`. Rewrite `hx` using `[← hd]`. Conclude with `((_root_.GlobalTheory.HermLat.mem_dual_iff H Λ x).1 hx).2 y hy`.
-/
private theorem hermForm_mem_one_of_isFramed {F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} {Λ : Submodule (𝓞 K) V}
    {I : Fin r → Submodule (𝓞 K) K} (h : _root_.GlobalTheory.HermLat.IsFramed F F' Λ I) {x y : V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  have hd := h.1.2
  rw [← hd] at hx
  exact ((_root_.GlobalTheory.HermLat.mem_dual_iff H Λ x).1 hx).2 y hy

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Take `⟨P, hP, hPΛ⟩` from `exists_triangular_lattice_vectors F Λ hl t ht`. Take `⟨Q, hQ, hQΛ⟩` from `exists_triangular_lattice_vectors F' Λ hl s hs`. Establish `hX` using `det_mem_one_of_entries_mem_one (P * (_root_.Formalism.HermitianLatticeCounting.S6.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl) * (Q.map star).transpose) fun a c => by`. Rewrite using `[← hermForm_combinations_eq_gram_mul]`. Conclude with `hermForm_mem_one_of_isFramed h (hPΛ a) (hQΛ c)`.

Establish `hs' : (Q.map star).det = star Q.det` using `((starRingEnd K).map_det Q).symm`. Rewrite `hX` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs', hP, hQ]`. Conclude with `hX`.
-/
private theorem prod_mul_Dl_mul_star_prod_mem_one {F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} {Λ : Submodule (𝓞 K) V}
    {I : Fin r → Submodule (𝓞 K) K} (h : _root_.GlobalTheory.HermLat.IsFramed F F' Λ I) {l : ℕ}
    (hl : l ≤ r + 1) (t s : Fin l → K)
    (ht : ∀ a, t a ∈ _root_.GlobalTheory.HermLat.lead F Λ (Fin.castLE hl a))
    (hs : ∀ a, s a ∈ _root_.GlobalTheory.HermLat.lead F' Λ (Fin.castLE hl a)) :
    (∏ a, t a) * _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl * star (∏ a, s a) ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨P, hP, hPΛ⟩ := exists_triangular_lattice_vectors F Λ hl t ht
  obtain ⟨Q, hQ, hQΛ⟩ := exists_triangular_lattice_vectors F' Λ hl s hs
  have hX := det_mem_one_of_entries_mem_one
    (P * (_root_.Formalism.HermitianLatticeCounting.S6.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl) * (Q.map star).transpose)
    fun a c => by
      rw [← hermForm_combinations_eq_gram_mul]
      exact hermForm_mem_one_of_isFramed h (hPΛ a) (hQΛ c)
  have hs' : (Q.map star).det = star Q.det := ((starRingEnd K).map_det Q).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs', hP, hQ] at hX
  exact hX

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
/- English proof (translation)
Establish `hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `N.𝔡_ne`. Establish `heq : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) = (∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a))) * ∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a))`. Rewrite using `[← fractionalIdeal_zpow_sum_eq_prod _ hJ, ← zpow_add₀ hJ, Finset.sum_neg_distrib]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hu` using `[heq]`. Establish `hmem : ∀ (a : Fin l) {v : K}, v ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a)) → v ∈ _root_.GlobalTheory.HermLat.lead N.F Λ (Fin.castLE hl a) ∧ star v ∈ _root_.GlobalTheory.HermLat.lead N.F' Λ (Fin.castLE hl a)`. Introduce `a v hv`.

Establish `hv' : v ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-((r : ℤ) - a))` using `hv`. Rewrite using `[lead_eq_ipow_of_isFrame N h.2.1, lead_eq_ipow_of_isFrame N h.2.2, Fin.coe_castLE]`. Use `⟨hv', star_mem_ipow_neg_of_nonneg N ?_ hv'⟩` and prove the remaining obligations. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `FractionalIdeal.mul_induction_on hu ?_ ?_` and prove the remaining obligations. Introduce `p hp q hq`. Rewrite using `[← mul_assoc]`. Use `mul_mem_of_forall_prod_mem _ _ _ _ (fun g hg => ?_) q hq` and prove the remaining obligations. Rewrite using `[mul_right_comm]`.

Use `mul_mem_of_forall_prod_mem _ _ _ _ (fun g' hg' => ?_) p hp` and prove the remaining obligations. Establish `key` using `prod_mul_Dl_mul_star_prod_mem_one h hl (fun a => g' a) (fun a => star (g a)) (fun a => (hmem a (hg' a (Finset.mem_range.2 a.isLt))).1) (fun a => (hmem a (hg a (Finset.mem_range.2 a.isLt))).2)`. Establish `hst` using `map_prod (starRingEnd K) (fun a : Fin l => star (g a)) Finset.univ`. Simplify using `only [starRingEnd_apply, star_star] at hst`. Rewrite `key` using `[hst, Fin.prod_univ_eq_prod_range (fun a => g' a) l, Fin.prod_univ_eq_prod_range (fun a => g a) l]`.

Use `key using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `y z hy hz`. Rewrite using `[mul_add]`. Conclude with `add_mem hy hz`.
-/
private theorem Dl_mul_mem_one_of_mem_ipow (N : _root_.GlobalTheory.DegCnt.NF H r) {Λ : Submodule (𝓞 K) V}
    (h : _root_.GlobalTheory.HermLat.IsFramed N.F N.F' Λ N.aa) {l : ℕ} (hl : l ≤ r + 1) {u : K}
    (hu : u ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)))) :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl * u ∈ (1 : Submodule (𝓞 K) K) := by
  have hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact N.𝔡_ne
  have heq : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) =
      (∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a))) *
        ∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a)) := by
    rw [← fractionalIdeal_zpow_sum_eq_prod _ hJ, ← zpow_add₀ hJ, Finset.sum_neg_distrib]
    congr 1
    ring
  rw [heq] at hu
  have hmem : ∀ (a : Fin l) {v : K}, v ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a)) →
      v ∈ _root_.GlobalTheory.HermLat.lead N.F Λ (Fin.castLE hl a) ∧
        star v ∈ _root_.GlobalTheory.HermLat.lead N.F' Λ (Fin.castLE hl a) := by
    intro a v hv
    have hv' : v ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-((r : ℤ) - a)) := hv
    rw [lead_eq_ipow_of_isFrame N h.2.1, lead_eq_ipow_of_isFrame N h.2.2, Fin.coe_castLE]
    refine ⟨hv', star_mem_ipow_neg_of_nonneg N ?_ hv'⟩
    have := a.isLt
    omega
  refine FractionalIdeal.mul_induction_on hu ?_ ?_
  · intro p hp q hq
    rw [← mul_assoc]
    refine mul_mem_of_forall_prod_mem _ _ _ _ (fun g hg => ?_) q hq
    rw [mul_right_comm]
    refine mul_mem_of_forall_prod_mem _ _ _ _ (fun g' hg' => ?_) p hp
    have key := prod_mul_Dl_mul_star_prod_mem_one h hl (fun a => g' a) (fun a => star (g a))
      (fun a => (hmem a (hg' a (Finset.mem_range.2 a.isLt))).1)
      (fun a => (hmem a (hg a (Finset.mem_range.2 a.isLt))).2)
    have hst := map_prod (starRingEnd K) (fun a : Fin l => star (g a)) Finset.univ
    simp only [starRingEnd_apply, star_star] at hst
    rw [hst, Fin.prod_univ_eq_prod_range (fun a => g' a) l,
      Fin.prod_univ_eq_prod_range (fun a => g a) l] at key
    convert key using 1
    ring
  · intro y z hy hz
    rw [mul_add]
    exact add_mem hy hz

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in

/- English proof (translation)
Distinguish the cases in `hl : l ≤ r + 1`. Use `swap`. Conclude with `⟨⊤, top_ne_bot, fun hl' => absurd hl' hl⟩`. Distinguish the cases in `hD : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = 0`. Conclude with `⟨⊤, top_ne_bot, fun _ _ hD' => absurd hD hD'⟩`.

Use `set e : ℤ := 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) with he`. Establish `hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `N.𝔡_ne`. Use `set I : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (_root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl) * (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-e) with hI`.

Establish `hI1 : I ≤ 1`. Rewrite using `[hI, FractionalIdeal.mul_le]`. Introduce `p hp q hq`. Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hp`. Use `Dl_mul_mem_one_of_mem_ipow N h hl hq` as an intermediate fact.

Rewrite using `[smul_mul_assoc, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]`. Conclude with `Submodule.smul_mem _ z this`. Take `⟨A, hA⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hI1`. Establish `hI0 : I ≠ 0`. Rewrite using `[hI]`.

Conclude with `mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]) (zpow_ne_zero _ hJ)`. Use `⟨A, ?_, fun hl' _ hD' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hI0` to reduce the goal to its premises. Rewrite using `[← hA, FractionalIdeal.coeIdeal_bot]`.

Establish `hn` using `congrArg FractionalIdeal.absNorm hA`. Rewrite `hn` using `[FractionalIdeal.coeIdeal_absNorm, hI, map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm]`. Unfold `_root_.GlobalTheory.DegCnt.NF.nD`. Rewrite using `[dif_pos hl']`. Establish `hq` using `congrArg (fun q : ℚ => (q : ℝ)) hn`.

Move the coercions through the operations in `at hq`. Rewrite using `[hq]`. Introduce `x hx y hy`. Establish `hx' : (x : K) ∈ I`. Rewrite using `[← hA]`.

Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩`. Establish `hy' : y ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ e` using `hy`. Establish `hxy` using `FractionalIdeal.mul_mem_mul hx' hy'`. Rewrite `hxy` using `[hI, mul_assoc, ← zpow_add₀ hJ, neg_add_cancel, zpow_zero, mul_one]`. Take `⟨z, hz⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hxy`.

Rewrite using `[← hz, Algebra.smul_def, mul_div_assoc, div_self hD', mul_one]`. Conclude with `Submodule.mem_one.2 ⟨z, rfl⟩`.
-/
theorem _root_.GlobalTheory.DegCnt.Absorb.exists_ideal (N : _root_.GlobalTheory.DegCnt.NF H r) {Λ : Submodule (𝓞 K) V}
    (h : _root_.GlobalTheory.HermLat.IsFramed N.F N.F' Λ N.aa) (l : ℕ) :
    ∃ A : Ideal (𝓞 K), A ≠ ⊥ ∧ ∀ hl : l ≤ r + 1, l ≤ N.j → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 →
      (Ideal.absNorm A : ℝ) = N.nD l ∧ ∀ x ∈ A, ∀ y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) := by
  by_cases hl : l ≤ r + 1
  swap
  · exact ⟨⊤, top_ne_bot, fun hl' => absurd hl' hl⟩
  by_cases hD : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = 0
  · exact ⟨⊤, top_ne_bot, fun _ _ hD' => absurd hD hD'⟩
  set e : ℤ := 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) with he
  have hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact N.𝔡_ne
  set I : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (_root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl) * (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-e)
    with hI
  have hI1 : I ≤ 1 := by
    rw [hI, FractionalIdeal.mul_le]
    intro p hp q hq
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hp
    have := Dl_mul_mem_one_of_mem_ipow N h hl hq
    rw [smul_mul_assoc, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
    exact Submodule.smul_mem _ z this
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hI1
  have hI0 : I ≠ 0 := by
    rw [hI]
    exact mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]) (zpow_ne_zero _ hJ)
  refine ⟨A, ?_, fun hl' _ hD' => ⟨?_, ?_⟩⟩
  · rintro rfl
    apply hI0
    rw [← hA, FractionalIdeal.coeIdeal_bot]
  · have hn := congrArg FractionalIdeal.absNorm hA
    rw [FractionalIdeal.coeIdeal_absNorm, hI, map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton,
      FractionalIdeal.coeIdeal_absNorm] at hn
    unfold _root_.GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl']
    have hq := congrArg (fun q : ℚ => (q : ℝ)) hn
    push_cast at hq
    rw [hq]
  · intro x hx y hy
    have hx' : (x : K) ∈ I := by
      rw [← hA]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩
    have hy' : y ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ e := hy
    have hxy := FractionalIdeal.mul_mem_mul hx' hy'
    rw [hI, mul_assoc, ← zpow_add₀ hJ, neg_add_cancel, zpow_zero, mul_one] at hxy
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).1 hxy
    rw [← hz, Algebra.smul_def, mul_div_assoc, div_self hD', mul_one]
    exact Submodule.mem_one.2 ⟨z, rfl⟩

end Flags

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv A _ (_root_.GlobalTheory.DegCnt.Absorb.sig K) rfl).toEquiv.symm`.
-/
private theorem absNorm_map_sig_eq (A : Ideal (𝓞 K)) :
    Ideal.absNorm (A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) = Ideal.absNorm A := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv A _ (_root_.GlobalTheory.DegCnt.Absorb.sig K) rfl).toEquiv.symm

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_sig_eq_star (x : 𝓞 K) :
    ((_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) : K) = star (x : K) := rfl

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Introduce `x hx`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_mul (hI a ha) (hJ b hb)`. Rewrite using `[map_add]`.

Conclude with `add_mem ha hb`.
-/
private theorem sig_mem_mul_of_sig_mem {I J : Ideal (𝓞 K)}
    (hI : ∀ x ∈ I, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I)
    (hJ : ∀ x ∈ J, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ J) :
    ∀ x ∈ I * J, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I * J := by
  intro x hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact Ideal.mul_mem_mul (hI a ha) (hJ b hb)
  · rw [map_add]; exact add_mem ha hb

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => intro x _`. Simplify using `[Ideal.one_eq_top]`. Consider the case `cons a s ha ih`. Rewrite using `[Finset.prod_cons]`.

Establish `h1 : ∀ x ∈ I a, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I a` using `h a (Finset.mem_cons_self a s)`. Establish `h2` using `ih fun l hl => h l (Finset.mem_cons_of_mem hl)`. Conclude with `sig_mem_mul_of_sig_mem h1 h2`.
-/
private theorem sig_mem_prod_of_sig_mem (s : Finset ℕ) (I : ℕ → Ideal (𝓞 K))
    (h : ∀ l ∈ s, ∀ x ∈ I l, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I l) :
    ∀ x ∈ ∏ l ∈ s, I l, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ ∏ l ∈ s, I l := by
  induction s using Finset.cons_induction with
  | empty => intro x _; simp [Ideal.one_eq_top]
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 : ∀ x ∈ I a, _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ I a := h a (Finset.mem_cons_self a s)
    have h2 := ih fun l hl => h l (Finset.mem_cons_of_mem hl)
    exact sig_mem_mul_of_sig_mem h1 h2

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Use `ext`. Use `show star (star (x : K)) = x`. Conclude with `star_star _`.
-/
private theorem sig_sig_eq (x : 𝓞 K) :
    _root_.GlobalTheory.DegCnt.Absorb.sig K (_root_.GlobalTheory.DegCnt.Absorb.sig K x) = x := by
  ext
  show star (star (x : K)) = x
  exact star_star _

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] [StarRing K] in
/- English proof (translation)
Introduce `x hx`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `(Ideal.mem_map_of_equiv _ _).1 hb`. Rewrite using `[map_mul, sig_sig_eq, mul_comm ((_root_.GlobalTheory.DegCnt.Absorb.sig K) a) c]`. Conclude with `Ideal.mul_mem_mul hc (Ideal.mem_map_of_mem _ ha)`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
private theorem sig_mem_mul_map_sig (A : Ideal (𝓞 K)) :
    ∀ x ∈ A * A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K),
      _root_.GlobalTheory.DegCnt.Absorb.sig K x ∈ A * A.map (_root_.GlobalTheory.DegCnt.Absorb.sig K) := by
  intro x hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_of_equiv _ _).1 hb
    rw [map_mul, sig_sig_eq, mul_comm ((_root_.GlobalTheory.DegCnt.Absorb.sig K) a) c]
    exact Ideal.mul_mem_mul hc (Ideal.mem_map_of_mem _ ha)
  · rw [map_add]; exact add_mem ha hb

open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hCM r N g Λ _ hΛ`. Use `haveI : IsTotallyComplex K := hCM.1`. Establish `hF` using `hΛ.1`. Use `choose A hA0 hA using fun l => _root_.GlobalTheory.DegCnt.Absorb.exists_ideal N hF l`. Use `set S := (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0) with hSdef`.

Establish `hjr` using `N.j_le`. Establish `hDne : ∀ l (hl : l ≤ r + 1), N.nD l ≠ 0 → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0`. Introduce `l hl hn hD`. Apply `hn` to reduce the goal to its premises. Unfold `_root_.GlobalTheory.DegCnt.NF.nD`.

Rewrite using `[dif_pos hl, hD]`. Simplify using the standard rewrite rules. Establish `hS : ∀ l ∈ S, ∃ hl : l ≤ r + 1, l ≤ N.j ∧ _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0`. Introduce `l hl`. Rewrite `hl` using `[hSdef, Finset.mem_filter, Finset.mem_Icc]`.

Establish `hl' : l ≤ r + 1` using `by omega`. Conclude with `⟨hl', hl.1.2, hDne l hl' hl.2⟩`. Establish `hnorm : ∀ l ∈ S, (Ideal.absNorm (A l) : ℝ) = N.nD l`. Introduce `l hl`. Take `⟨hl', hlj, hD⟩` from `hS l hl`.

Conclude with `((hA l) hl' hlj hD).1`. Establish `hge : ∀ l ∈ S, 1 ≤ N.nD l`. Introduce `l hl`. Rewrite using `[← hnorm l hl]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 l))` after adjusting the coercions.

Establish `hT : (N.T : K) ≠ 0`. Rewrite using `[← N.hT]`. Conclude with `N.F.hT`. Establish `hT' : (N.T : 𝓞 K) ≠ 0`. Introduce `h0`.

Apply `hT` to reduce the goal to its premises. Conclude with `congrArg (fun z : 𝓞 K => (z : K)) h0` after adjusting the coercions. Use `⟨Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)), ?_, ?_, ?_, fun Q hQ => hQ ?_ ?_ ?_ ?_⟩` and prove the remaining obligations. Establish `hsplit : (Ideal.absNorm (Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))) : ℝ) = (N.T : ℝ) ^ Module.finrank ℚ K * ∏ l ∈ S, N.nD l ^ 2`. Rewrite using `[map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]`.

Use `congr 1`. Rewrite using `[Ideal.absNorm_span_singleton, show (N.T : 𝓞 K) = algebraMap ℤ (𝓞 K) (N.T : ℤ) by simp, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[map_mul, absNorm_map_sig_eq, Nat.cast_mul, hnorm l hl, sq]`.

Rewrite using `[hsplit]`. Unfold `_root_.GlobalTheory.DegCnt.NF.Db _root_.GlobalTheory.DegCnt.NF.NT _root_.Formalism.HermitianLatticesTheory.fDeg`. Rewrite using `[IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add, mul_pow, ← Finset.prod_pow, ← pow_mul]`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.

Unfold `_root_.GlobalTheory.DegCnt.NF.Db`. Combine the equalities or inequalities in the displayed calculation. Unfold `_root_.GlobalTheory.DegCnt.NF.Del`. Establish `hj : N.j ≤ r + 1` using `by omega`. Establish `hDj : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j hj ≠ 0`.

Unfold `_root_.Formalism.HermitianLatticeCounting.S6.Dl`. Establish `hm : (_root_.Formalism.HermitianLatticeCounting.S6.Zhat N.F N.F').submatrix (Fin.castLE hj) (Fin.castLE hj) = N.w.mat * Matrix.diagonal (fun b => ((N.sgn b : ℤ) : K))`. Use extensionality with `a b`. Simplify using `[_root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.mul_diagonal, N.pair]`. Rewrite using `[hm, Matrix.det_mul, Matrix.det_diagonal]`.

Use `mul_ne_zero (_root_.GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h]`. Rewrite using `[← (hA N.j hj le_rfl hDj).1]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 _))` after adjusting the coercions. Rewrite using `[Ne, Ideal.mul_eq_bot, not_or]`.

Use `⟨by rwa [Ideal.span_singleton_eq_bot], ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff, not_exists]`. Introduce and unpack `l ⟨_, hl⟩`. Rewrite `hl` using `[Ideal.zero_eq_bot, Ideal.mul_eq_bot]`. Break down `hl with h | h` into its components or cases.

Conclude with `hA0 l h`. Conclude with `hA0 l (by rwa [Ideal.map_eq_bot_iff_of_injective (_root_.GlobalTheory.DegCnt.Absorb.sig K).injective] at h)`. Introduce `x hx`. Use `⟨_root_.GlobalTheory.DegCnt.Absorb.sig K x, ?_, coe_sig_eq_star x⟩` and prove the remaining obligations. Establish `hstab : ∀ z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)), _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))` using `sig_mem_prod_of_sig_mem S (fun l => A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) (fun l _ => sig_mem_mul_map_sig (A l))`.

Establish `hspan : ∀ z ∈ Ideal.span {(N.T : 𝓞 K)}, _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ Ideal.span {(N.T : 𝓞 K)}`. Introduce `y hy`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[map_mul, map_natCast]`. Conclude with `Ideal.mem_span_singleton.2 (dvd_mul_left _ _)`.

Conclude with `sig_mem_mul_of_sig_mem hspan hstab x hx`. Introduce `x hx`. Establish `h1 : Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) ≤ Ideal.span {(N.T : 𝓞 K)}` using `Ideal.mul_le_left`. Conclude with `Ideal.mem_span_singleton.1 (h1 hx)`. Introduce `l hl hlj hD x hx y hy`.

Break down `Nat.eq_zero_or_pos l with rfl | hl0` into its components or cases. Establish `hD0 : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' 0 hl = 1`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.Dl`. Conclude with `Matrix.det_isEmpty`. Rewrite using `[hD0, star_one, div_one]`.

Establish `hy' : y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 ((0 : ℕ) : ℤ)` using `by simpa using hy`. Take `⟨d, _, rfl⟩` from `(_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy'`. Conclude with `⟨Submodule.mem_one.2 ⟨x * d, by simp⟩, Submodule.mem_one.2 ⟨x * d, by simp⟩⟩`. Establish `hlS : l ∈ S`. Rewrite using `[hSdef, Finset.mem_filter, Finset.mem_Icc]`.

Use `⟨⟨hl0, hlj⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← (hA l hl hlj hD).1]`. Conclude with `Ideal.absNorm_eq_zero_iff.not.2 (hA0 l)` after adjusting the coercions. Establish `hxl : x ∈ A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)`. Establish `h1` using `Ideal.mul_le_right hx`.

Rewrite `h1` using `[← Finset.mul_prod_erase S _ hlS]`. Conclude with `Ideal.mul_le_left h1`. Use `⟨(hA l hl hlj hD).2 x (Ideal.mul_le_left hxl) y hy, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(Ideal.mem_map_of_equiv (_root_.GlobalTheory.DegCnt.Absorb.sig K) x).1 (Ideal.mul_le_right hxl)`. Establish `he : 0 ≤ 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)`.

Use `mul_nonneg (by norm_num) (Finset.sum_nonneg fun b hb => ?_)` and prove the remaining obligations. Use `Finset.mem_range.1 hb` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le he`. Rewrite `hy` using `[hk]`.

Take `⟨d, hd, rfl⟩` from `(_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy`. Take `⟨d', hd', hdd'⟩` from `exists_mem_pow_eq_star N k hd`. Establish `h2` using `(hA l hl hlj hD).2 a ha d' (by rw [hk]; exact (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h2`. Use `Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩` and prove the remaining obligations.

Establish `e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) = star (algebraMap (𝓞 K) K o)` using `coe_sig_eq_star o`. Establish `e2` using `coe_sig_eq_star a`. Rewrite using `[e1, ho, e2, hdd', star_div₀, star_mul', star_star]`.
-/
theorem _root_.GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔠 : Ideal (𝓞 K), (Ideal.absNorm 𝔠 : ℝ) ≤ (N.Db * N.NT) ^ 2 ∧ 1 ≤ N.Db ∧ 1 ≤ N.Del ∧ ∀ Q : Prop, (𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (_root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → Q) → Q := by
  intro K V _ _ _ _ _ _ _ _ H hCM r N g Λ _ hΛ
  haveI : IsTotallyComplex K := hCM.1
  have hF := hΛ.1
  choose A hA0 hA using fun l => _root_.GlobalTheory.DegCnt.Absorb.exists_ideal N hF l
  set S := (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0) with hSdef
  have hjr := N.j_le
  have hDne : ∀ l (hl : l ≤ r + 1), N.nD l ≠ 0 → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 := by
    intro l hl hn hD
    apply hn
    unfold _root_.GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl, hD]
    simp
  have hS : ∀ l ∈ S, ∃ hl : l ≤ r + 1, l ≤ N.j ∧ _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 := by
    intro l hl
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hl
    have hl' : l ≤ r + 1 := by omega
    exact ⟨hl', hl.1.2, hDne l hl' hl.2⟩
  have hnorm : ∀ l ∈ S, (Ideal.absNorm (A l) : ℝ) = N.nD l := by
    intro l hl
    obtain ⟨hl', hlj, hD⟩ := hS l hl
    exact ((hA l) hl' hlj hD).1
  have hge : ∀ l ∈ S, 1 ≤ N.nD l := by
    intro l hl
    rw [← hnorm l hl]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 l))
  have hT : (N.T : K) ≠ 0 := by
    rw [← N.hT]; exact N.F.hT
  have hT' : (N.T : 𝓞 K) ≠ 0 := by
    intro h0; apply hT; exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) h0
  refine ⟨Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)), ?_, ?_, ?_, fun Q hQ => hQ ?_ ?_ ?_ ?_⟩
  · have hsplit : (Ideal.absNorm (Ideal.span {(N.T : 𝓞 K)} * ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))) : ℝ) =
        (N.T : ℝ) ^ Module.finrank ℚ K * ∏ l ∈ S, N.nD l ^ 2 := by
      rw [map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
      congr 1
      · rw [Ideal.absNorm_span_singleton,
          show (N.T : 𝓞 K) = algebraMap ℤ (𝓞 K) (N.T : ℤ) by simp, Algebra.norm_algebraMap,
          RingOfIntegers.rank]
        simp
      · refine Finset.prod_congr rfl fun l hl => ?_
        rw [map_mul, absNorm_map_sig_eq, Nat.cast_mul, hnorm l hl, sq]
    rw [hsplit]
    unfold _root_.GlobalTheory.DegCnt.NF.Db
      _root_.GlobalTheory.DegCnt.NF.NT _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add, mul_pow, ← Finset.prod_pow, ← pow_mul]
    apply le_of_eq
    ring
  · unfold _root_.GlobalTheory.DegCnt.NF.Db
    calc (1 : ℝ) = ∏ l ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) hge
  · unfold _root_.GlobalTheory.DegCnt.NF.Del
    have hj : N.j ≤ r + 1 := by omega
    have hDj : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j hj ≠ 0 := by
      unfold _root_.Formalism.HermitianLatticeCounting.S6.Dl
      have hm : (_root_.Formalism.HermitianLatticeCounting.S6.Zhat N.F N.F').submatrix (Fin.castLE hj) (Fin.castLE hj) =
          N.w.mat *
            Matrix.diagonal (fun b => ((N.sgn b : ℤ) : K)) := by
        ext a b
        simp [_root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.mul_diagonal, N.pair]
      rw [hm, Matrix.det_mul, Matrix.det_diagonal]
      refine mul_ne_zero (_root_.GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero
        (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
      rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h]
    rw [← (hA N.j hj le_rfl hDj).1]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 (hA0 _))
  · rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨by rwa [Ideal.span_singleton_eq_bot], ?_⟩
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff, not_exists]
    rintro l ⟨_, hl⟩
    rw [Ideal.zero_eq_bot, Ideal.mul_eq_bot] at hl
    rcases hl with h | h
    · exact hA0 l h
    · exact hA0 l (by rwa [Ideal.map_eq_bot_iff_of_injective (_root_.GlobalTheory.DegCnt.Absorb.sig K).injective] at h)
  · intro x hx
    refine ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K x, ?_, coe_sig_eq_star x⟩
    have hstab : ∀ z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)),
        _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) :=
      sig_mem_prod_of_sig_mem S (fun l => A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K))
        (fun l _ => sig_mem_mul_map_sig (A l))
    have hspan : ∀ z ∈ Ideal.span {(N.T : 𝓞 K)},
        _root_.GlobalTheory.DegCnt.Absorb.sig K z ∈ Ideal.span {(N.T : 𝓞 K)} := by
      intro y hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      rw [map_mul, map_natCast]
      exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    exact sig_mem_mul_of_sig_mem hspan hstab x hx
  · intro x hx
    have h1 : Ideal.span {(N.T : 𝓞 K)} *
        ∏ l ∈ S, (A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K)) ≤
          Ideal.span {(N.T : 𝓞 K)} := Ideal.mul_le_left
    exact Ideal.mem_span_singleton.1 (h1 hx)
  · intro l hl hlj hD x hx y hy
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · have hD0 : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' 0 hl = 1 := by
        unfold _root_.Formalism.HermitianLatticeCounting.S6.Dl
        exact Matrix.det_isEmpty
      rw [hD0, star_one, div_one]
      have hy' : y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 ((0 : ℕ) : ℤ) := by simpa using hy
      obtain ⟨d, _, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy'
      exact ⟨Submodule.mem_one.2 ⟨x * d, by simp⟩, Submodule.mem_one.2 ⟨x * d, by simp⟩⟩
    · have hlS : l ∈ S := by
        rw [hSdef, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hl0, hlj⟩, ?_⟩
        rw [← (hA l hl hlj hD).1]
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 (hA0 l)
      have hxl : x ∈ A l * (A l).map (_root_.GlobalTheory.DegCnt.Absorb.sig K) := by
        have h1 := Ideal.mul_le_right hx
        rw [← Finset.mul_prod_erase S _ hlS] at h1
        exact Ideal.mul_le_left h1
      refine ⟨(hA l hl hlj hD).2 x (Ideal.mul_le_left hxl) y hy, ?_⟩
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv (_root_.GlobalTheory.DegCnt.Absorb.sig K) x).1 (Ideal.mul_le_right hxl)
      have he : 0 ≤ 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
        refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun b hb => ?_)
        have := Finset.mem_range.1 hb
        omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le he
      rw [hk] at hy
      obtain ⟨d, hd, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hy
      obtain ⟨d', hd', hdd'⟩ := exists_mem_pow_eq_star N k hd
      have h2 := (hA l hl hlj hD).2 a ha d'
        (by rw [hk]; exact (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 h2
      refine Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩
      have e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) =
          star (algebraMap (𝓞 K) K o) := coe_sig_eq_star o
      have e2 := coe_sig_eq_star a
      rw [e1, ho, e2, hdd', star_div₀, star_mul', star_star]

end GlobalTheory.DegCnt.Absorb
