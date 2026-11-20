import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

/- English proof (translation)
Establish `hB0 : ∀ x, 0 ≤ B x x`. Introduce `x`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(hp x hx).le`.

Establish `hE0 : ∀ χ, 0 ≤ E χ`. Introduce `χ`. Establish `h` using `hE χ`. Establish `h'` using `hB0 (y + m • χ)`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Use the polynomial consequences of the given equalities and inequalities. Establish `hinj : Function.Injective (fun χ : X => y + m • χ)`. Introduce `a b h`. Establish `h' : (m : ℤ) • a = (m : ℤ) • b` using `by simpa using h`.

Conclude with `smul_right_injective X (Int.natCast_ne_zero.mpr hm) h'`. Establish `hQ` using `GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef hs hp`. Establish `hfin : ∀ n : ℕ, {χ | (E χ).toNat = n}.Finite`. Introduce `n`. Use `(Set.Finite.preimage (fun _ _ _ _ h => hinj h) (GlobalTheory.ClassMin.finite_sublevel hQ ((D * n : ℤ) : ℝ))).subset ?_` and prove the remaining obligations.

Introduce `χ hχ`. Simplify using `only [Set.mem_setOf_eq] at hχ`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]`. Establish `h` using `hE χ`. Establish `h0` using `hE0 χ`.

Establish `h2` using `hB0 (y + m • χ)`. Establish `hEn : E χ = n` using `by omega`. Rewrite `h` using `[hEn]`. Establish `h3 : (B (y + m • χ) (y + m • χ) : ℝ) ≤ ((D * n : ℤ) : ℝ)` using `by exact_mod_cast h`. Establish `h4 : (0 : ℝ) ≤ B (y + m • χ) (y + m • χ)` using `by exact_mod_cast h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `GlobalTheory.hasSum_map_powerSeries_mk_finsum O C X φ h1 hX (fun χ => (E χ).toNat) hfin a`. Establish `hf : (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ))) = fun χ => φ (PowerSeries.C (a χ)) * φ PowerSeries.X ^ (E χ).toNat`. Use function extensionality and compare the values at `χ`. Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (hE0 χ)`.

Rewrite using `[hk]`. Simplify using `[hu, mul_comm]`. Establish `hg : (fun n : ℕ => ∑ᶠ (χ : X) (_ : E χ = n), a χ) = fun n : ℕ => ∑ᶠ (χ : X) (_ : (E χ).toNat = n), a χ`. Use function extensionality and compare the values at `n`. Use `finsum_congr fun χ => ?_` and prove the remaining obligations.

Establish `h0` using `hE0 χ`. Establish `hiff : (E χ = n) = ((E χ).toNat = n)` using `propext (by omega)`. Rewrite using `[hiff]`. Rewrite using `[hf, hg]`. Conclude with `h`.
-/
theorem hasSum_zpow_of_form_le {O C X : Type} [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (φ : PowerSeries O →+* C) (h1 : ∀ f, ‖φ f‖ ≤ 1) (hX : ‖φ PowerSeries.X‖ < 1) (u : Cˣ)
    (hu : (u : C) = φ PowerSeries.X) (B : LinearMap.BilinForm ℤ X) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (y : X) {m : ℕ} (hm : m ≠ 0) {D : ℤ} (hD : 0 < D) (E : X → ℤ)
    (hE : ∀ χ, B (y + m • χ) (y + m • χ) ≤ D * E χ) (a : X → O) :
    HasSum (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ)))
      (φ (PowerSeries.mk fun n => ∑ᶠ (χ : X) (_ : E χ = n), a χ)) := by
  classical
  have hB0 : ∀ x, 0 ≤ B x x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  have hE0 : ∀ χ, 0 ≤ E χ := by
    intro χ
    have h := hE χ
    have h' := hB0 (y + m • χ)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hinj : Function.Injective (fun χ : X => y + m • χ) := by
    intro a b h
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (Int.natCast_ne_zero.mpr hm) h'
  have hQ := GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef hs hp
  have hfin : ∀ n : ℕ, {χ | (E χ).toNat = n}.Finite := by
    intro n
    refine (Set.Finite.preimage (fun _ _ _ _ h => hinj h)
      (GlobalTheory.ClassMin.finite_sublevel hQ ((D * n : ℤ) : ℝ))).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq] at hχ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
    have h := hE χ
    have h0 := hE0 χ
    have h2 := hB0 (y + m • χ)
    have hEn : E χ = n := by omega
    rw [hEn] at h
    have h3 : (B (y + m • χ) (y + m • χ) : ℝ) ≤ ((D * n : ℤ) : ℝ) := by exact_mod_cast h
    have h4 : (0 : ℝ) ≤ B (y + m • χ) (y + m • χ) := by exact_mod_cast h2
    linarith
  have h := GlobalTheory.hasSum_map_powerSeries_mk_finsum O C X φ h1 hX (fun χ => (E χ).toNat) hfin a
  have hf : (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ))) =
      fun χ => φ (PowerSeries.C (a χ)) * φ PowerSeries.X ^ (E χ).toNat := by
    funext χ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (hE0 χ)
    rw [hk]
    simp [hu, mul_comm]
  have hg : (fun n : ℕ => ∑ᶠ (χ : X) (_ : E χ = n), a χ) =
      fun n : ℕ => ∑ᶠ (χ : X) (_ : (E χ).toNat = n), a χ := by
    funext n
    refine finsum_congr fun χ => ?_
    have h0 := hE0 χ
    have hiff : (E χ = n) = ((E χ).toNat = n) := propext (by omega)
    rw [hiff]
  rw [hf, hg]
  exact h

/- English proof (translation)
Establish `hB0 : ∀ y, 0 ≤ β.be y y`. Introduce `y`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Conclude with `(β.pos y hy).le`.

Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases. Establish `hk : k = 0` using `by simpa using hm`. Establish `h0 : β.be x x = 0`. Establish `h` using `β.dvd x x`. Simplify `h` using `[hk]`.

Simplify using `[h0]`. Establish `hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ)` using `mul_dvd_mul_left 2 (by exact_mod_cast hm)`. Establish `hjk : (j : ℤ) ∣ 2 * (k : ℤ)` using `dvd_mul_of_dvd_right (by exact_mod_cast hj) 2`. Take `⟨q, hq⟩` from `dvd_trans hmk (β.dvd x x)`. Take `⟨c, hc⟩` from `dvd_trans hjk (β.dvd z x)`.

Establish `hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2` using `by positivity`. Establish `hj1 : (1 : ℤ) ≤ j` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0`. Establish `hq' : β.be x x / (2 * m ^ 2) = q`. Rewrite using `[hq]`. Conclude with `Int.mul_ediv_cancel_left q hm2.ne'`.

Establish `hc' : β.be z x / j = c`. Rewrite using `[hc]`. Conclude with `Int.mul_ediv_cancel_left c (by omega)`. Rewrite using `[hq', hc']`. Establish `hexp` using `hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)`.

Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp`. Rewrite `hexp` using `[β.symm x z, hc]`. Establish `ha` using `hB0 z`. Establish `hs0 : 0 ≤ s` using `le_trans (mul_nonneg (by positivity) ha) hs`. Establish `hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1` using `by nlinarith`.

Establish `h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z))` using `mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))`. Establish `key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s)`. Use polynomial arithmetic with `[hexp, h5]`. Establish `hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Use `mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[hX, hq]`.
-/
theorem form_le_exponent {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by
  have hB0 : ∀ y, 0 ≤ β.be y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (β.pos y hy).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hk : k = 0 := by simpa using hm
    have h0 : β.be x x = 0 := by
      have h := β.dvd x x
      simpa [hk] using h
    simp [h0]
  · have hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ) := mul_dvd_mul_left 2 (by exact_mod_cast hm)
    have hjk : (j : ℤ) ∣ 2 * (k : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hj) 2
    obtain ⟨q, hq⟩ := dvd_trans hmk (β.dvd x x)
    obtain ⟨c, hc⟩ := dvd_trans hjk (β.dvd z x)
    have hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hq' : β.be x x / (2 * m ^ 2) = q := by
      rw [hq]
      exact Int.mul_ediv_cancel_left q hm2.ne'
    have hc' : β.be z x / j = c := by
      rw [hc]
      exact Int.mul_ediv_cancel_left c (by omega)
    rw [hq', hc']
    have hexp := hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp
    rw [β.symm x z, hc] at hexp
    have ha := hB0 z
    have hs0 : 0 ≤ s := le_trans (mul_nonneg (by positivity) ha) hs
    have hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1 := by nlinarith
    have h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z)) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))
    have key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s) := by
      nlinarith [hexp, h5]
    have hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg
      linarith
    nlinarith [hX, hq]

/- English proof (translation)
Introduce `O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2`. Establish `hm0 : m ≠ 0` using `hmo.pos.ne'`. Establish `hT` using `(GlobalTheory.T.hom_transport_alt O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2`. Establish `hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀)`. Introduce `χ₀`.

Rewrite using `[hp1, map_add, map_nsmul]`. Establish `hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y` using `fun x y => dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)`. Establish `hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2` using `by positivity`. Prove the components needed by the constructor for the conclusion. Establish `hsum` using `hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2 (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2)) (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)`.

Establish `key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) = (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) : Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀)))`. Introduce `χ₀`. Rewrite using `[(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _`.

Use `HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr (hsum.mul_left (I.lam : C))`. Introduce `j hj q₀ q hj0 hq1 hq2 s hs`. Establish `hsum` using `hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 (D := 4 * (m : ℤ) ^ 2) (by positivity) (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) + β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s) (fun χ => form_le_exponent β₀ hm hj hj …`. Establish `key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) = ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) + β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C …`.

Introduce `χ₀`. Rewrite using `[(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ, (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]`. Simplify using `only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree. Use `show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _`.

Rewrite using `[← tsum_mul_left]`. Use `HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) * φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))`.
-/
theorem twist_tx_ev_eq_map_arc : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2
  have hm0 : m ≠ 0 := hmo.pos.ne'
  have hT := (GlobalTheory.T.hom_transport_alt O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2
  have hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀) := by
    intro χ₀
    rw [hp1, map_add, map_nsmul]
  have hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y := fun x y =>
    dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)
  have hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  constructor
  · have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2))
      (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)
    have key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) =
        (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) :
          Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]
      ring
    show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr
      (hsum.mul_left (I.lam : C))
  · intro j hj q₀ q hj0 hq1 hq2 s hs
    have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0
      (D := 4 * (m : ℤ) ^ 2) (by positivity)
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s)
      (fun χ => form_le_exponent β₀ hm hj hj0 _ _ (s : ℤ) hs) (fun χ => N₀.evT m p₀ q₀.1.2 χ)
    have key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) =
        ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
          (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) +
            β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C) *
            φ (PowerSeries.C (N₀.evT m p₀ q₀.1.2 χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ,
        (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]
      simp only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _
    rw [← tsum_mul_left]
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
      φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr
      (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))

end GlobalTheory.Ex
