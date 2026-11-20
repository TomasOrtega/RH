import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerdisc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Point2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Logs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Final

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Take `⟨n, rfl⟩` from `ENat.ne_top_iff_exists.mp hb`. Establish `h' : a ≤ ((1 + n : ℕ) : ℕ∞)` using `by push_cast; exact h`. Establish `ha : a ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) h'`. Take `⟨m, rfl⟩` from `ENat.ne_top_iff_exists.mp ha`. Use `⟨ha, ?_⟩` and prove the remaining obligations.

Simplify using `only [ENat.toNat_coe]`. Conclude with `h'` after adjusting the coercions.
-/
private theorem ne_top_and_toNat_le_of_le_one_add (a b : ℕ∞) (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_coe]
  exact_mod_cast h'

/- English proof (translation)
Introduce `CK hCK hK M R J Ct eps A1 hJ hCt heps`. Take `⟨n0, c0, hc0, hLD⟩` from `layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two (by have := M.pos; omega)`. Take `⟨C, hC0, hC⟩` from `point2 CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2) hc0 hJ hCt heps (by positivity)`. Take `⟨x0, hx02, hx0⟩` from `final Ct eps C heps`. Use `⟨x0, fun e t hAdm X q d hPP hlogqd L₀ _ _ hTB hAB => ?_⟩` and prove the remaining obligations.

Take `⟨hmu, hfin, hcyc, hE⟩` from `hTB`. Establish `hSB : SecondBound 2 R L₀` using `hAB.2`. Take `⟨c, hζ, hZ⟩` from `exc 2 R L₀ hAB`. Establish `hc : c ≤ 16 * M.deg`. Establish `h1` using `rootdeg L₀ 2 c Nat.prime_two hζ`.

Establish `h2 : c < 2 ^ c` using `Nat.lt_two_pow_self`. Use linear arithmetic over natural numbers and integers. Take `⟨L₂, i1, i2, i3, hL₂⟩` from `layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu`. Take `⟨Exc, hExc⟩` from `hZ ⌊X ^ Ct⌋₊`. Use `⟨Exc, hExc.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩` and prove the remaining obligations.

Establish `hx1 : (1 : ℝ) ≤ x` using `by linarith`. Establish `hX1 : (1 : ℝ) ≤ X` using `by linarith`. Establish `hlog : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Take `⟨he2, h2e, -, htx⟩` from `hAdm x (by linarith)`. Establish `hw : (1 : ℝ) ≤ x ^ (eps / 4)` using `Real.one_le_rpow hx1 (by positivity)`.

Establish `hP : 0 < q * d` using `Nat.mul_pos hPP.1.pos hPP.2.2.1.pos`. Establish `hlogP : Real.log ((q * d : ℕ) : ℝ) ≤ x ^ (eps / 4)`. Use `push_cast`. Conclude with `hlogqd.trans (logs.2.1 J eps X x hJ heps hX1 hXx)`. Establish `hcyc' : Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * (q * d)) ℚ)`.

Rewrite using `[← mul_assoc]`. Conclude with `hcyc`. Take `⟨hn0, hdisc⟩` from `hLD (q * d) (x ^ (eps / 4)) hP hw hlogP L₀ L₂ hfin hcyc' hL₂`. Take `⟨m, L₁, j1, j2, j3, hL₁, hme, hsha⟩` from `hE (e x) he2 E hEc`. Establish `hm : (m : ℝ) ≤ (2 * |A1| + 2) * (1 + Real.log x)`.

Establish `h3` using `logs.2.2 (e x) A1 x hx1 h2e`. Establish `h4 : (m : ℝ) ≤ (e x : ℝ) + 2` using `by exact_mod_cast hme`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpb : 0 ≤ ptBound C eps x` using `by show 0 ≤ C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))`. Conclude with `add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)`.

Use `show VVat 2 E (t x) (Real.exp (x ^ (4 * eps / 5)))`. Use `vvat 2 (t x) E (x ^ Ct) (ptBound C eps x) _ hpb htx (hx0 x hx) ?_` and prove the remaining obligations. Introduce `k hk1 hkt`. Establish `hkx : (k : ℝ) ≤ x ^ Ct` using `le_trans (by exact_mod_cast hkt.le) htx`. Establish `hk` using `hC L₀ hmu hSB c X Exc hc hExc L₂ hL₂ hn0 x hx1 hXx hxX hG hdisc k hk1 hkx m L₁ hL₁ hm`.

Take `⟨hne, hle⟩` from `ne_top_and_toNat_le_of_le_one_add _ _ hk.1 (hsha k hk1)`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Establish `h5 : ((shaInv E 2 k).toNat : ℝ) ≤ 1 + ((shaInv L₁ 2 k).toNat : ℝ)`. Conclude with `hle` after adjusting the coercions. Combine the linear relations using `[hk.2]`.
-/
theorem UpperTheory.V.Win.partA :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (M : AbF) (R : ℕ) (J Ct eps A1 : ℝ), 0 < J → 0 ≤ Ct → 0 < eps →
      ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ (X : ℝ) (q d : ℕ), PrimePair M.m q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∀ (L₀ : Type) [Field L₀] [NumberField L₀], TwoBase M q d L₀ → ABound 2 R L₀ →
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            BaAt M eps e t q d x := by
  intro CK hCK hK M R J Ct eps A1 hJ hCt heps
  obtain ⟨n0, c0, hc0, hLD⟩ := layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two
    (by have := M.pos; omega)
  obtain ⟨C, hC0, hC⟩ := point2 CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2)
    hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := final Ct eps C heps
  refine ⟨x0, fun e t hAdm X q d hPP hlogqd L₀ _ _ hTB hAB => ?_⟩
  obtain ⟨hmu, hfin, hcyc, hE⟩ := hTB
  have hSB : SecondBound 2 R L₀ := hAB.2
  obtain ⟨c, hζ, hZ⟩ := exc 2 R L₀ hAB
  have hc : c ≤ 16 * M.deg := by
    have h1 := rootdeg L₀ 2 c Nat.prime_two hζ
    have h2 : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu
  obtain ⟨Exc, hExc⟩ := hZ ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨he2, h2e, -, htx⟩ := hAdm x (by linarith)
  have hw : (1 : ℝ) ≤ x ^ (eps / 4) := Real.one_le_rpow hx1 (by positivity)
  have hP : 0 < q * d := Nat.mul_pos hPP.1.pos hPP.2.2.1.pos
  have hlogP : Real.log ((q * d : ℕ) : ℝ) ≤ x ^ (eps / 4) := by
    push_cast
    exact hlogqd.trans (logs.2.1 J eps X x hJ heps hX1 hXx)
  have hcyc' : Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * (q * d)) ℚ) := by
    rw [← mul_assoc]; exact hcyc
  obtain ⟨hn0, hdisc⟩ := hLD (q * d) (x ^ (eps / 4)) hP hw hlogP L₀ L₂ hfin hcyc' hL₂
  obtain ⟨m, L₁, j1, j2, j3, hL₁, hme, hsha⟩ := hE (e x) he2 E hEc
  have hm : (m : ℝ) ≤ (2 * |A1| + 2) * (1 + Real.log x) := by
    have h3 := logs.2.2 (e x) A1 x hx1 h2e
    have h4 : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hme
    linarith
  have hpb : 0 ≤ ptBound C eps x := by
    show 0 ≤ C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))
    exact add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)
  show VVat 2 E (t x) (Real.exp (x ^ (4 * eps / 5)))
  refine vvat 2 (t x) E (x ^ Ct) (ptBound C eps x) _ hpb htx (hx0 x hx) ?_
  intro k hk1 hkt
  have hkx : (k : ℝ) ≤ x ^ Ct := le_trans (by exact_mod_cast hkt.le) htx
  have hk := hC L₀ hmu hSB c X Exc hc hExc L₂ hL₂ hn0 x hx1 hXx hxX hG hdisc k hk1 hkx
    m L₁ hL₁ hm
  obtain ⟨hne, hle⟩ := ne_top_and_toNat_le_of_le_one_add _ _ hk.1 (hsha k hk1)
  refine ⟨hne, ?_⟩
  have h5 : ((shaInv E 2 k).toNat : ℝ) ≤ 1 + ((shaInv L₁ 2 k).toNat : ℝ) := by
    exact_mod_cast hle
  linarith [hk.2]
