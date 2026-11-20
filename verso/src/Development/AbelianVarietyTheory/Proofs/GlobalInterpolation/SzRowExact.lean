import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps _ _ C hC`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨hv, hu, ⟨b1, hb, htop, -, -⟩, hpar⟩` from `hV.hc`. Establish `hm2` using `D.R.two_le_m`. Establish `hm0 : (D.R.m : ℝ) ≠ 0`.

Establish `: D.R.m ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hh0 : h0 L = (h0v L.sc ch : ℝ)`. Unfold `h0`. Rewrite using `[hV.eta_eq]`.

Clear the denominators using the available nonvanishing facts. Establish `hcen : ∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2`. Introduce `τ j`. Rewrite using `[(hb τ j).2, hh0]`. Use `push_cast`.

Simplify using the standard rewrite rules. Establish `hcc : D.host.ccK = ⊤` using `hV.host.2.2.2.2.2.2.1`. Establish `hx : 1 < L.sc.x` using `L.sc.one_lt_alt`. Use `⟨?_, ?_, ?_, fun τ hm => hcen τ _, ?_, hcen, hpar, ?_, D.host.pde_mod, D.host.pde_ne_g, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ t hm ht`.

Rewrite using `[(hb τ ⟨0, hm⟩).1, htop τ t ht]`. Use `push_cast`. Simplify using the standard rewrite rules. Introduce `τ h0 ht`. Rewrite using `[(hu τ (by omega) ht).1, hv τ ⟨0, h0⟩, L.Sc_eq, hV.Del_eq]`.

Establish `hD : (1 : ℝ) ≤ (Delv L.sc cD : ℝ)`. Establish `: 0 < Delv L.sc cD` using `Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)`. Conclude with `this` after adjusting the coercions. Establish `hk : (1 : ℝ) ≤ (D.R.k : ℝ)`. Establish `: 1 ≤ D.R.k` using `by omega`.

Conclude with `this` after adjusting the coercions. Simplify using `only [Nat.sub_zero]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Introduce `τ hk ht`.

Rewrite using `[(hu τ (by omega) ht).2, hv τ ⟨D.R.k - 2, by omega⟩]`. Simplify using the standard rewrite rules. Evaluate the numerical expressions. Introduce `τ j h`. Rewrite using `[(hb τ ⟨j + 1, h⟩).1, (hb τ ⟨j, by omega⟩).1, hh0]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> nlinarith`. Rewrite using `[hV.etaF_eq, hC.2.2.2.2.2.2.2.2.2.2.2.1]`. Rewrite using `[hcc, Ideal.absNorm_top]`. Simplify using `only [Nat.cast_one, Real.log_one]`.

Unfold `Scale.L`. Check the signs of the components of the expression. Rewrite using `[hcc, Ideal.absNorm_top, hC.2.2.2.2.2.2.1]`. Establish `: 1 ≤ D.host.d` using `D.host.hyp.2.1.one_le`. Simplify using `only [Nat.cast_one, one_mul]`.

Conclude with `this` after adjusting the coercions.
-/
theorem szRow_exact : SzRow (fun C D L => (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + (⌊L.sc.b' / L.sc.x⌋ : ℤ)) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * L.Sc) ∧ (∀ τ (hk : 2 ≤ D.R.k), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D.hc τ).v ⟨D.R.k - 2, by omega⟩ - 1 / 2) ∧ (∀ τ (hm : 0 < D.R.m), |((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ τ (j : ℕ) (h : j + 1 < D.R.m), h0 L ≤ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ∧ (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) ≤ h0 L + 1) ∧ (∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2) ∧ (∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) ∧ (D.div.etaF = C.P.CetaF * L.sc.x ^ (-C.P.CF)) ∧ (D.host.pde % 15 = 1 ∧ D.host.pde' % 15 = 1) ∧ (∀ i, D.host.pde ≠ D.host.g i ∧ D.host.pde' ≠ D.host.g i) ∧ (Real.log (Ideal.absNorm D.host.ccK) ≤ L.sc.L) ∧ ((Ideal.absNorm D.host.ccK : ℝ) ≤ C.P.CccK * D.host.d)) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  obtain ⟨hv, hu, ⟨b1, hb, htop, -, -⟩, hpar⟩ := hV.hc
  have hm2 := D.R.two_le_m
  have hm0 : (D.R.m : ℝ) ≠ 0 := by
    have : D.R.m ≠ 0 := by omega
    exact_mod_cast this
  have hh0 : h0 L = (h0v L.sc ch : ℝ) := by
    unfold h0
    rw [hV.eta_eq]
    field_simp
  have hcen : ∀ τ (j : Fin D.R.m), |((((D.hc τ).e j - (D.hc τ).b j : ℚ)) : ℝ) - h0 L / 2| ≤ 2 := by
    intro τ j
    rw [(hb τ j).2, hh0]
    push_cast
    simp
  have hcc : D.host.ccK = ⊤ := hV.host.2.2.2.2.2.2.1
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  refine ⟨?_, ?_, ?_, fun τ hm => hcen τ _, ?_, hcen, hpar, ?_, D.host.pde_mod, D.host.pde_ne_g, ?_, ?_⟩
  · intro τ t hm ht
    rw [(hb τ ⟨0, hm⟩).1, htop τ t ht]
    push_cast
    simp
  · intro τ h0 ht
    rw [(hu τ (by omega) ht).1, hv τ ⟨0, h0⟩, L.Sc_eq, hV.Del_eq]
    have hD : (1 : ℝ) ≤ (Delv L.sc cD : ℝ) := by
      have : 0 < Delv L.sc cD := Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
      exact_mod_cast this
    have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
      have : 1 ≤ D.R.k := by omega
      exact_mod_cast this
    simp only [Nat.sub_zero]
    push_cast
    nlinarith
  · intro τ hk ht
    rw [(hu τ (by omega) ht).2, hv τ ⟨D.R.k - 2, by omega⟩]
    simp
    norm_num
  · intro τ j h
    rw [(hb τ ⟨j + 1, h⟩).1, (hb τ ⟨j, by omega⟩).1, hh0]
    push_cast
    constructor <;> nlinarith
  · rw [hV.etaF_eq, hC.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hcc, Ideal.absNorm_top]
    simp only [Nat.cast_one, Real.log_one]
    unfold Scale.L
    positivity
  · rw [hcc, Ideal.absNorm_top, hC.2.2.2.2.2.2.1]
    have : 1 ≤ D.host.d := D.host.hyp.2.1.one_le
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast this

/- English proof (translation)
Introduce `eps _ _ C _`. Conclude with `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => hV.hc.2.2.2⟩⟩⟩`.
-/
theorem szRow_mu : SzRow (fun _ D _ => ∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) := by
  intro eps _ _ C _
  exact ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => hV.hc.2.2.2⟩⟩⟩

end GlobalTheory.EX
