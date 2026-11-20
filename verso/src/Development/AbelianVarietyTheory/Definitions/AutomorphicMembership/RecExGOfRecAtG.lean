import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

/- English proof (translation)
Take `⟨x0, h⟩` from `Inh.g_big eps h0 h1`. Use `⟨x0, fun s C cD ch P q1 a b c hs hx hok => ?_⟩` and prove the remaining obligations. Use `choose du hpos hdu using fun u => DuInt.duStarOf_nat P.R P.H (P.hcW u) hok.arith.2.1 fun i => h s P.R _ hs hx hok.rank (hok.val.2.2.2.2.1 i).1`. Conclude with `⟨du, hpos, hdu⟩`.
-/
theorem exists_du_nat (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (C : FC) (cD ch : ℝ) (P : PreCh) (q1 : ℕ)
    (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
    ∃ du : P.Word → ℕ, (∀ u, 0 < du u) ∧ ∀ u, (du u : ℝ) = duP P u := by
  obtain ⟨x0, h⟩ := Inh.g_big eps h0 h1
  refine ⟨x0, fun s C cD ch P q1 a b c hs hx hok => ?_⟩
  choose du hpos hdu using fun u => DuInt.duStarOf_nat P.R P.H (P.hcW u) hok.arith.2.1
    fun i => h s P.R _ hs hx hok.rank (hok.val.2.2.2.2.1 i).1
  exact ⟨du, hpos, hdu⟩

namespace Inh

/- English proof (translation)
Introduce and unpack `⟨ε0, hε0, h⟩`. Establish `he : 0 < min ε0 (1 / 100)` using `lt_min hε0 (by norm_num)`. Establish `he52 : min ε0 (1 / 100) < 1 / 52` using `(min_le_right _ _).trans_lt (by norm_num)`. Establish `hle` using `min_le_left ε0 (1 / 100)`. Generalize the expression as in `min ε0 (1 / 100) = eps at he he52 hle`.

Take `⟨CT2, C8, C5, c6, Cb, h8, -, -, -, la, hla, S, hG⟩` from `exists_chGood hH eps he he52`. Take `⟨K0, h⟩` from `h eps C8 C5 c6 Cb he hle he52 h8`. Take `⟨C, hS, hCT, hCp, hL, -⟩` from `GlobalTheory.EX.exists_std_large K0 K0 CT2 C8 h8`. Take `⟨c1, h⟩` from `h C hS hCp hL`. Establish `hcD : 0 ≤ max c1 0` using `le_max_right _ _`.

Take `⟨c2, h⟩` from `h _ (le_max_left c1 0)`. Generalize the expression as in `max c1 0 = cD at hcD h`. Take `⟨c2', hlow⟩` from `WinLow.window_lower h2b eps C he he52 hS cD hcD`. Take `⟨ch, a1, a2, a3⟩ : ∃ ch : ℝ, c2 ≤ ch ∧ c2' ≤ ch ∧ 402 ≤ ch` from `⟨max c2 (max c2' 402), by simp, by simp, by simp⟩`. Take `⟨x0, h⟩` from `h ch a1`.

Take `⟨x1, hlow⟩` from `hlow ch a2`. Take `⟨x2, hG⟩` from `hG C hS hCT hCp cD hcD ch a3`. Take `⟨x3, h3⟩` from `exists_levCh_of_levelPrime hLP eps 1 C he he52 one_pos hS`. Take `⟨x4, h4⟩` from `exists_du_nat eps he he52`. Take `⟨s, hs, hx, hm⟩` from `S.exists_mem hla.le he he52 (max x0 (max x1 (max x2 (max x3 x4))))`.

Simplify using `only [max_le_iff] at hx`. Take `⟨b0, b1, b2, b3, b4⟩` from `hx`. Take `⟨P, a, b, c, hg, -⟩` from `hG s hs b2 hm 0`. Take `⟨du, hpos, hdu⟩` from `h4 s C cD ch P _ a b c hs b4 hg.ok`. Take `⟨hD, hDle⟩` from `DsLow.DsP_pos_and_lower P`.

Take `⟨Lv, l1, l2, l3⟩` from `h3 cD ch s P _ a b c du _ hs b3 hg.ok hpos hD fun u => by`. Rewrite using `[one_mul]`. Conclude with `hlow s P _ a b c du _ hs b1 hg.ok hdu hDle u`. Conclude with `h ⟨s, C, cD, ch, P, _, a, b, c, hS, hg.ok, Lv, fun u => by rw [l1]; exact hdu u, l2, l3⟩ rfl rfl rfl hs b0 hg`.
-/
theorem not_evG_false (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) : ¬ EvG fun _ => False := by
  rintro ⟨ε0, hε0, h⟩
  have he : 0 < min ε0 (1 / 100) := lt_min hε0 (by norm_num)
  have he52 : min ε0 (1 / 100) < 1 / 52 := (min_le_right _ _).trans_lt (by norm_num)
  have hle := min_le_left ε0 (1 / 100)
  generalize min ε0 (1 / 100) = eps at he he52 hle
  obtain ⟨CT2, C8, C5, c6, Cb, h8, -, -, -, la, hla, S, hG⟩ := exists_chGood hH eps he he52
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he hle he52 h8
  obtain ⟨C, hS, hCT, hCp, hL, -⟩ := GlobalTheory.EX.exists_std_large K0 K0 CT2 C8 h8
  obtain ⟨c1, h⟩ := h C hS hCp hL
  have hcD : 0 ≤ max c1 0 := le_max_right _ _
  obtain ⟨c2, h⟩ := h _ (le_max_left c1 0)
  generalize max c1 0 = cD at hcD h
  obtain ⟨c2', hlow⟩ := WinLow.window_lower h2b eps C he he52 hS cD hcD
  obtain ⟨ch, a1, a2, a3⟩ : ∃ ch : ℝ, c2 ≤ ch ∧ c2' ≤ ch ∧ 402 ≤ ch := ⟨max c2 (max c2' 402), by simp, by simp, by simp⟩
  obtain ⟨x0, h⟩ := h ch a1
  obtain ⟨x1, hlow⟩ := hlow ch a2
  obtain ⟨x2, hG⟩ := hG C hS hCT hCp cD hcD ch a3
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps 1 C he he52 one_pos hS
  obtain ⟨x4, h4⟩ := exists_du_nat eps he he52
  obtain ⟨s, hs, hx, hm⟩ := S.exists_mem hla.le he he52 (max x0 (max x1 (max x2 (max x3 x4))))
  simp only [max_le_iff] at hx
  obtain ⟨b0, b1, b2, b3, b4⟩ := hx
  obtain ⟨P, a, b, c, hg, -⟩ := hG s hs b2 hm 0
  obtain ⟨du, hpos, hdu⟩ := h4 s C cD ch P _ a b c hs b4 hg.ok
  obtain ⟨hD, hDle⟩ := DsLow.DsP_pos_and_lower P
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s P _ a b c du _ hs b3 hg.ok hpos hD fun u => by
    rw [one_mul]
    exact hlow s P _ a b c du _ hs b1 hg.ok hdu hDle u
  exact h ⟨s, C, cD, ch, P, _, a, b, c, hS, hg.ok, Lv, fun u => by rw [l1]; exact hdu u, l2, l3⟩ rfl rfl rfl hs b0 hg

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Conclude with `not_evG_false hH hLP h2b (hp.imp fun K C5 c6 Cb hK h => hn ⟨K, C5, c6, Cb, hK, h⟩)`.
-/
theorem exists_of_evG (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) {p : Ctx → Prop} (hp : EvG p) :
    ∃ (K : Ctx) (C5 c6 Cb : ℝ), K.Good C5 c6 Cb ∧ p K := by
  by_contra hn
  exact not_evG_false hH hLP h2b (hp.imp fun K C5 c6 Cb hK h => hn ⟨K, C5, c6, Cb, hK, h⟩)

end Inh

end GlobalTheory.Mem.Top

end
