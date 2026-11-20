import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopStep

/- English proof (translation)
Introduce `E _ _ _ P hq N n hN r b c hn j h`. Substitute `hN` using the available equality. Establish `hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E))`. Introduce `k hk a l ha hl`. Establish `h0 : redP P (k.1 (Pi.single a 1) l) = 0`.

Apply the tactic sequence `have := twTQ_HQ_entry hk ha hl`. Rewrite `this` using `[redGL_val]`. Then use the resulting hypothesis. Apply the tactic sequence `exact intAt_div_of_redP hq (glint_entry k l a) h0`. Use `mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x l`.

Rewrite using `[extI_val]`. Distinguish the cases in `hl : l.1 < n`. Rewrite using `[dif_pos (show l.1 < n + 1 - 1 by omega)]`. Use `congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩` as an intermediate fact. Conclude with `this`.

Rewrite using `[dif_neg (show ¬ l.1 < n + 1 - 1 by omega)]`. Establish `e : l = Br.iL (rfl : n + 1 = n + 1)` using `Fin.ext (by have := l.2; show l.1 = n; omega)`. Substitute `e` using the available equality. Rewrite using `[sumE_last, Units.val_one, one_mul]`. Conclude with `fun a l ha hl => hent j h a l ha hl`.

Introduce `a l ha hl`. Use `hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl` as an intermediate fact. Conclude with `this`.
-/
theorem ext_mem_twisted_k1_level : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b →
    ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  intro E _ _ _ P hq N n hN r b c hn j h
  subst hN
  have hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b →
      ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E)) := by
    intro k hk a l ha hl
    have h0 : redP P (k.1 (Pi.single a 1) l) = 0 := by
      have := twTQ_HQ_entry hk ha hl
      rwa [redGL_val] at this
    exact intAt_div_of_redP hq (glint_entry k l a) h0
  refine mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_
  · intro x l
    rw [extI_val]
    by_cases hl : l.1 < n
    · rw [dif_pos (show l.1 < n + 1 - 1 by omega)]
      have := congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩
      exact this
    · rw [dif_neg (show ¬ l.1 < n + 1 - 1 by omega)]
      have e : l = Br.iL (rfl : n + 1 = n + 1) := Fin.ext (by have := l.2; show l.1 = n; omega)
      subst e
      rw [sumE_last, Units.val_one, one_mul]
  · exact fun a l ha hl => hent j h a l ha hl
  · intro a l ha hl
    have := hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl
    exact this

end GlobalTheory.TopStep
