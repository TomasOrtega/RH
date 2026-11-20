import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open Formalism.L2.Col

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `h x (Submodule.subset_span hx)`. Introduce `h x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [dotProduct_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [dotProduct_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [dotProduct_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem mem_dualFr_span_iff_dualsum {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Fin n → K))
    (φ : Fin n → K) :
    φ ∈ dualFr (Submodule.span (𝓞 K) S) ↔ ∀ x ∈ S, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
    | smul a x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Introduce `E K ι _ _ _ _ _ emb n N hN M L hL τ`. Substitute `hN` using the available equality. Establish `hC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k` using `fun k => rfl`. Establish `hLst : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n` using `rfl`. Establish `split : ∀ φ x : Fin (n + 1) → K, φ ⬝ᵥ x = (fun k => φ (Fin.castSucc k)) ⬝ᵥ (fun k => x (Fin.castSucc k)) + φ (Fin.last n) * x (Fin.last n)`.

Introduce `φ x`. Simplify using `only [dotProduct, Fin.sum_univ_castSucc]`. Use extensionality with `φ`. Rewrite using `[tauLat, mem_dualFr_span_iff_dualsum]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[tauLat, mem_dualFr_span_iff_dualsum]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Set `v : Fin (n + 1) → E` to `Fin.lastCases 0 m`.

Establish `hv : v ∈ L`. Rewrite using `[hL]`. Use `⟨?_, 0, ?_⟩` and prove the remaining obligations. Simplify `hm` using `[hC, v]`. Simplify using `[hLst, v]`.

Use `h _ ⟨v, hv, rfl⟩` as an intermediate fact. Rewrite `this` using `[split]`. Simplify `this` using `[hC, v]`. Set `v : Fin (n + 1) → E` to `Pi.single (Fin.last n) 1`. Establish `hv : v ∈ L`.

Rewrite using `[hL]`. Use `⟨?_, 1, ?_⟩` and prove the remaining obligations. Establish `: (fun k : Fin n => v (Formalism.L2.Col.Br.iC rfl k)) = 0`. Use function extensionality and compare the values at `k`. Simplify using `[hC, v, Fin.castSucc_ne_last]`.

Rewrite using `[this]`. Conclude with `M.zero_mem`. Simplify using `[hLst, v]`. Use `h _ ⟨v, hv, rfl⟩` as an intermediate fact. Rewrite `this` using `[split]`.

Establish `h0 : (fun k : Fin n => (fun a => emb τ (v a)) (Fin.castSucc k)) = 0`. Use function extensionality and compare the values at `k`. Simplify using `[v, Fin.castSucc_ne_last]`. Rewrite `this` using `[h0, dotProduct_zero, zero_add]`. Take `⟨c, hc⟩` from `Submodule.mem_one.1 this`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hLst, mul_one]`. Establish `hv1 : (fun (x : Fin (n + 1) → E) a => emb τ (x a)) v (Fin.last n) = 1` using `by simp [v]`. Rewrite `hc` using `[hv1, mul_one]`. Rewrite using `[← hc]`.

Introduce and unpack `⟨h1, c, hc⟩`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite `hv` using `[SetLike.mem_coe, hL]`. Take `⟨hvM, d, hd⟩` from `hv`. Rewrite using `[split]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite `h1` using `[tauLat, mem_dualFr_span_iff_dualsum]`. Use `h1 _ ⟨_, hvM, rfl⟩` as an intermediate fact. Simplify `this` using `[hC]`. Rewrite `hc`, `hd` using `[hLst]`.

Use `Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) d, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, mul_one]`. Use `show _ = _ * emb τ (v (Fin.last n))`. Rewrite using `[← hd]`. Both sides reduce to the same expression.
-/
theorem dualFr_tauLat_sumLat : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  intro E K ι _ _ _ _ _ emb n N hN M L hL τ
  subst hN
  have hC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => rfl
  have hLst : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have split : ∀ φ x : Fin (n + 1) → K, φ ⬝ᵥ x = (fun k => φ (Fin.castSucc k)) ⬝ᵥ (fun k => x (Fin.castSucc k))
      + φ (Fin.last n) * x (Fin.last n) := by
    intro φ x
    simp only [dotProduct, Fin.sum_univ_castSucc]
  ext φ
  rw [tauLat, mem_dualFr_span_iff_dualsum]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [tauLat, mem_dualFr_span_iff_dualsum]
      rintro _ ⟨m, hm, rfl⟩
      let v : Fin (n + 1) → E := Fin.lastCases 0 m
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 0, ?_⟩
        · simpa [hC, v] using hm
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      simpa [hC, v] using this
    · let v : Fin (n + 1) → E := Pi.single (Fin.last n) 1
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 1, ?_⟩
        · have : (fun k : Fin n => v (Formalism.L2.Col.Br.iC rfl k)) = 0 := by
            funext k; simp [hC, v, Fin.castSucc_ne_last]
          rw [this]; exact M.zero_mem
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      have h0 : (fun k : Fin n => (fun a => emb τ (v a)) (Fin.castSucc k)) = 0 := by
        funext k; simp [v, Fin.castSucc_ne_last]
      rw [h0, dotProduct_zero, zero_add] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      rw [hLst, mul_one]
      have hv1 : (fun (x : Fin (n + 1) → E) a => emb τ (x a)) v (Fin.last n) = 1 := by simp [v]
      rw [hv1, mul_one] at hc
      rw [← hc]
  · rintro ⟨h1, c, hc⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, hL] at hv
    obtain ⟨hvM, d, hd⟩ := hv
    rw [split]
    refine add_mem ?_ ?_
    · rw [tauLat, mem_dualFr_span_iff_dualsum] at h1
      have := h1 _ ⟨_, hvM, rfl⟩
      simpa [hC] using this
    · rw [hLst] at hc hd
      refine Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) d, ?_⟩
      rw [map_mul, hc, mul_one]
      show _ = _ * emb τ (v (Fin.last n))
      rw [← hd]
      rfl

end GlobalTheory
