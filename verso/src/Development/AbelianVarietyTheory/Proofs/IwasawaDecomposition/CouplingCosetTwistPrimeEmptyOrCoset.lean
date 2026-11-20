import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

/- English proof (translation)
Introduce `X Pr R sel S mu cst u j hQ r P`. Establish `hP : P.1 ∉ Pr.vGs` using `hQ P.1 P.2`. Distinguish the cases in `hj : j + 1 = R.m`. Use `right`. Take `⟨y0, -, hY⟩` from `r.mem_ybSet hj`.

Establish `hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0` using `pow_ne_zero _ (by`. Rewrite using `[Nat.cast_ne_zero]`. Unfold `qOf`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `P.1.ne_bot)`.

Use `⟨(frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0, (qOf P.1 : X.E) ^ cst.M, hq, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [cqOf, cosetIn, Set.mem_setOf_eq, if_neg hP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hx⟩`.

Rewrite `hy` using `[hY]`. Establish `h1` using `(mem_locLat _ _ _ _).1 hy ⟨P.1, Finset.mem_union_right _ P.2⟩`. Simplify using `only [if_neg hP, zpow_natCast] at h1`. Establish `h2` using `(GlobalTheory.ColPeriod.TopTwist.frsF_mem' sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩ hP (((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y - (frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0))).1 (by`. Rewrite using `[map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.

Conclude with `h1)`. Establish `h3` using `Submodule.add_mem _ hx h2`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Introduce `hx`. Conclude with `⟨y0, by rw [hY]; simp, hx⟩`. Use `left`. Establish `h1 : r.1.2 = ∅`.

Use `r.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne _ _ _ hj]`. Then use the resulting hypothesis. Use extensionality with `x`. Simplify using `[cqOf, cosetIn, h1]`.
-/
theorem cqOf_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  intro X Pr R sel S mu cst u j hQ r P
  classical
  have hP : P.1 ∉ Pr.vGs := hQ P.1 P.2
  by_cases hj : j + 1 = R.m
  · right
    obtain ⟨y0, -, hY⟩ := r.mem_ybSet hj
    have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ (by
      rw [Nat.cast_ne_zero]
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.1.ne_bot)
    refine ⟨(frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0, (qOf P.1 : X.E) ^ cst.M, hq, ?_⟩
    ext x
    simp only [cqOf, cosetIn, Set.mem_setOf_eq, if_neg hP]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hY] at hy
      have h1 := (mem_locLat _ _ _ _).1 hy ⟨P.1, Finset.mem_union_right _ P.2⟩
      simp only [if_neg hP, zpow_natCast] at h1
      have h2 := (GlobalTheory.ColPeriod.TopTwist.frsF_mem' sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩ hP
        (((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y -
          (frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0))).1 (by
        rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact h1)
      have h3 := Submodule.add_mem _ hx h2
      convert h3 using 1
      rw [← smul_add]
      congr 1
      abel
    · intro hx
      exact ⟨y0, by rw [hY]; simp, hx⟩
  · left
    have h1 : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne _ _ _ hj] at this
    ext x
    simp [cqOf, cosetIn, h1]

end GlobalTheory.Mem.Col2.ChEx
