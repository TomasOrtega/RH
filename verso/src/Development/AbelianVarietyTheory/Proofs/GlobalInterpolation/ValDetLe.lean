import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.DetIndexPf

/- English proof (translation)
Establish `key : ∀ j : Fin r, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : Fin r → 𝓞 K, ∑ k, c k • (fun a : Fin r => C a k) = s • (fun a : Fin r => A a j)`. Introduce `j`. Establish `h1 : (fun a : Fin r => A a j) ∈ localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j))` using `⟨1, w.asIdeal.primeCompl.one_mem, by`. Rewrite using `[one_smul]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩⟩`.

Take `⟨s, hs, hx⟩` from `h h1`. Conclude with `⟨s, hs, (Submodule.mem_span_range_iff_exists_fun _).1 hx⟩`. Use `choose s hs c hc using key`. Establish `e : A * Matrix.diagonal (fun j => algebraMap (𝓞 K) K (s j)) = C * (algebraMap (𝓞 K) K).mapMatrix (Matrix.of fun k j => c j k)`. Use extensionality with `a j`.

Use `congrFun (hc j) a` as an intermediate fact. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this`. Rewrite using `[mul_comm, ← this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `[mul_comm]`. Establish `e2` using `congrArg (fun M => w.valuation K (Matrix.det M)) e`. Simplify using `only [Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod, ← RingHom.map_det] at e2`. Establish `h1 : ∏ j, w.valuation K (algebraMap (𝓞 K) K (s j)) = 1` using `Finset.prod_eq_one fun j _ => (w.valuation_eq_one_iff_notMem).2 (hs j)`. Rewrite `e2` using `[h1, mul_one]`.

Rewrite using `[e2]`. Conclude with `mul_le_of_le_one_right' (w.valuation_le_one _)`.
-/
theorem val_det_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : ℕ}
    (A C : Matrix (Fin r) (Fin r) K)
    (h : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) ≤
      localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => C a j))) :
    w.valuation K A.det ≤ w.valuation K C.det := by
  have key : ∀ j : Fin r, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : Fin r → 𝓞 K,
      ∑ k, c k • (fun a : Fin r => C a k) = s • (fun a : Fin r => A a j) := by
    intro j
    have h1 : (fun a : Fin r => A a j) ∈
        localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
    obtain ⟨s, hs, hx⟩ := h h1
    exact ⟨s, hs, (Submodule.mem_span_range_iff_exists_fun _).1 hx⟩
  choose s hs c hc using key
  have e : A * Matrix.diagonal (fun j => algebraMap (𝓞 K) K (s j)) =
      C * (algebraMap (𝓞 K) K).mapMatrix (Matrix.of fun k j => c j k) := by
    ext a j
    have := congrFun (hc j) a
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [mul_comm, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  have e2 := congrArg (fun M => w.valuation K (Matrix.det M)) e
  simp only [Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod, ← RingHom.map_det] at e2
  have h1 : ∏ j, w.valuation K (algebraMap (𝓞 K) K (s j)) = 1 :=
    Finset.prod_eq_one fun j _ => (w.valuation_eq_one_iff_notMem).2 (hs j)
  rw [h1, mul_one] at e2
  rw [e2]
  exact mul_le_of_le_one_right' (w.valuation_le_one _)

/- English proof (translation)
Introduce `K _ _ w r B B' M' i q _ hM hB`. Use `set C : Matrix (Fin r) (Fin r) K := (B : Matrix (Fin r) (Fin r) K) * Matrix.diagonal (fun j => if j = i then q else 1) with hC`. Establish `hd : C.det = q * (B : Matrix (Fin r) (Fin r) K).det`. Rewrite using `[hC, Matrix.det_mul, Matrix.det_diagonal, mul_comm]`. Simplify using the standard rewrite rules.

Establish `hf : (fun j : Fin r => fun α : Fin r => (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j) = fun j : Fin r => fun α : Fin r => C α j`. Use function extensionality and compare the values at `j α`. Rewrite using `[hC, Matrix.mul_diagonal, mul_comm]`. Rewrite `hM` using `[hf]`. Establish `he` using `hB.symm.trans hM`.

Rewrite using `[← hd]`. Conclude with `le_antisymm (val_det_le w _ _ he.le) (val_det_le w _ _ he.ge)`.
-/
theorem detIndex : DetIndex := by
  intro K _ _ w r B B' M' i q _ hM hB
  set C : Matrix (Fin r) (Fin r) K :=
    (B : Matrix (Fin r) (Fin r) K) * Matrix.diagonal (fun j => if j = i then q else 1) with hC
  have hd : C.det = q * (B : Matrix (Fin r) (Fin r) K).det := by
    rw [hC, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
    simp
  have hf : (fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j) = fun j : Fin r => fun α : Fin r => C α j := by
    funext j α
    rw [hC, Matrix.mul_diagonal, mul_comm]
  rw [hf] at hM
  have he := hB.symm.trans hM
  rw [← hd]
  exact le_antisymm (val_det_le w _ _ he.le) (val_det_le w _ _ he.ge)

end GlobalTheory.DetIndexPf
