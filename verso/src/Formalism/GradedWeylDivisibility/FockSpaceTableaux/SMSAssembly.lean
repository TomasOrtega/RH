import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Introduce `hCL hCS hSS hLI B _ _ r n ν`. Apply `le_antisymm` to reduce the goal to its premises. Establish `key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl B r n ν, (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I}`. Introduce `d`. Proceed by induction on `d using WellFoundedLT.induction with`.

Consider the case `_ d ih`. Introduce `f hf hd`. Distinguish the cases in `hf0 : f = 0`. Rewrite using `[hf0]`. Conclude with `Submodule.zero_mem _`.

Establish `hm` using `(colLex r n).degree_mem_support hf0`. Take `⟨K, sz, hsz, I, hsh, hmono, hexp⟩` from `hSS r n ν _ (hCS B r n ν f hf _ hm) (hLI B r n ν f hf hf0)`. Take `⟨hdeg, hlc⟩` from `hCL B r n K sz hsz I hmono`. Establish `hg : bideterminant B sz hsz I ∈ dualWeyl B r n ν`. Rewrite using `[← hsh]`.

Conclude with `bidetMem B r n K sz hsz I`. Establish `hgS : bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I}` using `Submodule.subset_span ⟨K, sz, hsz, I, hsh, rfl⟩`. Establish `hf' : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ dualWeyl B r n ν` using `Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hg)`. Establish `h1 : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I}`. Distinguish the cases in `hne : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I = 0`.

Rewrite using `[hne]`. Conclude with `Submodule.zero_mem _`. Establish `hlt` using `lcassem_sub_lt (colLex r n) (hdeg.trans hexp) hlc hne`. Conclude with `ih _ (by rw [← hd]; exact hlt) _ hf' rfl`. Establish `h2` using `Submodule.add_mem _ h1 (Submodule.smul_mem _ ((colLex r n).leadingCoeff f) hgS)`.

Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `fun f hf => key _ f hf rfl`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨K, sz, hsz, I, hsh, rfl⟩`. Rewrite using `[← hsh]`.

Conclude with `bidetMem B r n K sz hsz I`.
-/
theorem semistandard_module_assembly : SMSAssembly := by
  intro hCL hCS hSS hLI B _ _ r n ν
  apply le_antisymm
  · have key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl B r n ν,
        (colLex r n).toSyn ((colLex r n).degree f) = d →
        f ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
          (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        have hm := (colLex r n).degree_mem_support hf0
        obtain ⟨K, sz, hsz, I, hsh, hmono, hexp⟩ :=
          hSS r n ν _ (hCS B r n ν f hf _ hm) (hLI B r n ν f hf hf0)
        obtain ⟨hdeg, hlc⟩ := hCL B r n K sz hsz I hmono
        have hg : bideterminant B sz hsz I ∈ dualWeyl B r n ν := by
          rw [← hsh]; exact bidetMem B r n K sz hsz I
        have hgS : bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ)
            (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
            shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} :=
          Submodule.subset_span ⟨K, sz, hsz, I, hsh, rfl⟩
        have hf' : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ dualWeyl B r n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hg)
        have h1 : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ Submodule.span B
            {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
              shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
          by_cases hne : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I = 0
          · rw [hne]; exact Submodule.zero_mem _
          have hlt := lcassem_sub_lt (colLex r n) (hdeg.trans hexp) hlc hne
          exact ih _ (by rw [← hd]; exact hlt) _ hf' rfl
        have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ ((colLex r n).leadingCoeff f) hgS)
        rwa [sub_add_cancel] at h2
    exact fun f hf => key _ f hf rfl
  · rw [Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← hsh]
    exact bidetMem B r n K sz hsz I

end Formalism.GradedWeylDivisibility
