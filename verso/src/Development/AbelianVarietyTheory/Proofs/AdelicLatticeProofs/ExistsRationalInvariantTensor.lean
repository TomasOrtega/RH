import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperatorStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HilbertFinitenessLeftInvariantMatrixPolyStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantFormEqSumInvariantTensorsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRationalKroneckerInvariantsStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

/- English proof (translation)
Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce and unpack `φ ⟨p, hp, b, rfl⟩`. Conclude with `⟨p, h hp, b, rfl⟩`.
-/
theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩`.
-/
theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

/- English proof (translation)
Take `⟨S, hS, fS, mS⟩` from `h1`. Take `⟨T, hT, fT, mT⟩` from `h2`. Use `⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS) (coordAlg_mono Set.subset_union_right mT)⟩` and prove the remaining obligations. Introduce and unpack `p (hp | hp)`. Conclude with `fS p hp`.

Conclude with `fT p hp`.
-/
theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

/- English proof (translation)
Take `⟨S, hS, fS, mS⟩` from `h1`. Conclude with `⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩`.
-/
theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)`.
-/
theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

/- English proof (translation)
Establish `h` using `GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl`. Use `clear hl`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem μ hμ`. Take `⟨h1, h2⟩` from `hμ`.

Use `choose q hq using h2`. Establish `hμ : μ = fun a => ((q a : ℚ) : ℂ)` using `funext hq`. Substitute `hμ` using the available equality. Use `⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `p rfl`.

Conclude with `h1`. Consider the case `zero`. Establish `: (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `good_zero Γ`. Consider the case `add u v _ _ hu hv`. Establish `: (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) = (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b`. Use function extensionality and compare the values at `y`.

Simplify using `[Matrix.add_vecMul]`. Rewrite using `[this]`. Conclude with `hu.add hv`. Consider the case `smul c u _ hu`. Establish `: (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) = c • (fun y => (u ᵥ* tpow n y) b)`.

Use function extensionality and compare the values at `y`. Simplify using `[Matrix.smul_vecMul]`. Rewrite using `[this]`. Conclude with `hu.smul c`.
-/
theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

/- English proof (translation)
Take `⟨l, hl, hev⟩` from `GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn`. Establish `: evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b`. Use function extensionality and compare the values at `y`. Rewrite using `[hev, Finset.sum_apply]`. Rewrite using `[this]`.

Conclude with `good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b`.
-/
theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

/- English proof (translation)
Take `⟨Rey, hR⟩` from `GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS`. Take `⟨s, hs, hgen⟩` from `GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR`. Establish `hg : ∀ F : s, Good Γ (evC F.1)` using `fun F => by`. Take `⟨h1, n, h2⟩` from `hs F.1 F.2`. Conclude with `good_homog hΓ hS n F.1 h1 h2`.

Use `choose S hfin hfix hmem using hg`. Use `⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨F, hF⟩` from `Set.mem_iUnion.1 hp`. Conclude with `hfix F p hF`.

Introduce `f hf`. Establish `h` using `hgen f hf`. Use `clear hf`. Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)`.

Consider the case `algebraMap c`. Establish `: evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c`. Use function extensionality and compare the values at `y`. Simplify using `[evC]`. Rewrite using `[this]`.

Conclude with `Subalgebra.algebraMap_mem _ c`. Consider the case `add u v _ _ hu hv`. Establish `: evC (u + v) = evC u + evC v` using `by funext y; simp [evC]`. Rewrite using `[this]`. Conclude with `Subalgebra.add_mem _ hu hv`.

Consider the case `mul u v _ _ hu hv`. Establish `: evC (u * v) = evC u * evC v` using `by funext y; simp [evC]`. Rewrite using `[this]`. Conclude with `Subalgebra.mul_mem _ hu hv`.
-/
theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

/- English proof (translation)
Introduce `ι _ _ Γ hΓ hS`. Take `⟨S, hfin, hfix, hmem⟩` from `exists_finite_family hΓ hS`. Take `⟨m, e, -, he⟩` from `hfin.fin_param`. Use `⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Use function extensionality and compare the values at `k`. Conclude with `congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2`. Introduce `f hf`. Establish `h` using `hmem f hf`. Generalize the expression as in `evC f = φ at h`.

Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem φ hφ`. Take `⟨p, hp, b, rfl⟩` from `hφ`. Rewrite `hp` using `[← he]`. Take `⟨i, rfl⟩` from `hp`.

Conclude with `⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩`. Consider the case `algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨P, hP⟩` from `hu`. Take `⟨Q, hQ⟩` from `hv`.

Conclude with `⟨P + Q, fun y => by rw [map_add, ← hP, ← hQ]; rfl⟩`. Consider the case `mul u v _ _ hu hv`. Take `⟨P, hP⟩` from `hu`. Take `⟨Q, hQ⟩` from `hv`. Conclude with `⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩`.
-/
theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add, ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
