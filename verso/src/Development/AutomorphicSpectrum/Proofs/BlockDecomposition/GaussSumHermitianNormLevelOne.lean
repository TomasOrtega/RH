import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZeroStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.GaussOne

variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

open Classical in

/- English proof (translation)
Use `set S := ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) with hS`. Establish `key : χ (A * b) * S = S`. Rewrite using `[hS, Finset.mul_sum]`. Use `Finset.sum_nbij' (fun t => t + b) (fun t => t - b) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t ht`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢`. Rewrite using `[map_add, ht, hb]`. Introduce `t ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢`. Rewrite using `[map_sub, ht, hb]`.

Introduce `t _`. Simplify using the standard rewrite rules. Introduce `t _`. Simplify using the standard rewrite rules. Introduce `t _`.

Rewrite using `[← AddChar.map_add_eq_mul, mul_add, add_comm]`. Establish `h1 : (1 - χ (A * b)) * S = 0` using `by rw [sub_mul, one_mul, key, sub_self]`. Break down `mul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hχ`. Conclude with `h`.
-/
theorem sum_fixed_eq_zero (χ : AddChar E ℂ) (A b : E) (hb : τ b = b) (hχ : χ (A * b) ≠ 1) :
    ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) = 0 := by
  set S := ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) with hS
  have key : χ (A * b) * S = S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_nbij' (fun t => t + b) (fun t => t - b) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_add, ht, hb]
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_sub, ht, hb]
    · intro t _
      simp
    · intro t _
      simp
    · intro t _
      rw [← AddChar.map_add_eq_mul, mul_add, add_comm]
  have h1 : (1 - χ (A * b)) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ
  · exact h

open Classical in

/- English proof (translation)
Establish `hf : Finset.univ.filter (fun w : E => τ w * w = t) = Finset.univ.filter (fun a : E => a * τ a = t)`. Use extensionality with `w`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[mul_comm]`. Rewrite using `[hf, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem card_filter_norm (t : E) :
    (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℤ) =
      (Nat.card {a : E // a * τ a = t} : ℤ) := by
  have hf : Finset.univ.filter (fun w : E => τ w * w = t) =
      Finset.univ.filter (fun a : E => a * τ a = t) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_comm]
  rw [hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in

/- English proof (translation)
Establish `hmap : ∀ w ∈ (Finset.univ : Finset E), τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t)`. Introduce `w _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]`. Conclude with `mul_comm _ _`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmap]`.

Establish `hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t), (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) = (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t)`. Introduce `t ht`. Establish `ht' : τ t = t` using `(Finset.mem_filter.mp ht).2`. Rewrite using `[Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const, nsmul_eq_mul]`. Use `congr 1`.

Establish `hc` using `card_filter_norm (τ := τ) t`. Establish `hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) = ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ)`. Rewrite using `[← hc]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hc']`. Distinguish the cases in `h0 : t = 0`. Substitute `h0` using the available equality. Rewrite using `[GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hfib]`.

Simplify using `only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]`. Rewrite using `[sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]`. Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_core (h : ResAlg E τ q ε) (χ : AddChar E ℂ) (A b : E) (hb : τ b = b)
    (hχ : χ (A * b) ≠ 1) :
    ∑ w : E, χ (A * (τ w * w)) = (ε : ℂ) * q := by
  have hmap : ∀ w ∈ (Finset.univ : Finset E),
      τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t) := by
    intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]
    exact mul_comm _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t),
      (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) =
        (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t) := by
    intro t ht
    have ht' : τ t = t := (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    have hc := card_filter_norm (τ := τ) t
    have hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) =
        ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ) := by
      rw [← hc]
      push_cast
      rfl
    rw [hc']
    by_cases h0 : t = 0
    · subst h0
      rw [GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]
      push_cast
      ring
    · rw [GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]
      push_cast
      ring
  rw [Finset.sum_congr rfl hfib]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
    map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

end GlobalTheory.CompanionTheory.SiegLoc.GaussOne

namespace GlobalTheory.CompanionTheory.SiegLoc

/- English proof (translation)
Introduce `R _ σ ϖ q ε hR _ ψ hψ a ha hna`. Establish `hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hna (hψ.prim a ha hcon)`.

Take `⟨b, hb, hχ⟩` from `hex`. Use `GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_` and prove the remaining obligations. Rewrite using `[barσ_mk, hb]`. Rewrite using `[← map_mul]` and apply the resulting hypothesis.
-/
theorem gauss_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ),
    IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 →
    (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) =
      (ε : ℂ) * q := by
  intro R _ σ ϖ q ε hR _ ψ hψ a ha hna
  have hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hna (hψ.prim a ha hcon)
  obtain ⟨b, hb, hχ⟩ := hex
  refine GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_
  · rw [barσ_mk, hb]
  · rwa [← map_mul]

end GlobalTheory.CompanionTheory.SiegLoc
