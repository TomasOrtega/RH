import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `k E _ _ _ n e Q g y _ hg`. Use `set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE`. Use `set I := secIdeal QE y with hI`. Use `set ι : E →+* SecAlg QE y := algebraMap E (SecAlg QE y) with hι`. Use `set x : Fin n → SecAlg QE y := secCoord QE y with hx`.

Establish `hmk : ∀ p : MvPolynomial (Fin n) E, Ideal.Quotient.mk I p = eval₂ ι x p`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => rw [eval₂_C, hι]`. Both sides reduce to the same expression.

Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => rw [map_mul, hp, eval₂_mul, eval₂_X]`. Both sides reduce to the same expression. Establish `hlin : ∀ u : Fin n → E, ∑ j, ι (u j) * x j = Ideal.Quotient.mk I (linForm u)`. Introduce `u`.

Simplify using `[hmk, linForm, eval₂_sum, mul_comm]`. Establish `hchart : ∑ j, ι (y (.inr j)) * x j = 1`. Rewrite using `[hlin, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hform : ∀ i, ∑ j, ι (y (.inl (i, j))) * x j = 0`.

Introduce `i`. Rewrite using `[hlin, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))`. Use `set θ : MvPolynomial (Fin n) (SecAlg QE y) := ∑ j, X j * C (x j) with hθ`. Use `set c : k →+* MvPolynomial (Fin n) (SecAlg QE y) := (C : SecAlg QE y →+* _).comp (ι.comp (algebraMap k E)) with hc`.

Set `vφ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y)` to `Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y)) (X ij.2 - θ * C (ι (y (.inr ij.2)))) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1`. Set `vψ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y)` to `Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y)) (X ij.2) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1`. Use `set φ := eval₂Hom c vφ with hφ`. Use `set ψ := eval₂Hom c vψ with hψ`. Establish `hker : incIdeal Q (e + 1) ≤ RingHom.ker φ`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `q hq`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hφ, coe_eval₂Hom, eval₂_rename]`. Establish `h : eval₂ c (vφ ∘ Sum.inl) q = C (Ideal.Quotient.mk I (q.map (algebraMap k E)))`.

Rewrite using `[hmk, eval₂_map, eval₂_comp_left]`. Both sides reduce to the same expression. Rewrite using `[h, Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sum]`. Simplify using `only [map_mul, hφ, eval₂Hom_X', vφ, Sum.elim_inl, Sum.elim_inr]`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use `show ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) = 0`.

Establish `h : ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) = θ - θ * C (∑ j, ι (y (.inr j)) * x j)`. Simplify using `only [map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[eq_sub_iff_add_eq, ← Finset.sum_add_distrib]`. Use `conv_rhs => rw [hθ]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Rewrite using `[h, hchart, map_one, mul_one, sub_self]`. Simplify using `only [Fin.cases_succ, ← map_mul, ← map_sum, hform, map_zero]`. Take `⟨M, hM⟩` from `h₁ k n (e + 1) Q g hg`. Use `set G := φ (rename Sum.inr g) with hG`. Establish `hGx : ∀ j, G ^ M * C (x j) ^ M = 0`.

Introduce `j`. Use `hker (hM j)` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_pow, map_mul, hφ, eval₂Hom_X']`. Rewrite using `[← mul_pow]`. Conclude with `this`.

Establish `hG0 : G ^ M = 0`. Establish `h1 : Ideal.span (Set.range fun j => (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))) = ⊤`. Rewrite using `[Ideal.eq_top_iff_one, ← map_one C, ← hchart, map_sum]`. Conclude with `sum_mem fun j _ => by`. Rewrite using `[map_mul]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)`. Establish `h2` using `Ideal.span_pow_eq_top _ h1 M`. Establish `h3 : (1 : MvPolynomial (Fin n) (SecAlg QE y)) ∈ Ideal.span ((fun z => z ^ M) '' Set.range fun j => C (x j))`. Rewrite using `[h2]`. Conclude with `Submodule.mem_top`.

Establish `key : ∀ z ∈ Ideal.span ((fun z => z ^ M) '' Set.range fun j => (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))), G ^ M * z = 0`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨_, ⟨j, rfl⟩, rfl⟩` from `hz`.

Conclude with `hGx j`. Consider the case `zero => exact mul_zero _`. Consider the case `add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]`. Consider the case `smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]`. Simplify using `using key 1 h3`.

Use `set π := Ideal.Quotient.mk (Ideal.span {θ}) with hπ`. Establish `hπθ : π θ = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self θ)`. Establish `hcomp : π.comp φ = π.comp ψ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[hφ, hψ]`. Introduce `v`. Break down `v with j | ⟨i, j⟩` into its components or cases. Simplify using `[hφ, hψ, vφ, vψ]`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `[hφ, hψ, vφ, vψ, hπθ]`. Simplify using `[hφ, hψ, vφ, vψ]`. Establish `hspec : ψ (rename Sum.inr g) = (specRest (algebraMap k E) g y).map (algebraMap E (SecAlg QE y))`. Rewrite using `[hψ, coe_eval₂Hom, eval₂_rename]`. Unfold `specRest`.

Rewrite using `[eval₂_comp_left]`. Use `congr 1`. Conclude with `RingHom.ext fun a => by simp [hc, hι]`. Use function extensionality and compare the values at `ij`. Take `⟨i, j⟩` from `ij`.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp [vψ, hι]`. Use `⟨M + 1, M.succ_pos, ?_⟩` and prove the remaining obligations. Establish `hz : π (ψ (rename Sum.inr g) ^ (M + 1)) = 0`. Rewrite using `[map_pow, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, pow_succ, ← map_pow, ← hG, hG0, map_zero, zero_mul]`. Rewrite using `[← hspec, ← Ideal.mem_span_singleton]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hz`.
-/
theorem ChowSecDvd.proof (h₁ : IncidenceNull.Statement) : ChowSecDvd.Statement := by
  intro k E _ _ _ n e Q g y _ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  set I := secIdeal QE y with hI
  set ι : E →+* SecAlg QE y := algebraMap E (SecAlg QE y) with hι
  set x : Fin n → SecAlg QE y := secCoord QE y with hx
  have hmk : ∀ p : MvPolynomial (Fin n) E, Ideal.Quotient.mk I p = eval₂ ι x p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [eval₂_C, hι]; rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, hp, eval₂_mul, eval₂_X]; rfl
  have hlin : ∀ u : Fin n → E, ∑ j, ι (u j) * x j = Ideal.Quotient.mk I (linForm u) := by
    intro u
    simp [hmk, linForm, eval₂_sum, mul_comm]
  have hchart : ∑ j, ι (y (.inr j)) * x j = 1 := by
    rw [hlin, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hform : ∀ i, ∑ j, ι (y (.inl (i, j))) * x j = 0 := by
    intro i
    rw [hlin, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  set θ : MvPolynomial (Fin n) (SecAlg QE y) := ∑ j, X j * C (x j) with hθ
  set c : k →+* MvPolynomial (Fin n) (SecAlg QE y) := (C : SecAlg QE y →+* _).comp (ι.comp (algebraMap k E))
    with hc
  let vφ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2 - θ * C (ι (y (.inr ij.2)))) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  let vψ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  set φ := eval₂Hom c vφ with hφ
  set ψ := eval₂Hom c vψ with hψ

  have hker : incIdeal Q (e + 1) ≤ RingHom.ker φ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, coe_eval₂Hom, eval₂_rename]
      have h : eval₂ c (vφ ∘ Sum.inl) q = C (Ideal.Quotient.mk I (q.map (algebraMap k E))) := by
        rw [hmk, eval₂_map, eval₂_comp_left]
        rfl
      rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
      simp only [map_mul, hφ, eval₂Hom_X', vφ, Sum.elim_inl, Sum.elim_inr]
      refine Fin.cases ?_ (fun i => ?_) i
      · show ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) = 0
        have h : ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) =
            θ - θ * C (∑ j, ι (y (.inr j)) * x j) := by
          simp only [map_sum, map_mul, Finset.mul_sum]
          rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
          conv_rhs => rw [hθ]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h, hchart, map_one, mul_one, sub_self]
      · simp only [Fin.cases_succ, ← map_mul, ← map_sum, hform, map_zero]
  obtain ⟨M, hM⟩ := h₁ k n (e + 1) Q g hg
  set G := φ (rename Sum.inr g) with hG
  have hGx : ∀ j, G ^ M * C (x j) ^ M = 0 := by
    intro j
    have := hker (hM j)
    rw [RingHom.mem_ker, map_pow, map_mul, hφ, eval₂Hom_X'] at this
    rw [← mul_pow]
    exact this
  have hG0 : G ^ M = 0 := by
    have h1 : Ideal.span (Set.range fun j => (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← map_one C, ← hchart, map_sum]
      exact sum_mem fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := Ideal.span_pow_eq_top _ h1 M
    have h3 : (1 : MvPolynomial (Fin n) (SecAlg QE y)) ∈
        Ideal.span ((fun z => z ^ M) '' Set.range fun j => C (x j)) := by
      rw [h2]; exact Submodule.mem_top
    have key : ∀ z ∈ Ideal.span ((fun z => z ^ M) '' Set.range fun j =>
        (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))), G ^ M * z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hz
        exact hGx j
      | zero => exact mul_zero _
      | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
      | smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
    simpa using key 1 h3

  set π := Ideal.Quotient.mk (Ideal.span {θ}) with hπ
  have hπθ : π θ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self θ)
  have hcomp : π.comp φ = π.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [hφ, hψ]
    · intro v
      rcases v with j | ⟨i, j⟩
      · simp [hφ, hψ, vφ, vψ]
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [hφ, hψ, vφ, vψ, hπθ]
        · simp [hφ, hψ, vφ, vψ]
  have hspec : ψ (rename Sum.inr g) =
      (specRest (algebraMap k E) g y).map (algebraMap E (SecAlg QE y)) := by
    rw [hψ, coe_eval₂Hom, eval₂_rename]
    unfold specRest
    rw [eval₂_comp_left]
    congr 1
    · exact RingHom.ext fun a => by simp [hc, hι]
    · funext ij
      obtain ⟨i, j⟩ := ij
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [vψ, hι]
  refine ⟨M + 1, M.succ_pos, ?_⟩
  have hz : π (ψ (rename Sum.inr g) ^ (M + 1)) = 0 := by
    rw [map_pow, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, pow_succ, ← map_pow, ← hG, hG0,
      map_zero, zero_mul]
  rw [← hspec, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end

end GroundTheory.Heights₂.Heights.Vertical
