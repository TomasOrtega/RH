import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs hfix hspan A hA`. Establish `key : ∀ z y, y - z ∈ Λ → W z s = γ (w • z) (y - z) • W y s`. Introduce `z y hyz`. Establish `h1` using `h.comp z (y - z) s`. Rewrite `h1` using `[hfix _ hyz, add_sub_cancel]`. Then use the resulting hypothesis.

Set `P : X ⧸ Λ → Prop` to `fun q => ∃ a ∈ A, (Submodule.Quotient.mk a : X ⧸ Λ) = q`. Set `rep : X ⧸ Λ → X` to `fun q => if hq : P q then hq.choose else Quotient.out q`. Establish `hrep : ∀ q, (Submodule.Quotient.mk (rep q) : X ⧸ Λ) = q`. Introduce `q`. Distinguish the cases in `hq : P q`.

Simplify using `only [rep, dif_pos hq]`. Conclude with `hq.choose_spec.2`. Simplify using `only [rep, dif_neg hq]`. Conclude with `Quotient.out_eq q`. Establish `hrepA : ∀ q, P q → rep q ∈ A`.

Introduce `q hq`. Simplify using `only [rep, dif_pos hq]`. Conclude with `hq.choose_spec.1`. Set `e : X ⧸ Λ → M` to `fun q => W (rep q) s`. Establish `he : ∀ z, W z s = γ (w • z) (rep (Submodule.Quotient.mk z) - z) • e (Submodule.Quotient.mk z)`.

Introduce `z`. Conclude with `key z _ ((Submodule.Quotient.eq Λ).1 (hrep _))`. Establish `hli : LinearIndependent ℂ e`. Use `linearIndependent_of_simultaneous_eigen e (fun q (l : Λ) => γ l (rep q)) (fun l : Λ => W l) ?_ ?_ ?_` and prove the remaining obligations. Introduce `q q' hq`.

Establish `hm : rep q - rep q' ∈ Λ`. Rewrite using `[hΛ]`. Introduce `a ha`. Apply `h.swap_eq_one` to reduce the goal to its premises. Establish `h1 : γ a (rep q) = γ a (rep q')` using `congrFun hq ⟨a, ha⟩`.

Rewrite using `[sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]`. Rewrite using `[← hrep q, ← hrep q']`. Conclude with `(Submodule.Quotient.eq Λ).2 hm`. Introduce `l q show W l (W (rep q) s) = γ l (rep q) • W (rep q) s`. Rewrite using `[h.comm, hfix l l.2]`.

Introduce `q h0`. Establish `h1` using `h.neg_comp (rep q) s`. Rewrite `h1` using `[show W (rep q) s = 0 from h0, map_zero]`. Conclude with `hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range e)`.

Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, rfl⟩`. Use `show W z s ∈ _`. Rewrite using `[he z]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.

Set `b` to `Module.Basis.mk hli hsp`. Set `ℓ : M →ₗ[ℂ] ℂ` to `b.constr ℂ (fun q => if P q then (1 : ℂ) else 0)`. Establish `hℓ : ∀ q, ℓ (e q) = if P q then (1 : ℂ) else 0`. Introduce `q`. Use `b.constr_basis ℂ (fun q => if P q then (1 : ℂ) else 0) q` as an intermediate fact.

Rewrite `this` using `[Module.Basis.mk_apply]`. Then use the resulting hypothesis. Establish `hwA : ∀ a ∈ A, ∀ b ∈ A, γ (w • a) b = 1` using `fun a ha b hb => hA _ (A.smul_mem w ha) b hb`. Use `⟨ℓ, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : P (Submodule.Quotient.mk 0)` using `⟨0, A.zero_mem, rfl⟩`. Establish `h1` using `he 0`.

Rewrite `h1` using `[h.zero, hwA 0 A.zero_mem _ (A.sub_mem (hrepA _ h0) A.zero_mem), one_smul]`. Rewrite using `[h1, hℓ, if_pos h0]`. Introduce `a ha v`. Establish `hext : ℓ ∘ₗ W a = ℓ`. Use `b.ext fun q => ?_` and prove the remaining obligations.

Rewrite using `[Module.Basis.mk_apply, LinearMap.comp_apply]`. Use `show ℓ (W a (W (rep q) s)) = ℓ (e q)`. Rewrite using `[h.comp, he (a + rep q), map_smul, map_smul, hℓ, hℓ]`. Distinguish the cases in `hq : P q`. Establish `hA1 : a + rep q ∈ A` using `A.add_mem ha (hrepA q hq)`.

Establish `hq' : P (Submodule.Quotient.mk (a + rep q))` using `⟨_, hA1, rfl⟩`. Rewrite using `[if_pos hq, if_pos hq', hwA a ha _ (hrepA q hq), hwA _ hA1 _ (A.sub_mem (hrepA _ hq') hA1)]`. Simplify using the standard rewrite rules. Establish `hq' : ¬ P (Submodule.Quotient.mk (a + rep q))`. Introduce and unpack `⟨c, hc, hce⟩`.

Apply `hq` to reduce the goal to its premises. Use `⟨c - a, A.sub_mem hc ha, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.mk_sub, hce, ← Submodule.Quotient.mk_sub, add_sub_cancel_left, hrep]`. Rewrite using `[if_neg hq, if_neg hq']`. Simplify using the standard rewrite rules.

Conclude with `LinearMap.congr_fun hext v`.
-/
theorem exists_linearForm_invariant_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs hfix hspan A hA
  have key : ∀ z y, y - z ∈ Λ → W z s = γ (w • z) (y - z) • W y s := by
    intro z y hyz
    have h1 := h.comp z (y - z) s
    rwa [hfix _ hyz, add_sub_cancel] at h1
  let P : X ⧸ Λ → Prop := fun q => ∃ a ∈ A, (Submodule.Quotient.mk a : X ⧸ Λ) = q
  let rep : X ⧸ Λ → X := fun q => if hq : P q then hq.choose else Quotient.out q
  have hrep : ∀ q, (Submodule.Quotient.mk (rep q) : X ⧸ Λ) = q := by
    intro q
    by_cases hq : P q
    · simp only [rep, dif_pos hq]; exact hq.choose_spec.2
    · simp only [rep, dif_neg hq]; exact Quotient.out_eq q
  have hrepA : ∀ q, P q → rep q ∈ A := by
    intro q hq
    simp only [rep, dif_pos hq]; exact hq.choose_spec.1
  let e : X ⧸ Λ → M := fun q => W (rep q) s
  have he : ∀ z, W z s = γ (w • z) (rep (Submodule.Quotient.mk z) - z) • e (Submodule.Quotient.mk z) := by
    intro z
    exact key z _ ((Submodule.Quotient.eq Λ).1 (hrep _))
  have hli : LinearIndependent ℂ e := by
    refine linearIndependent_of_simultaneous_eigen e (fun q (l : Λ) => γ l (rep q)) (fun l : Λ => W l) ?_ ?_ ?_
    · intro q q' hq
      have hm : rep q - rep q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (rep q) = γ a (rep q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← hrep q, ← hrep q']
      exact (Submodule.Quotient.eq Λ).2 hm
    · intro l q
      show W l (W (rep q) s) = γ l (rep q) • W (rep q) s
      rw [h.comm, hfix l l.2]
    · intro q h0
      have h1 := h.neg_comp (rep q) s
      rw [show W (rep q) s = 0 from h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [he z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  let ℓ : M →ₗ[ℂ] ℂ := b.constr ℂ (fun q => if P q then (1 : ℂ) else 0)
  have hℓ : ∀ q, ℓ (e q) = if P q then (1 : ℂ) else 0 := by
    intro q
    have := b.constr_basis ℂ (fun q => if P q then (1 : ℂ) else 0) q
    rwa [Module.Basis.mk_apply] at this
  have hwA : ∀ a ∈ A, ∀ b ∈ A, γ (w • a) b = 1 := fun a ha b hb => hA _ (A.smul_mem w ha) b hb
  refine ⟨ℓ, ?_, ?_⟩
  · have h0 : P (Submodule.Quotient.mk 0) := ⟨0, A.zero_mem, rfl⟩
    have h1 := he 0
    rw [h.zero, hwA 0 A.zero_mem _ (A.sub_mem (hrepA _ h0) A.zero_mem), one_smul] at h1
    rw [h1, hℓ, if_pos h0]
  · intro a ha v
    have hext : ℓ ∘ₗ W a = ℓ := by
      refine b.ext fun q => ?_
      rw [Module.Basis.mk_apply, LinearMap.comp_apply]
      show ℓ (W a (W (rep q) s)) = ℓ (e q)
      rw [h.comp, he (a + rep q), map_smul, map_smul, hℓ, hℓ]
      by_cases hq : P q
      · have hA1 : a + rep q ∈ A := A.add_mem ha (hrepA q hq)
        have hq' : P (Submodule.Quotient.mk (a + rep q)) := ⟨_, hA1, rfl⟩
        rw [if_pos hq, if_pos hq', hwA a ha _ (hrepA q hq), hwA _ hA1 _ (A.sub_mem (hrepA _ hq') hA1)]
        simp
      · have hq' : ¬ P (Submodule.Quotient.mk (a + rep q)) := by
          rintro ⟨c, hc, hce⟩
          apply hq
          refine ⟨c - a, A.sub_mem hc ha, ?_⟩
          rw [Submodule.Quotient.mk_sub, hce, ← Submodule.Quotient.mk_sub, add_sub_cancel_left, hrep]
        rw [if_neg hq, if_neg hq']
        simp
    exact LinearMap.congr_fun hext v

end GlobalTheory.SphTheta
