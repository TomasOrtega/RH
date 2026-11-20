import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

set_option autoImplicit false

open Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.WeylBasis

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [map_zsmul]`. Conclude with `zsmul_mem hy a`.
-/
theorem map_mem_span {σ ι : Type} (R : Type) [CommRing R] (g : ι → MvPolynomial σ ℤ) {f : MvPolynomial σ ℤ}
    (hf : f ∈ Submodule.span ℤ (Set.range g)) :
    MvPolynomial.map (Int.castRingHom R) f ∈
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (g i)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a

/- English proof (translation)
Take `⟨c, hc, -⟩` from `sSBasis ℤ n n ν`. Establish `: Finite (ssIdx n n ν)` using `(sSIdxFinite n n ν).to_subtype`. Establish `: Module.Finite ℤ (dualWeyl ℤ n n ν)`. Rewrite using `[← hc.2.1]`. Conclude with `Module.Finite.span_of_finite ℤ (Set.finite_range c)`.

Conclude with `Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ n n le_rfl ν hν)) (Submodule.inclusion_injective _)`.
-/
theorem weyl_finite (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) : Module.Finite ℤ (weyl ℤ n n le_rfl ν) := by
  obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
  have : Finite (ssIdx n n ν) := (sSIdxFinite n n ν).to_subtype
  have : Module.Finite ℤ (dualWeyl ℤ n n ν) := by
    rw [← hc.2.1]
    exact Module.Finite.span_of_finite ℤ (Set.finite_range c)
  exact Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ n n le_rfl ν hν))
    (Submodule.inclusion_injective _)

/- English proof (translation)
Introduce `n ν hν`. Use `weyl_finite n ν hν` as an intermediate fact. Establish `: Module.Free ℤ (weyl ℤ n n le_rfl ν)` using `inferInstance`. Set `B` to `Module.Free.chooseBasis ℤ (weyl ℤ n n le_rfl ν)`. Establish `hspan : Submodule.span ℤ (Set.range fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ)) = weyl ℤ n n le_rfl ν`.

Establish `h` using `congrArg (Submodule.map (weyl ℤ n n le_rfl ν).subtype) B.span_eq`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]`. Conclude with `h`. Establish `hR : ∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (B i : MvPolynomial (Fin n × Fin n) ℤ))`. Introduce `R _`.

Apply `le_antisymm` to reduce the goal to its premises. Unfold `weyl`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw' : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ n n le_rfl ν` using `Submodule.subset_span ⟨w, rfl⟩`.

Rewrite `hw'` using `[← hspan]`. Establish `h` using `map_mem_span R _ hw'`. Rewrite `h` using `[← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Conclude with `h`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h` using `map_mem_span R (fun w : List (Fin n × Fin n × ℕ) => applyWord ℤ w (hw ℤ le_rfl ν)) (B i).2`. Simplify using `only [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h`. Conclude with `h`. Use `⟨_, inferInstance, fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ), ?_, hR, ?_⟩` and prove the remaining obligations.

Conclude with `B.linearIndependent.map' (weyl ℤ n n le_rfl ν).subtype (Submodule.ker_subtype _)`. Introduce `K _ _`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨c, hc, -⟩` from `sSBasis ℤ n n ν`. Rewrite using `[← span_map_weightBasis_eq_dualWeyl (K := K) hc, Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Establish `hj : c j ∈ dualWeyl ℤ n n ν` using `hc.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩`. Take `⟨m, hm, hmj⟩` from `weylRational n n le_rfl ν hν _ hj`. Rewrite `hmj` using `[← hspan]`. Establish `h` using `map_mem_span K _ hmj`.

Rewrite `h` using `[map_zsmul, ← Int.cast_smul_eq_zsmul K]`. Conclude with `(Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hm)).1 h`. Rewrite using `[← hR K]`. Conclude with `weylLeDual K n n le_rfl ν hν`.
-/
theorem exists_weyl_basis : ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∃ (P : Type) (_ : Fintype P) (b : P → MvPolynomial (Fin n × Fin n) ℤ), LinearIndependent ℤ b ∧ (∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (b i))) ∧ ∀ (K : Type) [Field K] [CharZero K], dualWeyl K n n ν = Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (b i)) := by
  intro n ν hν
  have := weyl_finite n ν hν
  have : Module.Free ℤ (weyl ℤ n n le_rfl ν) := inferInstance
  let B := Module.Free.chooseBasis ℤ (weyl ℤ n n le_rfl ν)
  have hspan : Submodule.span ℤ (Set.range fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ)) = weyl ℤ n n le_rfl ν := by
    have h := congrArg (Submodule.map (weyl ℤ n n le_rfl ν).subtype) B.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h
    exact h
  have hR : ∀ (R : Type) [CommRing R], weyl R n n le_rfl ν =
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (B i : MvPolynomial (Fin n × Fin n) ℤ)) := by
    intro R _
    apply le_antisymm
    · unfold weyl
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      have hw' : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ n n le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
      rw [← hspan] at hw'
      have h := map_mem_span R _ hw'
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h := map_mem_span R (fun w : List (Fin n × Fin n × ℕ) => applyWord ℤ w (hw ℤ le_rfl ν)) (B i).2
      simp only [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
  refine ⟨_, inferInstance, fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ), ?_, hR, ?_⟩
  · exact B.linearIndependent.map' (weyl ℤ n n le_rfl ν).subtype (Submodule.ker_subtype _)
  · intro K _ _
    apply le_antisymm
    · obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
      rw [← span_map_weightBasis_eq_dualWeyl (K := K) hc, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : c j ∈ dualWeyl ℤ n n ν := hc.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨m, hm, hmj⟩ := weylRational n n le_rfl ν hν _ hj
      rw [← hspan] at hmj
      have h := map_mem_span K _ hmj
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul K] at h
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hm)).1 h
    · rw [← hR K]
      exact weylLeDual K n n le_rfl ν hν

end GlobalTheory.WeylBasis
