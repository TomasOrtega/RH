import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Use `set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM`. Establish `: Module.Finite (v.adicCompletionIntegers F) M` using `Module.Finite.iff_fg.2 (basLat_fg v L hLat)`. Establish `: Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E)` using `Module.IsTorsionFree.of_smul_eq_zero fun r x h => by`. Establish `h' : (r : Fv F v) • x = 0` using `h`. Break down `smul_eq_zero.1 h' with h0 | h0` into its components or cases.

Conclude with `Or.inl (Subtype.ext h0)`. Conclude with `Or.inr h0`. Establish `: Module.Free (v.adicCompletionIntegers F) M` using `Module.free_of_finite_type_torsion_free'`. Set `bM` to `Module.finBasis (v.adicCompletionIntegers F) M`. Set `b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E` to `fun i => (bM i : _)`.

Establish `hli0 : LinearIndependent (v.adicCompletionIntegers F) b0` using `bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Establish `hli : LinearIndependent (Fv F v) b0` using `(LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0`. Establish `hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b0 i`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)`. Rewrite `h` using `[Submodule.coe_sum]`. Conclude with `h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2`. Use `⟨_, b0, hli, hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[← basSpan_top v L hLat, Submodule.span_le]`. Introduce `x hx`.

Take `⟨c, rfl⟩` from `(hmem x).1 hx`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem exists_basO (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    ∃ (m : ℕ) (b : Fin m → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      (∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i) ∧
      ⊤ ≤ Submodule.span (Fv F v) (Set.range b) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (basLat_fg v L hLat)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  refine ⟨_, b0, hli, hmem, ?_⟩
  rw [← basSpan_top v L hLat, Submodule.span_le]
  intro x hx
  obtain ⟨c, rfl⟩ := (hmem x).1 hx
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce and unpack `⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Take `⟨m, b, hli, hmem, hsp⟩` from `exists_basO v L hLat`. Establish `hm : m = 2 * n`.

Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`. Rewrite `h1` using `[Fintype.card_fin]`. Rewrite using `[← h1, Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hm` using the available equality. Conclude with `⟨b, hli, hmem⟩`.
-/
theorem latBasO_holds (a : ℕ) (Y : TupV (E := E) v n a) : LatBasO σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

/- English proof (translation)
The claim follows from `resIdx_holds v`.
-/
theorem resIdx_holds' : ResIdx v := resIdx_holds v

end PI.OmLocU
