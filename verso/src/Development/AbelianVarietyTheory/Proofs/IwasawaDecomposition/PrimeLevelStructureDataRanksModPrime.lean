import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.LRank

open scoped TensorProduct in

/- English proof (translation)
Establish `: IsArtinianRing (R ⧸ I)` using `isArtinian_of_finite`. Take `⟨b⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N) (fun P => by`. Use `P.isMaximal` as an intermediate fact. Set `: Field ((R ⧸ I) ⧸ P.asIdeal)` to `Ideal.Quotient.field _`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥`. Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]`. Conclude with `h1)`. Rewrite using `[← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]`.
-/
theorem natCard_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

/- English proof (translation)
Establish `: IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype`. Use `⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩` and prove the remaining obligations. Use `isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s`. Establish `hy : y ∈ Submodule.span K (p : Set V)` using `h ▸ Submodule.mem_top`.

Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, ht⟩, t), rfl⟩`. Rewrite using `[← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl, IsFractionRing.finrank_right_eq (𝓞 K) K V]`.
-/
theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

/- English proof (translation)
Establish `h1 : 1 < Nat.card F` using `Finite.one_lt_card`. Establish `: Finite V` using `Nat.finite_of_card_ne_zero (by rw [h]; positivity)`. Establish `: Module.Finite F V` using `Module.Finite.of_finite`. Establish `h2` using `Module.natCard_eq_pow_finrank (K := F) (V := V)`. Rewrite `h2` using `[h]`.

Conclude with `(Nat.pow_right_injective h1 h2).symm`.
-/
theorem finrank_of_card {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {n : ℕ}
    (h : Nat.card V = Nat.card F ^ n) : Module.finrank F V = n := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite F V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := F) (V := V)
  rw [h] at h2
  exact (Nat.pow_right_injective h1 h2).symm

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) N` using `Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))`. Establish `: Module.FinitePresentation (𝓞 E) N` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Flat (𝓞 E) N` using `inferInstance`. Establish `: Module.Projective (𝓞 E) N` using `Module.Flat.projective_of_finitePresentation`. Establish `: Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`.

Establish `hr : Module.finrank (𝓞 E) N = n`. Simplify using `using finrank_of_span_top N hN.span_eq_top`. Establish `h` using `natCard_quot (R := 𝓞 E) (N := N) P.asIdeal`. Rewrite `h` using `[hr]`. Conclude with `finrank_of_card (F := Res P) h`.
-/
theorem finrank_red {E : Type} [Field E] [NumberField E] {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsLattice E N) (P : HeightOneSpectrum (𝓞 E)) :
    Module.finrank (Res P) (TDat.Red N P) = n := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    simpa using finrank_of_span_top N hN.span_eq_top
  have h := natCard_quot (R := 𝓞 E) (N := N) P.asIdeal
  rw [hr] at h
  exact finrank_of_card (F := Res P) h

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `E K _ _ _ _ n S ST A T _ h`. Conclude with `⟨fun P c => finrank_red _ (h.N_lat _ _) P.1, fun P c => finrank_red _ (h.dnN_lat _ _ P) P.1⟩`.
-/
theorem ranks : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  intro E K _ _ _ _ n S ST A T _ h
  exact ⟨fun P c => finrank_red _ (h.N_lat _ _) P.1, fun P c => finrank_red _ (h.dnN_lat _ _ P) P.1⟩

end GlobalTheory.Mem.Col2.LRank
