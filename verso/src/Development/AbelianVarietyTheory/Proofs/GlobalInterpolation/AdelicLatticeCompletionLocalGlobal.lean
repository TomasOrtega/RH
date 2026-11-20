import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIffStatement

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.LatLocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

/- English proof (translation)
Take `⟨m, l, -, hl⟩` from `GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ`. Establish `hv : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Fin k → E ⊗[F] v.adicCompletion F), w ∈ locLat v Λ ↔ ∃ t : Fin m → v.adicCompletion F, (∀ j, t j ∈ (v.adicCompletionIntegers F).toSubring) ∧ w = fun i => ∑ j, l j i ⊗ₜ[F] t j` using `fun v w => hl _ _ w`. Rewrite using `[hl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩ v`.

Use `(hv v _).2 ⟨fun j => t j v, fun j => ht j v, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => Formalism.UG.P.afsplit_prV_tmul v _ _`. Introduce `h choose t ht hu using fun v => (hv v _).1 (h v)`.

Set `s : Fin m → FiniteAdeleRing (𝓞 F) F` to `fun j => ⟨fun v => t v j, Filter.Eventually.of_forall fun v => ht v j⟩`. Use `⟨s, fun j v => ht v j, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Use `Formalism.UG.P.afsplit_inj _ fun v => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, sub_eq_zero, map_sum]`. Use `(congrFun (hu v) i).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun j _ => (Formalism.UG.P.afsplit_prV_tmul v (l j i) (s j)).symm`.
-/
theorem mem_latS_adele_iff (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ := by
  obtain ⟨m, l, -, hl⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  have hv : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Fin k → E ⊗[F] v.adicCompletion F),
      w ∈ locLat v Λ ↔ ∃ t : Fin m → v.adicCompletion F,
        (∀ j, t j ∈ (v.adicCompletionIntegers F).toSubring) ∧ w = fun i => ∑ j, l j i ⊗ₜ[F] t j :=
    fun v w => hl _ _ w
  rw [hl]
  constructor
  · rintro ⟨t, ht, rfl⟩ v
    refine (hv v _).2 ⟨fun j => t j v, fun j => ht j v, ?_⟩
    funext i
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => Formalism.UG.P.afsplit_prV_tmul v _ _
  · intro h
    choose t ht hu using fun v => (hv v _).1 (h v)
    let s : Fin m → FiniteAdeleRing (𝓞 F) F := fun j =>
      ⟨fun v => t v j, Filter.Eventually.of_forall fun v => ht v j⟩
    refine ⟨s, fun j v => ht v j, ?_⟩
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    rw [map_sub, sub_eq_zero, map_sum]
    refine (congrFun (hu v) i).trans ?_
    exact Finset.sum_congr rfl fun j _ => (Formalism.UG.P.afsplit_prV_tmul v (l j i) (s j)).symm

/- English proof (translation)
Rewrite using `[← Formalism.UG.P.global_lattice_one_holds F E (Fin k) Λ hΛ hspan]`. Use `show ((1⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ`. Rewrite using `[inv_one, Units.val_one, one_mulVec, mem_latS_adele_iff Λ hΛ]`. Conclude with `hx`.
-/
theorem mem_of_forall_locLat (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (x : Fin k → E)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) : x ∈ Λ := by
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin k) Λ hΛ hspan]
  show ((1⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [inv_one, Units.val_one, one_mulVec, mem_latS_adele_iff Λ hΛ]
  exact hx

/- English proof (translation)
Set `Λ : Submodule (𝓞 E) (Fin 1 → E)` to `Submodule.span (𝓞 E) {fun _ => 1}`. Establish `h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ` using `Submodule.subset_span rfl`. Establish `hfin : Module.Finite (𝓞 E) Λ` using `Module.Finite.span_of_finite _ (Set.finite_singleton _)`. Establish `hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `: x = x 0 • (fun _ => 1 : Fin 1 → E)`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`. Use `mem_of_forall_locLat (F := F) Λ hfin hspan (fun _ => a) fun v => by` as an intermediate fact. Establish `h2 : (fun _ => inclE (F` using `F) (v.adicCompletion F) (1 : E)) ∈ locLat v Λ := Submodule.subset_span ⟨_, h1, rfl⟩`. Establish `h3` using `(locLat v Λ).smul_mem (⟨_, ha v⟩ : intV E v) h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `show _ = inclE (F := F) (v.adicCompletion F) a * inclE (F := F) (v.adicCompletion F) (1 : E)`. Rewrite using `[map_one, mul_one]`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 this`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrFun hc 0` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`.
-/
theorem mem_range_of_forall_intV (a : E)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) :
    a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have := mem_of_forall_locLat (F := F) Λ hfin hspan (fun _ => a) fun v => by
    have h2 : (fun _ => inclE (F := F) (v.adicCompletion F) (1 : E)) ∈ locLat v Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := (locLat v Λ).smul_mem (⟨_, ha v⟩ : intV E v) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (v.adicCompletion F) a * inclE (F := F) (v.adicCompletion F) (1 : E)
    rw [map_one, mul_one]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ Λ hΛ` and use `⟨mem_latS_adele_iff Λ hΛ, mem_of_forall_locLat Λ hΛ, mem_range_of_forall_intV⟩`.
-/
theorem latS_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range :=
  fun _ _ _ _ _ _ _ _ Λ hΛ =>
    ⟨mem_latS_adele_iff Λ hΛ, mem_of_forall_locLat Λ hΛ, mem_range_of_forall_intV⟩

end GlobalTheory.LatLocGlob
