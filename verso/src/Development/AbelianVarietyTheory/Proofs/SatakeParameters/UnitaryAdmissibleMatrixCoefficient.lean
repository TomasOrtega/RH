import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepresent

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise

namespace GlobalTheory.SmoothRiesz

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent`. Consider the case `exact _root_.GlobalTheory.ExistsRepresentation.exists_represent`. Consider the case `(apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)`.
-/
theorem exists_mem_eq_on_of_finiteDimensional {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  first
  | exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent
  | exact _root_.GlobalTheory.ExistsRepresentation.exists_represent
  | (apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)

/- English proof (translation)
Set `S : Set G` to `{g | σ g y = y}`. Establish `hSo : IsOpen S` using `hsm y`. Take `⟨t, ht⟩` from `hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _) (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)`. Use `((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`.

Take `⟨i, hi, hki⟩` from `Set.mem_iUnion₂.1 (ht hk)`. Take `⟨s, hs, rfl⟩` from `Set.mem_smul_set.1 hki`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Establish `hs' : σ s y = y` using `hs`. Simplify using `only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']`.
-/
theorem finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by
  let S : Set G := {g | σ g y = y}
  have hSo : IsOpen S := hsm y
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)
  refine ((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 hki
  refine ⟨i, hi, ?_⟩
  have hs' : σ s y = y := hs
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc`. Take `⟨u, huK, hu⟩` from `exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)`. Establish `hfix : ∀ k ∈ K, σ k u = u` using `fun k hk => by`. Simplify using `using huK ⟨k, hk⟩`. Use `⟨u, fun w => ?_⟩` and prove the remaining obligations.

Establish `hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x` using `fun a b x => by`. Rewrite using `[map_mul, Module.End.mul_apply]`. Set `O : Finset V` to `(finite_orbit σ hadm.1 K hKc w).toFinset`. Establish `hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x` using `fun x => by simp [O]`. Establish `hwO : w ∈ O` using `(hO w).2 ⟨1, K.one_mem, by simp⟩`.

Establish `hcard : ((O.card : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)`. Establish `heK : (∑ x ∈ O, x) ∈ fixed σ K`. Introduce `k`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]`. Use `Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨c, hc, rfl⟩` from `(hO x).1 hx`. Conclude with `(hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩`. Introduce `x hx`. Take `⟨c, hc, rfl⟩` from `(hO x).1 hx`.

Conclude with `(hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩`. Introduce `x _`. Rewrite using `[hcomp]`. Simplify using the standard rewrite rules. Introduce `x _`.

Rewrite using `[hcomp]`. Simplify using the standard rewrite rules. Introduce `x _`. Both sides reduce to the same expression. Establish `hLO : ∀ x ∈ O, L x = L w` using `fun x hx => by`.

Take `⟨c, hc, rfl⟩` from `(hO x).1 hx`. Conclude with `hL c hc w`. Establish `hBO : ∀ x ∈ O, Bf u x = Bf u w` using `fun x hx => by`. Take `⟨c, hc, rfl⟩` from `(hO x).1 hx`. Use `conv_lhs => rw [← hfix c hc]`.

Conclude with `hinv c u w`. Establish `key` using `hu _ heK`. Rewrite `key` using `[map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]`. Conclude with `mul_left_cancel₀ hcard key`.
-/
theorem exists_eq_of_invariant {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by
  haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc
  obtain ⟨u, huK, hu⟩ := exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)
  have hfix : ∀ k ∈ K, σ k u = u := fun k hk => by
    simpa using huK ⟨k, hk⟩
  refine ⟨u, fun w => ?_⟩
  have hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x := fun a b x => by
    rw [map_mul, Module.End.mul_apply]
  let O : Finset V := (finite_orbit σ hadm.1 K hKc w).toFinset
  have hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x := fun x => by simp [O]
  have hwO : w ∈ O := (hO w).2 ⟨1, K.one_mem, by simp⟩
  have hcard : ((O.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)
  have heK : (∑ x ∈ O, x) ∈ fixed σ K := by
    intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]
    refine Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rfl
  have hLO : ∀ x ∈ O, L x = L w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    exact hL c hc w
  have hBO : ∀ x ∈ O, Bf u x = Bf u w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    conv_lhs => rw [← hfix c hc]
    exact hinv c u w
  have key := hu _ heK
  rw [map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ hcard key

end GlobalTheory.SmoothRiesz

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL`. Establish `hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k))` using `hSo.inter SplitFlip.isOpen_KO`. Establish `hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k))` using `SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right`. Conclude with `SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc fun s hs => hL s hs.1`.
-/
theorem exists_vector_of_smooth_antilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  intro k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL
  have hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right
  exact SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc
    fun s hs => hL s hs.1

end GlobalTheory
