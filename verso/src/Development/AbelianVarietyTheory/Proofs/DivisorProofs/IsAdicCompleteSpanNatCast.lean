import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.FinProjComplete

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, -, rfl⟩`. Conclude with `⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩`. Introduce and unpack `⟨m, rfl⟩`.

Conclude with `⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩`.
-/
theorem mem_span_pow_smul_top_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M) ↔ ∃ m : M, x = (p ^ n : ℕ) • m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, mem_span_pow_smul_top_iff]`.
-/
theorem smodEq_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M))] ↔
      ∃ m : M, x - y = (p ^ n : ℕ) • m := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]

end GlobalTheory.FinProjComplete

open GlobalTheory.FinProjComplete in
/- English proof (translation)
Introduce `p O A _ _ _ _ _ hO`. Take `⟨k, π, hπ⟩` from `Module.Finite.exists_fin' O A`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π (LinearMap.id) hπ`. Establish `hπs : ∀ a, π (s a) = a` using `fun a => by simpa using LinearMap.congr_fun hs a`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations.

Introduce `x hx`. Establish `hc : ∀ i, s x i = 0`. Introduce `i`. Apply `hO.toIsHausdorff.haus'` to reduce the goal to its premises. Introduce `n`.

Take `⟨m, hm⟩` from `(smodEq_iff p n x 0).1 (hx n)`. Rewrite using `[smodEq_iff]`. Use `⟨s m i, ?_⟩` and prove the remaining obligations. Rewrite `hm`, the goal using `[sub_zero]`. Rewrite using `[hm, map_nsmul, Pi.smul_apply]`.

Establish `: s x = 0` using `funext hc`. Rewrite using `[← hπs x, this, map_zero]`. Introduce `f hf`. Establish `hcoord : ∀ i, ∃ L : O, ∀ n, s (f n) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ n • (⊤ : Submodule O O))]`. Introduce `i`.

Apply `hO.toIsPrecomplete.prec'` to reduce the goal to its premises. Introduce `m n hmn`. Take `⟨c, hc⟩` from `(smodEq_iff p m (f m) (f n)).1 (hf hmn)`. Rewrite using `[smodEq_iff]`. Use `⟨s c i, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Pi.sub_apply, ← map_sub, hc, map_nsmul, Pi.smul_apply]`. Use `choose L hL using hcoord`. Use `⟨π L, fun n => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ i, ∃ c : O, s (f n) i - L i = (p ^ n : ℕ) • c` using `fun i => (smodEq_iff p n _ _).1 (hL i n)`. Use `choose c hc using hd`.

Rewrite using `[smodEq_iff]`. Use `⟨π c, ?_⟩` and prove the remaining obligations. Establish `hv : s (f n) - L = (p ^ n : ℕ) • c` using `funext fun i => by simpa using hc i`. Rewrite using `[← map_nsmul, ← hv, map_sub, hπs]`.
-/
theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  have hπs : ∀ a, π (s a) = a := fun a => by simpa using LinearMap.congr_fun hs a
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hc : ∀ i, s x i = 0 := by
      intro i
      apply hO.toIsHausdorff.haus'
      intro n
      obtain ⟨m, hm⟩ := (smodEq_iff p n x 0).1 (hx n)
      rw [smodEq_iff]
      refine ⟨s m i, ?_⟩
      rw [sub_zero] at hm ⊢
      rw [hm, map_nsmul, Pi.smul_apply]
    have : s x = 0 := funext hc
    rw [← hπs x, this, map_zero]
  · intro f hf
    have hcoord : ∀ i, ∃ L : O, ∀ n, s (f n) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ n • (⊤ : Submodule O O))] := by
      intro i
      apply hO.toIsPrecomplete.prec'
      intro m n hmn
      obtain ⟨c, hc⟩ := (smodEq_iff p m (f m) (f n)).1 (hf hmn)
      rw [smodEq_iff]
      refine ⟨s c i, ?_⟩
      rw [← Pi.sub_apply, ← map_sub, hc, map_nsmul, Pi.smul_apply]
    choose L hL using hcoord
    refine ⟨π L, fun n => ?_⟩
    have hd : ∀ i, ∃ c : O, s (f n) i - L i = (p ^ n : ℕ) • c := fun i => (smodEq_iff p n _ _).1 (hL i n)
    choose c hc using hd
    rw [smodEq_iff]
    refine ⟨π c, ?_⟩
    have hv : s (f n) - L = (p ^ n : ℕ) • c := funext fun i => by simpa using hc i
    rw [← map_nsmul, ← hv, map_sub, hπs]
