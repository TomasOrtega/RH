import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushoutStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Use `B.complete.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `hx n`.
-/
theorem eq_zero_of_mem_adI_pow {l : ℕ} {R : Type} [CommRing R] (B : Obj l R) (x : B.A)
    (hx : ∀ n : ℕ, x ∈ adI B ^ n) : x = 0 := by
  refine B.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact hx n

/- English proof (translation)
Introduce `l _ R _ B C h hc`. Establish `hinj : ∀ m : ℕ, Function.Injective (qmap h m)` using `fun m => RingHom.FaithfullyFlat.injective (hc.ff m)`. Establish `hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m` using `fun m b hb => by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Apply `hinj m` to reduce the goal to its premises.

Rewrite using `[qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hb`. Use `⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_` and prove the remaining obligations.

Rewrite using `[map_sub, hxy, sub_self]`. Conclude with `Ideal.zero_mem _`. Establish `happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m` using `fun m => by`. Establish `hd` using `(GlobalTheory.T.faithfullyFlat_descent_elements_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2 (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])`. Take `⟨b', hb'⟩` from `hd`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b'`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite `hb'` using `[qmap_mk, Ideal.Quotient.eq]`. Conclude with `hb'`. Use `choose b hb using happ`.

Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Use `hlev m _ ?_` and prove the remaining obligations. Establish `e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c)` using `by rw [map_sub]; ring`.

Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))`. Take `⟨L, hL⟩` from `B.complete.toIsPrecomplete.prec' b hcauchy`. Use `⟨L, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `eq_zero_of_mem_adI_pow C _ fun n => ?_` and prove the remaining obligations. Establish `h1 : b n - L ∈ adI B ^ n`. Use `hL n` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis. Establish `h2 : h.f (b n - L) ∈ adI C ^ n` using `adI_pow_le h n h1`.

Establish `e : h.f L - c = (h.f (b n) - c) - h.f (b n - L)` using `by rw [map_sub]; ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (hb n) h2`.
-/
theorem cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C),
    Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q →
      ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  intro l _ R _ B C h hc

  have hinj : ∀ m : ℕ, Function.Injective (qmap h m) := fun m =>
    RingHom.FaithfullyFlat.injective (hc.ff m)

  have hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m := fun m b hb => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj m
    rw [qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  refine ⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_
    rw [map_sub, hxy, sub_self]; exact Ideal.zero_mem _
  ·
    have happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m := fun m => by
      have hd := (GlobalTheory.T.faithfullyFlat_descent_elements_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2
        (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])
      obtain ⟨b', hb'⟩ := hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      refine ⟨b, ?_⟩
      rw [qmap_mk, Ideal.Quotient.eq] at hb'
      exact hb'
    choose b hb using happ
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine hlev m _ ?_
      have e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c) := by rw [map_sub]; ring
      rw [e]
      exact Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))
    obtain ⟨L, hL⟩ := B.complete.toIsPrecomplete.prec' b hcauchy
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow C _ fun n => ?_
    have h1 : b n - L ∈ adI B ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h2 : h.f (b n - L) ∈ adI C ^ n := adI_pow_le h n h1
    have e : h.f L - c = (h.f (b n) - c) - h.f (b n - L) := by rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (hb n) h2

end GlobalTheory.BSP
