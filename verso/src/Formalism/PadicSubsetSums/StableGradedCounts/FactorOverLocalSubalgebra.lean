import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `O _ _ X' _ T hT t c F s hF hs`. Use `hT` as an intermediate fact. Set `c' : T` to `algebraMap O T c`. Establish `hev_c : ∀ x, ev T x c' = c` using `fun x => by simp [ev, c']`. Establish `hq : ((X - C c') ^ t : T[X]).Monic` using `(monic_X_sub_C c').pow t`.

Establish `hqO : ((X - C c) ^ t : O[X]).Monic` using `(monic_X_sub_C c).pow t`. Establish `hqmap : ∀ x, ((X - C c') ^ t : T[X]).map (ev T x) = (X - C c) ^ t`. Introduce `x`. Rewrite using `[Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hev_c]`. Establish `hR : F %ₘ (X - C c') ^ t = 0`.

Use extensionality with `n x`. Establish `h1 : (F %ₘ (X - C c') ^ t).map (ev T x) = 0`. Rewrite using `[map_modByMonic _ hq, hqmap, hF, (modByMonic_eq_zero_iff_dvd hqO).mpr (dvd_mul_left _ _)]`. Establish `h2` using `congrArg (fun p => p.coeff n) h1`. Simplify `h2` using `[Polynomial.coeff_map, ev]`.

Establish `hmapP : ∀ x, (F /ₘ (X - C c') ^ t).map (ev T x) = s x`. Introduce `x`. Rewrite using `[map_divByMonic _ hq, hqmap, hF, mul_comm, mul_divByMonic_cancel_left _ hqO]`. Use `⟨F /ₘ (X - C c') ^ t, ?_, ?_, hmapP⟩` and prove the remaining obligations. Establish `h` using `modByMonic_add_div F ((X - C c') ^ t)`.

Rewrite `h` using `[hR, zero_add]`. Rewrite using `[mul_comm]`. Conclude with `h.symm`. Choose the witnesses or unpack the hypotheses as in `⟨x⟩ : Nonempty X' := by`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_nonempty_iff]`. Establish `hsub : Subsingleton T` using `⟨fun a b => Subtype.ext (funext fun x => (IsEmpty.false x).elim)⟩`. Conclude with `not_subsingleton T hsub`. Use `IsLocalHom.of_surjective (ev T x) (fun o => ⟨algebraMap O T o, by simp [ev]⟩)` as an intermediate fact. Apply `isUnit_of_map_unit (ev T x)` to reduce the goal to its premises.

Rewrite using `[← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmapP, hev_c]`. Conclude with `hs x`.
-/
theorem factorOverLocalSubalgebra : FactorOverLocalSubalgebra := by
  intro O _ _ X' _ T hT t c F s hF hs
  have := hT
  let c' : T := algebraMap O T c
  have hev_c : ∀ x, ev T x c' = c := fun x => by simp [ev, c']
  have hq : ((X - C c') ^ t : T[X]).Monic := (monic_X_sub_C c').pow t
  have hqO : ((X - C c) ^ t : O[X]).Monic := (monic_X_sub_C c).pow t
  have hqmap : ∀ x, ((X - C c') ^ t : T[X]).map (ev T x) = (X - C c) ^ t := by
    intro x
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hev_c]
  have hR : F %ₘ (X - C c') ^ t = 0 := by
    ext n x
    have h1 : (F %ₘ (X - C c') ^ t).map (ev T x) = 0 := by
      rw [map_modByMonic _ hq, hqmap, hF, (modByMonic_eq_zero_iff_dvd hqO).mpr (dvd_mul_left _ _)]
    have h2 := congrArg (fun p => p.coeff n) h1
    simpa [Polynomial.coeff_map, ev] using h2
  have hmapP : ∀ x, (F /ₘ (X - C c') ^ t).map (ev T x) = s x := by
    intro x
    rw [map_divByMonic _ hq, hqmap, hF, mul_comm, mul_divByMonic_cancel_left _ hqO]
  refine ⟨F /ₘ (X - C c') ^ t, ?_, ?_, hmapP⟩
  · have h := modByMonic_add_div F ((X - C c') ^ t)
    rw [hR, zero_add] at h
    rw [mul_comm]
    exact h.symm
  · obtain ⟨x⟩ : Nonempty X' := by
      by_contra h
      rw [not_nonempty_iff] at h
      have hsub : Subsingleton T := ⟨fun a b => Subtype.ext (funext fun x => (IsEmpty.false x).elim)⟩
      exact not_subsingleton T hsub
    have := IsLocalHom.of_surjective (ev T x) (fun o => ⟨algebraMap O T o, by simp [ev]⟩)
    apply isUnit_of_map_unit (ev T x)
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmapP, hev_c]
    exact hs x

end Formalism.IrreducibleCountingLemmas.Z
