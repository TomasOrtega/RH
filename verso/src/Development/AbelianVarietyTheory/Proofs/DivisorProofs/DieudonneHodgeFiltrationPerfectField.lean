import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobeniusStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

/- English proof (translation)
Use `letI := (frobRing (p_eq_zero p k)).toAlgebra`. Introduce `t`. Take `⟨x, rfl⟩` from `(omega_baseChange_bijective G k (p_eq_zero p k)).2 t`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩`. Consider the case `tmul r w`.

Use `⟨(frobeniusEquiv k p).symm r • w, ?_⟩` and prove the remaining obligations. Rewrite using `[liftSemi_tmul, map_smulₛₗ]`. Use `congr 1`. Use `show frobRing (p_eq_zero p k) _ = r`. Rewrite using `[frobRing_apply, frobeniusEquiv_symm_pow_p]`.
-/
theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Introduce `p _ T k _ _ _ G`. Take `⟨-, hVinj, hVsm, -, -⟩` from `GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G`. Take `⟨hbij, -, -⟩` from `GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G`. Take `⟨-, -, -, hver, -, -, -⟩` from `rigExt_field_of_charP p k (p_eq_zero p k) G`. Establish `key : ∀ m, (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) = rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m)`.

Introduce `m`. Rewrite using `[← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]`. Rewrite using `[← SemiHom.ofHom_rig]`. Conclude with `T.base.red_smap trivial trivial (SemiHom.ofHom _) m`. Establish `rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨m, rfl⟩` from `T.base.red_surjective G trivial x`. Rewrite `hx` using `[← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), T.base.red_eq_zero]`. Take `⟨n, hn⟩` from `hx`.

Take `⟨n', rfl⟩` from `hbij.2 n`. Establish `hm : m = p • n'` using `hbij.1 (by rw [hn, map_nsmul])`. Conclude with `(T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩`. Establish `osurj` using `frobProj_omega_surjective G`. Establish `h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, rfl⟩`. Establish `hm : (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) ∈ LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega`. Rewrite using `[key, ← hver]`.

Conclude with `⟨_, rfl⟩`. Take `⟨w', hw'⟩` from `hm`. Take `⟨w, rfl⟩` from `osurj w'`. Conclude with `⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩`. Introduce and unpack `⟨w, rfl⟩`.

Establish `hw : (frobTwist (p_eq_zero p k) G).rigOfOmega ((frobProj (p_eq_zero p k) G).omega w) ∈ LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G))`. Rewrite using `[hver]`. Conclude with `⟨_, rfl⟩`. Take `⟨y, hy⟩` from `hw`. Take `⟨m, rfl⟩` from `T.base.red_surjective G trivial y`.

Conclude with `⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩`. Establish `h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n`. Introduce `m`. Use `(T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hn]`.

Conclude with `(T.V_F G n).symm`. Rewrite using `[hn]`. Conclude with `T.V_F G n`. Use `⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩` and prove the remaining obligations. Rewrite using `[G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Take `⟨m', hm'⟩` from `(h1 _).2 (by simpa using hm)`. Establish `h0 : T.red G (m - T.V G m') = 0` using `by rw [map_sub, hm', sub_self]`. Take `⟨n, hn⟩` from `(T.base.red_eq_zero G trivial _).1 h0`.

Use `⟨m' + T.F G n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, T.V_F G n, ← hn, add_sub_cancel]`. Introduce and unpack `⟨n, rfl⟩`. Take `⟨w, hw⟩` from `(h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩`. Conclude with `⟨w, hw⟩`.
-/
theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), T.base.red_eq_zero] at hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega ((frobProj (p_eq_zero p k) G).omega w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 (by simpa using hm)
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add, T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
