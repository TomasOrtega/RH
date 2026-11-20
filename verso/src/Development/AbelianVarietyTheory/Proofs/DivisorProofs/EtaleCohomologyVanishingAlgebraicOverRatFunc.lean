import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFuncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomologyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CdOne

open GroundTheory.ProfCoh

/- English proof (translation)
Set `A : Rep.{0} (ULift.{0} ℤ) G` to `Rep.trivial (ULift.{0} ℤ) G (ULift.{0} (ZMod q))`. Establish `hq0 : q ≠ 0` using `NeZero.ne q`. Establish `hA : ∀ a : A, q • a = 0` using `fun a => by`. Express the relevant statement in the definitionally equal form `(q • a : ULift.{0} (ZMod q)) = 0`. Use `ext`.

Simplify using the standard rewrite rules. Establish `htors : IsAddTorsion A` using `fun a => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, Nat.pos_of_ne_zero hq0, hA a⟩`. Establish `hsub : Subsingleton (cohomology A n)`. It suffices to establish `h' : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩`. Introduce `x`.

Use `eq_zero_of_primaryComponent_eq_bot q hq0 (fun ℓ hℓ hℓq => ?_) x (nsmul_cohomology_eq_zero A hA n x)` and prove the remaining obligations. Use `primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) A htors ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Set `e : A ≃+ (Rep.trivial (ZMod q) G (ZMod q) : Rep (ZMod q) G)` to `AddEquiv.ulift`. Conclude with `(cohomologyAddEquivOfEquiv (A := A) (A' := Rep.trivial (ZMod q) G (ZMod q)) e (fun _ _ => rfl) n).symm.injective.subsingleton`.
-/
theorem subsingleton_cohomology_trivial_zmod (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) [NeZero q]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → cdp ℓ G ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology (Rep.trivial (ZMod q) G (ZMod q)) n) := by
  let A : Rep.{0} (ULift.{0} ℤ) G := Rep.trivial (ULift.{0} ℤ) G (ULift.{0} (ZMod q))
  have hq0 : q ≠ 0 := NeZero.ne q
  have hA : ∀ a : A, q • a = 0 := fun a => by
    change (q • a : ULift.{0} (ZMod q)) = 0
    ext
    simp
  have htors : IsAddTorsion A := fun a =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, Nat.pos_of_ne_zero hq0, hA a⟩
  have hsub : Subsingleton (cohomology A n) := by
    suffices h' : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    refine eq_zero_of_primaryComponent_eq_bot q hq0 (fun ℓ hℓ hℓq => ?_) x
      (nsmul_cohomology_eq_zero A hA n x)
    refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) A htors ?_
    calc cdp ℓ G ≤ 1 := h ℓ hℓ hℓq
      _ < n := by exact_mod_cast (show 1 < n by omega)
  let e : A ≃+ (Rep.trivial (ZMod q) G (ZMod q) : Rep (ZMod q) G) := AddEquiv.ulift
  exact (cohomologyAddEquivOfEquiv (A := A) (A' := Rep.trivial (ZMod q) G (ZMod q)) e
    (fun _ _ => rfl) n).symm.injective.subsingleton

end GlobalTheory.EtC.CdOne

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `q _ k K _ _ _ _ _ hq n i hn`. Set `f : k →+* K` to `(algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))`. Establish `hq0 : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hqk : (q : k) ≠ 0`. Introduce `h0`.

Establish `: (q : K) = 0` using `by rw [← map_natCast f q, h0, map_zero]`. Conclude with `hq.ne_zero this`. Use `haveI : NeZero (q : k) := ⟨hqk⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic q k) (Polynomial.degree_cyclotomic_pos q k hq0).ne'`. Establish `hζk : IsPrimitiveRoot ζ q` using `(Polynomial.isRoot_cyclotomic_iff).1 hζ`.

Establish `hζK : IsPrimitiveRoot (f ζ) q` using `hζk.map_of_injective f.injective`. Establish `hroot : ∃ z : K, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0`. Use `⟨f ζ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hζK.isRoot_cyclotomic hq0`.

Take `⟨u⟩` from `GlobalTheory.T.tateTwistCohomology_spec_twist_independent q K hq hroot n i 0`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)`. Establish `hm : 2 ≤ m` using `by omega`. Set `Ω` to `SeparableClosure K`. Establish `hζΩ : IsPrimitiveRoot (algebraMap K Ω (f ζ)) q` using `hζK.map_of_injective (algebraMap K Ω).injective`.

Take `⟨e⟩` from `GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology q K Ω hq 0 (Rep.trivial (ZMod q) (Ω ≃ₐ[K] Ω) (ZMod q)) _ hζΩ (Module.Basis.singleton Unit (ZMod q)) (fun σ a _ => by simp) m`. Establish `hsub` using `GlobalTheory.EtC.CdOne.subsingleton_cohomology_trivial_zmod (Ω ≃ₐ[K] Ω) q (fun ℓ hℓ _ => GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc k K Ω ℓ hℓ) m hm`. Conclude with `(u.trans e).injective.subsingleton`.
-/
theorem gaugeSplitting_holds : C1 := by
  intro q _ k K _ _ _ _ _ hq n i hn
  let f : k →+* K := (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqk : (q : k) ≠ 0 := by
    intro h0
    have : (q : K) = 0 := by rw [← map_natCast f q, h0, map_zero]
    exact hq.ne_zero this
  haveI : NeZero (q : k) := ⟨hqk⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k hq0).ne'
  have hζk : IsPrimitiveRoot ζ q := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  have hζK : IsPrimitiveRoot (f ζ) q := hζk.map_of_injective f.injective
  have hroot : ∃ z : K, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨f ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζK.isRoot_cyclotomic hq0
  obtain ⟨u⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q K hq hroot n i 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  have hm : 2 ≤ m := by omega
  let Ω := SeparableClosure K
  have hζΩ : IsPrimitiveRoot (algebraMap K Ω (f ζ)) q :=
    hζK.map_of_injective (algebraMap K Ω).injective
  obtain ⟨e⟩ := GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology q K Ω hq 0 (Rep.trivial (ZMod q) (Ω ≃ₐ[K] Ω) (ZMod q)) _ hζΩ
    (Module.Basis.singleton Unit (ZMod q)) (fun σ a _ => by simp) m
  have hsub := GlobalTheory.EtC.CdOne.subsingleton_cohomology_trivial_zmod (Ω ≃ₐ[K] Ω) q
    (fun ℓ hℓ _ => GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc k K Ω ℓ hℓ) m hm
  exact (u.trans e).injective.subsingleton

end GlobalTheory.EtC
