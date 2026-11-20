import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSplitInjectiveAndExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactEigenSubDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwistStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualEigenSubDegreeTransposeStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.ConjEq

/- English proof (translation)
Use `haveI : Nonempty S := ⟨s⟩`. Take `⟨m, hm⟩` from `Finite.exists_max (fun s => |h s|)`. Take `⟨u, hu⟩` from `H m`. Establish `h1 : |h u| = p * |h m|`. Rewrite using `[hu, abs_mul, Nat.abs_cast]`.

Establish `h2 : |h u| ≤ |h m|` using `hm u`. Establish `h3 : (2 : ℤ) ≤ p` using `by exact_mod_cast hp`. Establish `h4 : |h m| = 0`. Establish `h5 : 0 ≤ |h m|` using `abs_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h6 : |h s| ≤ 0` using `h4 ▸ hm s`. Conclude with `abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))`.
-/
theorem eq_zero_of_scale {S : Type} [Finite S] (h : S → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (H : ∀ s, ∃ u, h u = p * h s) (s : S) : h s = 0 := by
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun s => |h s|)
  obtain ⟨u, hu⟩ := H m
  have h1 : |h u| = p * |h m| := by
    rw [hu, abs_mul, Nat.abs_cast]
  have h2 : |h u| ≤ |h m| := hm u
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have h4 : |h m| = 0 := by
    have h5 : 0 ≤ |h m| := abs_nonneg _
    nlinarith
  have h6 : |h s| ≤ 0 := h4 ▸ hm s
  exact abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))

variable {K : Type} [Field K]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [eig, Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce `H a`. Use `H (star a)` as an intermediate fact.

Rewrite `this` using `[star_star, ← h]`. Then use the resulting hypothesis. Introduce `H a`. Use `H (star a)` as an intermediate fact. Rewrite `this` using `[h, star_star]`. Then use the resulting hypothesis.
-/
theorem eig_star {O V : Type} [CommRing O] [StarRing O] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ χ' : O → K) (h : ∀ a, χ' a = χ (star a)) :
    eig (fun a => ρ (star a)) χ = eig ρ χ' := by
  ext x
  simp only [eig, Submodule.mem_iInf]
  constructor
  · intro H a
    have := H (star a)
    rwa [star_star, ← h] at this
  · intro H a
    have := H (star a)
    rwa [h, star_star] at this

section Data

variable (C : ACurve K) {p : ℕ} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (D : ConjData C p O d)

/- English proof (translation)
Introduce `i x hx`. Take `⟨y, hy, rfl⟩` from `(D.hodge.2.2.2.2 i x).1 hx`. Use `(D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩` and prove the remaining obligations. Simplify using `using D.ρH_fst a y`.
-/
theorem lie_hom (a : O) : IsHom C D.lie D.lie (Matrix.toLin' (D.ρ a)) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  refine (D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩
  simpa using D.ρH_fst a y

/- English proof (translation)
The claim follows from `(deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1`.
-/
theorem dual_bun : IsBun C (dotDual C D.lie) :=
  (deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1

variable {k S : Type} [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k))

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _) (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge (fun a x => by simpa using …`. Establish `h2` using `eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose) (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a)) (fun a => by rw [hst])`. Establish `h3` using `GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t`. Rewrite using `[h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hodge_eq (hχ : IsSplit χ) (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t : S)
    (hst : ∀ a, χ t a = χ s (star a)) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))) =
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _)
    (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH
    (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge
    (fun a x => by simpa using (D.ρH_inr a x).symm) (fun a y => by simpa using D.ρH_fst a y) s
  have h2 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h3 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, h2, h3]
  ring

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie)) D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj (fun a x …`. Establish `hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p`. Use function extensionality and compare the values at `a`. Rewrite using `[hu, map_pow]`. Establish `h2` using `GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))`.

Establish `h3` using `GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose) (fun a => algebraMap k K (χ s a))`. Establish `h4` using `eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose) (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a)) (fun a => by rw [hst])`. Establish `h5` using `GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t`. Rewrite using `[h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun, SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_eq [Fact p.Prime] [CharP K p] (hχ : IsSplit χ)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t u : S)
    (hst : ∀ a, χ t a = χ s (star a)) (hu : ∀ a, χ u a = χ s a ^ p) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ u a))) =
      p * (subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a)))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie))
    D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH
    (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj
    (fun a x => by simpa using D.α_act a x) (fun a y => by simpa using D.β_act a y) u
  have hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p := by
    funext a
    rw [hu, map_pow]
  have h2 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))
  have h3 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose)
    (fun a => algebraMap k K (χ s a))
  have h4 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h5 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]
  ring

end Data

/- English proof (translation)
Introduce `K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst`. Establish `hp : p.Prime` using `Fact.out`. Use `haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p`. Use `haveI : ExpChar k p := ExpChar.prime hp`. Establish `hall` using `(isSplit_injective_and_exists O k S χ hχ).2`.

Establish `hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a)` using `fun s => by`. Take `⟨t, ht⟩` from `hall ((χ s).comp (starRingEnd O))`. Conclude with `⟨t, fun a => by rw [ht]; rfl⟩`. Establish `hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p` using `fun s => by`. Take `⟨u, hu⟩` from `hall ((frobenius k p).comp (χ s))`.

Conclude with `⟨u, fun a => by rw [hu]; rfl⟩`. Establish `hzero` using `eq_zero_of_scale (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a)))) p hp.two_le (fun s => by`. Take `⟨t, ht⟩` from `hconj s`. Take `⟨u, hu⟩` from `hfrob s`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Rewrite using `[conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s`. Establish `h` using `hodge_eq C D χ hχ hk s t hst`. Rewrite `h` using `[hzero]`. Conclude with `sub_eq_zero.1 h.symm`.
-/
theorem subDeg_eig_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  intro K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst
  have hp : p.Prime := Fact.out
  haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hall := (isSplit_injective_and_exists O k S χ hχ).2
  have hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a) := fun s => by
    obtain ⟨t, ht⟩ := hall ((χ s).comp (starRingEnd O))
    exact ⟨t, fun a => by rw [ht]; rfl⟩
  have hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p := fun s => by
    obtain ⟨u, hu⟩ := hall ((frobenius k p).comp (χ s))
    exact ⟨u, fun a => by rw [hu]; rfl⟩
  have hzero := eq_zero_of_scale
    (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))))
    p hp.two_le (fun s => by
      obtain ⟨t, ht⟩ := hconj s
      obtain ⟨u, hu⟩ := hfrob s
      refine ⟨u, ?_⟩
      rw [conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s
  have h := hodge_eq C D χ hχ hk s t hst
  rw [hzero] at h
  exact sub_eq_zero.1 h.symm

end GlobalTheory.CompanionTheory.Ar.Crv.ConjEq
