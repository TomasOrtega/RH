import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingLoc

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime`. Consider the case `exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime`. Consider the case `(apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)`.
-/
theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)

open Formalism.MainNotions.TaylorLogMetric in

/- English proof (translation)
Introduce `D cc δ p N N' L L' hp hcc hA`. Establish `hL : StandardLatticesGL3.SD D L` using `hA.2.2.1`. Establish `hL' : StandardLatticesGL3.SD D L'` using `hA.2.2.2`. Take `⟨s, y, y', hy, hy', hexp⟩` from `GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'`. Set `Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E)` to `Submodule.span (𝓞 D.host.K) (Set.range y)`.

Establish `hYle : ∀ x ∈ Y, x ∈ YYl D L L'`. Introduce `x hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hx`. Conclude with `(YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)`. Establish `hYge : ∀ x ∈ YYl D L L', x ∈ Y`.

Introduce `x hx`. Establish `hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i)` using `fun i => GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)`. Use `choose t ht using hi`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [hexp x]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← ht]`. Both sides reduce to the same expression. Take `⟨r, b, hli, hb, hw⟩` from `exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))`. Use `set n : ℕ := Ideal.absNorm cc with hn`.

Establish `hn0 : n ≠ 0`. Introduce `h`. Rewrite `hcc` using `[h, Nat.coprime_zero_left]`. Conclude with `hp.one_lt.ne' hcc`. Establish `hnK : (n : D.host.K) ≠ 0` using `by exact_mod_cast hn0`.

Use `⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Use `hli.units_smul fun _ => Units.mk0 _ hnK` as an intermediate fact. Establish `e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b`. Use function extensionality and compare the values at `i`. Simplify using `[Units.smul_def, Nat.cast_smul_eq_nsmul]`.

Rewrite using `[e]`. Conclude with `this`. Use `⟨1, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, one_smul]`. Conclude with `nsmul_mem (hYle _ (hb i)) n`.

Take `⟨k, hk, hkw⟩` from `hw w (hYge w hwY)`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hkw`. Use `⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Both sides reduce to the same expression. Use `AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩, b i, hYle _ (hb i), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `τ j k`.

Express the relevant statement in the definitionally equal form `δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)`. Rewrite using `[Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]`.
-/
theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
