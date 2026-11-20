import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderFiniteProjectiveStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.OrdGen

/- English proof (translation)
Assume the negation of the conclusion as `hxy`. Take `⟨r, hr, hm⟩` from `hS (Pi.single x 1)`. Establish `h1` using `h ⟨_, hm⟩`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hxy), smul_zero, Algebra.smul_def, mul_one, mul_zero] at h1`. Conclude with `hr ((IsFractionRing.injective R K) (by simpa using h1))`.
-/
theorem eq_of_eval_eq {R K T : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R (T → K)) (hS : ∀ f : T → K, ∃ r : R, r ≠ 0 ∧ r • f ∈ S) {x y : T}
    (h : ∀ a : S, (a : T → K) x = (a : T → K) y) : x = y := by
  classical
  by_contra hxy
  obtain ⟨r, hr, hm⟩ := hS (Pi.single x 1)
  have h1 := h ⟨_, hm⟩
  simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hxy), smul_zero, Algebra.smul_def,
    mul_one, mul_zero] at h1
  exact hr ((IsFractionRing.injective R K) (by simpa using h1))

/- English proof (translation)
Use `Fintype.ofFinite T` as an intermediate fact. Establish `hinj` using `IsFractionRing.injective R K`. Use `choose r hr hm using fun x : T => hS (Pi.single x 1)`. Set `d : T → S` to `fun x => ⟨_, hm x⟩`. Establish `hd : ∀ x, (d x : T → K) = r x • Pi.single x 1` using `fun _ => rfl`.

Establish `hsum : ∑ x, (∏ y ∈ Finset.univ.erase x, r y) • d x = algebraMap R S (∏ y, r y)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Rewrite using `[AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single z]`. Rewrite using `[Subalgebra.coe_smul, hd, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ z)]`.

Simplify using `[Algebra.smul_def]`. Introduce `b _ hb`. Rewrite using `[Subalgebra.coe_smul, hd]`. Simplify using `[Pi.single_eq_of_ne (Ne.symm hb)]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ z) h`. Establish `hex : ∃ x, φ (d x) ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `h1` using `congrArg φ hsum`.

Rewrite `h1` using `[map_sum, φ.commutes]`. Simplify using `only [map_smul, hne, smul_zero, Finset.sum_const_zero] at h1`. Conclude with `Finset.prod_ne_zero_iff.2 (fun y _ => hr y) (hinj (by rw [← h1, map_zero]))`. Take `⟨x, hx⟩` from `hex`. Use `⟨x, fun a => ?_⟩` and prove the remaining obligations.

Take `⟨n, m, hm0, hnm⟩` from `IsFractionRing.div_surjective (A := R) ((a : T → K) x)`. Establish `hm1 : algebraMap R K m ≠ 0` using `fun h => nonZeroDivisors.ne_zero hm0 (hinj (by rw [h, map_zero]))`. Establish `hn : algebraMap R K n = algebraMap R K m * (a : T → K) x`. Rewrite using `[← hnm]`. Clear the denominators using the available nonvanishing facts.

Establish `key : m • (a * d x) = n • d x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Rewrite using `[Subalgebra.coe_smul, Subalgebra.coe_smul, Subalgebra.coe_mul, hd]`. Distinguish the cases in `hz : z = x`.

Substitute `hz` using the available equality. Simplify using `only [Pi.smul_apply, Pi.mul_apply, Algebra.smul_def, hn, _root_.mul_assoc]`. Simplify using `[Pi.single_eq_of_ne hz]`. Establish `h2` using `congrArg φ key`. Rewrite `h2` using `[map_smul, map_smul, map_mul, Algebra.smul_def, Algebra.smul_def, hn, _root_.mul_assoc]`.

Conclude with `mul_right_cancel₀ hx (mul_left_cancel₀ hm1 h2)`.
-/
theorem exists_eval {R K T : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Finite T]
    (S : Subalgebra R (T → K)) (hS : ∀ f : T → K, ∃ r : R, r ≠ 0 ∧ r • f ∈ S) (φ : S →ₐ[R] K) :
    ∃ x : T, ∀ a : S, φ a = (a : T → K) x := by
  classical
  have := Fintype.ofFinite T
  have hinj := IsFractionRing.injective R K
  choose r hr hm using fun x : T => hS (Pi.single x 1)
  let d : T → S := fun x => ⟨_, hm x⟩
  have hd : ∀ x, (d x : T → K) = r x • Pi.single x 1 := fun _ => rfl
  have hsum : ∑ x, (∏ y ∈ Finset.univ.erase x, r y) • d x = algebraMap R S (∏ y, r y) := by
    apply Subtype.ext
    funext z
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single z]
    · rw [Subalgebra.coe_smul, hd, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ z)]
      simp [Algebra.smul_def]
    · intro b _ hb
      rw [Subalgebra.coe_smul, hd]
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ z) h
  have hex : ∃ x, φ (d x) ≠ 0 := by
    by_contra hne
    push Not at hne
    have h1 := congrArg φ hsum
    rw [map_sum, φ.commutes] at h1
    simp only [map_smul, hne, smul_zero, Finset.sum_const_zero] at h1
    exact Finset.prod_ne_zero_iff.2 (fun y _ => hr y) (hinj (by rw [← h1, map_zero]))
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, fun a => ?_⟩
  obtain ⟨n, m, hm0, hnm⟩ := IsFractionRing.div_surjective (A := R) ((a : T → K) x)
  have hm1 : algebraMap R K m ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hm0 (hinj (by rw [h, map_zero]))
  have hn : algebraMap R K n = algebraMap R K m * (a : T → K) x := by
    rw [← hnm]; field_simp
  have key : m • (a * d x) = n • d x := by
    apply Subtype.ext
    funext z
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Subalgebra.coe_mul, hd]
    by_cases hz : z = x
    · subst hz
      simp only [Pi.smul_apply, Pi.mul_apply, Algebra.smul_def, hn, _root_.mul_assoc]
    · simp [Pi.single_eq_of_ne hz]
  have h2 := congrArg φ key
  rw [map_smul, map_smul, map_mul, Algebra.smul_def, Algebra.smul_def, hn, _root_.mul_assoc] at h2
  exact mul_right_cancel₀ hx (mul_left_cancel₀ hm1 h2)

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ io θ hθ`. Take `⟨Idx, _, q, c, hc⟩` from `GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN`. Establish `hfin : Finite (Tors G N K)`. Establish `: ∀ i, Finite ((c i).C →ₐ[R] K)` using `fun i => (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q i) (c i)).1`. Use `Finite.of_surjective (fun p : Σ i, ((c i).C →ₐ[R] K) => torsMap p.2 (c p.1).j) fun z => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hc K z`. Take `⟨ψ, -, hψ⟩` from `((c i).bij K).surjOn hi`. Conclude with `⟨⟨i, ψ⟩, hψ⟩`. Establish `hS` using `(GlobalTheory.T.torsion_order_finite_projective R K G hG N hN).2.2`. Use `⟨fun x y hxy => eq_of_eval_eq _ hS fun a => ?_, fun φ => ?_⟩` and prove the remaining obligations.

Take `⟨b, rfl⟩` from `io.surjective a`. Rewrite using `[← hθ, ← hθ, hxy]`. Take `⟨x, hx⟩` from `exists_eval _ hS (φ.comp (io.symm : ord G N K →ₐ[R] A))`. Use `⟨x, AlgHom.ext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hθ, ← hx]`.

Simplify using the standard rewrite rules.
-/
theorem pt_bijective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] (io : A ≃ₐ[R] ord G N K) (θ : TorsPt G N A), (∀ (x : Tors G N K) (a : A), θ.pt K x a = (io a : Tors G N K → K) x) → Function.Bijective (θ.pt K) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ io θ hθ
  obtain ⟨Idx, _, q, c, hc⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  have hfin : Finite (Tors G N K) := by
    have : ∀ i, Finite ((c i).C →ₐ[R] K) := fun i => (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q i) (c i)).1
    refine Finite.of_surjective (fun p : Σ i, ((c i).C →ₐ[R] K) => torsMap p.2 (c p.1).j) fun z => ?_
    obtain ⟨i, hi⟩ := hc K z
    obtain ⟨ψ, -, hψ⟩ := ((c i).bij K).surjOn hi
    exact ⟨⟨i, ψ⟩, hψ⟩
  have hS := (GlobalTheory.T.torsion_order_finite_projective R K G hG N hN).2.2
  refine ⟨fun x y hxy => eq_of_eval_eq _ hS fun a => ?_, fun φ => ?_⟩
  · obtain ⟨b, rfl⟩ := io.surjective a
    rw [← hθ, ← hθ, hxy]
  · obtain ⟨x, hx⟩ := exists_eval _ hS (φ.comp (io.symm : ord G N K →ₐ[R] A))
    refine ⟨x, AlgHom.ext fun a => ?_⟩
    rw [hθ, ← hx]
    simp

end GlobalTheory.GroupBplus.Aff.OrdGen
