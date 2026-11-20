import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DetH

variable {D : D7}

/- English proof (translation)
Use `(traceForm_nondegenerate ℚ D.host.E).1 t fun e => ?_` and prove the remaining obligations. Establish `halg : IsAlgebraic ℤ e` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic`. Take `⟨y, hy0, hyi⟩` from `halg.exists_integral_multiple`. Establish `h1 : Algebra.trace ℚ D.host.E (t * (y • e)) = 0` using `h ⟨y • e, hyi⟩`. Rewrite `h1` using `[mul_smul_comm, map_zsmul, zsmul_eq_mul]`.

Rewrite using `[Algebra.traceForm_apply]`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `absurd (by exact_mod_cast h2) hy0`. Conclude with `h2`.
-/
theorem eq_zero_of_trace {t : D.host.E}
    (h : ∀ o : 𝓞 D.host.E, Algebra.trace ℚ D.host.E (t * o) = 0) : t = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 t fun e => ?_
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic
  obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ D.host.E (t * (y • e)) = 0 := h ⟨y • e, hyi⟩
  rw [mul_smul_comm, map_zsmul, zsmul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (by exact_mod_cast h2) hy0
  · exact h2

variable (X : HidaSetting D)

/- English proof (translation)
Establish `h1 : ∀ y ∈ X.Lb, (VS D).hT x y = 0` using `fun y hy => eq_zero_of_trace fun o => by`. Establish `h2` using `h (o • y) (X.Lb.smul_mem o hy)`. Rewrite `h2` using `[← algebraMap_smul D.host.E o y, LinearMap.map_smul, smul_eq_mul, mul_comm]`. Then use the resulting hypothesis. Establish `hxW` using `(mem_Wb X).1 (Lb_le_alt X hx)`. Establish `he : ∀ c, (VS D).hT x (X.eX c) = 0` using `fun c => by`.

Rewrite using `[herm_swap (X.eX c) x, (hxW c).1, star_zero]`. Establish `hf : ∀ c, (VS D).hT x (X.fY c) = 0` using `fun c => by`. Rewrite using `[herm_swap (X.fY c) x, (hxW c).2, star_zero]`. Establish `h2 : ∀ y ∈ (VS D).L0, (VS D).hT x y = 0`. Introduce `y hy`.

Take `⟨α, β, l, hl, rfl⟩` from `decomp X hy`. Simplify using `[map_add, map_sum, map_smul, he, hf, h1 l hl]`. Establish `hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤ LinearMap.ker ((VS D).hT x)` using `Submodule.span_le.2 fun y hy => LinearMap.mem_ker.2 (h2 y hy)`. Use `(VS D).nondeg.1 x fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V)`.

Rewrite using `[(VS D).standardTuple_isLattice.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `LinearMap.mem_ker.1 (hle hv)`.
-/
theorem eq_zero_of_trB {x : (VS D).V} (hx : x ∈ X.Lb)
    (h : ∀ y ∈ X.Lb, Algebra.trace ℚ D.host.E ((VS D).hT x y) = 0) : x = 0 := by
  have h1 : ∀ y ∈ X.Lb, (VS D).hT x y = 0 := fun y hy => eq_zero_of_trace fun o => by
    have h2 := h (o • y) (X.Lb.smul_mem o hy)
    rwa [← algebraMap_smul D.host.E o y, LinearMap.map_smul, smul_eq_mul, mul_comm] at h2
  have hxW := (mem_Wb X).1 (Lb_le_alt X hx)
  have he : ∀ c, (VS D).hT x (X.eX c) = 0 := fun c => by
    rw [herm_swap (X.eX c) x, (hxW c).1, star_zero]
  have hf : ∀ c, (VS D).hT x (X.fY c) = 0 := fun c => by
    rw [herm_swap (X.fY c) x, (hxW c).2, star_zero]
  have h2 : ∀ y ∈ (VS D).L0, (VS D).hT x y = 0 := by
    intro y hy
    obtain ⟨α, β, l, hl, rfl⟩ := decomp X hy
    simp [map_add, map_sum, map_smul, he, hf, h1 l hl]
  have hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤ LinearMap.ker ((VS D).hT x) :=
    Submodule.span_le.2 fun y hy => LinearMap.mem_ker.2 (h2 y hy)
  refine (VS D).nondeg.1 x fun v => ?_
  have hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by
    rw [(VS D).standardTuple_isLattice.span_eq_top]; trivial
  exact LinearMap.mem_ker.1 (hle hv)

/- English proof (translation)
Establish `e : y = ∑ i, (ℓ.repr ⟨y, hy⟩ i) • (ℓ i : (VS D).V)`. Establish `h` using `congrArg Subtype.val (ℓ.sum_repr ⟨y, hy⟩)`. Rewrite `h` using `[Submodule.coe_sum]`. Simplify `h.symm` using `[Submodule.coe_smul]`. Use `conv_lhs => rw [e]`.

Conclude with `trB_sum_right _ _ _`.
-/
theorem trB_expand {N : ℕ} (ℓ : Module.Basis (Fin N) ℤ (X.Lb.restrictScalars ℤ)) (x y : (VS D).V) (hy : y ∈ X.Lb) :
    Algebra.trace ℚ D.host.E ((VS D).hT x y) =
      ∑ i, ((ℓ.repr ⟨y, hy⟩ i : ℤ) : ℚ) * Algebra.trace ℚ D.host.E ((VS D).hT x (ℓ i : (VS D).V)) := by
  have e : y = ∑ i, (ℓ.repr ⟨y, hy⟩ i) • (ℓ i : (VS D).V) := by
    have h := congrArg Subtype.val (ℓ.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    simpa [Submodule.coe_smul] using h.symm
  conv_lhs => rw [e]
  exact trB_sum_right _ _ _

end DetH

open DetH in

/- English proof (translation)
Introduce `D X N ℓ ℓs`. Establish `hGi : ∀ m i, ∃ z : ℤ, Algebra.trace ℚ D.host.E ((VS D).hT (ℓ m : (VS D).V) (ℓ i : (VS D).V)) = z` using `fun m i => (Lb_le_Ldual X (ℓ m).2).2 _ (ℓ i).2`. Use `choose Gz hGz using hGi`. Establish `hHi : ∀ k j, ∃ z : ℤ, Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V)) = z` using `fun k j => (ℓs k).2.2 _ (ℓ j).2`. Use `choose Hz hHz using hHi`.

Use `set G : Matrix (Fin N) (Fin N) ℤ := Matrix.of Gz with hG`. Use `set H : Matrix (Fin N) (Fin N) ℤ := Matrix.of Hz with hH`. Establish `hind : LinearIndependent ℤ (fun m => (ℓ m : (VS D).V))` using `ℓ.linearIndependent.map' (X.Lb.restrictScalars ℤ).subtype (Submodule.ker_subtype _)`. Establish `hcomb : ∀ (a : Fin N → ℤ) (i : Fin N), Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, a m • (ℓ m : (VS D).V)) (ℓ i : (VS D).V)) = ((Matrix.vecMul a G) i : ℚ)`. Introduce `a i`.

Rewrite using `[trB_sum_left]`. Simplify using `only [hGz, Matrix.vecMul, dotProduct, hG, Matrix.of_apply]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hmem : ∀ a : Fin N → ℤ, ∑ m, a m • (ℓ m : (VS D).V) ∈ X.Lb` using `fun a => Submodule.sum_mem _ fun m _ => Submodule.smul_of_tower_mem _ _ (ℓ m).2`.

Establish `hdet : G.det ≠ 0`. Introduce `h0`. Take `⟨a, ha0, ha⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Establish `hx : ∑ m, a m • (ℓ m : (VS D).V) = 0`. Use `eq_zero_of_trB X (hmem a) fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[trB_expand X ℓ _ y hy]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcomb, ha]`. Simplify using the standard rewrite rules. Conclude with `ha0 (funext fun m => Fintype.linearIndependent_iff.1 hind a hx m)`.

Establish `hdetQ : ((G.det : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast hdet`. Use `set r : ℚ := ((G.det : ℤ) : ℚ)⁻¹ with hr`. Set `xs : Fin N → (VS D).V` to `fun j => ((r : ℚ) : D.host.E) • ∑ m, G.adjugate j m • (ℓ m : (VS D).V)`. Establish `hpair : ∀ j (y : (VS D).V), Algebra.trace ℚ D.host.E ((VS D).hT (xs j) y) = r * Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, G.adjugate j m • (ℓ m : (VS D).V)) y)`. Introduce `j y`.

Simplify using `only [xs, LinearMap.map_smulₛₗ₂, smul_eq_mul]`. Rewrite using `[map_ratCast, ← Rat.smul_def, LinearMap.map_smul, smul_eq_mul]`. Establish `hdual : ∀ j i, Algebra.trace ℚ D.host.E ((VS D).hT (xs j) (ℓ i : (VS D).V)) = ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ)`. Introduce `j i`. Rewrite using `[hpair, hcomb]`.

Establish `hv : (Matrix.vecMul (G.adjugate j) G) i = (G.adjugate * G) j i` using `rfl`. Rewrite using `[hv, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, hr, ← mul_assoc, inv_mul_cancel₀ hdetQ, one_mul]`. Establish `hxsW : ∀ j, xs j ∈ Ldual X`. Introduce `j`. Use `⟨(Wb X).smul_mem _ (Lb_le_alt X (hmem _)), fun y hy => ?_⟩` and prove the remaining obligations.

Use `⟨ℓ.repr ⟨y, hy⟩ j, ?_⟩` and prove the remaining obligations. Rewrite using `[trB_expand X ℓ _ y hy]`. Simplify using `only [hdual, Matrix.one_apply]`. Use `push_cast`. Simplify using the standard rewrite rules.

Set `C : Matrix (Fin N) (Fin N) ℤ` to `Matrix.of fun j k => ℓs.repr ⟨xs j, hxsW j⟩ k`. Establish `hCH : C * H = 1`. Use extensionality with `j i`. Establish `e : xs j = ∑ k, C j k • (ℓs k : (VS D).V)`. Establish `h` using `congrArg Subtype.val (ℓs.sum_repr ⟨xs j, hxsW j⟩)`.

Rewrite `h` using `[Submodule.coe_sum]`. Simplify `h.symm` using `[C, Submodule.coe_smul]`. Establish `h1` using `hdual j i`. Rewrite `h1` using `[e, trB_sum_left]`. Simplify using `only [hHz] at h1`.

Establish `h2 : (((C * H) j i : ℤ) : ℚ) = ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ)`. Rewrite using `[← h1, Matrix.mul_apply]`. Use `push_cast`. Simplify using `[hH]`. Conclude with `h2` after adjusting the coercions.

Establish `hHC : H.det * C.det = 1` using `by rw [mul_comm, ← Matrix.det_mul, hCH, Matrix.det_one]`. Establish `hunit : IsUnit H.det` using `⟨⟨H.det, C.det, hHC, by rw [mul_comm]; exact hHC⟩, rfl⟩`. Establish `hmat : (Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))) = H.map (Int.cast : ℤ → ℚ)`. Use extensionality with `k j`. Simplify using `[hH, hHz]`.

Establish `hdH : (H.map (Int.cast : ℤ → ℚ)).det = ((H.det : ℤ) : ℚ)`. Simplify using `using (RingHom.map_det (Int.castRingHom ℚ) H).symm`. Rewrite using `[hmat, hdH]`. Apply the tactic sequence `rcases Int.isUnit_iff.1 hunit with h | h <;> simp [h]`.
-/
theorem detHOne_holds : DetHOne := by
  intro D X N ℓ ℓs
  have hGi : ∀ m i, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E ((VS D).hT (ℓ m : (VS D).V) (ℓ i : (VS D).V)) = z := fun m i =>
    (Lb_le_Ldual X (ℓ m).2).2 _ (ℓ i).2
  choose Gz hGz using hGi
  have hHi : ∀ k j, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V)) = z := fun k j =>
    (ℓs k).2.2 _ (ℓ j).2
  choose Hz hHz using hHi
  set G : Matrix (Fin N) (Fin N) ℤ := Matrix.of Gz with hG
  set H : Matrix (Fin N) (Fin N) ℤ := Matrix.of Hz with hH
  have hind : LinearIndependent ℤ (fun m => (ℓ m : (VS D).V)) :=
    ℓ.linearIndependent.map' (X.Lb.restrictScalars ℤ).subtype (Submodule.ker_subtype _)

  have hcomb : ∀ (a : Fin N → ℤ) (i : Fin N),
      Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, a m • (ℓ m : (VS D).V)) (ℓ i : (VS D).V)) =
        ((Matrix.vecMul a G) i : ℚ) := by
    intro a i
    rw [trB_sum_left]
    simp only [hGz, Matrix.vecMul, dotProduct, hG, Matrix.of_apply]
    push_cast; rfl
  have hmem : ∀ a : Fin N → ℤ, ∑ m, a m • (ℓ m : (VS D).V) ∈ X.Lb := fun a =>
    Submodule.sum_mem _ fun m _ => Submodule.smul_of_tower_mem _ _ (ℓ m).2

  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have hx : ∑ m, a m • (ℓ m : (VS D).V) = 0 := by
      refine eq_zero_of_trB X (hmem a) fun y hy => ?_
      rw [trB_expand X ℓ _ y hy]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcomb, ha]; simp
    exact ha0 (funext fun m => Fintype.linearIndependent_iff.1 hind a hx m)
  have hdetQ : ((G.det : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hdet

  set r : ℚ := ((G.det : ℤ) : ℚ)⁻¹ with hr
  let xs : Fin N → (VS D).V := fun j => ((r : ℚ) : D.host.E) • ∑ m, G.adjugate j m • (ℓ m : (VS D).V)
  have hpair : ∀ j (y : (VS D).V), Algebra.trace ℚ D.host.E ((VS D).hT (xs j) y) =
      r * Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, G.adjugate j m • (ℓ m : (VS D).V)) y) := by
    intro j y
    simp only [xs, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rw [map_ratCast, ← Rat.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hdual : ∀ j i, Algebra.trace ℚ D.host.E ((VS D).hT (xs j) (ℓ i : (VS D).V)) =
      ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ) := by
    intro j i
    rw [hpair, hcomb]
    have hv : (Matrix.vecMul (G.adjugate j) G) i = (G.adjugate * G) j i := rfl
    rw [hv, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, hr, ← mul_assoc,
      inv_mul_cancel₀ hdetQ, one_mul]
  have hxsW : ∀ j, xs j ∈ Ldual X := by
    intro j
    refine ⟨(Wb X).smul_mem _ (Lb_le_alt X (hmem _)), fun y hy => ?_⟩
    refine ⟨ℓ.repr ⟨y, hy⟩ j, ?_⟩
    rw [trB_expand X ℓ _ y hy]
    simp only [hdual, Matrix.one_apply]
    push_cast
    simp

  let C : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun j k => ℓs.repr ⟨xs j, hxsW j⟩ k
  have hCH : C * H = 1 := by
    ext j i
    have e : xs j = ∑ k, C j k • (ℓs k : (VS D).V) := by
      have h := congrArg Subtype.val (ℓs.sum_repr ⟨xs j, hxsW j⟩)
      rw [Submodule.coe_sum] at h
      simpa [C, Submodule.coe_smul] using h.symm
    have h1 := hdual j i
    rw [e, trB_sum_left] at h1
    simp only [hHz] at h1
    have h2 : (((C * H) j i : ℤ) : ℚ) = ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ) := by
      rw [← h1, Matrix.mul_apply]; push_cast; simp [hH]
    exact_mod_cast h2
  have hHC : H.det * C.det = 1 := by rw [mul_comm, ← Matrix.det_mul, hCH, Matrix.det_one]
  have hunit : IsUnit H.det := ⟨⟨H.det, C.det, hHC, by rw [mul_comm]; exact hHC⟩, rfl⟩
  have hmat : (Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))) =
      H.map (Int.cast : ℤ → ℚ) := by
    ext k j; simp [hH, hHz]
  have hdH : (H.map (Int.cast : ℤ → ℚ)).det = ((H.det : ℤ) : ℚ) := by
    simpa using (RingHom.map_det (Int.castRingHom ℚ) H).symm
  rw [hmat, hdH]
  rcases Int.isUnit_iff.1 hunit with h | h <;> simp [h]

end Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD
