import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G G0 h n x k hK z hz hb`. Take `⟨s₀, hs⟩` from `selScale l L G G0 h n x false z hz hb`. Take `⟨z', hz', hzz⟩` from `hs s₀ le_rfl`. Take `⟨s', c, Y, hY, hYt, hYe⟩` from `hK z' hz'`. Use `set f := algebraMap x.A x.Fr with hf`.

Establish `ht : f x.t ≠ 0`. Introduce `h0`. Apply `PowerSeries.X_ne_zero (R := x.K)` to reduce the goal to its premises. Conclude with `IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)`. Establish `hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f`.

Introduce `a M`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) = x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y`. Introduce `g`.

Establish `e` using `congrFun hYe g`. Simplify `e` using `[dY, Finset.sum_apply]`. Establish `key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g = x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f`. Introduce `g`. Establish `e` using `congrArg f.mapMatrix (key g)`.

Simplify `e` using `[map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply]`. Use `set u := (f x.t ^ (s' + s₀))⁻¹ with hu`. Use `⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Take `⟨h1, h2⟩` from `hY i j`.

Use `⟨fun hij => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations. Establish `h3` using `h1 hij`. Rewrite `h3`, the goal using `[Submodule.mem_bot]`. Simplify using `[h3]`. Use extensionality with `i j`.

Establish `h3` using `congrFun (congrFun hYt i) j`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply] at h3`. Simplify using `[Matrix.transpose_apply, h3]`. Use function extensionality and compare the values at `g`. Establish `e` using `key2 g`.

Rewrite `e` using `[hzz g, smul_smul, ← pow_add]`. Simplify using `only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]`. Simplify using `[smul_smul]`.
-/
theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)
    simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
