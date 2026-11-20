import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.LaurentCoeffZero

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Establish `hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W` using `fun t y hy => by`. Use `hinv t y hy` as an intermediate fact. Rewrite `this` using `[Matrix.toLin'_apply]`. Then use the resulting hypothesis. Set `S : Set W` to `{y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}`. Establish `hspan : Submodule.span k S = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨y, hy⟩ -`. Establish `hsum` using `sum_prj P w y`. Establish `hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S`. Introduce `m _`.

Distinguish the cases in `hm : m < 0`. Establish `h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0` using `Subtype.ext (prj_neg P w m hm y (hpos y hy))`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨m.toNat, ?_⟩` and prove the remaining obligations. Establish `: ((m.toNat : ℕ) : ℤ) = m` using `Int.toNat_of_nonneg (by omega)`. Simplify using `only [this]`. Conclude with `prj_prj P w m y`. Establish `: (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Conclude with `hsum.symm`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ hmem`.

Take `⟨b, hbS, hbspan, hli⟩` from `exists_linearIndependent k S`. Establish `hfin : Finite b` using `hli.finite`. Set `_ : Fintype b` to `Fintype.ofFinite b`. Set `B : Basis b k W` to `Basis.mk hli (by`. Rewrite using `[Subtype.range_coe, hbspan, hspan])`.

Establish `hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W)` using `fun j => hbS j.2`. Use `choose mj hmj using hwt`. Use `⟨∑ j, mj j, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.det_toMatrix B]`. Establish `hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j))`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Establish `hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j) = (t : k) ^ (mj j) • B j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]`.

Establish `h1` using `gt_prj P w t (mj j) ((j : W) : Fin n → k)`. Rewrite `h1` using `[hmj j]`. Establish `h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j)` using `by simp [zpow_natCast]`. Rewrite `h1` using `[h2]`. Conclude with `h1`.

Rewrite using `[hfj, map_smul, Basis.repr_self, diagonal_apply]`. Simplify using `only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hij, Ne.symm hij]`. Rewrite using `[hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]`.
-/
theorem wtI [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W,
      Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val) y ∈ W)
    (hpos : ∀ y ∈ W, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) :
    ∃ m : ℕ, ∀ t : kˣ,
      LinearMap.det ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict
        (hinv t)) = (t : k) ^ m := by
  classical
  have hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W := fun t y hy => by
    have := hinv t y hy
    rwa [Matrix.toLin'_apply] at this

  let S : Set W := {y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}
  have hspan : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hsum := sum_prj P w y
    have hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S := by
      intro m _
      by_cases hm : m < 0
      · have h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0 :=
          Subtype.ext (prj_neg P w m hm y (hpos y hy))
        rw [h0]; exact Submodule.zero_mem _
      · apply Submodule.subset_span
        refine ⟨m.toNat, ?_⟩
        have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        simp only [this]
        exact prj_prj P w m y
    have : (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [this]
    exact Submodule.sum_mem _ hmem
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent k S
  have hfin : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  let B : Basis b k W := Basis.mk hli (by
    rw [Subtype.range_coe, hbspan, hspan])
  have hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W) := fun j => hbS j.2
  choose mj hmj using hwt
  refine ⟨∑ j, mj j, fun t => ?_⟩
  rw [← LinearMap.det_toMatrix B]
  have hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) *
      P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j)
        = (t : k) ^ (mj j) • B j := by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]
      have h1 := gt_prj P w t (mj j) ((j : W) : Fin n → k)
      rw [hmj j] at h1
      have h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j) := by simp [zpow_natCast]
      rw [h2] at h1
      exact h1
    rw [hfj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
