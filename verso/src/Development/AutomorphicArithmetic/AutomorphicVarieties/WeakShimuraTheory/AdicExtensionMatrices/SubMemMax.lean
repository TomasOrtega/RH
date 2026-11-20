import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Apply the tactic sequence `have h : w = w.1 • ((1, 0) : ℤ × ℤ) + w.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp`. Use `conv_lhs => rw [h]`. Rewrite using `[ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow]`. Both sides reduce to the same expression.
-/
private theorem char_eq_wv {R : Type} [CommRing R] (t : Multiplicative (ℤ × ℤ) →* Rˣ) (w : ℤ × ℤ) :
    t (Multiplicative.ofAdd w) = wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w := by
  have h : w = w.1 • ((1, 0) : ℤ × ℤ) + w.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp
  conv_lhs => rw [h]
  rw [ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow]
  rfl

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ c (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)`.
-/
private theorem const_mem {Λ X R : Type} [CommRing Λ] [AddCommGroup X] [CommRing R] [Algebra Λ R] (W : WPres Λ X R)
    (c : Λ) : algebraMap Λ R c ∈ W.part 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff Λ, map_sub, AlgHom.commutes, h]`. Conclude with `sub_self _`.
-/
private theorem sub_mem_max {Λ R : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {x : R} {c : Λ} (h : res Λ R x = residue Λ c) : x - algebraMap Λ R c ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff Λ, map_sub, AlgHom.commutes, h]
  exact sub_self _

/- English proof (translation)
Introduce `O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D hD`. Take `⟨hN, hU⟩` from `hD`. Set `c : Γ → Fin 4 → Fin 4 → Λ` to `fun g i j => if i = j then a (Φ.χ i g) else 0`. Set `S : Type` to `(Γ × Fin 4 × Fin 4) ⊕ (Σ v : Φ.ι, Fin 4 × Φ.Gv v)`. Set `e : S → R` to `Sum.elim (fun x => D.r x.1 x.2.1 x.2.2 - algebraMap Λ R (c x.1 x.2.1 x.2.2)) (fun x => D.ψ x.1 x.2.1 x.2.2 - algebraMap Λ R (a (Φ.χ x.2.1 x.2.2)))`.

Set `w : S → ℤ × ℤ` to `Sum.elim (fun x => wt x.2.1 x.2.2) (fun _ => 0)`. Establish `hc : ∀ g i j, i ≠ j → c g i j = 0` using `fun g i j h => if_neg h`. Use `(coord_grading Λ (ℤ × ℤ) R S e w ?_ ?_ ?_).elim fun W ⟨u, hu, hW⟩ => ?_` and prove the remaining obligations. Use `rotate_right`. Use `⟨W, fun s => ?_, fun g i j => ?_, fun v i s => ?_, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[(hu s).1]`. Break down `u s with ⟨g, i, j⟩ | ⟨v, i, t⟩` into its components or cases. Use `show D.r g i j - algebraMap Λ R (c g i j) ∈ _`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Conclude with `sub_mem_max ((hN.diag g i).trans (by simp [c]))`. Rewrite using `[hc g i j h, map_zero, sub_zero]`. Conclude with `hN.off g i j h le_rfl`. Conclude with `sub_mem_max (hN.redψ v i t)`. Establish `h1 : D.r g i j - algebraMap Λ R (c g i j) ∈ W.part (wt i j)` using `hW (Sum.inl (g, i, j))`.

Distinguish the cases in `h : i = j`. Rewrite `h1`, the goal using `[(wt_eq_zero i j).2 h]`. Simplify using `using add_mem h1 (const_mem W (c g i j))`. Rewrite `h1` using `[hc g i j h, map_zero, sub_zero]`. Then use the resulting hypothesis. Establish `h1 : D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)) ∈ W.part 0` using `hW (Sum.inr ⟨v, i, s⟩)`.

Simplify using `using add_mem h1 (const_mem W (a (Φ.χ i s)))`. Rewrite using `[(hu s).1, (hu s).2]`. Break down `u s with ⟨g, i, j⟩ | ⟨v, i, t⟩` into its components or cases. Conclude with `Or.inl ⟨g, i, j, c g i j, rfl, rfl, hc g i j⟩`. Conclude with `Or.inr ⟨v, i, t, _, rfl, rfl⟩`.

Introduce and unpack `(⟨g, i, j⟩ | ⟨v, i, t⟩)`. Use `show D.r g i j - algebraMap Λ R (c g i j) ∈ _`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Conclude with `sub_mem_max ((hN.diag g i).trans (by simp [c]))`.

Rewrite using `[hc g i j h, map_zero, sub_zero]`. Conclude with `hN.off g i j h le_rfl`. Conclude with `sub_mem_max (hN.redψ v i t)`. Introduce `R' _ _ _ f f' h`. Use `(hU R' (D.map (f' : R →+* R')) (sxNearMap f' hN)).unique ?_ rfl` and prove the remaining obligations.

Use `RD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_) (funext fun v => funext fun i => MonoidHom.ext fun s => ?_)` and prove the remaining obligations. Establish `h1 : f (D.r g i j - algebraMap Λ R (c g i j)) = f' (D.r g i j - algebraMap Λ R (c g i j))` using `h (Sum.inl (g, i, j))`. Rewrite `h1` using `[map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj]`. Conclude with `h1`. Establish `h1 : f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) = f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)))` using `h (Sum.inr ⟨v, i, s⟩)`.

Rewrite `h1` using `[map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj]`. Conclude with `h1`. Introduce `R' _ _ _ f t _`. Take `⟨D', hD', hr, hψ⟩` from `sxNearConj (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) (sxNearMap f hN)`. Take `⟨f', hf', -⟩` from `hU R' D' hD'`.

Use `⟨f', ?_⟩` and prove the remaining obligations. Introduce and unpack `(⟨g, i, j⟩ | ⟨v, i, s⟩)`. Use `show f' (D.r g i j - algebraMap Λ R (c g i j)) = t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j - algebraMap Λ R (c g i j))`. Establish `h1 : f' (D.r g i j) = t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j)`. Establish `h2 : f' (D.r g i j) = D'.r g i j` using `by rw [← hf']; rfl`.

Rewrite using `[h2, hr, char_eq_wv t (wt i j)]`. Both sides reduce to the same expression. Distinguish the cases in `h : i = j`. Rewrite `h1`, the goal using `[(wt_eq_zero i j).2 h]`. Rewrite using `[map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]`.

Simplify using the standard rewrite rules. Rewrite using `[hc g i j h, map_zero, sub_zero, h1]`. Use `show f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) = t (Multiplicative.ofAdd 0) * f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)))`. Establish `h1 : f' (D.ψ v i s) = f (D.ψ v i s)`. Establish `h2 : f' (D.ψ v i s) = D'.ψ v i s` using `by rw [← hf']; rfl`.

Rewrite using `[h2, hψ]`. Both sides reduce to the same expression. Rewrite using `[map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Ws.sxGradD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R}, Φ.RUniv a D → ∃ W : WPres Λ (ℤ × ℤ) R, D.Graded W := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D hD
  obtain ⟨hN, hU⟩ := hD
  let c : Γ → Fin 4 → Fin 4 → Λ := fun g i j => if i = j then a (Φ.χ i g) else 0
  let S : Type := (Γ × Fin 4 × Fin 4) ⊕ (Σ v : Φ.ι, Fin 4 × Φ.Gv v)
  let e : S → R := Sum.elim (fun x => D.r x.1 x.2.1 x.2.2 - algebraMap Λ R (c x.1 x.2.1 x.2.2))
    (fun x => D.ψ x.1 x.2.1 x.2.2 - algebraMap Λ R (a (Φ.χ x.2.1 x.2.2)))
  let w : S → ℤ × ℤ := Sum.elim (fun x => wt x.2.1 x.2.2) (fun _ => 0)
  have hc : ∀ g i j, i ≠ j → c g i j = 0 := fun g i j h => if_neg h
  refine (coord_grading Λ (ℤ × ℤ) R S e w ?_ ?_ ?_).elim fun W ⟨u, hu, hW⟩ => ?_
  rotate_right
  · refine ⟨W, fun s => ?_, fun g i j => ?_, fun v i s => ?_, fun s => ?_⟩
    · rw [(hu s).1]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
        by_cases h : i = j
        · subst h
          exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
        · rw [hc g i j h, map_zero, sub_zero]
          exact hN.off g i j h le_rfl
      · exact sub_mem_max (hN.redψ v i t)
    · have h1 : D.r g i j - algebraMap Λ R (c g i j) ∈ W.part (wt i j) := hW (Sum.inl (g, i, j))
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        simpa using add_mem h1 (const_mem W (c g i j))
      · rwa [hc g i j h, map_zero, sub_zero] at h1
    · have h1 : D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)) ∈ W.part 0 := hW (Sum.inr ⟨v, i, s⟩)
      simpa using add_mem h1 (const_mem W (a (Φ.χ i s)))
    · rw [(hu s).1, (hu s).2]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · exact Or.inl ⟨g, i, j, c g i j, rfl, rfl, hc g i j⟩
      · exact Or.inr ⟨v, i, t, _, rfl, rfl⟩
  · rintro (⟨g, i, j⟩ | ⟨v, i, t⟩)
    · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
      by_cases h : i = j
      · subst h
        exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
      · rw [hc g i j h, map_zero, sub_zero]
        exact hN.off g i j h le_rfl
    · exact sub_mem_max (hN.redψ v i t)
  · intro R' _ _ _ f f' h
    refine (hU R' (D.map (f' : R →+* R')) (sxNearMap f' hN)).unique ?_ rfl
    refine RD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_) (funext fun v => funext fun i => MonoidHom.ext fun s => ?_)
    · have h1 : f (D.r g i j - algebraMap Λ R (c g i j)) = f' (D.r g i j - algebraMap Λ R (c g i j)) :=
        h (Sum.inl (g, i, j))
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
    · have h1 : f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) = f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) :=
        h (Sum.inr ⟨v, i, s⟩)
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
  · intro R' _ _ _ f t _
    obtain ⟨D', hD', hr, hψ⟩ := sxNearConj (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
      (sxNearMap f hN)
    obtain ⟨f', hf', -⟩ := hU R' D' hD'
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, s⟩)
    · show f' (D.r g i j - algebraMap Λ R (c g i j)) =
        t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j - algebraMap Λ R (c g i j))
      have h1 : f' (D.r g i j) = t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j) := by
        have h2 : f' (D.r g i j) = D'.r g i j := by rw [← hf']; rfl
        rw [h2, hr, char_eq_wv t (wt i j)]
        rfl
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · rw [hc g i j h, map_zero, sub_zero, h1]
    · show f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) =
        t (Multiplicative.ofAdd 0) * f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)))
      have h1 : f' (D.ψ v i s) = f (D.ψ v i s) := by
        have h2 : f' (D.ψ v i s) = D'.ψ v i s := by rw [← hf']; rfl
        rw [h2, hψ]
        rfl
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
      simp
