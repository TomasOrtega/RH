import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.MonoZero

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Conclude with `h.ne_zero ((res_eq_zero_iff Λ S x).2 hn)`.
-/
private theorem eqMono_unit {Λ S : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing S] [Algebra Λ S] [IsCO Λ S] {x : S}
    (h : IsUnit (res Λ S x)) : IsUnit x := by
  by_contra hn
  exact h.ne_zero ((res_eq_zero_iff Λ S x).2 hn)

/- English proof (translation)
Rewrite `h` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Establish `h2 : IsUnit (∏ j ∈ Finset.univ.erase i, (x - c j))` using `IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj)`. Conclude with `sub_eq_zero.1 (h2.mul_left_eq_zero.1 h)`.
-/
private theorem eqMono_root {S : Type} [CommRing S] (x : S) (c : Fin 4 → S) (i : Fin 4)
    (h : ∏ j, (x - c j) = 0) (hu : ∀ j, j ≠ i → IsUnit (x - c j)) : x = c i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  have h2 : IsUnit (∏ j ∈ Finset.univ.erase i, (x - c j)) :=
    IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj)
  exact sub_eq_zero.1 (h2.mul_left_eq_zero.1 h)

/- English proof (translation)
Introduce `O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hOk hNear hGr D' hD' cp hcp R' _ _ _ f f' hff' x hx`. Set `φA : W.gr 0 →ₐ[Λ] R` to `{ toRingHom := (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A) commutes' := fun c => rfl }`. Establish `hAinj : Function.Injective (algebraMap (W.gr 0) W.A)` using `fun b c h => Subtype.ext h`. Set `E : Subring R` to `(AlgHom.equalizer f f').toSubring.map (φA : W.gr 0 →+* R)`. Establish `hmem : ∀ b : W.gr 0, f b = f' b → φA b ∈ E` using `fun b hb => Subring.mem_map.mpr ⟨b, hb, rfl⟩`.

Establish `hrep` using `hNear.rep`. Establish `hdex : ∀ i : Fin 4, ∃ d : W.gr 0, φA d = D.r Φ.g0 i i`. Introduce `i`. Establish `h` using `hGr.ent Φ.g0 i i`. Rewrite `h` using `[(wt_eq_zero i i).mpr rfl]`.

Conclude with `⟨⟨⟨_, W.part_le_A h⟩, h⟩, rfl⟩`. Use `choose d hd using hdex`. Establish `hresd : ∀ i, res Λ (W.gr 0) (d i) = residue Λ (a ↑((Φ.χ i) Φ.g0))`. Introduce `i`. Rewrite using `[← res_map φA, hd]`.

Conclude with `hNear.diag Φ.g0 i`. Establish `hdist : ∀ i j, i ≠ j → IsUnit (res Λ (W.gr 0) (d i - d j))`. Introduce `i j hij`. Establish `h` using `hOk.dist i j hij`. Simplify using `only [RingHom.comp_apply] at h`.

Rewrite using `[map_sub, hresd, hresd, ← map_sub]`. Conclude with `h`. Establish `hD'r : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R)`. Introduce `g`. Rewrite using `[← hD']`.

Both sides reduce to the same expression. Establish `hD'g0 : D'.r Φ.g0 = Matrix.diagonal (fun i => algebraMap (W.gr 0) W.A (d i))`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = (W.A.val : W.A →+* R) _`. Establish `h1 : (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = D.r Φ.g0 i j`.

Rewrite using `[hD'r]`. Both sides reduce to the same expression. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, h1, ← hd i]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.diagonal_apply_ne _ hij, map_zero, h1]`. Conclude with `hrep.nrm hij`. Establish `hcp0 : cp Φ.g0 = ∏ j, (X - C (d j))`. Apply `Polynomial.map_injective _ hAinj` to reduce the goal to its premises.

Rewrite using `[hcp, hD'g0, Matrix.charpoly_diagonal, Polynomial.map_prod]`. Simplify using the standard rewrite rules. Establish `hmapeq : (cp Φ.g0).map (f : W.gr 0 →+* R') = (cp Φ.g0).map (f' : W.gr 0 →+* R')`. Use extensionality with `n`. Simplify using `using hff' Φ.g0 n`.

Establish `hfix : ∀ i, f (d i) = f' (d i)`. Introduce `i`. Establish `hroot : ∏ j, (f' (d i) - f (d j)) = 0`. Establish `h1 : ((cp Φ.g0).map (f' : W.gr 0 →+* R')).eval (f' (d i)) = 0`. Rewrite using `[hcp0, Polynomial.map_prod, Polynomial.eval_prod]`.

Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite `h1` using `[← hmapeq, hcp0, Polynomial.map_prod, Polynomial.eval_prod]`. Simplify using `using h1`. Establish `hu : ∀ j, j ≠ i → IsUnit (f' (d i) - f (d j))`.

Introduce `j hji`. Apply `eqMono_unit (Λ := Λ)` to reduce the goal to its premises. Rewrite using `[map_sub, res_map, res_map, ← map_sub]`. Conclude with `hdist i j (Ne.symm hji)`. Conclude with `(eqMono_root (f' (d i)) (fun j => f (d j)) i hroot hu).symm`.

Establish `hν : ∀ g, ∃ ν ∈ E, IsGSp ν (D.r g)` using `fun g => ⟨_, hmem (algebraMap Λ (W.gr 0) (a ↑(Φ.ν g))) (by rw [f.commutes, f'.commutes]), hrep.mult g⟩`. Establish `htr : ∀ g, Matrix.trace (D.r g) ∈ E`. Introduce `g`. Establish `h2 : Matrix.trace (D'.r g) = algebraMap (W.gr 0) W.A (-(cp g).coeff 3)`. Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hcp, Polynomial.coeff_map, map_neg]`.

Establish `h3 : Matrix.trace (D.r g) = (W.A.val : W.A →+* R) (Matrix.trace (D'.r g))`. Rewrite using `[hD'r g]`. Simplify using `[Matrix.trace, map_sum]`. Establish `h1 : Matrix.trace (D.r g) = φA (-(cp g).coeff 3)`. Rewrite using `[h3, h2]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `hmem _ (by rw [map_neg, map_neg, hff' g 3])`. Establish `hEdiag : ∀ i, D.r Φ.g0 i i ∈ E` using `fun i => by`. Rewrite using `[← hd i]`.

Conclude with `hmem _ (hfix i)`. Establish `hsep : ∀ i j, i ≠ j → ∃ u ∈ E, u * (D.r Φ.g0 i i - D.r Φ.g0 j j) = 1`. Introduce `i j hij`. Take `⟨U, hU⟩` from `eqMono_unit (Λ := Λ) (S := W.gr 0) (hdist i j hij)`. Establish `hfe : f (d i - d j) = f' (d i - d j)` using `by rw [map_sub, map_sub, hfix, hfix]`.

Establish `e1 : f ↑U⁻¹ * f (d i - d j) = 1` using `by rw [← hU, ← map_mul, Units.inv_mul, map_one]`. Establish `e2 : f' ↑U⁻¹ * f' (d i - d j) = 1` using `by rw [← hU, ← map_mul, Units.inv_mul, map_one]`. Establish `hinv : f (↑U⁻¹ : W.gr 0) = f' ↑U⁻¹`. Combine the equalities or inequalities in the displayed calculation. Use `⟨φA ↑U⁻¹, hmem _ hinv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hd i, ← hd j, ← map_sub, ← map_mul, ← hU, Units.inv_mul, map_one]`. Establish `hsub` using `sxMonoZero E D.r Φ.g0 hν htr hrep.nrm hEdiag hsep`. Take `⟨b, hb, hbx⟩` from `Subring.mem_map.mp (hsub hx)`. Conclude with `⟨b, hbx, hb⟩`.
-/
theorem UpperTheory.V.Ws.sxEqMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Ok ((residue Λ).comp a) → Φ.Near a 0 D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → ∀ x ∈ mono D.r 0, ∃ b : W.gr 0, ((b : W.A) : R) = x ∧ f b = f' b := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hOk hNear hGr D' hD' cp hcp R' _ _ _ f f' hff' x hx
  classical
  let φA : W.gr 0 →ₐ[Λ] R :=
    { toRingHom := (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A)
      commutes' := fun c => rfl }
  have hAinj : Function.Injective (algebraMap (W.gr 0) W.A) := fun b c h => Subtype.ext h
  let E : Subring R := (AlgHom.equalizer f f').toSubring.map (φA : W.gr 0 →+* R)
  have hmem : ∀ b : W.gr 0, f b = f' b → φA b ∈ E := fun b hb => Subring.mem_map.mpr ⟨b, hb, rfl⟩
  have hrep := hNear.rep
  have hdex : ∀ i : Fin 4, ∃ d : W.gr 0, φA d = D.r Φ.g0 i i := by
    intro i
    have h := hGr.ent Φ.g0 i i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact ⟨⟨⟨_, W.part_le_A h⟩, h⟩, rfl⟩
  choose d hd using hdex
  have hresd : ∀ i, res Λ (W.gr 0) (d i) = residue Λ (a ↑((Φ.χ i) Φ.g0)) := by
    intro i
    rw [← res_map φA, hd]
    exact hNear.diag Φ.g0 i
  have hdist : ∀ i j, i ≠ j → IsUnit (res Λ (W.gr 0) (d i - d j)) := by
    intro i j hij
    have h := hOk.dist i j hij
    simp only [RingHom.comp_apply] at h
    rw [map_sub, hresd, hresd, ← map_sub]
    exact h
  have hD'r : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := by
    intro g
    rw [← hD']
    rfl
  have hD'g0 : D'.r Φ.g0 = Matrix.diagonal (fun i => algebraMap (W.gr 0) W.A (d i)) := by
    ext i j
    change (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = (W.A.val : W.A →+* R) _
    have h1 : (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = D.r Φ.g0 i j := by
      rw [hD'r]
      rfl
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, h1, ← hd i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, h1]
      exact hrep.nrm hij
  have hcp0 : cp Φ.g0 = ∏ j, (X - C (d j)) := by
    apply Polynomial.map_injective _ hAinj
    rw [hcp, hD'g0, Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp
  have hmapeq : (cp Φ.g0).map (f : W.gr 0 →+* R') = (cp Φ.g0).map (f' : W.gr 0 →+* R') := by
    ext n
    simpa using hff' Φ.g0 n
  have hfix : ∀ i, f (d i) = f' (d i) := by
    intro i
    have hroot : ∏ j, (f' (d i) - f (d j)) = 0 := by
      have h1 : ((cp Φ.g0).map (f' : W.gr 0 →+* R')).eval (f' (d i)) = 0 := by
        rw [hcp0, Polynomial.map_prod, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp
      rw [← hmapeq, hcp0, Polynomial.map_prod, Polynomial.eval_prod] at h1
      simpa using h1
    have hu : ∀ j, j ≠ i → IsUnit (f' (d i) - f (d j)) := by
      intro j hji
      apply eqMono_unit (Λ := Λ)
      rw [map_sub, res_map, res_map, ← map_sub]
      exact hdist i j (Ne.symm hji)
    exact (eqMono_root (f' (d i)) (fun j => f (d j)) i hroot hu).symm
  have hν : ∀ g, ∃ ν ∈ E, IsGSp ν (D.r g) := fun g =>
    ⟨_, hmem (algebraMap Λ (W.gr 0) (a ↑(Φ.ν g))) (by rw [f.commutes, f'.commutes]), hrep.mult g⟩
  have htr : ∀ g, Matrix.trace (D.r g) ∈ E := by
    intro g
    have h2 : Matrix.trace (D'.r g) = algebraMap (W.gr 0) W.A (-(cp g).coeff 3) := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hcp, Polynomial.coeff_map, map_neg]
    have h3 : Matrix.trace (D.r g) = (W.A.val : W.A →+* R) (Matrix.trace (D'.r g)) := by
      rw [hD'r g]
      simp [Matrix.trace, map_sum]
    have h1 : Matrix.trace (D.r g) = φA (-(cp g).coeff 3) := by
      rw [h3, h2]
      rfl
    rw [h1]
    exact hmem _ (by rw [map_neg, map_neg, hff' g 3])
  have hEdiag : ∀ i, D.r Φ.g0 i i ∈ E := fun i => by
    rw [← hd i]
    exact hmem _ (hfix i)
  have hsep : ∀ i j, i ≠ j → ∃ u ∈ E, u * (D.r Φ.g0 i i - D.r Φ.g0 j j) = 1 := by
    intro i j hij
    obtain ⟨U, hU⟩ := eqMono_unit (Λ := Λ) (S := W.gr 0) (hdist i j hij)
    have hfe : f (d i - d j) = f' (d i - d j) := by rw [map_sub, map_sub, hfix, hfix]
    have e1 : f ↑U⁻¹ * f (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have e2 : f' ↑U⁻¹ * f' (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have hinv : f (↑U⁻¹ : W.gr 0) = f' ↑U⁻¹ := by
      calc f ↑U⁻¹ = f ↑U⁻¹ * (f' (d i - d j) * f' ↑U⁻¹) := by rw [mul_comm (f' _), e2, mul_one]
        _ = (f ↑U⁻¹ * f (d i - d j)) * f' ↑U⁻¹ := by rw [hfe]; ring
        _ = f' ↑U⁻¹ := by rw [e1, one_mul]
    refine ⟨φA ↑U⁻¹, hmem _ hinv, ?_⟩
    rw [← hd i, ← hd j, ← map_sub, ← map_mul, ← hU, Units.inv_mul, map_one]
  have hsub := sxMonoZero E D.r Φ.g0 hν htr hrep.nrm hEdiag hsep
  obtain ⟨b, hb, hbx⟩ := Subring.mem_map.mp (hsub hx)
  exact ⟨b, hbx, hb⟩
