import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Weyl

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

/- English proof (translation)
Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Apply `isWeightedHomogeneous_one` to reduce the goal to its premises. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `l j _`. Simplify using the standard rewrite rules.
-/
theorem one_mem_dualWeyl (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · apply isWeightedHomogeneous_one
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j _
    simp

/- English proof (translation)
Establish `h1 : hw R (le_refl k) (0 : Fin k → ℕ) = 1`. Simplify using `[hw]`. Conclude with `Submodule.subset_span ⟨[], by simp [applyWord, h1]⟩`.
-/
theorem one_mem_weyl (k : ℕ) : (1 : MvPolynomial (Fin k × Fin k) R) ∈ weyl R k k le_rfl 0 := by
  have h1 : hw R (le_refl k) (0 : Fin k → ℕ) = 1 := by
    simp [hw]
  exact Submodule.subset_span ⟨[], by simp [applyWord, h1]⟩

/- English proof (translation)
Unfold `nablaLTw`. Use `Submodule.mem_map.mpr ⟨1, ?_, by simp⟩` and prove the remaining obligations. Establish `hν : (fun t : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) t - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Rewrite using `[hν]`. Unfold `nablaL`. Rewrite using `[Submodule.mem_comap]`. Simplify using `only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]`. Conclude with `Submodule.mem_map.mpr ⟨1, one_mem_dualWeyl R (m + 1) (m + 1), by simp⟩`.
-/
theorem one_mem_nablaLTw (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ nablaLTw R K m 0 g := by
  unfold nablaLTw
  refine Submodule.mem_map.mpr ⟨1, ?_, by simp⟩
  have hν : (fun t : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) t - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
    funext t
    simp
  rw [hν]
  unfold nablaL
  rw [Submodule.mem_comap]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]
  exact Submodule.mem_map.mpr ⟨1, one_mem_dualWeyl R (m + 1) (m + 1), by simp⟩

/- English proof (translation)
Unfold `deltaLTw`. Use `Submodule.mem_map.mpr ⟨1, ?_, by simp⟩` and prove the remaining obligations. Establish `hν : nuOf (0 : Fin (m + 1) → ℤ) = 0`. Use function extensionality and compare the values at `t`. Simplify using `[nuOf]`.

Rewrite using `[hν]`. Unfold `deltaL`. Rewrite using `[Submodule.mem_comap]`. Simplify using `only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]`. Conclude with `Submodule.mem_map.mpr ⟨1, one_mem_weyl R (m + 1), by simp⟩`.
-/
theorem one_mem_deltaLTw (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ deltaLTw R K m 0 g := by
  unfold deltaLTw
  refine Submodule.mem_map.mpr ⟨1, ?_, by simp⟩
  have hν : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
    funext t
    simp [nuOf]
  rw [hν]
  unfold deltaL
  rw [Submodule.mem_comap]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]
  exact Submodule.mem_map.mpr ⟨1, one_mem_weyl R (m + 1), by simp⟩

/- English proof (translation)
Unfold `H0`. Rewrite using `[if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]`. Simplify using `only [Submodule.mem_iInf]`. Introduce `g _`. Conclude with `one_mem_nablaLTw R K m g`.
-/
theorem one_mem_H0_weight_zero (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) : (1 : MvPolynomial _ K) ∈ H0 R m 0 Λ := by
  unfold H0
  rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  simp only [Submodule.mem_iInf]
  intro g _
  exact one_mem_nablaLTw R K m g

/- English proof (translation)
Unfold `Dl0`. Rewrite using `[if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]`. Simplify using `only [Submodule.mem_iInf]`. Introduce `g _`. Conclude with `one_mem_deltaLTw R K m g`.
-/
theorem one_mem_lattice_degree_zero (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) : (1 : MvPolynomial _ K) ∈ Dl0 R m 0 Λ := by
  unfold Dl0
  rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  simp only [Submodule.mem_iInf]
  intro g _
  exact one_mem_deltaLTw R K m g

/- English proof (translation)
Unfold `lamAt`. Use `split_ifs`. Apply the tactic sequence `all_goals (funext i; simp)`.
-/
theorem lamAt_zero {n' m : ℕ} (s : Fin n') : lamAt (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) s = 0 := by
  unfold lamAt
  split_ifs
  all_goals (funext i; simp)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨fun _ => 1, h, by simp⟩`.
-/
theorem one_mem_tensorLat {S : Type*} [Fintype S] {k n : ℕ} (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, (1 : MvPolynomial _ K) ∈ M s) : (1 : MvPolynomial _ K) ∈ tensorLat R K M := Submodule.subset_span ⟨fun _ => 1, h, by simp⟩

end Weyl

section Lat

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 1`.
-/
theorem map_colSpan' (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hL`. Use `⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, map_colSpan' A g⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnits_det_units A).mul hg`.
-/
theorem isLattice_map (A : GL (Fin k) K) {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, map_colSpan' A g⟩
  rw [Matrix.det_mul]
  exact (Matrix.isUnits_det_units A).mul hg

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Establish `hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) ∘ₗ ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R) = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec_mulVec]`. Rewrite using `[hid, Submodule.map_id]`.
-/
theorem map_map_inv (A : GL (Fin k) K) (L : Submodule R (Fin k → K)) :
    (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) = L := by
  rw [← Submodule.map_comp]
  have hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) ∘ₗ
      ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]
  rw [hid, Submodule.map_id]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by have h' := isLattice_map (A⁻¹) h rwa [map_map_inv] at h', isLattice_map A⟩`.
-/
theorem isLattice_map_iff (A : GL (Fin k) K) (L : Submodule R (Fin k → K)) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) ↔ IsLattice R L := ⟨fun h => by
    have h' := isLattice_map (A⁻¹) h
    rwa [map_map_inv] at h', isLattice_map A⟩

end Lat

section Form

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)

/- English proof (translation)
The claim follows from `forall_congr' fun v => isLattice_map_iff _ _`.
-/
theorem isLatTup_smul_iff (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := forall_congr' fun v => isLattice_map_iff _ _

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨fun _ => 1, h, by simp⟩`.
-/
theorem one_mem_tenV (M : ∀ v, Submodule O (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf))
    (h : ∀ v, (1 : MvPolynomial _ Kf) ∈ M v) : (1 : P.Xsp) ∈ P.tenV M := Submodule.subset_span ⟨fun _ => 1, h, by simp⟩

variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)

include h0 in
/- English proof (translation)
Unfold `Places.Htup`. Apply `one_mem_tenV` to reduce the goal to its premises. Introduce `v`. Unfold `Hten`. Apply `one_mem_tensorLat` to reduce the goal to its premises.

Introduce `s`. Simplify using `only [h0 v, lamAt_zero]`. Conclude with `one_mem_H0_weight_zero O Kf _ _`.
-/
theorem one_mem_Htup (L : P.Tup) : (1 : P.Xsp) ∈ P.Htup L := by
  unfold Places.Htup
  apply one_mem_tenV
  intro v
  unfold Hten
  apply one_mem_tensorLat
  intro s
  simp only [h0 v, lamAt_zero]
  exact one_mem_H0_weight_zero O Kf _ _

include h0 in
/- English proof (translation)
Unfold `Places.HtupW`. Apply `one_mem_tenV` to reduce the goal to its premises. Introduce `v`. Unfold `HtenW`. Apply `one_mem_tensorLat` to reduce the goal to its premises.

Introduce `s`. Simplify using `only [h0 v, lamAt_zero]`. Conclude with `one_mem_lattice_degree_zero O Kf _ _`.
-/
theorem one_mem_HtupW (L : P.Tup) : (1 : P.Xsp) ∈ P.HtupW L := by
  unfold Places.HtupW
  apply one_mem_tenV
  intro v
  unfold HtenW
  apply one_mem_tensorLat
  intro s
  simp only [h0 v, lamAt_zero]
  exact one_mem_lattice_degree_zero O Kf _ _

include h0 in
/- English proof (translation)
Simplify using `[Places.natAct, h0, lamAt_zero]`.
-/
theorem natAct_one' (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) : P.natAct A 1 = 1 := by
  simp [Places.natAct, h0, lamAt_zero]

open Classical in

def oneFn : P.Tup → P.Xsp := fun L => if P.IsLatTup L then 1 else 0

/- English proof (translation)
Simplify using `[oneFn, h]`.
-/
theorem oneFn_pos {L : P.Tup} (h : P.IsLatTup L) : oneFn P L = 1 := by simp [oneFn, h]

/- English proof (translation)
Simplify using `[oneFn, h]`.
-/
theorem oneFn_neg {L : P.Tup} (h : ¬ P.IsLatTup L) : oneFn P L = 0 := by simp [oneFn, h]

include h0 in
/- English proof (translation)
Unfold `Level.funMod`. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply]`. Introduce `L hL`. Rewrite using `[oneFn_pos P hL]`.

Conclude with `hH L`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]`. Introduce `L hL`. Conclude with `oneFn_neg P hL`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply, hχ, MonoidHom.one_apply, Units.val_one, one_smul]`.

Introduce `γ L`. Distinguish the cases in `hL : P.IsLatTup L`. Rewrite using `[oneFn_pos P ((isLatTup_smul_iff P C γ L).mpr hL), oneFn_pos P hL]`. Simplify using `[Level.actX, natAct_one' P h0]`. Rewrite using `[oneFn_neg P (mt (isLatTup_smul_iff P C γ L).mp hL), oneFn_neg P hL]`.

Simplify using the standard rewrite rules.
-/
theorem oneFn_mem (hχ : C.χ = 1) (Hv : P.Tup → Submodule O P.Xsp) (hH : ∀ L, (1 : P.Xsp) ∈ Hv L) :
    oneFn P ∈ C.funMod Hv := by
  unfold Level.funMod
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply]
    intro L hL
    rw [oneFn_pos P hL]
    exact hH L
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
    intro L hL
    exact oneFn_neg P hL
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, hχ, MonoidHom.one_apply, Units.val_one, one_smul]
    intro γ L
    by_cases hL : P.IsLatTup L
    · rw [oneFn_pos P ((isLatTup_smul_iff P C γ L).mpr hL), oneFn_pos P hL]
      simp [Level.actX, natAct_one' P h0]
    · rw [oneFn_neg P (mt (isLatTup_smul_iff P C γ L).mp hL), oneFn_neg P hL]
      simp

end Form

section Ex

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

/- English proof (translation)
Establish `h0 : ∀ v, (gat1 h).P.lam0 v = fun _ _ => 0`. Introduce `v`. Both sides reduce to the same expression. Establish `hχ : ∀ i, ((gat1 h).lev i).χ = 1`. Introduce `i`.

Both sides reduce to the same expression. Establish `hc : Nonempty (gat1 h).comp` using `by first`. Consider the case `exact ⟨()⟩`. Consider the case `(unfold gat1; exact (rfl : 1 = 1))`. Take `⟨i0⟩` from `hc`.

Set `L0 : (gat1 h).P.Tup` to `fun v => colSpan ((gat1 h).P.W v) (1 : Matrix (Fin ((gat1 h).P.m + 1)) (Fin ((gat1 h).P.m + 1)) ((gat1 h).P.Qq v))`. Establish `hL0 : (gat1 h).P.IsLatTup L0` using `fun v => ⟨1, by simp, rfl⟩`. Use `⟨fun _ => oneFn (gat1 h).P, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [GAtP.M, GAtP.funMod, Submodule.mem_pi]`. Introduce `i _`.

Conclude with `oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_HtupW _ h0 L)`. Simplify using `only [GAtP.Mna, GAtP.funMod, Submodule.mem_pi]`. Introduce `i _`. Conclude with `oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_Htup _ h0 L)`. Introduce `hF`.

Establish `h1` using `congrFun (congrFun hF i0) L0`. Simplify using `only [Pi.zero_apply] at h1`. Rewrite `h1` using `[oneFn_pos _ hL0]`. Conclude with `one_ne_zero h1`.
-/
theorem exists_integral_nonzero_form (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    ∃ F : (gat1 h).Fn, F ∈ (gat1 h).M ∧ F ∈ (gat1 h).Mna ∧ F ≠ 0 := by
  have h0 : ∀ v, (gat1 h).P.lam0 v = fun _ _ => 0 := by
    intro v
    rfl
  have hχ : ∀ i, ((gat1 h).lev i).χ = 1 := by
    intro i
    rfl
  have hc : Nonempty (gat1 h).comp := by
    first
      | exact ⟨()⟩
      | (unfold gat1; exact (rfl : 1 = 1))
  obtain ⟨i0⟩ := hc
  let L0 : (gat1 h).P.Tup := fun v => colSpan ((gat1 h).P.W v)
    (1 : Matrix (Fin ((gat1 h).P.m + 1)) (Fin ((gat1 h).P.m + 1)) ((gat1 h).P.Qq v))
  have hL0 : (gat1 h).P.IsLatTup L0 := fun v => ⟨1, by simp, rfl⟩
  refine ⟨fun _ => oneFn (gat1 h).P, ?_, ?_, ?_⟩
  · simp only [GAtP.M, GAtP.funMod, Submodule.mem_pi]
    intro i _
    exact oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_HtupW _ h0 L)
  · simp only [GAtP.Mna, GAtP.funMod, Submodule.mem_pi]
    intro i _
    exact oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_Htup _ h0 L)
  · intro hF
    have h1 := congrFun (congrFun hF i0) L0
    simp only [Pi.zero_apply] at h1
    rw [oneFn_pos _ hL0] at h1
    exact one_ne_zero h1

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `h` using `Formalism.BasicNotions.Examples₂.LevelValuationRings.hidaSettingOfEven p 2 h5 le_rfl even_two`. Take `⟨F, h1, h2, h3⟩` from `exists_integral_nonzero_form h`. Use `⟨gat1 h, le_rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, ?_, ?_⟩` and prove the remaining obligations. Introduce `hb`.

Rewrite `h1` using `[hb]`. Conclude with `h3 ((Submodule.mem_bot _).1 h1)`. Introduce `hb`. Rewrite `h2` using `[hb]`. Conclude with `h3 ((Submodule.mem_bot _).1 h2)`.
-/
theorem gat_nonempty_form (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ G.TrivStab ∧ G.FinClasses ∧ G.M ≠ ⊥ ∧ G.Mna ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Formalism.BasicNotions.Examples₂.LevelValuationRings.hidaSettingOfEven p 2 h5 le_rfl even_two
  obtain ⟨F, h1, h2, h3⟩ := exists_integral_nonzero_form h
  refine ⟨gat1 h, le_rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, ?_, ?_⟩
  · intro hb; rw [hb] at h1; exact h3 ((Submodule.mem_bot _).1 h1)
  · intro hb; rw [hb] at h2; exact h3 ((Submodule.mem_bot _).1 h2)

end Ex

end Formalism.MainNotions.G.Inhab

end
