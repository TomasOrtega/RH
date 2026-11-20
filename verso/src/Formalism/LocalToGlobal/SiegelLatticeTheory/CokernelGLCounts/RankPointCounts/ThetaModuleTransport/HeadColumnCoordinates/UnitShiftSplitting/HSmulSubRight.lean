import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Establish `: c • (x - y) = c • x + (-c) • y` using `by rw [smul_sub, sub_eq_add_neg, neg_smul]`. Rewrite using `[this, H.h_add_left, H.h_smul_left, H.h_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_smul_sub_left (H : HermSp M V) (c : E) (x y z : V) :
    H.h (c • (x - y)) z = c * (H.h x z - H.h y z) := by
  have : c • (x - y) = c • x + (-c) • y := by rw [smul_sub, sub_eq_add_neg, neg_smul]
  rw [this, H.h_add_left, H.h_smul_left, H.h_smul_left]
  ring

/- English proof (translation)
Rewrite using `[H.h_herm, h_smul_sub_left, map_mul, map_sub, ← H.h_herm, ← H.h_herm]`.
-/
theorem h_smul_sub_right (H : HermSp M V) (c : E) (x y z : V) :
    H.h z (c • (x - y)) = M.L.cj c * (H.h z x - H.h z y) := by
  rw [H.h_herm, h_smul_sub_left, map_mul, map_sub, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
The claim follows from `g.e_cj x`.
-/
theorem e_cj (g : SplitG M.L) (x : E) : g.e (M.L.cj x) = ((g.e x).2, (g.e x).1) := g.e_cj x

/- English proof (translation)
Establish `hq0 : (g.q : F) ≠ 0` using `fun h => g.q_irr.ne_zero (Subtype.ext h)`. Use `set q : F := (g.q : F) with hqdef`. Use `set qi : E := algebraMap F E q⁻¹ with hqi`. Establish `hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a))`. Unfold `HermSp.MMfam`.

Rewrite using `[hs]`. Establish `memf : ∀ a, t.f a ∈ MMo H t` using `fun a => Submodule.subset_span ⟨Sum.inl a, by rw [hMM]; rfl⟩`. Establish `memg : ∀ a, qi • (t.f' a - t.f a) ∈ MMo H t` using `fun a => Submodule.subset_span ⟨Sum.inr a, by rw [hMM]; rfl⟩`. Establish `i1` using `comp_mem_O g (hint _ (memg b) _ (memf a))`. Establish `i2` using `comp_mem_O g (hint _ (memg a) _ (memf b))`.

Establish `i3` using `comp_mem_O g (hint _ (memg b) _ (memg a))`. Rewrite `i1`, `i2` using `[h_smul_sub_left]`. Rewrite `i3` using `[h_smul_sub_left, h_smul_sub_right, h_smul_sub_right, H.h_herm (t.f' a) (t.f b)]`. Take `⟨c, hc⟩` from `hT`. Establish `eqi : g.e qi = (q⁻¹, q⁻¹)` using `e_alg g _`.

Establish `cqi : M.L.cj qi = qi` using `cj_alg _`. Establish `eZ : ∀ a b, H.Zhat t.f t.f' a b = H.h (t.f' b) (t.f a)` using `fun _ _ => rfl`. Unfold `HermSp.ZZplusOf`. Rewrite using `[hs]`. Simplify using `only [Matrix.of_apply, eZ]`.

Use `set z := g.e (H.h (t.f' b) (t.f a)) with hz`. Use `set w := g.e (H.h (t.f' a) (t.f b)) with hw`. Distinguish the cases in `hab : a = Fin.last r ∧ b = Fin.last r`. Take `⟨rfl, rfl⟩` from `hab`. Rewrite using `[if_pos ⟨rfl, rfl⟩]`.

Rewrite `i1` using `[hF.2]`. Rewrite `i3` using `[hF.2, hF'.2]`. Simplify using `only [map_mul, map_sub, map_add, map_neg, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at i1 i3`. Rewrite `i1`, `i3` using `[← hz]`. Apply `mem_R_of hs` to reduce the goal to its premises.

Simplify using `only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, ← hz, ← hqdef]`. Use `i1.1 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Simplify using `only [map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub, ← hz, ← hqdef]`.

Establish `: -(z.2 / q) - t.T' / q = -(q⁻¹ * (z.2 - -t.T)) + q * c` using `by field_simp; linear_combination hc`. Rewrite using `[this]`. Conclude with `(𝒪[F]).add_mem ((𝒪[F]).neg_mem i1.2) ((𝒪[F]).mul_mem g.q.2 c.2)`. Use `⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, ← hz, ← hqdef]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[if_neg hab, sub_zero]`. Establish `hab' : a ≠ Fin.last r ∨ b ≠ Fin.last r` using `not_and_or.1 hab`. Establish `hba' : b ≠ Fin.last r ∨ a ≠ Fin.last r` using `hab'.symm`.

Rewrite `i1` using `[hF.1 b a hba']`. Rewrite `i2` using `[hF.1 a b hab']`. Rewrite `i3` using `[hF.1 b a hba', hF'.1 b a hba']`. Simplify using `only [map_mul, map_sub, map_add, map_neg, map_zero, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero] at i1 i2 i3`. Rewrite `i1`, `i3` using `[← hz]`.

Rewrite `i2`, `i3` using `[← hw]`. Apply `mem_R_of hs` to reduce the goal to its premises. Simplify using `only [AlgEquiv.apply_symm_apply, ← hqdef]`. Use `i1.1 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Simplify using `only [AlgEquiv.apply_symm_apply, ← hqdef]`. Use `(𝒪[F]).neg_mem i2.2 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩` and prove the remaining obligations. Simplify using `only [AlgEquiv.apply_symm_apply, ← hqdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zz_mem_R {g : SplitG M.L} (hs : M.split = some g) (H : HermSp M V) {r : ℕ} (t : Term V M r)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hT : ∃ c : 𝒪[F], t.T - t.T' = (g.q : F) ^ 2 * c) (hint : MMInt H t) (a b : Fin (r + 1)) :
    HermSp.ZZplusOf M (H.Zhat t.f t.f') t.T t.T' a b ∈ M.R := by
  have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  set q : F := (g.q : F) with hqdef
  set qi : E := algebraMap F E q⁻¹ with hqi
  have hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) := by
    unfold HermSp.MMfam; rw [hs]
  have memf : ∀ a, t.f a ∈ MMo H t := fun a => Submodule.subset_span ⟨Sum.inl a, by rw [hMM]; rfl⟩
  have memg : ∀ a, qi • (t.f' a - t.f a) ∈ MMo H t :=
    fun a => Submodule.subset_span ⟨Sum.inr a, by rw [hMM]; rfl⟩
  have i1 := comp_mem_O g (hint _ (memg b) _ (memf a))
  have i2 := comp_mem_O g (hint _ (memg a) _ (memf b))
  have i3 := comp_mem_O g (hint _ (memg b) _ (memg a))
  rw [h_smul_sub_left] at i1 i2
  rw [h_smul_sub_left, h_smul_sub_right, h_smul_sub_right, H.h_herm (t.f' a) (t.f b)] at i3
  obtain ⟨c, hc⟩ := hT
  have eqi : g.e qi = (q⁻¹, q⁻¹) := e_alg g _
  have cqi : M.L.cj qi = qi := cj_alg _
  have eZ : ∀ a b, H.Zhat t.f t.f' a b = H.h (t.f' b) (t.f a) := fun _ _ => rfl
  unfold HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply, eZ]
  set z := g.e (H.h (t.f' b) (t.f a)) with hz
  set w := g.e (H.h (t.f' a) (t.f b)) with hw
  by_cases hab : a = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hab
    rw [if_pos ⟨rfl, rfl⟩]
    rw [hF.2] at i1
    rw [hF.2, hF'.2] at i3
    simp only [map_mul, map_sub, map_add, map_neg, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at i1 i3
    rw [← hz] at i1 i3
    apply mem_R_of hs
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, ← hz, ← hqdef]
      convert i1.1 using 1; field_simp; try ring
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub, ← hz, ← hqdef]
      have : -(z.2 / q) - t.T' / q = -(q⁻¹ * (z.2 - -t.T)) + q * c := by
        field_simp; linear_combination hc
      rw [this]
      exact (𝒪[F]).add_mem ((𝒪[F]).neg_mem i1.2) ((𝒪[F]).mul_mem g.q.2 c.2)
    · refine ⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩
      simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, ← hz, ← hqdef]
      field_simp
      try ring
  · rw [if_neg hab, sub_zero]
    have hab' : a ≠ Fin.last r ∨ b ≠ Fin.last r := not_and_or.1 hab
    have hba' : b ≠ Fin.last r ∨ a ≠ Fin.last r := hab'.symm
    rw [hF.1 b a hba'] at i1
    rw [hF.1 a b hab'] at i2
    rw [hF.1 b a hba', hF'.1 b a hba'] at i3
    simp only [map_mul, map_sub, map_add, map_neg, map_zero, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero,
      Prod.snd_zero] at i1 i2 i3
    rw [← hz] at i1 i3
    rw [← hw] at i2 i3
    apply mem_R_of hs
    · simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      convert i1.1 using 1; field_simp; try ring
    · simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      convert (𝒪[F]).neg_mem i2.2 using 1; field_simp; ring
    · refine ⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩
      simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      field_simp
      ring

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
