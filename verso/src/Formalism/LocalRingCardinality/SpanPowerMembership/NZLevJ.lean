import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevI

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

/- English proof (translation)
Establish `key : ∀ v, ∃ A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v), ∃ n : Fin (P.m + 1) → ℤ, LowT A ∧ (∀ a, A a a = (p : P.Qq v) ^ (n a)) ∧ L v = colSpan (P.W v) A`. Introduce `v`. Use `haveI := (P.setting v).frac_alt`. Take `⟨A, n, h1, h2, h3⟩` from `hermite (Q := P.Qq v) (p : P.W v) (P.setting v).p_unif (L v) (hL v)`. Conclude with `⟨A, n, h1, fun a => by rw [h2 a, map_natCast], h3⟩`.

Use `choose A n hlow hdiag hLA using key`. Establish `hp0 : ∀ v, (p : P.Qq v) ≠ 0` using `fun v => by haveI := (P.setting v).frac_alt`. Rewrite using `[← map_natCast (algebraMap (P.W v) (P.Qq v))]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (P.setting v).p_unif.ne_zero`. Establish `hdet : ∀ v, (A v).det ≠ 0`.

Introduce `v`. Rewrite using `[det_lowT _ (hlow v)]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => by rw [hdiag]; exact zpow_ne_zero _ (hp0 v)`. Set `Ag : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)` to `fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (A v) (hdet v)`. Take `⟨c, ⟨z, rfl⟩, hc⟩` from `natAct_inv_lowT P (p : Kf) hp Ag hlow (fun v s a => ⟨n v a, by`.

Rewrite using `[gPos_diag]`. Use `show P.ι v ((P.σ v ^ s.val) (A v a a)) = _`. Rewrite using `[hdiag, map_zpow₀, map_zpow₀, map_natCast, map_natCast]⟩)`. Establish `hmem : (Ag⁻¹, (1 : Oˣ)) ∈ Γsub P hp` using `⟨z, by rw [hc]; simp⟩`. Establish `hmem' : (Ag, (1 : Oˣ)) ∈ Γsub P hp`.

Use `(Γsub P hp).inv_mem hmem` as an intermediate fact. Simplify using `using this`. Use `⟨⟨(Ag, 1), hmem'⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Use `show (L0 P v).map ((Matrix.mulVecLin (A v)).restrictScalars (P.W v)) = L v`.

Rewrite using `[hLA v]`. Unfold `L0`. Rewrite using `[Formalism.MainNotions.G.Inhab.map_colSpan', Matrix.mul_one]`.
-/
theorem exists_trans (L : P.Tup) (hL : P.IsLatTup L) : ∃ γ : ↥(Γsub P hp), (levB P hp).smul γ (standardTuple P) = L := by
  classical
  have key : ∀ v, ∃ A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v), ∃ n : Fin (P.m + 1) → ℤ,
      LowT A ∧ (∀ a, A a a = (p : P.Qq v) ^ (n a)) ∧ L v = colSpan (P.W v) A := by
    intro v
    haveI := (P.setting v).frac_alt
    obtain ⟨A, n, h1, h2, h3⟩ := hermite (Q := P.Qq v) (p : P.W v) (P.setting v).p_unif (L v) (hL v)
    exact ⟨A, n, h1, fun a => by rw [h2 a, map_natCast], h3⟩
  choose A n hlow hdiag hLA using key
  have hp0 : ∀ v, (p : P.Qq v) ≠ 0 := fun v => by
    haveI := (P.setting v).frac_alt
    rw [← map_natCast (algebraMap (P.W v) (P.Qq v))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (P.setting v).p_unif.ne_zero
  have hdet : ∀ v, (A v).det ≠ 0 := by
    intro v; rw [det_lowT _ (hlow v)]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by rw [hdiag]; exact zpow_ne_zero _ (hp0 v)
  let Ag : ∀ v, GL (Fin (P.m + 1)) (P.Qq v) := fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (A v) (hdet v)
  obtain ⟨c, ⟨z, rfl⟩, hc⟩ := natAct_inv_lowT P (p : Kf) hp Ag hlow (fun v s a => ⟨n v a, by
    rw [gPos_diag]
    show P.ι v ((P.σ v ^ s.val) (A v a a)) = _
    rw [hdiag, map_zpow₀, map_zpow₀, map_natCast, map_natCast]⟩)
  have hmem : (Ag⁻¹, (1 : Oˣ)) ∈ Γsub P hp := ⟨z, by rw [hc]; simp⟩
  have hmem' : (Ag, (1 : Oˣ)) ∈ Γsub P hp := by
    have := (Γsub P hp).inv_mem hmem
    simpa using this
  refine ⟨⟨(Ag, 1), hmem'⟩, ?_⟩
  funext v
  show (L0 P v).map ((Matrix.mulVecLin (A v)).restrictScalars (P.W v)) = L v
  rw [hLA v]
  unfold L0
  rw [Formalism.MainNotions.G.Inhab.map_colSpan', Matrix.mul_one]

def gOf (L : P.Tup) (hL : P.IsLatTup L) : (levB P hp).Γ := (exists_trans P hp L hL).choose

/- English proof (translation)
The claim follows from `(exists_trans P hp L hL).choose_spec`.
-/
theorem gOf_spec (L : P.Tup) (hL : P.IsLatTup L) : (levB P hp).smul (gOf P hp L hL) (standardTuple P) = L :=
  (exists_trans P hp L hL).choose_spec

variable (v0 : Fin P.nV)

include v0 in
/- English proof (translation)
Establish `hk : (levB P hp).smul (g'⁻¹ * g) (standardTuple P) = standardTuple P`. Rewrite using `[jd_smul_mul, h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]`. Establish `hs` using `stab_EV P hp v0 (g'⁻¹ * g) hk`. Establish `hg : g = g' * (g'⁻¹ * g)` using `by group`. Use `conv_lhs => rw [hg, map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul, ← LinearMap.map_smul_of_tower, hs]`.
-/
theorem wd (g g' : (levB P hp).Γ) (h : (levB P hp).smul g (standardTuple P) = (levB P hp).smul g' (standardTuple P)) :
    ((levB P hp).χ g : O) • (levB P hp).actX g (EV P) = ((levB P hp).χ g' : O) • (levB P hp).actX g' (EV P) := by
  have hk : (levB P hp).smul (g'⁻¹ * g) (standardTuple P) = standardTuple P := by
    rw [jd_smul_mul, h, ← jd_smul_mul, inv_mul_cancel, jd_smul_one]
  have hs := stab_EV P hp v0 (g'⁻¹ * g) hk
  have hg : g = g' * (g'⁻¹ * g) := by group
  conv_lhs => rw [hg, map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul,
    ← LinearMap.map_smul_of_tower, hs]

open Classical in

def valE (L : P.Tup) : P.Xsp :=
  if hL : P.IsLatTup L then ((levB P hp).χ (gOf P hp L hL) : O) • (levB P hp).actX (gOf P hp L hL) (EV P) else 0

include v0 in
/- English proof (translation)
Unfold `valE`. Rewrite using `[dif_pos (standardTuple_isLattice P)]`. Use `wd P hp v0 (gOf P hp (standardTuple P) (standardTuple_isLattice P)) 1 (by rw [gOf_spec, jd_smul_one])` as an intermediate fact. Rewrite using `[this, map_one, Units.val_one, one_smul, jd_actX_one, LinearMap.id_apply]`.
-/
theorem value_standardTuple : valE P hp (standardTuple P) = EV P := by
  classical
  unfold valE
  rw [dif_pos (standardTuple_isLattice P)]
  have := wd P hp v0 (gOf P hp (standardTuple P) (standardTuple_isLattice P)) 1 (by rw [gOf_spec, jd_smul_one])
  rw [this, map_one, Units.val_one, one_smul, jd_actX_one, LinearMap.id_apply]

include v0 in
/- English proof (translation)
Unfold `valE`. Distinguish the cases in `hL : P.IsLatTup L`. Establish `hL' : P.IsLatTup ((levB P hp).smul γ L)` using `(Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mpr hL`. Rewrite using `[dif_pos hL', dif_pos hL]`. Rewrite using `[wd P hp v0 (gOf P hp _ hL') (γ * gOf P hp L hL) (by rw [gOf_spec, jd_smul_mul, gOf_spec])]`.

Rewrite using `[map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul, LinearMap.map_smul_of_tower]`. Establish `hL' : ¬ P.IsLatTup ((levB P hp).smul γ L)` using `fun h => hL ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mp h)`. Rewrite using `[dif_neg hL', dif_neg hL, map_zero, smul_zero]`.
-/
theorem valE_smul (γ : (levB P hp).Γ) (L : P.Tup) :
    valE P hp ((levB P hp).smul γ L) = ((levB P hp).χ γ : O) • (levB P hp).actX γ (valE P hp L) := by
  classical
  unfold valE
  by_cases hL : P.IsLatTup L
  · have hL' : P.IsLatTup ((levB P hp).smul γ L) := (Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mpr hL
    rw [dif_pos hL', dif_pos hL]
    rw [wd P hp v0 (gOf P hp _ hL') (γ * gOf P hp L hL) (by rw [gOf_spec, jd_smul_mul, gOf_spec])]
    rw [map_mul, Units.val_mul, jd_actX_mul, LinearMap.comp_apply, mul_smul, LinearMap.map_smul_of_tower]
  · have hL' : ¬ P.IsLatTup ((levB P hp).smul γ L) := fun h =>
      hL ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff P (levB P hp) γ L).mp h)
    rw [dif_neg hL', dif_neg hL, map_zero, smul_zero]

/- English proof (translation)
Unfold `valE`. Rewrite using `[dif_pos hL]`. Establish `h1` using `Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () (gOf P hp L hL) (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)`. Establish `h2 : (gatU P hp).P.HtupW (((gatU P hp).lev ()).smul (gOf P hp L hL) (standardTuple P)) = P.HtupW L` using `by show P.HtupW ((levB P hp).smul (gOf P hp L hL) (standardTuple P)) = _`. Rewrite using `[gOf_spec]`.

Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem valE_mem (L : P.Tup) (hL : P.IsLatTup L) : valE P hp L ∈ P.HtupW L := by
  classical
  unfold valE
  rw [dif_pos hL]
  have h1 := Formalism.L2.G.Cmp.equivSys_HtupW (gatU P hp) () (gOf P hp L hL) (standardTuple P) (standardTuple_isLattice P) (EV P) (EV_mem P)
  have h2 : (gatU P hp).P.HtupW (((gatU P hp).lev ()).smul (gOf P hp L hL) (standardTuple P)) = P.HtupW L := by
    show P.HtupW ((levB P hp).smul (gOf P hp L hL) (standardTuple P)) = _
    rw [gOf_spec]
  rw [h2] at h1
  exact h1

end Formalism.BasicNotions.Examples₂.NZ
