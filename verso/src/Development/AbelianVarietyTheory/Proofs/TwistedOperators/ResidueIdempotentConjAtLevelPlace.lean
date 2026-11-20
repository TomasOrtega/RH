import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjIdem

/- English proof (translation)
Establish `h0 : resS D.host.F PP ((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) = 0`. Use `(map_natCast (resS D.host.F PP) g).trans ?_` and prove the remaining obligations. Use `(map_natCast (Ideal.Quotient.mk PP.asIdeal) g).symm.trans ?_` and prove the remaining obligations. Conclude with `(Ideal.Quotient.eq_zero_iff_mem).2 hg`. Establish `h1` using `(GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).1 h0`.

Establish `e : (((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) : EAf D) = (g : EAf D)` using `map_natCast (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D).subtype g`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem natCast_cpt_lt {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (g : EAf D)) < 1 := by
  have h0 : resS D.host.F PP ((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) = 0 := by
    refine (map_natCast (resS D.host.F PP) g).trans ?_
    refine (map_natCast (Ideal.Quotient.mk PP.asIdeal) g).symm.trans ?_
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hg
  have h1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).1 h0
  have e : (((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) : EAf D) = (g : EAf D) := map_natCast (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D).subtype g
  rwa [e] at h1

/- English proof (translation)
Rewrite using `[Matrix.mulVec_add, Pi.add_apply]`.
-/
theorem mulVec_add_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (i : Fin n) :
    (M *ᵥ (x + y)) i = (M *ᵥ x) i + (M *ᵥ y) i := by
  rw [Matrix.mulVec_add, Pi.add_apply]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`.
-/
theorem mulVec_smul_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (c : R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ (c • y)) i = c * (M *ᵥ y) i := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_zero, Pi.zero_apply]`.
-/
theorem mulVec_zero_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (M *ᵥ (0 : Fin n → R)) i = 0 := by
  rw [Matrix.mulVec_zero, Pi.zero_apply]

/- English proof (translation)
Establish `hL : ∀ x : VA (II D), x ∈ (II D).Lf → ∀ i, ((β⁻¹).val *ᵥ (x : Fin (Yc D 0).rank → EAf D)) i ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D`. Introduce `x hx`. Establish `h1 : x ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := (GlobalTheory.ConjPlaceRed.mem_Lf D x).2 hx`. Rewrite `h1` using `[hβ]`. Conclude with `(GlobalTheory.AdIsom.mem_hat_lat β x).1 h1`.

Unfold `mL at hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Introduce `i`.

Use `⟨((β⁻¹).val *ᵥ (y : Fin (Yc D 0).rank → EAf D)) i, hL y hy i, ?_⟩` and prove the remaining obligations. Establish `e1 : (((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) = (g : EAf D)` using `map_natCast (IntAf (II D).F (II D).E).subtype g`. Establish `e2` using `mulVec_smul_apply (β⁻¹).val (show EAf D from ((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) (y : Fin (Yc D 0).rank → EAf D) i`. Rewrite `e2` using `[e1]`. Conclude with `e2`.

Consider the case `zero => intro i`. Conclude with `⟨0, zero_mem _, (mulVec_zero_apply (β⁻¹).val i).trans (mul_zero _).symm⟩`. Consider the case `add x y _ _ hx hy`. Introduce `i`. Take `⟨a, ha, ea⟩` from `hx i`.

Take `⟨b, hb, eb⟩` from `hy i`. Use `⟨a + b, add_mem ha hb, ?_⟩` and prove the remaining obligations. Use `(mulVec_add_apply (β⁻¹).val (x : Fin (Yc D 0).rank → EAf D) y i).trans ?_` and prove the remaining obligations. Rewrite using `[ea, eb, mul_add]`. Consider the case `smul c x _ hx`.

Introduce `i`. Take `⟨a, ha, ea⟩` from `hx i`. Use `⟨(show EAf D from c.1) * a, mul_mem c.2 ha, ?_⟩` and prove the remaining obligations. Use `(mulVec_smul_apply (β⁻¹).val (show EAf D from c.1) (x : Fin (Yc D 0).rank → EAf D) i).trans ?_` and prove the remaining obligations. Rewrite using `[ea]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord_mL {D : D7} (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : GlobalTheory.PlaceModel.latFrame (Yc D 0) = GlobalTheory.NormSum.AdLattice.lat β) (w : VA (II D)) (hw : w ∈ mL (II D) g) :
    ∀ i, ∃ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, ((β⁻¹).val *ᵥ (w : Fin (Yc D 0).rank → EAf D)) i = (g : EAf D) * a := by
  have hL : ∀ x : VA (II D), x ∈ (II D).Lf → ∀ i, ((β⁻¹).val *ᵥ (x : Fin (Yc D 0).rank → EAf D)) i ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D := by
    intro x hx
    have h1 : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := (GlobalTheory.ConjPlaceRed.mem_Lf D x).2 hx
    rw [hβ] at h1
    exact (GlobalTheory.AdIsom.mem_hat_lat β x).1 h1
  unfold mL at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    refine ⟨((β⁻¹).val *ᵥ (y : Fin (Yc D 0).rank → EAf D)) i, hL y hy i, ?_⟩
    have e1 : (((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) = (g : EAf D) :=
      map_natCast (IntAf (II D).F (II D).E).subtype g
    have e2 := mulVec_smul_apply (β⁻¹).val (show EAf D from ((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) (y : Fin (Yc D 0).rank → EAf D) i
    rw [e1] at e2
    exact e2
  | zero => intro i; exact ⟨0, zero_mem _, (mulVec_zero_apply (β⁻¹).val i).trans (mul_zero _).symm⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    obtain ⟨b, hb, eb⟩ := hy i
    refine ⟨a + b, add_mem ha hb, ?_⟩
    refine (mulVec_add_apply (β⁻¹).val (x : Fin (Yc D 0).rank → EAf D) y i).trans ?_
    rw [ea, eb, mul_add]
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    refine ⟨(show EAf D from c.1) * a, mul_mem c.2 ha, ?_⟩
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c.1) (x : Fin (Yc D 0).rank → EAf D) i).trans ?_
    rw [ea]
    ring

end GlobalTheory.SeeConjIdem

namespace GlobalTheory.SeeConjIdem

/- English proof (translation)
Establish `h` using `Formalism.L2.SG.InstExistsPf.rank_eq D`. Establish `h2 : (Yc D 0).rank = D.R.r` using `h`. Take `⟨j, hj⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Rewrite using `[h2]`.

Simplify using `only [Formalism.BasicNotions.Ranks.r]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_pos (D : D7) : 0 < (Yc D 0).rank := by
  have h := Formalism.L2.SG.InstExistsPf.rank_eq D
  have h2 : (Yc D 0).rank = D.R.r := h
  obtain ⟨j, hj⟩ := D.R.m_even
  have := D.R.two_le_m
  rw [h2]
  simp only [Formalism.BasicNotions.Ranks.r]
  omega

/- English proof (translation)
Take `⟨β, hβ⟩` from `GlobalTheory.AdIsom.exists_eq_lat (GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)).1`. Set `i0 : Fin (Yc D 0).rank` to `⟨0, rank_pos D⟩`. Set `y : Fin (Yc D 0).rank → EAf D` to `β.val *ᵥ Pi.single i0 1`. Establish `hby : (β⁻¹).val *ᵥ y = Pi.single i0 1`. Simplify using `only [y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Set `yv : VA (II D)` to `y`. Establish `hyL : yv ∈ (II D).Lf`. Use `(GlobalTheory.ConjPlaceRed.mem_Lf D y).1 ?_` and prove the remaining obligations. Rewrite using `[hβ]`. Use `(GlobalTheory.AdIsom.mem_hat_lat β y).2 fun i => ?_` and prove the remaining obligations.

Rewrite using `[hby, Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Take `⟨a, ha, ea⟩` from `coord_mL g β hβ _ (hy yv hyL) i0`.

Establish `e3 : ((β⁻¹).val *ᵥ ((c • yv : VA (II D)) : Fin (Yc D 0).rank → EAf D)) i0 = (show EAf D from c)`. Use `(mulVec_smul_apply (β⁻¹).val (show EAf D from c) y i0).trans ?_` and prove the remaining obligations. Rewrite using `[hby, Pi.single_eq_same, mul_one]`. Establish `ea' : (show EAf D from c) = (g : EAf D) * a` using `e3.symm.trans ea`. Rewrite using `[ea', map_mul, Valuation.map_mul, mul_comm]`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((GlobalTheory.AdIsom.mem_OA a).1 ha PP) zero_le (natCast_cpt_lt g PP hg)`.
-/
theorem cpt_lt_of_smul_mem {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal)
    (c : (II D).E ⊗[(II D).F] Af (II D).F) (hy : ∀ y ∈ (II D).Lf, c • y ∈ mL (II D) g) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (show EAf D from c)) < 1 := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdIsom.exists_eq_lat (GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)).1
  let i0 : Fin (Yc D 0).rank := ⟨0, rank_pos D⟩
  let y : Fin (Yc D 0).rank → EAf D := β.val *ᵥ Pi.single i0 1
  have hby : (β⁻¹).val *ᵥ y = Pi.single i0 1 := by
    simp only [y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let yv : VA (II D) := y
  have hyL : yv ∈ (II D).Lf := by
    refine (GlobalTheory.ConjPlaceRed.mem_Lf D y).1 ?_
    rw [hβ]
    refine (GlobalTheory.AdIsom.mem_hat_lat β y).2 fun i => ?_
    rw [hby, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨a, ha, ea⟩ := coord_mL g β hβ _ (hy yv hyL) i0
  have e3 : ((β⁻¹).val *ᵥ ((c • yv : VA (II D)) : Fin (Yc D 0).rank → EAf D)) i0 = (show EAf D from c) := by
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c) y i0).trans ?_
    rw [hby, Pi.single_eq_same, mul_one]
  have ea' : (show EAf D from c) = (g : EAf D) * a := e3.symm.trans ea
  rw [ea', map_mul, Valuation.map_mul, mul_comm]
  exact mul_lt_one_of_nonneg_of_lt_one_right ((GlobalTheory.AdIsom.mem_OA a).1 ha PP) zero_le (natCast_cpt_lt g PP hg)

/- English proof (translation)
Establish `he' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP e = GlobalTheory.StdFrames.cpt PP e`. Rewrite using `[← map_mul, he]`. Establish `hs' : GlobalTheory.StdFrames.cpt PP s * GlobalTheory.StdFrames.cpt PP s = GlobalTheory.StdFrames.cpt PP s`. Rewrite using `[← map_mul, hs]`. Establish `hes' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP s = 0`.

Rewrite using `[← map_mul, hes, map_zero]`. Establish `i01 : ∀ x : PP.adicCompletion D.host.E, x * x = x → x = 0 ∨ x = 1`. Introduce `x hx`. Establish `: x * (x - 1) = 0` using `by rw [mul_sub, hx, mul_one, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `Or.inl h`. Conclude with `Or.inr (sub_eq_zero.1 h)`. Establish `r0 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 0 → resS D.host.F PP t = 0` using `fun t h => (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP t).2 (by rw [h, map_zero]; exact zero_lt_one)`. Establish `r1 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 1 → resS D.host.F PP t = 1`. Introduce `t h`.

Use `r0 (1 - t) (by` as an intermediate fact. Rewrite using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, h, sub_self])`. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `this.symm`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Establish `hf0 : GlobalTheory.StdFrames.cpt PP s = 0`. Rewrite `hes'` using `[h1, one_mul]`. Conclude with `hes'`. Conclude with `⟨r1 ⟨e, hei⟩ h1, r0 ⟨s, hsi⟩ hf0⟩`.

Introduce `hne`. Establish `he0 : GlobalTheory.StdFrames.cpt PP e = 0` using `(i01 _ he').resolve_right hne`. Establish `hf1 : GlobalTheory.StdFrames.cpt PP s = 1`. Break down `i01 _ hs' with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : GlobalTheory.StdFrames.cpt PP (1 - e - s) = 1`. Rewrite using `[map_sub (GlobalTheory.StdFrames.cpt PP), map_sub (GlobalTheory.StdFrames.cpt PP), map_one, he0, h, sub_zero, sub_zero]`. Rewrite `key` using `[h1, Valuation.map_one]`. Conclude with `lt_irrefl _ key`. Conclude with `h`.

Conclude with `⟨r0 ⟨e, hei⟩ he0, r1 ⟨s, hsi⟩ hf1⟩`.
-/
theorem resS_of_idem {D : D7} (PP : Pl D.host.E) (e s : EAf D) (he : e * e = e) (hs : s * s = s) (hes : e * s = 0)
    (hei : e ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) (hsi : s ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D)
    (key : Valued.v (GlobalTheory.StdFrames.cpt PP (1 - e - s)) < 1) :
    (GlobalTheory.StdFrames.cpt PP e = 1 → resS D.host.F PP ⟨e, hei⟩ = 1 ∧ resS D.host.F PP ⟨s, hsi⟩ = 0) ∧
      (GlobalTheory.StdFrames.cpt PP e ≠ 1 → resS D.host.F PP ⟨e, hei⟩ = 0 ∧ resS D.host.F PP ⟨s, hsi⟩ = 1) := by
  have he' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP e = GlobalTheory.StdFrames.cpt PP e := by
    rw [← map_mul, he]
  have hs' : GlobalTheory.StdFrames.cpt PP s * GlobalTheory.StdFrames.cpt PP s = GlobalTheory.StdFrames.cpt PP s := by
    rw [← map_mul, hs]
  have hes' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP s = 0 := by
    rw [← map_mul, hes, map_zero]
  have i01 : ∀ x : PP.adicCompletion D.host.E, x * x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have : x * (x - 1) = 0 := by rw [mul_sub, hx, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have r0 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 0 → resS D.host.F PP t = 0 :=
    fun t h => (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP t).2 (by rw [h, map_zero]; exact zero_lt_one)
  have r1 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 1 → resS D.host.F PP t = 1 := by
    intro t h
    have := r0 (1 - t) (by
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, h, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  constructor
  · intro h1
    have hf0 : GlobalTheory.StdFrames.cpt PP s = 0 := by
      rw [h1, one_mul] at hes'; exact hes'
    exact ⟨r1 ⟨e, hei⟩ h1, r0 ⟨s, hsi⟩ hf0⟩
  · intro hne
    have he0 : GlobalTheory.StdFrames.cpt PP e = 0 := (i01 _ he').resolve_right hne
    have hf1 : GlobalTheory.StdFrames.cpt PP s = 1 := by
      rcases i01 _ hs' with h | h
      · exfalso
        have h1 : GlobalTheory.StdFrames.cpt PP (1 - e - s) = 1 := by
          rw [map_sub (GlobalTheory.StdFrames.cpt PP), map_sub (GlobalTheory.StdFrames.cpt PP), map_one, he0, h, sub_zero, sub_zero]
        rw [h1, Valuation.map_one] at key
        exact lt_irrefl _ key
      · exact h
    exact ⟨r0 ⟨e, hei⟩ he0, r1 ⟨s, hsi⟩ hf1⟩

/- English proof (translation)
Introduce `D g ew hid hperp hint hy PP hg`. Establish `hs : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `GlobalTheory.AdIsom.cjA_mem hint`. Establish `hss : sigA (II D) ew * sigA (II D) ew = sigA (II D) ew` using `by rw [← map_mul, hid]`. Conclude with `⟨hint, hs, resS_of_idem PP ew (sigA (II D) ew) hid hss hperp hint hs (cpt_lt_of_smul_mem g PP hg _ hy)⟩`.
-/
theorem resS_idem_conj : ∀ {D : D7} (g : ℕ) (ew : (II D).E ⊗[(II D).F] Af (II D).F), ew * ew = ew → ew * sigA (II D) ew = 0 → ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → (∀ y ∈ (II D).Lf, (1 - ew - sigA (II D) ew) • y ∈ mL (II D) g) → ∀ PP : Pl D.host.E, ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h2 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (GlobalTheory.StdFrames.cpt PP ew = 1 → resS D.host.F PP ⟨ew, h1⟩ = 1 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 0) ∧ (GlobalTheory.StdFrames.cpt PP ew ≠ 1 → resS D.host.F PP ⟨ew, h1⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 1) := by
  intro D g ew hid hperp hint hy PP hg
  have hs : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hint
  have hss : sigA (II D) ew * sigA (II D) ew = sigA (II D) ew := by rw [← map_mul, hid]
  exact ⟨hint, hs, resS_of_idem PP ew (sigA (II D) ew) hid hss hperp hint hs (cpt_lt_of_smul_mem g PP hg _ hy)⟩

end GlobalTheory.SeeConjIdem
