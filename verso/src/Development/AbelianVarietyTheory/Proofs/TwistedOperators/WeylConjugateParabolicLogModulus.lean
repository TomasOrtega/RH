import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyUnipotentInvariant
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab diagH)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.LeviShift.WeylDelta

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]`. Simplify using `[hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]`.
-/
theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (coordR V R x) (coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum,
    starRingEnd_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[coordR]`.
-/
theorem coordR_smul (c : E) (x : V.V) : coordR (F := F) V R (c • x) = inclR (F := F) R c • coordR V R x := by
  funext i; simp [coordR]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `hR R hc.sig V.gram x (act hc V g y) = hR R hc.sig V.gram (act hc V g⁻¹ x) y`. Rewrite using `[← hR_act hc V g (act hc V g⁻¹ x) y, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]`.
-/
theorem hLin_act_left (g : HA R hc.sig V.gram) (y x : Fin V.rank → R ⊗[F] E) :
    hLin hc.sig V.gram R (act hc V g y) x = hLin hc.sig V.gram R y (act hc V g⁻¹ x) := by
  change hR R hc.sig V.gram x (act hc V g y) = hR R hc.sig V.gram (act hc V g⁻¹ x) y
  rw [← hR_act hc V g (act hc V g⁻¹ x) y, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]

/- English proof (translation)
Establish `h` using `hLin_smul_left hc.sig V.gram R 0 0 x`. Rewrite `h` using `[zero_smul, zero_mul]`. Then use the resulting hypothesis.
-/
theorem hLin_zero_left (x : Fin V.rank → R ⊗[F] E) : hLin hc.sig V.gram R 0 x = 0 := by
  have h := hLin_smul_left hc.sig V.gram R 0 0 x
  rwa [zero_smul, zero_mul] at h

/- English proof (translation)
Unfold `bas dbas`. Apply the tactic sequence `by_cases ht : u t = -1 <;> by_cases hi : u i = -1`. Rewrite using `[if_pos ht, if_pos hi, HSpace.hD, ← V.herm.eq, ← HSpace.hD, Φ.ef]`. Distinguish the cases in `e : i = t`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg e, if_neg (Ne.symm e), map_zero]`. Rewrite using `[if_pos ht, if_neg hi, Φ.ff, if_neg (fun e : t = i => hi (e ▸ ht))]`. Rewrite using `[if_neg ht, if_pos hi, Φ.ee, if_neg (fun e : t = i => ht (e ▸ hi))]`. Rewrite using `[if_neg ht, if_neg hi, Φ.ef]`.
-/
theorem hD_bas_dbas (Φ : WittFrame V) (u : SV (wittIndex V)) (t i : Fin (wittIndex V)) :
    V.hD (bas Φ u t) (dbas Φ u i) = if t = i then 1 else 0 := by
  unfold bas dbas
  by_cases ht : u t = -1 <;> by_cases hi : u i = -1
  · rw [if_pos ht, if_pos hi, HSpace.hD, ← V.herm.eq, ← HSpace.hD, Φ.ef]
    by_cases e : i = t
    · subst e; simp
    · rw [if_neg e, if_neg (Ne.symm e), map_zero]
  · rw [if_pos ht, if_neg hi, Φ.ff, if_neg (fun e : t = i => hi (e ▸ ht))]
  · rw [if_neg ht, if_pos hi, Φ.ee, if_neg (fun e : t = i => ht (e ▸ hi))]
  · rw [if_neg ht, if_neg hi, Φ.ef]

/- English proof (translation)
Unfold `bas`. Use `split_ifs`. Introduce `h`. Use `Φ.ef i i` as an intermediate fact. Rewrite `this` using `[if_pos rfl, h]`.

Simplify using `[HSpace.hD] at this`. Conclude with `Φ.linearIndependent_e.ne_zero i`.
-/
theorem bas_ne_zero (Φ : WittFrame V) (u : SV (wittIndex V)) (i : Fin (wittIndex V)) : bas Φ u i ≠ 0 := by
  unfold bas
  split_ifs
  · intro h
    have := Φ.ef i i
    rw [if_pos rfl, h] at this
    simp [HSpace.hD] at this
  · exact Φ.linearIndependent_e.ne_zero i

/- English proof (translation)
Unfold `bas`. Use `split_ifs with h`. Conclude with `Submodule.subset_span (Or.inr ⟨i, h, rfl⟩)`. Establish `: u i = 1`. Generalize the expression as in `u i = s at hi h`.

Apply the tactic sequence `cases s <;> simp_all`. Conclude with `Submodule.subset_span (Or.inl ⟨i, this, rfl⟩)`.
-/
theorem bas_mem_sub (Φ : WittFrame V) {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) :
    bas Φ u i ∈ Φ.sub u := by
  unfold bas
  split_ifs with h
  · exact Submodule.subset_span (Or.inr ⟨i, h, rfl⟩)
  · have : u i = 1 := by
      generalize u i = s at hi h
      cases s <;> simp_all
    exact Submodule.subset_span (Or.inl ⟨i, this, rfl⟩)

/- English proof (translation)
The claim follows from `Matrix.mulVec_smul _ _ _`.
-/
theorem act_smul' (g : HA R hc.sig V.gram) (a : R ⊗[F] E) (y : Fin V.rank → R ⊗[F] E) :
    act hc V g (a • y) = a • act hc V g y := Matrix.mulVec_smul _ _ _

end General

end GlobalTheory.LeviShift.WeylDelta

namespace GlobalTheory.LeviShift.WeylDelta

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

/- English proof (translation)
The claim follows from `act_diagH (AF D.host.F) γ x`.
-/
theorem act_rat_coordR (γ : GF V) (x : V.V) :
    act D.sp.cm V (rat V γ) (coordR V (AF D.host.F) x) = coordR V (AF D.host.F) (ratAct D.sp.cm V γ x) :=
  act_diagH (AF D.host.F) γ x

/- English proof (translation)
Apply the tactic sequence `unfold stdVec; split_ifs <;> decide`.
-/
theorem stdVec_ne_neg_one {k : ℕ} (j i : Fin k) : stdVec j i ≠ -1 := by
  unfold stdVec; split_ifs <;> decide

/- English proof (translation)
Establish `key : ∀ i, ∃ c : D.host.E, invSV π ε (stdVec j) i ≠ 0 → c ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c • Φ.e (π i)`. Introduce `i`. Distinguish the cases in `hu : invSV π ε (stdVec j) i = 0`. Conclude with `⟨1, fun h => absurd hu h⟩`. Establish `hs : stdVec j (π i) = 1`.

Establish `: stdVec j (π i) ≠ 0` using `fun h => hu (by simp [invSV, h])`. Unfold `stdVec at this ⊢`. Apply the tactic sequence `split_ifs at this ⊢ <;> simp_all`. Establish `hv : invSV π ε (Pi.single (π i) 1) i = invSV π ε (stdVec j) i`. Simplify using `[invSV, hs]`.

Establish `hmem : bas Φ (invSV π ε (stdVec j)) i ∈ Φ.sub (invSV π ε (Pi.single (π i) 1))`. Establish `hb : bas Φ (invSV π ε (stdVec j)) i = bas Φ (invSV π ε (Pi.single (π i) 1)) i`. Unfold `bas`. Rewrite using `[hv]`. Rewrite using `[hb]`.

Conclude with `bas_mem_sub Φ (by rw [hv]; exact hu)`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 (RadInv.sub_single_le Φ (π i) (hw _ _ hmem))`. Use `⟨c, fun _ => ⟨?_, hc.symm⟩⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hc` using `[zero_smul]`.

Apply `bas_ne_zero Φ (invSV π ε (stdVec j)) i` to reduce the goal to its premises. Rewrite using `[← RadInv.ratAct_inv_apply w (bas Φ _ i), ← hc, map_zero]`. Use `choose c hc using key`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_scalar {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    (hw : Φ.IsWeylRep D.sp.cm π ε w) (j : Fin (wittIndex V)) :
    ∃ c : Fin (wittIndex V) → D.host.E, ∀ i, invSV π ε (stdVec j) i ≠ 0 →
      c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c i • Φ.e (π i) := by
  have key : ∀ i, ∃ c : D.host.E, invSV π ε (stdVec j) i ≠ 0 →
      c ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c • Φ.e (π i) := by
    intro i
    by_cases hu : invSV π ε (stdVec j) i = 0
    · exact ⟨1, fun h => absurd hu h⟩
    have hs : stdVec j (π i) = 1 := by
      have : stdVec j (π i) ≠ 0 := fun h => hu (by simp [invSV, h])
      unfold stdVec at this ⊢
      split_ifs at this ⊢ <;> simp_all
    have hv : invSV π ε (Pi.single (π i) 1) i = invSV π ε (stdVec j) i := by
      simp [invSV, hs]
    have hmem : bas Φ (invSV π ε (stdVec j)) i ∈ Φ.sub (invSV π ε (Pi.single (π i) 1)) := by
      have hb : bas Φ (invSV π ε (stdVec j)) i = bas Φ (invSV π ε (Pi.single (π i) 1)) i := by
        unfold bas; rw [hv]
      rw [hb]
      exact bas_mem_sub Φ (by rw [hv]; exact hu)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (RadInv.sub_single_le Φ (π i) (hw _ _ hmem))
    refine ⟨c, fun _ => ⟨?_, hc.symm⟩⟩
    rintro rfl
    rw [zero_smul] at hc
    apply bas_ne_zero Φ (invSV π ε (stdVec j)) i
    rw [← RadInv.ratAct_inv_apply w (bas Φ _ i), ← hc, map_zero]
  choose c hc using key
  exact ⟨c, hc⟩

variable {u : SV (wittIndex V)} {π : Equiv.Perm (Fin (wittIndex V))} {w : GF V} {c : Fin (wittIndex V) → D.host.E}

/- English proof (translation)
Establish `gen : ∀ t, u t ≠ 0 → V.hD (ratAct D.sp.cm V w (bas Φ u t)) (Φ.f k) = c (π.symm k) * V.hD (bas Φ u t) (dbas Φ u (π.symm k))`. Introduce `t ht`. Rewrite using `[(hc t ht).2, hD_bas_dbas]`. Establish `e1 : V.hD (c t • Φ.e (π t)) (Φ.f k) = c t * V.hD (Φ.e (π t)) (Φ.f k)`. Simplify using `[HSpace.hD]`.

Rewrite using `[e1, Φ.ef]`. Distinguish the cases in `h : t = π.symm k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun e => h (by rw [← e, Equiv.symm_apply_apply])), mul_zero, mul_zero]`.

Establish `h` using `(Submodule.span_le (p := LinearMap.ker ((V.hT (Φ.f k)).comp (ratAct D.sp.cm V w) - c (π.symm k) • V.hT (dbas Φ u (π.symm k))))).2 ?_ hx`. Use `LinearMap.mem_ker.1 h` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] at this`. Simplify `this` using `[HSpace.hD]`. Introduce and unpack `_ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)`.

Establish `ht' : u t ≠ 0` using `by rw [show u t = 1 from ht]; decide`. Establish `hb : bas Φ u t = Φ.e t` using `by unfold bas; rw [if_neg (by rw [show u t = 1 from ht]; decide)]`. Use `gen t ht'` as an intermediate fact. Rewrite `this` using `[hb]`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]`.

Simplify `this` using `[HSpace.hD]`. Establish `ht' : u t ≠ 0` using `by rw [show u t = -1 from ht]; decide`. Establish `hb : bas Φ u t = Φ.f t` using `by unfold bas; rw [if_pos (show u t = -1 from ht)]`. Use `gen t ht'` as an intermediate fact. Rewrite `this` using `[hb]`.

Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]`. Simplify `this` using `[HSpace.hD]`.
-/
theorem hD_ratAct_f (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    (k : Fin (wittIndex V)) {x : V.V} (hx : x ∈ Φ.sub u) :
    V.hD (ratAct D.sp.cm V w x) (Φ.f k) = c (π.symm k) * V.hD x (dbas Φ u (π.symm k)) := by
  have gen : ∀ t, u t ≠ 0 → V.hD (ratAct D.sp.cm V w (bas Φ u t)) (Φ.f k) =
      c (π.symm k) * V.hD (bas Φ u t) (dbas Φ u (π.symm k)) := by
    intro t ht
    rw [(hc t ht).2, hD_bas_dbas]
    have e1 : V.hD (c t • Φ.e (π t)) (Φ.f k) = c t * V.hD (Φ.e (π t)) (Φ.f k) := by
      simp [HSpace.hD]
    rw [e1, Φ.ef]
    by_cases h : t = π.symm k
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (by rw [← e, Equiv.symm_apply_apply])), mul_zero, mul_zero]
  have h := (Submodule.span_le (p := LinearMap.ker ((V.hT (Φ.f k)).comp (ratAct D.sp.cm V w) -
      c (π.symm k) • V.hT (dbas Φ u (π.symm k))))).2 ?_ hx
  · have := LinearMap.mem_ker.1 h
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] at this
    simpa [HSpace.hD] using this
  rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · have ht' : u t ≠ 0 := by rw [show u t = 1 from ht]; decide
    have hb : bas Φ u t = Φ.e t := by unfold bas; rw [if_neg (by rw [show u t = 1 from ht]; decide)]
    have := gen t ht'
    rw [hb] at this
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_eq_zero]
    simpa [HSpace.hD] using this
  · have ht' : u t ≠ 0 := by rw [show u t = -1 from ht]; decide
    have hb : bas Φ u t = Φ.f t := by unfold bas; rw [if_pos (show u t = -1 from ht)]
    have := gen t ht'
    rw [hb] at this
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_eq_zero]
    simpa [HSpace.hD] using this

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Rewrite using `[← hLin_act_left, act_rat_coordR, hLin_coordR, hLin_coordR, hD_ratAct_f Φ hc k hx, map_mul]`. Consider the case `zero => rw [hLin_zero_left, hLin_zero_left, mul_zero]`.

Consider the case `add y y' _ _ ih ih' => rw [hLin_add_left, hLin_add_left, ih, ih', mul_add]`. Consider the case `smul a y _ ih => rw [hLin_smul_left, hLin_smul_left, ih, mul_left_comm]`.
-/
theorem hLin_inv_f (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    (k : Fin (wittIndex V)) {z : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u)) :
    hLin D.sp.cm.sig V.gram (AF D.host.F) z (act D.sp.cm V (rat V w)⁻¹ (coordR V (AF D.host.F) (Φ.f k))) =
      inclR (F := D.host.F) (AF D.host.F) (c (π.symm k)) *
        hLin D.sp.cm.sig V.gram (AF D.host.F) z (coordR V (AF D.host.F) (dbas Φ u (π.symm k))) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hLin_act_left, act_rat_coordR, hLin_coordR, hLin_coordR, hD_ratAct_f Φ hc k hx, map_mul]
  | zero => rw [hLin_zero_left, hLin_zero_left, mul_zero]
  | add y y' _ _ ih ih' => rw [hLin_add_left, hLin_add_left, ih, ih', mul_add]
  | smul a y _ ih => rw [hLin_smul_left, hLin_smul_left, ih, mul_left_comm]

/- English proof (translation)
Take `⟨h0, h1⟩` from `hc _ hl`. Rewrite `h1` using `[Equiv.apply_symm_apply]`. Establish `e : Φ.e l = (c (π.symm l))⁻¹ • ratAct D.sp.cm V w (bas Φ u (π.symm l))`. Rewrite using `[h1, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Rewrite using `[← map_inv, act_rat_coordR, e, map_smul, RadInv.ratAct_inv_apply, coordR_smul]`.
-/
theorem act_inv_e (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    {l : Fin (wittIndex V)} (hl : u (π.symm l) ≠ 0) :
    act D.sp.cm V (rat V w)⁻¹ (coordR V (AF D.host.F) (Φ.e l)) =
      inclR (F := D.host.F) (AF D.host.F) (c (π.symm l))⁻¹ • coordR V (AF D.host.F) (bas Φ u (π.symm l)) := by
  obtain ⟨h0, h1⟩ := hc _ hl
  rw [Equiv.apply_symm_apply] at h1
  have e : Φ.e l = (c (π.symm l))⁻¹ • ratAct D.sp.cm V w (bas Φ u (π.symm l)) := by
    rw [h1, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [← map_inv, act_rat_coordR, e, map_smul, RadInv.ratAct_inv_apply, coordR_smul]

end GlobalTheory.LeviShift.WeylDelta

namespace GlobalTheory.LeviShift.WeylDelta

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

/- English proof (translation)
Establish `h1 : ∀ y ∈ Φ.sub (invSV π ε (stdVec j)), ratAct D.sp.cm V w y ∈ Φ.sub (stdVec j)` using `fun y hy => hw _ y hy`. Establish `h2 : ∀ y ∈ Φ.sub (stdVec j), ratAct D.sp.cm V w⁻¹ y ∈ Φ.sub (invSV π ε (stdVec j))`. Introduce `y hy`. Rewrite `hy` using `[Φ.sub_stdVec]`. Use `(Submodule.span_le (p := (Φ.sub (invSV π ε (stdVec j))).comap (ratAct D.sp.cm V w⁻¹))).2 ?_ hy` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `RadInv.ratAct_inv_e_mem Φ hw (show i ≤ j from Nat.lt_succ_iff.1 hi)`. Establish `hi : (rat V w)⁻¹ = rat V w⁻¹` using `(map_inv _ _).symm`. Establish `hm' : ∀ y, y ∈ (extSub (F` using `D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) ↔ act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) := hm`. Use `show ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _) ↔ act D.sp.cm V (rat V w * m * (rat V w)⁻¹) y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _)`.

Introduce `y`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `h3 : act D.sp.cm V (rat V w⁻¹) y ∈ extSub (F` using `D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := RadInv.act_rat_mem h2 hy`.

Rewrite `h3` using `[← hi]`. Conclude with `RadInv.act_rat_mem h1 ((hm' _).1 h3)`. Introduce `hy`. Establish `h3` using `RadInv.act_rat_mem h2 hy`. Rewrite `h3` using `[← hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv]`.

Establish `h4` using `RadInv.act_rat_mem h1 ((hm' _).2 h3)`. Establish `e : act D.sp.cm V (rat V w) (act D.sp.cm V (rat V w)⁻¹ y) = y`. Rewrite using `[← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]`. Rewrite `h4` using `[e]`. Conclude with `h4`.
-/
theorem conj_mem_parab {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    (hw : Φ.IsWeylRep D.sp.cm π ε w) (j : Fin (wittIndex V)) {m : GA D V}
    (hm : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j)))) :
    rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) := by
  have h1 : ∀ y ∈ Φ.sub (invSV π ε (stdVec j)), ratAct D.sp.cm V w y ∈ Φ.sub (stdVec j) := fun y hy => hw _ y hy
  have h2 : ∀ y ∈ Φ.sub (stdVec j), ratAct D.sp.cm V w⁻¹ y ∈ Φ.sub (invSV π ε (stdVec j)) := by
    intro y hy
    rw [Φ.sub_stdVec] at hy
    refine (Submodule.span_le (p := (Φ.sub (invSV π ε (stdVec j))).comap (ratAct D.sp.cm V w⁻¹))).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact RadInv.ratAct_inv_e_mem Φ hw (show i ≤ j from Nat.lt_succ_iff.1 hi)
  have hi : (rat V w)⁻¹ = rat V w⁻¹ := (map_inv _ _).symm
  have hm' : ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) ↔
      act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) := hm
  show ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _) ↔
      act D.sp.cm V (rat V w * m * (rat V w)⁻¹) y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _)
  intro y
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul]
  constructor
  · intro hy
    have h3 : act D.sp.cm V (rat V w⁻¹) y ∈ extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) :=
      RadInv.act_rat_mem h2 hy
    rw [← hi] at h3
    exact RadInv.act_rat_mem h1 ((hm' _).1 h3)
  · intro hy
    have h3 := RadInv.act_rat_mem h2 hy
    rw [← hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv] at h3
    have h4 := RadInv.act_rat_mem h1 ((hm' _).2 h3)
    have e : act D.sp.cm V (rat V w) (act D.sp.cm V (rat V w)⁻¹ y) = y := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
    rw [e] at h4
    exact h4

/- English proof (translation)
Use `set u := invSV π ε (stdVec j) with hu`. Establish `hsupp : ∀ k, stdVec j k ≠ 0 ↔ u (π.symm k) ≠ 0` using `fun k => by`. Rewrite using `[hu]`. Simplify using `only [invSV, Equiv.apply_symm_apply]`. Conclude with `⟨fun h => mul_ne_zero (Units.ne_zero _) h, fun h h' => h (by rw [h', mul_zero])⟩`.

Set `σe : Supp (stdVec j) ≃ Supp u` to `Equiv.subtypeEquiv π.symm hsupp`. Establish `hm' : ∀ y, y ∈ (extSub (F` using `D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) ↔ act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) := hm`. Establish `hmat : detMat Φ D.sp.cm (AF D.host.F) (stdVec j) (rat V w * m * (rat V w)⁻¹) = Matrix.diagonal (fun k : Supp (stdVec j) => inclR (F` using `D.host.F) (AF D.host.F) (c (π.symm k))) * (detMat Φ D.sp.cm (AF D.host.F) u m).submatrix σe σe * Matrix.diagonal (fun l : Supp (stdVec j) => inclR (F := D.host.F) (AF D.host.F) (c (π.symm l))⁻¹) := by`. Use extensionality with `k l`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]`.

Establish `hl : u (π.symm l) ≠ 0` using `(hsupp l).1 l.2`. Establish `hb : bas Φ (stdVec j) l = Φ.e l` using `if_neg (stdVec_ne_neg_one j l)`. Establish `hdb : dbas Φ (stdVec j) k = Φ.f k` using `if_neg (stdVec_ne_neg_one j k)`. Establish `hZ : act D.sp.cm V m (coordR V (AF D.host.F) (bas Φ u (π.symm l))) ∈ extSub (F` using `D.host.F) V (AF D.host.F) (Φ.sub u) := (hm' _).1 (Submodule.subset_span ⟨_, bas_mem_sub Φ hl, rfl⟩)`. Simplify using `only [detMat, Matrix.of_apply, σe, Equiv.subtypeEquiv_apply]`.

Rewrite using `[hb, hdb, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, act_inv_e Φ hc hl, act_smul', act_smul', hLin_smul_left, hLin_act_left D.sp.cm (AF D.host.F) (rat V w), hLin_inv_f Φ hc k hZ]`. Expand and normalize the polynomial expressions, which then agree. Unfold `detU`. Rewrite using `[hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_submatrix_equiv_self, mul_comm _ (Finset.prod _ _), ← mul_assoc, ← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_eq_one fun k _ => by rw [← map_mul, inv_mul_cancel₀ (hc _ ((hsupp k).1 k.2)).1, map_one], one_mul]`.
-/
theorem detU_conj {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    {j : Fin (wittIndex V)} {m : GA D V}
    (hm : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))))
    {c : Fin (wittIndex V) → D.host.E}
    (hc : ∀ i, invSV π ε (stdVec j) i ≠ 0 →
      c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c i • Φ.e (π i)) :
    detU Φ D.sp.cm (AF D.host.F) (stdVec j) (rat V w * m * (rat V w)⁻¹) =
      detU Φ D.sp.cm (AF D.host.F) (invSV π ε (stdVec j)) m := by
  set u := invSV π ε (stdVec j) with hu
  have hsupp : ∀ k, stdVec j k ≠ 0 ↔ u (π.symm k) ≠ 0 := fun k => by
    rw [hu]
    simp only [invSV, Equiv.apply_symm_apply]
    exact ⟨fun h => mul_ne_zero (Units.ne_zero _) h, fun h h' => h (by rw [h', mul_zero])⟩
  let σe : Supp (stdVec j) ≃ Supp u := Equiv.subtypeEquiv π.symm hsupp
  have hm' : ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) ↔
      act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) := hm
  have hmat : detMat Φ D.sp.cm (AF D.host.F) (stdVec j) (rat V w * m * (rat V w)⁻¹) =
      Matrix.diagonal (fun k : Supp (stdVec j) => inclR (F := D.host.F) (AF D.host.F) (c (π.symm k))) *
        (detMat Φ D.sp.cm (AF D.host.F) u m).submatrix σe σe *
        Matrix.diagonal (fun l : Supp (stdVec j) => inclR (F := D.host.F) (AF D.host.F) (c (π.symm l))⁻¹) := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
    have hl : u (π.symm l) ≠ 0 := (hsupp l).1 l.2
    have hb : bas Φ (stdVec j) l = Φ.e l := if_neg (stdVec_ne_neg_one j l)
    have hdb : dbas Φ (stdVec j) k = Φ.f k := if_neg (stdVec_ne_neg_one j k)
    have hZ : act D.sp.cm V m (coordR V (AF D.host.F) (bas Φ u (π.symm l))) ∈
        extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) :=
      (hm' _).1 (Submodule.subset_span ⟨_, bas_mem_sub Φ hl, rfl⟩)
    simp only [detMat, Matrix.of_apply, σe, Equiv.subtypeEquiv_apply]
    rw [hb, hdb, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, act_inv_e Φ hc hl, act_smul', act_smul',
      hLin_smul_left, hLin_act_left D.sp.cm (AF D.host.F) (rat V w), hLin_inv_f Φ hc k hZ]
    ring
  unfold detU
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_submatrix_equiv_self,
    mul_comm _ (Finset.prod _ _), ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one fun k _ => by rw [← map_mul, inv_mul_cancel₀ (hc _ ((hsupp k).1 k.2)).1, map_one], one_mul]

end GlobalTheory.LeviShift.WeylDelta

/- English proof (translation)
Introduce `D V Φ π ε w hw j m hm`. Take `⟨c, hc⟩` from `WeylDelta.exists_scalar Φ hw j`. Use `⟨WeylDelta.conj_mem_parab Φ hw j hm, ?_⟩` and prove the remaining obligations. Unfold `logDelta`. Rewrite using `[WeylDelta.detU_conj Φ hm hc]`.
-/
theorem GlobalTheory.LeviShift.logDelta_conj_weylRep : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V), Φ.IsWeylRep D.sp.cm π ε w → ∀ (j : Fin (wittIndex V)) (m : GA D V), m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) → rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) ∧ logDelta Φ (stdVec j) (rat V w * m * (rat V w)⁻¹) = logDelta Φ (invSV π ε (stdVec j)) m := by
  intro D V Φ π ε w hw j m hm
  obtain ⟨c, hc⟩ := WeylDelta.exists_scalar Φ hw j
  refine ⟨WeylDelta.conj_mem_parab Φ hw j hm, ?_⟩
  unfold logDelta
  rw [WeylDelta.detU_conj Φ hm hc]

end
