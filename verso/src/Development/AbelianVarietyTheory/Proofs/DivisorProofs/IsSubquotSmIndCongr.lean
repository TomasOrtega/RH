import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal

namespace GlobalTheory.LGrp.SatakeCompare

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
Substitute using the available equality. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
private theorem isSubquotient_smInd_congr {G V W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {H H' : Subgroup G} (h : H = H') (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H), σ ⟨g, hg⟩ = σ' ⟨g, h ▸ hg⟩) (π : Representation ℂ G V) :
    _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H σ) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H' σ') := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g g.2
  rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem blk_points (n : Type) (j : n) :
    _root_.GlobalTheory.SmGL.blk (_root_.GlobalTheory.SmGL.points n) j = j :=
  _root_.GlobalTheory.SmGL.blk_apply (_root_.GlobalTheory.SmGL.points n) j ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
private theorem borelGL_Q_eq_parab_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).Q =
      _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  simp only [_root_.GlobalTheory.SmGL.mem_parab, blk_points]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem borelGL_p_apply_eq_diag (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) (i : n) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).p q i : kˣ) : k) = (q : GL n k) i i := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data.

Simplify using the standard rewrite rules.
-/
private theorem leviProj_points_eq_leviTorus_borel_p (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q)
    (hq : (q : GL n k) ∈ _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n)) :
    _root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points n) ⟨q, hq⟩ =
      _root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q) := by
  funext a
  ext i j
  rw [_root_.GlobalTheory.SmGL.leviProj_apply]
  cases i; cases j
  simp [_root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points, borelGL_p_apply_eq_diag]

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Substitute using the available equality. Equip the data with the indicated structure.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem modulus_leviEmb_eq_smGL_modulus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) (U : Subgroup (GL n k))
    (hU : U = _root_.GlobalTheory.SmGL.unipRad k e) (hc : IsClosed (U : Set (GL n k)))
    (g : _root_.GlobalTheory.SmGL.Levi k m) (x : Subgroup.normalizer (U : Set (GL n k)))
    (hx : (x : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g) :
    ((_root_.GlobalTheory.LGrp.modulus U hc x : NNReal) : ℝ) = _root_.GlobalTheory.SmGL.modulus k m g := by
  obtain ⟨x, hg⟩ := x
  simp only at hx
  subst hx
  subst hU
  letI : MeasurableSpace (_root_.GlobalTheory.SmGL.unipRad k e) := borel _
  haveI : BorelSpace (_root_.GlobalTheory.SmGL.unipRad k e) := ⟨rfl⟩
  haveI : LocallyCompactSpace (_root_.GlobalTheory.SmGL.unipRad k e) :=
    hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (_root_.GlobalTheory.SmGL.unipRad k e) := Measure.haar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    inferInstance
  have hK : MeasurableSet (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    K.isCompact.isClosed.measurableSet
  have h1 := _root_.GlobalTheory.LGrp.modulus_measure _ hc μ ⟨_, hg⟩ (K : Set _)
  have h2 := _root_.GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul k α n m e μ g _ hK
  have hset : (_root_.GlobalTheory.LGrp.conjAut (_root_.GlobalTheory.SmGL.unipRad k e) ⟨_, hg⟩) '' (K : Set _) =
      {u : _root_.GlobalTheory.SmGL.unipRad k e | ∃ s ∈ (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)),
        (u : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g * (s : GL n k) *
          (_root_.GlobalTheory.SmGL.leviEmb k e g)⁻¹} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, _root_.GlobalTheory.LGrp.conjAut_coe _ _ _⟩
    · rintro ⟨s, hs, hu⟩
      exact ⟨s, hs, Subtype.ext ((_root_.GlobalTheory.LGrp.conjAut_coe _ _ _).trans hu.symm)⟩
  rw [hset, h2] at h1
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 := (ENNReal.mul_left_inj hpos hfin).1 h1
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact ((ENNReal.ofReal_eq_ofReal_iff (_root_.GlobalTheory.SmGL.modulus_pos k g).le
    (NNReal.coe_nonneg _)).1 h3).symm

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Simplify to obtain the desired conclusion from the available facts.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem borelGL_U_eq_unipRad_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).U = _root_.GlobalTheory.SmGL.unipRad k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  rw [_root_.GlobalTheory.LGrp.LeviDatum.mem_U,
    _root_.GlobalTheory.SmGL.mem_unipRad, ← borelGL_Q_eq_parab_points]
  constructor
  · rintro ⟨hQ, hp⟩
    refine ⟨hQ, fun a i j => ?_⟩
    have h := congrArg (fun u : kˣ => (u : k)) (congrFun hp a)
    simp only [borelGL_p_apply_eq_diag, Pi.one_apply, Units.val_one] at h
    cases i; cases j
    simpa using h
  · rintro ⟨hQ, hd⟩
    refine ⟨hQ, funext fun a => Units.ext ?_⟩
    rw [borelGL_p_apply_eq_diag]
    simpa using hd a () ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem borelGL_s_eq_leviEmb_points_leviTorus (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (t : n → kˣ) :
    (_root_.GlobalTheory.LGrp.borelGL k n).s t =
      _root_.GlobalTheory.SmGL.leviEmb k (_root_.GlobalTheory.SmGL.points n) (_root_.GlobalTheory.SmGL.leviTorus k n t) := by
  ext i j
  change ((_root_.GlobalTheory.LGrp.diagHom k n t : GL n k) : Matrix n n k) i j = _
  rw [_root_.GlobalTheory.LGrp.diagHom_val]
  simp [_root_.GlobalTheory.SmGL.leviEmb, _root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points]
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

open MeasureTheory ValuativeRel in
open scoped NNReal in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).deltaHalf q : ℂˣ) : ℂ) =
      ((_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : n => Unit)
        (_root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q)) : ℂˣ) : ℂ) := by
  rw [_root_.GlobalTheory.LGrp.LeviDatum.deltaHalf_coe, _root_.GlobalTheory.SmGL.val_deltaHalf,
    _root_.GlobalTheory.LGrp.LeviDatum.delta_apply,
    modulus_leviEmb_eq_smGL_modulus k (_root_.GlobalTheory.SmGL.points n) _
      (borelGL_U_eq_unipRad_points k n) _ _ _ (borelGL_s_eq_leviEmb_points_leviTorus k n _)]

open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) :
    _root_.GlobalTheory.LGrp.IsSubquot π (_root_.GlobalTheory.LGrp.psGL k α) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π
        (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar k (α i)) := by
  change _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.LGrp.psGL k α) ↔ _
  unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd _root_.GlobalTheory.LGrp.LeviDatum.nIndQ
  unfold _root_.GlobalTheory.SmGL.prinSeries _root_.GlobalTheory.SmGL.indB _root_.GlobalTheory.SmGL.parInd
  refine isSubquotient_smInd_congr (borelGL_Q_eq_parab_points k n) _ _ (fun g hg => ?_) π
  refine LinearMap.ext fun z => ?_
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.LGrp.twist_apply,
    _root_.GlobalTheory.LGrp.charRep_apply, _root_.GlobalTheory.SmGL.twist_apply,
    _root_.GlobalTheory.SmGL.ofChar_apply]
  rw [leviProj_points_eq_leviTorus_borel_p k n ⟨g, hg⟩, borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus]
  simp [_root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.LGrp.unrTorus_apply,
    _root_.GlobalTheory.LGrp.unrChar_eq]

open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by
  intro k _ _ _ _ n V _ _ _ _ _ π S
  unfold _root_.GlobalTheory.LGrp.HasSatakeGL _root_.GlobalTheory.LGrp.InUPSGL _root_.GlobalTheory.SmGL.HasSatake
    _root_.GlobalTheory.SmGL.IsSpherical _root_.GlobalTheory.LGrp.IsIrrSmooth
  rw [_root_.GlobalTheory.LGrp.isSpherical_iff]
  constructor
  · rintro ⟨⟨α, hα, ⟨-, hirr⟩, hsub⟩, hsph⟩
    exact ⟨α, hα, hirr, hsph, (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).1 hsub⟩
  · rintro ⟨α, hα, hirr, hsph, hsub⟩
    have hsub' := (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).2 hsub
    refine ⟨⟨α, hα, ⟨?_, hirr⟩, hsub'⟩, hsph⟩
    refine _root_.GlobalTheory.SmGL.IsSubquotient.isSmooth hsub' ?_
    unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd
    exact _root_.GlobalTheory.LGrp.LeviDatum.nInd_isSmooth _ _

end GlobalTheory.LGrp.SatakeCompare
