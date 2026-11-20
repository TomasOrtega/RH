import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cplxKer : CplxKer := by
  intro E _ φ m N A c hc
  letI : Algebra E ℂ := φ.toAlgebra
  let b := Module.Basis.ofVectorSpace E ℂ
  let J := Finset.univ.biUnion (fun i : Fin N => (b.repr (c i)).support)
  let s : Module.Basis.ofVectorSpaceIndex E ℂ → Fin N → E := fun j i => b.repr (c i) j
  have hs : ∀ j, A *ᵥ s j = 0 := by
    intro j
    funext k
    have h0 : (A.map φ *ᵥ c) k = 0 := by rw [hc]; rfl
    have h1 : ∑ i, A k i • c i = 0 := by
      rw [← h0]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra]
    have h2 := congrArg (fun z => b.repr z j) h1
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    simpa [Matrix.mulVec, dotProduct, s] using h2
  have hcsum : c = ∑ j ∈ J, b j • (fun i => φ (s j i)) := by
    funext i
    rw [Finset.sum_apply]
    conv_lhs => rw [← b.linearCombination_repr (c i)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (b.repr (c i)).support) (Finset.mem_univ i))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, s]
      ring
    · intro j _; simp
  rw [hcsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s j, hs j, rfl⟩)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_add_r {n : ℕ} (ε : Fin n → Bool) (a y z : Fin n → ℂ) : hJ ε a (y + z) = hJ ε a y + hJ ε a z := by
  unfold hJ
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a y : Fin n → ℂ) (c : ℂ) : hJ ε a (c • y) = c * hJ ε a y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_zero_r {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℂ) : hJ ε a 0 = 0 := by
  unfold hJ
  rw [Matrix.mulVec_zero, dotProduct_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_sum_r {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (a : Fin n → ℂ) (c : ι → ℂ)
    (y : ι → Fin n → ℂ) : hJ ε a (∑ i, c i • y i) = ∑ i, c i * hJ ε a (y i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section Pts

variable {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

abbrev psiV (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem psiV_add (p q : (VS D).V) : psiV X v (p + q) = psiV X v p + psiV X v q := by
  simp only [psiV, rv]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp only [HidaSetting.crd, Pi.add_apply]
  rw [← map_add]
  congr 1
  simp [crdOf, map_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem psiV_smul (c : D.host.E) (p : (VS D).V) : psiV X v (c • p) = embS D (X.pl v) c • psiV X v p := by
  unfold psiV rv HidaSetting.crd crdOf
  rw [← Matrix.mulVec_smul]; congr 1; funext i
  simp [X.φ_eq]

def psiHom : (VS D).V →+ (Fin X.B.I.n → ℂ) := AddMonoidHom.mk' (psiV X v) (psiV_add X v)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiV_sum {ι : Type} (J : Finset ι) (f : ι → (VS D).V) : psiV X v (∑ i ∈ J, f i) = ∑ i ∈ J, psiV X v (f i) := by exact map_sum (psiHom X v) f J

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiV_zero : psiV X v 0 = 0 := by exact map_zero (psiHom X v)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hJ_psiV (p q : (VS D).V) :
    hJ (X.B.I.ε v) (psiV X v p) (psiV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem psiV_span (y : Fin X.B.I.n → ℂ) : ∃ c : Fin X.B.I.n → ℂ, y = ∑ i, c i • psiV X v (X.bas i) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  refine ⟨X.B.I.P v *ᵥ y, ?_⟩
  have h1 : ∀ i, psiV X v (X.bas i) = (X.B.I.P v)⁻¹ *ᵥ (fun k => if i = k then (1 : ℂ) else 0) := by
    intro i
    unfold psiV rv HidaSetting.crd crdOf
    congr 1
    funext k
    by_cases h : i = k <;> simp [h]
  simp only [h1, ← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu,
    Matrix.one_mulVec]

/- English proof (translation)
Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cplx_comb {ι : Type} [Fintype ι] (g : ι → (VS D).V) (U : Submodule D.host.E (VS D).V) (c : ι → ℂ)
    (hc : ∀ p ∈ U, ∑ i, c i * embS D (X.pl v) ((VS D).hT p (g i)) = 0) :
    ∑ i, c i • psiV X v (g i) ∈ spanAt X v (perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g)) := by
  letI : Algebra D.host.E ℂ := (embS D (X.pl v)).toAlgebra
  let b := Module.Basis.ofVectorSpace D.host.E ℂ
  let J := Finset.univ.biUnion (fun i : ι => (b.repr (c i)).support)
  let s : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → ι → D.host.E := fun j i => b.repr (c i) j
  let w : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → (VS D).V := fun j => ∑ i, s j i • g i
  have hw : ∀ j, w j ∈ perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g) := by
    intro j
    refine ⟨fun p hp => ?_,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
    have h1 : ∑ i, (VS D).hT p (g i) • c i = 0 := by
      rw [← hc p hp]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 := congrArg (fun z => b.repr z j) h1
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    show (VS D).hT p (w j) = 0
    simp only [w, map_sum, map_smul, smul_eq_mul]
    rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [s]; ring
  have hc' : ∀ i, c i = ∑ j ∈ J, embS D (X.pl v) (s j i) * b j := by
    intro i
    conv_lhs => rw [← b.linearCombination_repr (c i)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (b.repr (c i)).support) (Finset.mem_univ i))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · intro j _; simp
  have hsum : ∑ i, c i • psiV X v (g i) = ∑ j ∈ J, b j • psiV X v (w j) := by
    simp only [w, psiV_sum, psiV_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w j, hw j, rfl⟩)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem spanAt_mono {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : spanAt X v U ≤ spanAt X v U' := by
  unfold spanAt
  exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr h))

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cplx_part1 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 : Submodule D.host.E (VS D).V)
    (hsup : perpS (VS D) V0 ⊔ F.X = F.XplusPerp) (y : Fin X.B.I.n → ℂ)
    (hy : ∀ p ∈ F.Xplus, hJ (X.B.I.ε v) (psiV X v p) y = 0) :
    ∃ x ∈ spanAt X v F.X, ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0 := by
  obtain ⟨c, rfl⟩ := psiV_span X v y
  have hmem := cplx_comb X v X.bas F.Xplus c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  have hmem' := spanAt_mono X v (inf_le_left.trans (le_of_eq rfl) :
    perpS (VS D) F.Xplus ⊓ Submodule.span D.host.E (Set.range X.bas) ≤ F.XplusPerp) hmem
  rw [← hsup] at hmem'
  refine Submodule.span_induction (p := fun y _ => ∃ x ∈ spanAt X v F.X,
      ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0) ?_ ?_ ?_ ?_ hmem'
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.1 hw
    refine ⟨psiV X v x, Submodule.subset_span ⟨x, hx, rfl⟩, fun p hp => ?_⟩
    show hJ (X.B.I.ε v) (psiV X v p) (psiV X v (a + x) - psiV X v x) = 0
    rw [psiV_add, add_sub_cancel_right, hJ_psiV, ha p hp, map_zero]
  · exact ⟨0, Submodule.zero_mem _, fun p _ => by rw [sub_zero, hJ_zero_r]⟩
  · rintro y1 y2 - - ⟨x1, hx1, h1⟩ ⟨x2, hx2, h2⟩
    refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, fun p hp => ?_⟩
    rw [show y1 + y2 - (x1 + x2) = (y1 - x1) + (y2 - x2) by abel, hJ_add_r, h1 p hp, h2 p hp, add_zero]
  · rintro a y1 - ⟨x1, hx1, h1⟩
    refine ⟨a • x1, Submodule.smul_mem _ _ hx1, fun p hp => ?_⟩
    rw [← smul_sub, hJ_smul_r, h1 p hp, mul_zero]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cplx_part3 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 I : Submodule D.host.E (VS D).V)
    (hinf : perpS (VS D) V0 ⊓ F.X = I) (y : Fin X.B.I.n → ℂ) (hyX : y ∈ spanAt X v F.X)
    (hy : ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) y = 0) : y ∈ spanAt X v I := by
  have hle : spanAt X v F.X ≤ Submodule.span ℂ (Set.range fun a => psiV X v (F.e a)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    refine Submodule.span_induction (p := fun p _ => psiV X v p ∈
      Submodule.span ℂ (Set.range fun a => psiV X v (F.e a))) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a, rfl⟩; exact Submodule.subset_span ⟨a, rfl⟩
    · rw [psiV_zero]; exact Submodule.zero_mem _
    · intro x1 x2 _ _ h1 h2; rw [psiV_add]; exact Submodule.add_mem _ h1 h2
    · intro a x1 _ h1; rw [psiV_smul]; exact Submodule.smul_mem _ _ h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hyX)
  have hmem := cplx_comb X v F.e V0 c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  rw [← hinf]
  exact hmem

end Pts

def NFRat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊓ (lf D (X.Fu u)).fl.X = Isp (lf D (X.Fu u)).fl (frq X q).fl ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (lf D (X.Fu u)).fl.X = (lf D (X.Fu u)).fl.XplusPerp ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (frq X q).fl.X = (frq X q).fl.XplusPerp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cplxNF_of (h : NFRat) : CplxNF := by
  intro D X u u' Λ Λ' q hrel hG v
  obtain ⟨h1, h2, h3⟩ := h D X u u' Λ Λ' q hrel hG
  exact ⟨cplx_part1 X v _ _ h2, cplx_part1 X v _ _ h3, cplx_part3 X v _ _ _ h1⟩

end PI.SchurPlaces
