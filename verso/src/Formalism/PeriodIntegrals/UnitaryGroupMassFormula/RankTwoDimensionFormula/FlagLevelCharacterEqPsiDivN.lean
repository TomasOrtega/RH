import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC

noncomputable section

namespace PI.UnitaryDimensionFormula.unitaryCongruence

open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Gen

variable (I : AutInst)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_mul (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_one : I.fmat 1 = 1 := rfl
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  rw [← fmat_mul I, inv_mul_cancel, fmat_one I]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem K_one : (1 : I.Gf) ∈ I.Kset := by
  show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  exact (Formalism.UG.stabGL I.Lf).one_mem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem K_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx
/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem K_mv {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) : I.fmat x *ᵥ y ∈ I.Lf := by
  have h : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  exact (h y).1 hy
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem K_sub_mv {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) *ᵥ y ∈ I.Lf := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (K_mv I hx hy) hy

def mvO (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : VA I →ₗ[IntAf I.F I.E] VA I where
  toFun v := M *ᵥ v
  map_add' := Matrix.mulVec_add M
  map_smul' c v := by
    show M *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v) = (c : I.E ⊗[I.F] Af I.F) • (M *ᵥ v)
    exact Matrix.mulVec_smul M _ v

def Mo (g : ℕ) (S : Set (VA I)) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) S ⊔ mL I g

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem smul_mem_mL {g : ℕ} {y : VA I} (hy : y ∈ I.Lf) :
    ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g := by
  unfold Formalism.L2.SG.HidaSetting.mL
  exact Submodule.subset_span ⟨y, hy, rfl⟩

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem Mo_mono {g : ℕ} {S T : Set (VA I)} (h : S ⊆ T) : Mo I g S ≤ Mo I g T := by
  unfold Mo
  exact sup_le_sup_right (Submodule.span_mono h) _
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem sub_Mo {g : ℕ} {S : Set (VA I)} : S ⊆ Mo I g S := by
  intro s hs
  unfold Mo
  exact Submodule.mem_sup_left (Submodule.subset_span hs)
/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mL_Mo {g : ℕ} {S : Set (VA I)} : mL I g ≤ Mo I g S := by
  unfold Mo
  exact le_sup_right

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem mv_mem (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (g : ℕ) (S : Set (VA I))
    (N : Submodule (IntAf I.F I.E) (VA I)) (hS : ∀ s ∈ S, M *ᵥ s ∈ N)
    (hm : ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N) :
    ∀ v ∈ Mo I g S, M *ᵥ v ∈ N := by
  intro v hv
  have h : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤ N.comap (mvO I M) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · unfold Formalism.L2.SG.HidaSetting.mL
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hm y hy
  exact h hv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mL_mv {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf)
    (g : ℕ) {N : Submodule (IntAf I.F I.E) (VA I)} (hN : mL I g ≤ N) :
    ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N := by
  intro y hy
  rw [Matrix.mulVec_smul]
  exact hN (smul_mem_mL I (hM y hy))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pres {x : I.Gf} (hx : x ∈ I.Kset) (g : ℕ) (S : Set (VA I)) (N : Submodule (IntAf I.F I.E) (VA I))
    (hSN : S ⊆ N) (hS : ∀ s ∈ S, (I.fmat x - 1) *ᵥ s ∈ N) (hN : mL I g ≤ N) :
    ∀ v ∈ Mo I g S, I.fmat x *ᵥ v ∈ N := by
  refine mv_mem I (I.fmat x) g S N (fun s hs => ?_) (mL_mv I (fun y hy => K_mv I hx hy) g hN)
  have e : I.fmat x *ᵥ s = (I.fmat x - 1) *ᵥ s + s := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [e]
  exact N.add_mem (hS s hs) (hSN hs)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pres1 {x : I.Gf} (hx : x ∈ I.Kset) (g : ℕ) (S : Set (VA I)) (N : Submodule (IntAf I.F I.E) (VA I))
    (hS : ∀ s ∈ S, (I.fmat x - 1) *ᵥ s ∈ N) (hN : mL I g ≤ N) :
    ∀ v ∈ Mo I g S, (I.fmat x - 1) *ᵥ v ∈ N := by
  exact mv_mem I (I.fmat x - 1) g S N hS (mL_mv I (fun y hy => K_sub_mv I hx hy) g hN)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem mul_id (x y : I.Gf) (v : VA I) :
    (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
  rw [fmat_mul I]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
  abel

/- English proof (translation)
Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem inv_id (x : I.Gf) (v : VA I) :
    (I.fmat x⁻¹ - 1) *ᵥ v = -(I.fmat x⁻¹ *ᵥ ((I.fmat x - 1) *ᵥ v)) := by
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, fmat_inv_mul I]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem fmat_mul_identity (x y : I.Gf) (v : VA I) :
    I.fmat (x * y) *ᵥ v = (I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ v) + I.fmat x *ᵥ v + I.fmat y *ᵥ v - v := by
  rw [fmat_mul I]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
  abel

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigA_tmul (a : I.E) (b : Af I.F) : sigA I (a ⊗ₜ[I.F] b) = star a ⊗ₜ[I.F] b := by
  exact Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) a b

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem sigA_sigA (a : I.E ⊗[I.F] Af I.F) : sigA I (sigA I a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [sigA_tmul, sigA_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigA_inclE (a : I.E) : sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  show sigA I (a ⊗ₜ[I.F] (1 : Af I.F)) = star a ⊗ₜ[I.F] (1 : Af I.F)
  exact sigA_tmul I a 1

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem star_intOE {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) : star a ∈ Formalism.UG.intOE I.E := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨⟨star (x : I.E), x.isIntegral_coe.map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sigA_mem {a : I.E ⊗[I.F] Af I.F} (ha : a ∈ IntAf I.F I.E) : sigA I a ∈ IntAf I.F I.E := by
  have h : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, hs⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigA I (s ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [sigA_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨star s, star_intOE I hs⟩, rfl⟩)
    · show sigA I ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E
      rw [sigA_tmul, star_one]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact h ha

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclE_mem {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem hA_add_right (u v w : VA I) : hA I u (v + w) = hA I u v + hA I u w := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_right (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I u (c • v) = c * hA I u v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem hA_add_left (u u' v : VA I) : hA I (u + u') v = hA I u v + hA I u' v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_left (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I (c • u) v = sigA I c * hA I u v := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def hL (u : VA I) : VA I →ₗ[I.E ⊗[I.F] Af I.F] (I.E ⊗[I.F] Af I.F) where
  toFun := hA I u
  map_add' := hA_add_right I u
  map_smul' c v := hA_smul_right I u v c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hL_apply (u v : VA I) : hL I u v = hA I u v := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem hA_incl (x y : Fin I.n → I.E) : hA I (incl I x) (incl I y) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform Formalism.L2.SG.HidaSetting.incl
  simp only [Matrix.map_apply, map_sum, map_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_inclE]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem J_conj (i j : Fin I.n) : star (I.J i j) = I.J j i := by
  have h0 : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h := congrFun (congrFun h0 j) i
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
  exact h

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_symm (u v : VA I) : hA I v u = sigA I (hA I u v) := by
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [map_sum, map_mul, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_sigA, sigA_inclE, J_conj]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem hA_int {u v : VA I} (hu : u ∈ I.Lf) (hv : v ∈ I.Lf) : hA I u v ∈ IntAf I.F I.E := by
  have gen : ∀ x ∈ I.L, ∀ y ∈ I.L, hA I (incl I x) (incl I y) ∈ IntAf I.F I.E := by
    intro x hx y hy
    rw [hA_incl]
    exact inclE_mem I ((I.L_dual y).1 hy x hx)
  have h1 : ∀ x ∈ I.L, ∀ w ∈ I.Lf, hA I (incl I x) w ∈ IntAf I.F I.E := by
    intro x hx w hw
    let P : Submodule (IntAf I.F I.E) (VA I) :=
      { carrier := {w | hA I (incl I x) w ∈ IntAf I.F I.E}
        add_mem' := fun {a b} ha hb => by
          show hA I (incl I x) (a + b) ∈ IntAf I.F I.E
          rw [hA_add_right]
          exact add_mem ha hb
        zero_mem' := by
          show hL I (incl I x) 0 ∈ IntAf I.F I.E
          rw [map_zero]
          exact zero_mem _
        smul_mem' := fun c w hw => by
          show hA I (incl I x) ((c : I.E ⊗[I.F] Af I.F) • w) ∈ IntAf I.F I.E
          rw [hA_smul_right]
          exact mul_mem c.2 hw }
    have hle : I.Lf ≤ P := by
      show Submodule.span _ _ ≤ P
      rw [Submodule.span_le]
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      exact gen x hx y hy
    exact hle hw
  let Q : Submodule (IntAf I.F I.E) (VA I) :=
    { carrier := {w | hA I w v ∈ IntAf I.F I.E}
      add_mem' := fun {a b} ha hb => by
        show hA I (a + b) v ∈ IntAf I.F I.E
        rw [hA_add_left]
        exact add_mem ha hb
      zero_mem' := by
        show hA I 0 v ∈ IntAf I.F I.E
        have h0 := hA_smul_left I 0 v 0
        rw [zero_smul, map_zero, zero_mul] at h0
        rw [h0]
        exact zero_mem _
      smul_mem' := fun c w hw => by
        show hA I ((c : I.E ⊗[I.F] Af I.F) • w) v ∈ IntAf I.F I.E
        rw [hA_smul_left]
        exact mul_mem (sigA_mem I c.2) hw }
  have hle : I.Lf ≤ Q := by
    show Submodule.span _ _ ≤ Q
    rw [Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact h1 y hy v hv
  exact hle hu

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hA_sub_right (u v w : VA I) : hA I u (v - w) = hA I u v - hA I u w := by
  show hL I u (v - w) = hL I u v - hL I u w
  exact map_sub _ _ _

end Gen

section Cong

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem lt_sub {r : ℕ} {p q : ℕ} (h : p ≤ q) : {c : Fin r | c.1 < p} ⊆ {c | c.1 < q} := by
  intro c hc
  exact lt_of_lt_of_le hc h

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (bw : Fin k → VA I)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem SE {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) (m : ℕ) :
    ∀ v ∈ Mo I g (e0 '' {b | b.1 < m}), I.fmat x *ᵥ v ∈ Mo I g (e0 '' {b | b.1 < m}) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ ⟨b, hb, rfl⟩
  exact Mo_mono I ((Set.image_mono (lt_sub (le_of_lt hb)) : e0 '' _ ⊆ e0 '' _)) (hc b)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem SR {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) :
    ∀ v ∈ Mo I g (Set.range e0), I.fmat x *ᵥ v ∈ Mo I g (Set.range e0) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ ⟨a, rfl⟩
  exact Mo_mono I (Set.image_subset_range _ _) (hc a)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem SB {x : I.Gf} (hx : x ∈ I.Kset)
    (hc1 : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}))
    (hc3 : ∀ i : Fin k, (I.fmat x - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1})) (m : ℕ) :
    ∀ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}),
      I.fmat x *ᵥ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ (⟨a, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact Mo_mono I ((Set.image_subset_range _ _).trans (fun _ h => Or.inl h)) (hc1 a)
  · exact Mo_mono I (fun _ h => Or.imp id (fun h' => (Set.image_mono (lt_sub (le_of_lt hi)) : bw '' _ ⊆ bw '' _) h') h) (hc3 i)

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cong_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x)
    (hcy : K2cong I g e0 z0 bw y) : K2cong I g e0 z0 bw (x * y) := by
  unfold Formalism.L2.SG.HidaSetting.K2cong at hcx hcy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hcx
  obtain ⟨hy1, hy2, hy3⟩ := hcy
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩
  · show (I.fmat (x * y) - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})
    rw [mul_id I]
    exact add_mem (SE I g e0 hx hx1 a.1 _ (hy1 a)) (hx1 a)
  · show (I.fmat (x * y) - 1) *ᵥ z0 ∈ Mo I g (Set.range e0)
    rw [mul_id I]
    exact add_mem (SR I g e0 hx hx1 _ hy2) hx2
  · show (I.fmat (x * y) - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1})
    rw [mul_id I]
    exact add_mem (SB I g e0 bw hx hx1 hx3 i.1 _ (hy3 i)) (hx3 i)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem inv_e {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) :
    ∀ a : Fin r, (I.fmat x⁻¹ - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}) := by
  have key : ∀ m : ℕ, ∀ a : Fin r, a.1 < m →
      (I.fmat x⁻¹ - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}) := by
    intro m
    induction m with
    | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
    | succ m ih =>
      intro a ha
      rw [inv_id I]
      refine neg_mem (pres I (K_inv I hx) g _ _ (sub_Mo I) ?_ (mL_Mo I) _ (hc a))
      rintro _ ⟨b, hb, rfl⟩
      exact Mo_mono I ((Set.image_mono (lt_sub (le_of_lt hb)) : e0 '' _ ⊆ e0 '' _))
        (ih b (lt_of_lt_of_le hb (Nat.lt_succ_iff.mp ha)))
  intro a
  exact key (a.1 + 1) a (Nat.lt_succ_self _)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem inv_b {x : I.Gf} (hx : x ∈ I.Kset)
    (hc1 : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}))
    (hc3 : ∀ i : Fin k, (I.fmat x - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1})) :
    ∀ i : Fin k, (I.fmat x⁻¹ - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) := by
  have he := inv_e I g e0 hx hc1
  have key : ∀ m : ℕ, ∀ i : Fin k, i.1 < m →
      (I.fmat x⁻¹ - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [inv_id I]
      refine neg_mem (pres I (K_inv I hx) g _ _ (sub_Mo I) ?_ (mL_Mo I) _ (hc3 i))
      rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Mo_mono I ((Set.image_subset_range _ _).trans (fun _ h => Or.inl h)) (he a)
      · exact Mo_mono I (fun _ h => Or.imp id (fun h' => (Set.image_mono (lt_sub (le_of_lt hj)) : bw '' _ ⊆ bw '' _) h') h)
          (ih j (lt_of_lt_of_le hj (Nat.lt_succ_iff.mp hi)))
  intro i
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cong_inv {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) :
    K2cong I g e0 z0 bw x⁻¹ := by
  unfold Formalism.L2.SG.HidaSetting.K2cong at hcx ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hcx
  refine ⟨inv_e I g e0 hx hx1, ?_, inv_b I g e0 bw hx hx1 hx3⟩
  show (I.fmat x⁻¹ - 1) *ᵥ z0 ∈ Mo I g (Set.range e0)
  rw [inv_id I]
  exact neg_mem (SR I g e0 (K_inv I hx) (inv_e I g e0 hx hx1) _ hx2)

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem cong_one : K2cong I g e0 z0 bw 1 := by
  unfold Formalism.L2.SG.HidaSetting.K2cong Formalism.L2.SG.HidaSetting.InMod
  simp only [fmat_one I, sub_self, Matrix.zero_mulVec]
  exact ⟨fun a => zero_mem _, zero_mem _, fun i => zero_mem _⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem K_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

end Cong

section Chi

variable (I : AutInst) (g : ℕ)

/- English proof (translation)
Replace the relevant objects with their definitions. Supply the required witnesses or components.
-/
theorem Z_zero : ZMod' I g 0 := by
  unfold Formalism.L2.SG.HidaSetting.ZMod'
  exact ⟨0, zero_mem _, (mul_zero _).symm⟩
/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Z_add {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a + b) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha hb ⊢
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, (mul_add _ _ _).symm⟩
/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Z_sub {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a - b) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha hb ⊢
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s - t, sub_mem hs ht, (mul_sub _ _ _).symm⟩
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Z_sum {ι : Type*} (s : Finset ι) (f : ι → I.E ⊗[I.F] Af I.F) (h : ∀ i ∈ s, ZMod' I g (f i)) :
    ZMod' I g (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (ZMod' I g) (fun a b ha hb => Z_add I g ha hb) (Z_zero I g) h
/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Z_smul {c a : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) : ZMod' I g (c * a) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha ⊢
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨c * t, mul_mem hc ht, by ring⟩
/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Z_sig {a : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) : ZMod' I g (sigA I a) := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at ha ⊢
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨sigA I t, sigA_mem I ht, by rw [map_mul, map_natCast]⟩

def Qs (f : VA I) : Submodule (IntAf I.F I.E) (VA I) where
  carrier := {v | ZMod' I g (hA I f v)}
  add_mem' {v w} hv hw := by
    show ZMod' I g (hA I f (v + w)); rw [hA_add_right]; exact Z_add I g hv hw
  zero_mem' := by
    show ZMod' I g (hL I f 0); rw [map_zero]; exact Z_zero I g
  smul_mem' c v hv := by
    show ZMod' I g (hA I f ((c : I.E ⊗[I.F] Af I.F) • v)); rw [hA_smul_right]; exact Z_smul I g c.2 hv

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mL_Qs {f : VA I} (hf : f ∈ I.Lf) : mL I g ≤ Qs I g f := by
  unfold Formalism.L2.SG.HidaSetting.mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  show ZMod' I g (hA I f ((g : I.E ⊗[I.F] Af I.F) • x))
  rw [hA_smul_right]
  unfold Formalism.L2.SG.HidaSetting.ZMod'
  exact ⟨_, hA_int I hf hx, rfl⟩

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem divN_add (a b : I.E ⊗[I.F] Af I.F) : divN I g (a + b) = divN I g a + divN I g b := by
  unfold Formalism.L2.SG.HidaSetting.divN
  exact mul_add _ _ _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem inv_g (hg : g ≠ 0) :
    algebraMap I.F (I.E ⊗[I.F] Af I.F) ((g : I.F)⁻¹) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
  have h : (g : I.F) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) g, ← map_mul, inv_mul_cancel₀ h, map_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem divN_gmul (hg : g ≠ 0) (t : I.E ⊗[I.F] Af I.F) : divN I g ((g : I.E ⊗[I.F] Af I.F) * t) = t := by
  unfold Formalism.L2.SG.HidaSetting.divN
  rw [← mul_assoc, inv_g I g hg, one_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem gmul_divN (hg : g ≠ 0) (c : I.E ⊗[I.F] Af I.F) : (g : I.E ⊗[I.F] Af I.F) * divN I g c = c := by
  unfold Formalism.L2.SG.HidaSetting.divN
  rw [← mul_assoc, mul_comm (g : I.E ⊗[I.F] Af I.F), inv_g I g hg, one_mul]

variable {ψ : I.E ⊗[I.F] Af I.F → ℂ} (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
  (hint : ∀ x ∈ IntAf I.F I.E, ψ x = 1)
include hadd hint

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem psi_Z (hg : g ≠ 0) {c : I.E ⊗[I.F] Af I.F} (hc : ZMod' I g c) : ψ (divN I g c) = 1 := by
  unfold Formalism.L2.SG.HidaSetting.ZMod' at hc
  obtain ⟨t, ht, rfl⟩ := hc
  rw [divN_gmul I g hg]
  exact hint t ht

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem psi_mul_of_Z (hg : g ≠ 0) {a b c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g (c - a - b)) :
    ψ (divN I g c) = ψ (divN I g a) * ψ (divN I g b) := by
  have e : c = (c - a - b) + a + b := by abel
  rw [e, divN_add I g, divN_add I g, hadd, hadd,
    psi_Z (I := I) (g := g) (hadd := hadd) (hint := hint) hg h, one_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem psi_pow (n : ℕ) (a : I.E ⊗[I.F] Af I.F) : ψ ((n : I.E ⊗[I.F] Af I.F) * a) = ψ a ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero]; exact hint 0 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, pow_succ]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem psi_norm (hg : g ≠ 0) {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) : ‖ψ (divN I g c)‖ = 1 := by
  have h1 : ψ (divN I g c) ^ g = 1 := by
    rw [← psi_pow (I := I) (hadd := hadd) (hint := hint) (n := g) (a := divN I g c), gmul_divN I g hg]
    exact hint c hc
  have h2 : ‖ψ (divN I g c)‖ ^ g = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hg).mp h2

end Chi

section Frame

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)

def Afun (x : I.Gf) : I.E ⊗[I.F] Af I.F :=
  (∑ a, hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a)) +
    ∑ i : Fin k, if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flagLevelCharacter_eq_psi_divN (ψ : I.E ⊗[I.F] Af I.F → ℂ) (x : I.Gf) :
    chi2f I ψ g e0 f0 z0 bw bwd x = ψ (divN I g (Afun I e0 f0 z0 bw bwd x)) := rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem term_Z {x y : I.Gf} (f n : VA I) (hn : ZMod' I g (hA I f n))
    (hq : (I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n) ∈ Qs I g f) :
    ZMod' I g (hA I f (I.fmat (x * y) *ᵥ n) - hA I f (I.fmat x *ᵥ n) - hA I f (I.fmat y *ᵥ n)) := by
  have hq' : ZMod' I g (hA I f ((I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n))) := hq
  rw [fmat_mul_identity I, hA_sub_right, hA_add_right, hA_add_right]
  have e : hA I f ((I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n)) + hA I f (I.fmat x *ᵥ n) +
        hA I f (I.fmat y *ᵥ n) - hA I f n - hA I f (I.fmat x *ᵥ n) - hA I f (I.fmat y *ᵥ n) =
      hA I f ((I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n)) - hA I f n := by abel
  rw [e]
  exact Z_sub I g hq' hn

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem congruence_fixed_term {x : I.Gf} (f n : VA I) (hn : ZMod' I g (hA I f n))
    (hq : (I.fmat x - 1) *ᵥ n ∈ Qs I g f) : ZMod' I g (hA I f (I.fmat x *ᵥ n)) := by
  have e : I.fmat x *ᵥ n = (I.fmat x - 1) *ᵥ n + n := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  have hq' : ZMod' I g (hA I f ((I.fmat x - 1) *ᵥ n)) := hq
  rw [e, hA_add_right]
  exact Z_add I g hq' hn

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem Me_Q (hf0 : ∀ a, f0 a ∈ I.Lf) (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (a : Fin r) : Mo I g (e0 '' {b | b.1 < a.1}) ≤ Qs I g (f0 a) := by
  unfold Mo
  refine sup_le ?_ (mL_Qs I g (hf0 a))
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  exact hfe a b (by intro h; subst h; exact lt_irrefl a.1 hb)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem Mb_Q (hbwd : ∀ i, bwd i ∈ I.Lf) (hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a)))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) (i : Fin k) :
    Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) ≤ Qs I g (bwd i) := by
  unfold Mo
  refine sup_le ?_ (mL_Qs I g (hbwd i))
  rw [Submodule.span_le]
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hbe i a
  · exact hbb i j (by intro h; subst h; exact lt_irrefl i.1 hj)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem nxt_Z (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0)) (a : Fin r) : ZMod' I g (hA I (f0 a) (nxt e0 z0 a)) := by
  unfold Formalism.L2.SG.HidaSetting.nxt
  split_ifs with h
  · exact hfe a _ (fun e => absurd (congrArg Fin.val e) (by simp))
  · exact hfz a

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem nxt_mem (he0 : ∀ a, e0 a ∈ I.Lf) (hz0 : z0 ∈ I.Lf) (a : Fin r) : nxt e0 z0 a ∈ I.Lf := by
  unfold Formalism.L2.SG.HidaSetting.nxt
  split_ifs with h
  · exact he0 _
  · exact hz0

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem nxt_cong {y : I.Gf} (hcy : K2cong I g e0 z0 bw y) (a : Fin r) :
    (I.fmat y - 1) *ᵥ nxt e0 z0 a ∈ Mo I g (e0 '' {b | b.1 < a.1 + 1}) := by
  unfold Formalism.L2.SG.HidaSetting.K2cong at hcy
  obtain ⟨h1, h2, -⟩ := hcy
  unfold Formalism.L2.SG.HidaSetting.nxt
  split_ifs with h
  · exact h1 ⟨a.1 + 1, h⟩
  · refine Mo_mono I ?_ h2
    rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_, rfl⟩
    show b.1 < a.1 + 1
    have := b.2
    omega

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem e_step {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (a : Fin r) :
    ∀ v ∈ Mo I g (e0 '' {b | b.1 < a.1 + 1}),
      (I.fmat x - 1) *ᵥ v ∈ Mo I g (e0 '' {b | b.1 < a.1}) := by
  unfold Formalism.L2.SG.HidaSetting.K2cong at hcx
  refine pres1 I hx g _ _ ?_ (mL_Mo I)
  rintro _ ⟨b, hb, rfl⟩
  exact Mo_mono I ((Set.image_mono (lt_sub (Nat.lt_succ_iff.mp hb)) : e0 '' _ ⊆ e0 '' _)) (hcx.1 b)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem b_step {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (i : Fin k) :
    ∀ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1 + 1}),
      (I.fmat x - 1) *ᵥ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) := by
  unfold Formalism.L2.SG.HidaSetting.K2cong at hcx
  refine pres1 I hx g _ _ ?_ (mL_Mo I)
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact Mo_mono I ((Set.image_subset_range _ _).trans (fun _ h => Or.inl h)) (hcx.1 a)
  · exact Mo_mono I (fun _ h => Or.imp id (fun h' => (Set.image_mono (lt_sub (Nat.lt_succ_iff.mp hj)) : bw '' _ ⊆ bw '' _) h') h)
      (hcx.2.2 j)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Afun_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x)
    (hcy : K2cong I g e0 z0 bw y)
    (hf0 : ∀ a, f0 a ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf)
    (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0))
    (hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a)))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) :
    ZMod' I g (Afun I e0 f0 z0 bw bwd (x * y) - Afun I e0 f0 z0 bw bwd x - Afun I e0 f0 z0 bw bwd y) := by
  have h : Afun I e0 f0 z0 bw bwd (x * y) - Afun I e0 f0 z0 bw bwd x - Afun I e0 f0 z0 bw bwd y =
      (∑ a, (hA I (f0 a) (I.fmat (x * y) *ᵥ nxt e0 z0 a) - hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a) -
        hA I (f0 a) (I.fmat y *ᵥ nxt e0 z0 a))) +
      ∑ i : Fin k, ((if h : i.1 + 1 < k then hA I (bwd i) (I.fmat (x * y) *ᵥ bw ⟨i.1 + 1, h⟩) else 0) -
        (if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0) -
        (if h : i.1 + 1 < k then hA I (bwd i) (I.fmat y *ᵥ bw ⟨i.1 + 1, h⟩) else 0)) := by
    simp only [Afun, Finset.sum_sub_distrib]; ring
  rw [h]
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · exact term_Z I g _ _ (nxt_Z I g e0 f0 z0 hfe hfz a)
      (Me_Q I g e0 f0 hf0 hfe a (e_step I g e0 z0 bw hx hcx a _ (nxt_cong I g e0 z0 bw hcy a)))
  · by_cases h : i.1 + 1 < k
    · simp only [dif_pos h]
      exact term_Z I g _ _ (hbb i _ (fun he => by rw [Fin.ext_iff] at he; simp at he))
        (Mb_Q I g e0 bw bwd hbwd hbe hbb i (b_step I g e0 z0 bw hx hcx i _ (hcy.2.2 ⟨i.1 + 1, h⟩)))
    · simp only [dif_neg h, sub_self]; exact Z_zero I g

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem Afun_int {x : I.Gf} (hx : x ∈ I.Kset) (he0 : ∀ a, e0 a ∈ I.Lf) (hf0 : ∀ a, f0 a ∈ I.Lf)
    (hz0 : z0 ∈ I.Lf) (hbw : ∀ i, bw i ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf) :
    Afun I e0 f0 z0 bw bwd x ∈ IntAf I.F I.E := by
  unfold Afun
  refine add_mem (sum_mem fun a _ => hA_int I (hf0 a)
    (K_mv I hx (nxt_mem (I := I) (e0 := e0) (z0 := z0) he0 hz0 a))) (sum_mem fun i _ => ?_)
  split_ifs with h
  · exact hA_int I (hbwd i) (K_mv I hx (hbw _))
  · exact zero_mem _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Kg_sub {x : I.Gf} (hx : x ∈ I.Kg g) : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ mL I g := by
  intro y hy
  obtain ⟨-, hx2⟩ := hx
  obtain ⟨z, hz, e⟩ := hx2 y hy
  rw [e]
  exact smul_mem_mL I hz

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Supply the required witnesses or components.
-/
theorem cong_Kg {x : I.Gf} (hx : x ∈ I.Kg g) (he0 : ∀ a, e0 a ∈ I.Lf) (hz0 : z0 ∈ I.Lf)
    (hbw : ∀ i, bw i ∈ I.Lf) : K2cong I g e0 z0 bw x := by
  have h := Kg_sub I g hx
  unfold Formalism.L2.SG.HidaSetting.K2cong Formalism.L2.SG.HidaSetting.InMod
  exact ⟨fun a => Submodule.mem_sup_right (h _ (he0 a)), Submodule.mem_sup_right (h _ hz0),
    fun i => Submodule.mem_sup_right (h _ (hbw i))⟩

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem Afun_Kg {x : I.Gf} (hx : x ∈ I.Kg g) (he0 : ∀ a, e0 a ∈ I.Lf) (hf0 : ∀ a, f0 a ∈ I.Lf)
    (hz0 : z0 ∈ I.Lf) (hbw : ∀ i, bw i ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf)
    (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) :
    ZMod' I g (Afun I e0 f0 z0 bw bwd x) := by
  have hK := Kg_sub I g hx
  unfold Afun
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · exact congruence_fixed_term I g (f0 a) _ (nxt_Z I g e0 f0 z0 hfe hfz a)
      (mL_Qs I g (hf0 a) (hK _ (nxt_mem (I := I) (e0 := e0) (z0 := z0) he0 hz0 a)))
  · split_ifs with h
    · exact congruence_fixed_term I g (bwd i) _ (hbb i _ (fun e => absurd (congrArg Fin.val e) (by simp)))
        (mL_Qs I g (hbwd i) (hK _ (hbw _)))
    · exact Z_zero I g

end Frame

end PI.UnitaryDimensionFormula.unitaryCongruence
