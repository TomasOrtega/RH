import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

section Gen

variable {R : Type} [CommRing R] {n : ℕ}

def rx : GL (Fin (n + n)) R ≃* GL (Fin n ⊕ Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rx_val (g : GL (Fin (n + n)) R) : (rx g).1 = g.1.submatrix finSumFinEquiv finSumFinEquiv := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem rx_inv_val (g : GL (Fin (n + n)) R) :
    ((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R).1 = (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← map_inv]; rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_rx [TopologicalSpace R] : Continuous (rx : GL (Fin (n + n)) R → GL (Fin n ⊕ Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin (n + n)) R => (((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := funext rx_inv_val
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_rx_symm [TopologicalSpace R] :
    Continuous (rx.symm : GL (Fin n ⊕ Fin n) R → GL (Fin (n + n)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin n ⊕ Fin n) R => (((rx.symm g)⁻¹ : GL (Fin (n + n)) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin n ⊕ Fin n) R).1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem form_iff {ι : Type} [Fintype ι] (c : R →+* R) (hc : ∀ x, c (c x) = x) {J : Matrix ι ι R} (hJ : J.map c = J)
    (g : Matrix ι ι R) : Formalism.UG.cT c g * J * g = J ↔ gᵀ * J * g.map c = J := by
  have key : (Formalism.UG.cT c g * J * g).map c = gᵀ * J * g.map c := by
    rw [Matrix.map_mul, Matrix.map_mul, hJ]
    congr 2
    ext i j
    simp [Formalism.UG.cT, hc]
  constructor
  · intro h
    rw [← key, h, hJ]
  · intro h
    have h2 := congrArg (fun M => M.map c) h
    simp only [Matrix.map_mul, hJ] at h2
    have e : (gᵀ).map c = Formalism.UG.cT c g := by ext i j; simp [Formalism.UG.cT]
    have e2 : (g.map c).map c = g := by ext i j; simp [hc]
    rwa [e, e2] at h2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem keeps_iff_int {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring R) (m : GL ι R) :
    (∀ y : ι → R, (∀ i, y i ∈ O) ↔ ∀ i, (m.1 *ᵥ y) i ∈ O) ↔
      ∀ r c, m.1 r c ∈ O ∧ (m⁻¹ : GL ι R).1 r c ∈ O := by
  constructor
  · intro h r c
    have hs : ∀ i, (Pi.single c (1 : R) : ι → R) i ∈ O := fun i => by
      by_cases e : i = c
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem]
    refine ⟨by simpa using (h _).1 hs r, ?_⟩
    have h2 := (h (((m⁻¹ : GL ι R).1) *ᵥ Pi.single c 1)).2 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hs) r
    simpa using h2
  · intro h y
    have key : ∀ (M : Matrix ι ι R), (∀ r c, M r c ∈ O) → ∀ y : ι → R, (∀ i, y i ∈ O) → ∀ i, (M *ᵥ y) i ∈ O :=
      fun M hM y hy i => O.sum_mem fun j _ => O.mul_mem (hM i j) (hy j)
    refine ⟨key _ (fun r c => (h r c).1) y, fun hy => ?_⟩
    have := key _ (fun r c => (h r c).2) _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Gen

section Sub

variable {R : Type} {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sub_inj {X Y : Matrix (Fin (n + n)) (Fin (n + n)) R} :
    X.submatrix finSumFinEquiv finSumFinEquiv = Y.submatrix finSumFinEquiv finSumFinEquiv ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa using this

end Sub

section Std

variable (D : D7) {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  have h := isCMExt_host D
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Treat this case separately.
-/
theorem sigR_sigR (z : AE D) : sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _
    rw [sig_sig]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigR_inclR (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (AF D.host.F) x) = inclR (AF D.host.F) (D.sp.cm.sig x) := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Jst_map : (GlobalTheory.StdUnn.Jst D n).map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem JR_map : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).map (sigR (AF D.host.F) D.sp.cm.sig) =
    JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) := by
  ext i j
  simp only [Matrix.map_apply, JR, sigR_inclR]
  rw [← Matrix.map_apply (f := D.sp.cm.sig), Jst_map]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem J_eq : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv =
    Ad.J (AE D) (-1) (Fin n) := by
  have key : ∀ x y, (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv x y =
      inclR (F := D.host.F) (E := D.host.E) (AF D.host.F) ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) x y) := fun x y => by
    simp only [JR, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  ext x y
  rw [key]
  rcases x with a | a <;> rcases y with b | b <;> simp [Ad.J, Matrix.one_apply, apply_ite (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))]

variable (χ : (AE D)ˣ →* Circle)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities.
-/
theorem mem_uSub_iff (g : GL (Fin (n + n)) (AE D)) :
    rx g ∈ (adCM D.sp.cm.sig χ).uSub (-1) (Fin n) ↔ g ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) := by
  change (rx g).1ᵀ * Ad.J (AE D) (-1) (Fin n) * (rx g).1.map (sigR (AF D.host.F) D.sp.cm.sig) = Ad.J (AE D) (-1) (Fin n) ↔
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1 * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1 = JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)
  rw [form_iff _ (sigR_sigR D) (JR_map D), ← J_eq, rx_val, ← sub_inj (X := _ * _ * _)]
  have : (g.1ᵀ * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1.map (sigR (AF D.host.F) D.sp.cm.sig)).submatrix finSumFinEquiv finSumFinEquiv =
      (g.1.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv *
        (g.1.submatrix finSumFinEquiv finSumFinEquiv).map (sigR (AF D.host.F) D.sp.cm.sig) := by
    rw [← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    rfl
  rw [this]

def toU (g : GlobalTheory.StdUnn.G D n) : UD D χ n :=
  ⟨rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g), (mem_uSub_iff D χ _).2 (Subtype.prop (p := (· ∈ HR _ _ _)) g)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toU_val (g : GlobalTheory.StdUnn.G D n) : (toU D χ g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

def ofU (u : UD D χ n) : GlobalTheory.StdUnn.G D n :=
  (⟨rx.symm u.1, (mem_uSub_iff D χ _).1 (by simpa using u.2)⟩ : HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofU_val (u : UD D χ n) : matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) (ofU D χ u) = rx.symm u.1 := rfl

def Psi (n : ℕ) : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n where
  toFun := toU D χ
  invFun := ofU D χ
  left_inv g := matHom_injective _ _ _ (by rw [ofU_val, toU_val]; exact rx.symm_apply_apply _)
  right_inv u := Subtype.ext (by rw [toU_val, ofU_val]; exact rx.apply_symm_apply _)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, toU_val, toU_val, toU_val, map_mul, map_mul])
  continuous_toFun := (continuous_rx.comp (isEmbedding_matHom _ _ _).continuous).subtype_mk _
  continuous_invFun := (isEmbedding_matHom _ _ _).continuous_iff.2 (continuous_rx_symm.comp continuous_subtype_val)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Psi_val (g : GlobalTheory.StdUnn.G D n) : (Psi D χ n g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

end Std

end GlobalTheory.CompanionTheory.StdChart

end
