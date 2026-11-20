import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ}

variable {R : RD d} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem lagrangian_condition_mul_fixing {γ r : d.G}
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) :
    LagrangianCondition L (γ * r) ↔ LagrangianCondition L γ := by
  have e : ∀ i, inFrame d.b (γ * r) (Sum.inr i) (Sum.inl L.i₀) = inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) := by
    intro i
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
    simp only [hx, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [LagrangianCondition, e]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem lagrangian_condition_stabiliser_iff {p g : d.G} (hp : p ∈ par2 σ d.Y) : LagrangianCondition L (p * g) ↔ LagrangianCondition L g := by
  have h21 : ∀ {q : d.G}, q ∈ par2 σ d.Y → ∀ i j, inFrame d.b q (Sum.inr i) (Sum.inl j) = 0 := by
    intro q hq i j
    have := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame q).1 hq
    have := congrFun (congrFun this i) j
    simpa [Matrix.toBlocks₂₁] using this
  have key : ∀ {q γ : d.G}, q ∈ par2 σ d.Y → LagrangianCondition L γ → LagrangianCondition L (q * γ) := by
    intro q γ hq hγ i
    have hγ' : ∀ k, inFrame d.b γ (Sum.inr k) (Sum.inl L.i₀) = 0 := hγ
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [h21 hq, hγ']
  refine ⟨fun h => ?_, key hp⟩
  have := key (inv_mem hp) h
  rwa [inv_mul_cancel_left] at this

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eisenstein_sum_reindex {M : Type} [AddCommMonoid M] [TopologicalSpace M] (H : ℂ → M) {s₁ : ℂ} {f : d.G → ℂ}
    (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, H (phz d f s₁ z (rep q.1 * (r * g))) =
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, H (phz d f s₁ z (rep q.1 * g)) := by
  classical
  let γr : rat2 σ d.Y := ⟨r, hr⟩
  let e0 := GlobalTheory.Eis.rmulEquiv (par2 σ d.Y) (rat2 σ d.Y) γr
  have hrep : ∀ q : Cs d, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ rep (e0 q) = p * (rep q * r) := by
    intro q
    have h1 : e0 q = GlobalTheory.AutomorphicL2Unitary.mk _ (Quotient.out q * γr) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ γr q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    have h2 : GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out q * γr) =
        GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out (e0 q)) := by
      rw [← h1]; exact (Quotient.out_eq _).symm
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h2
    refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
    have := congrArg Subtype.val hγ
    show ((Quotient.out (e0 q) : rat2 σ d.Y) : d.G) = _
    rw [← this]
    rfl
  have hS : ∀ q : Cs d, ¬ LagrangianCondition L (rep q) ↔ ¬ LagrangianCondition L (rep (e0 q)) := by
    intro q
    obtain ⟨p, hp, -, he⟩ := hrep q
    rw [he, lagrangian_condition_stabiliser_iff hp, lagrangian_condition_mul_fixing hx]
  let e : {q : Cs d // ¬ LagrangianCondition L (rep q)} ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)} := e0.subtypeEquiv hS
  have hterm : ∀ q : {q : Cs d // ¬ LagrangianCondition L (rep q)},
      phz d f s₁ z (rep q.1 * (r * g)) = phz d f s₁ z (rep (e q).1 * g) := by
    intro q
    obtain ⟨p, hp, hpr, he⟩ := hrep q.1
    show _ = phz d f s₁ z (rep (e0 q.1) * g)
    rw [he, mul_assoc, mul_assoc, C4.phz_rat hf z hp hpr]
  rw [tsum_congr fun q => congrArg H (hterm q)]
  exact e.tsum_eq (fun q => H (phz d f s₁ z (rep q.1 * g)))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eisenstein_rational_invariant_reindex {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : E2 L (phz d f s₁ z) (r * g) = E2 L (phz d f s₁ z) g :=
  eisenstein_sum_reindex id hf z hr hx g

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eisenstein_norm_sum_reindex {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (r * g))‖ₑ =
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * g)‖ₑ :=
  eisenstein_sum_reindex (fun w => ‖w‖ₑ) hf z hr hx g

def eO (L : LD d) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ 1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem em_ne' (L : LD d) (j : Fin L.n) : L.i₀ ≠ L.em j := (ComplexParameterFamilyContinuity.em_ne L j).symm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eO_mul_eO : eO L * eO L = eO L := by
  simp [eO]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eO_single (x : AE F E) : eO L * Matrix.single L.i₀ L.i₀ x = Matrix.single L.i₀ L.i₀ x := by
  simp [eO]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem single_eO (x : AE F E) : Matrix.single L.i₀ L.i₀ x * eO L = Matrix.single L.i₀ L.i₀ x := by
  simp [eO]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem wf_blocks (α β : AE F E) :
    (1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
      Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) α + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) β :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L) := by
  ext (i | i) (j | j) <;> simp [eO, Matrix.single, Matrix.one_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem wf_mul (α β α' β' : AE F E) (ha : α * α' = 1) (hb : β * β' = 1) :
    Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L) *
      Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - eO L) = 1 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have h1 : (1 - eO L) * (1 - eO L) = 1 - eO L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, eO_mul_eO]; abel
  congr 1
  · rw [h1, Matrix.single_mul_single_same, ha, ← eO]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, eO_single, single_eO]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, eO_single, single_eO]; abel
  · rw [h1, Matrix.single_mul_single_same, hb, ← eO]; abel

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem det_one_add_col (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hN : ∀ i j, j ≠ L.i₀ → N i j = 0)
    (h0 : N L.i₀ L.i₀ = 0) : (1 + N).det = 1 := by
  have e : N = Matrix.replicateCol Unit (fun i => N i L.i₀) * Matrix.replicateRow Unit (Pi.single L.i₀ (1 : AE F E)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hj : j = L.i₀
    · subst hj; simp
    · rw [hN i j hj]; simp [hj]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h0]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem section_w1_siegel_invariant_of_hyp (h : Hyp L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : phz d f s₁ z (w₁ * (sM R L b * g)) = phz d f s₁ z (w₁ * g) := by
  classical
  obtain ⟨a₁, b₁, ha₁, hb₁, hW⟩ := h.wf
  set α : AE F E := inclR (F := F) (AF F) a₁
  set β : AE F E := inclR (F := F) (AF F) b₁
  set α' : AE F E := inclR (F := F) (AF F) a₁⁻¹
  set β' : AE F E := inclR (F := F) (AF F) b₁⁻¹
  have hα : α * α' = 1 := by rw [← map_mul, mul_inv_cancel₀ ha₁, map_one]
  have hβ : β * β' = 1 := by rw [← map_mul, mul_inv_cancel₀ hb₁, map_one]
  set W := Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - eO L)
  set W' := Matrix.fromBlocks (1 - eO L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - eO L)
  have hW1 : inFrame d.b w₁ = W := by rw [hW, wf_blocks]
  have hWW : W * W' = 1 := wf_mul α β α' β' hα hβ
  have hWi : inFrame d.b w₁⁻¹ = W' := by
    have h1 : inFrame d.b w₁⁻¹ * W = 1 := by rw [← hW1, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    calc inFrame d.b w₁⁻¹ = inFrame d.b w₁⁻¹ * (W * W') := by rw [hWW, Matrix.mul_one]
      _ = W' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  set S := sB R L b
  set p : d.G := w₁ * sM R L b * w₁⁻¹
  have hP : inFrame d.b p = W * bMat S * W' := by
    simp only [p, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW1, hWi, inFrame_sM']
    rfl
  have hS0 : S L.i₀ L.i₀ = 0 := sB_i0i0 b
  have h1e : (1 - eO L) * (1 - eO L) = 1 - eO L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, eO_mul_eO]; abel
  have h21 : (inFrame d.b p).toBlocks₂₁ = 0 := by
    rw [hP]
    simp only [W, W', bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [add_mul, Matrix.single_mul_mul_single, hS0, mul_sub, mul_one, single_eO, sub_mul, one_mul, eO_single]
    simp
  set N := (1 - eO L) * S * Matrix.single L.i₀ L.i₀ α'
  have h11 : (inFrame d.b p).toBlocks₁₁ = 1 + N := by
    rw [hP]
    simp only [W, W', bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [h1e, add_mul, Matrix.single_mul_single_same, hα, ← eO]
    simp only [N]; abel
  have hN : ∀ i j, j ≠ L.i₀ → N i j = 0 := fun i j hj => by
    simp only [N]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ hj _
  have hN0 : N L.i₀ L.i₀ = 0 := by
    simp only [N, Matrix.mul_single_apply_same, sub_mul, one_mul, Matrix.sub_apply, eO, Matrix.single_mul_apply_same,
      one_mul, sub_self]
  have hp : p ∈ par2 σ d.Y := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame p).2 h21
  obtain ⟨t, ht⟩ := GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff.1 hp
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  have htv := ((kunf.isPar_frame ht₀ p t).1 ht).2
  have hdet : Matrix.GeneralLinearGroup.det t = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, htv, Matrix.det_mul, Matrix.det_mul, h11, det_one_add_col N hN hN0,
      mul_one, Units.val_one, ← Matrix.det_mul, kunf.incM_GL_mul_inv, Matrix.det_one]
  have hg : w₁ * (sM R L b * g) = p * (w₁ * g) := by simp only [p]; group
  rw [hg, C4.phz_par hf z ht hdet]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Treat this case separately.
-/
theorem ratV_incl {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    ∃ x : Fin L.n → E, v = fun i => inclR (F := F) (AF F) (x i) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv => obtain ⟨x, hx⟩ := hv; exact ⟨x, by rw [← hx]; rfl⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨x, rfl⟩ := hv; obtain ⟨x', rfl⟩ := hw; exact ⟨x + x', by ext i; simp⟩
  | neg v _ hv => obtain ⟨x, rfl⟩ := hv; exact ⟨-x, by ext i; simp⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_uA_i0i0 (u : Fin L.n → AE F E) : uA L u L.i₀ L.i₀ = 1 := by
  simp [uA, Matrix.sum_apply, Matrix.single, ComplexParameterFamilyContinuity.em_ne L]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_uA_i0em (u : Fin L.n → AE F E) (l : Fin L.n) : uA L u L.i₀ (L.em l) = u l := by
  simp [uA, Matrix.sum_apply, Matrix.single, Matrix.one_apply, em_ne' L, L.inj.eq_iff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem unipotent_block_embedded_zero (u : Fin L.n → AE F E) (k : Fin L.n) : uA L u (L.em k) L.i₀ = 0 := by
  simp [uA, Matrix.sum_apply, Matrix.single, Matrix.one_apply, ComplexParameterFamilyContinuity.em_ne L, em_ne' L]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_uA_emem (u : Fin L.n → AE F E) (k l : Fin L.n) :
    uA L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp [uA, Matrix.sum_apply, Matrix.single, Matrix.one_apply, ComplexParameterFamilyContinuity.em_ne L, em_ne' L, L.inj.eq_iff]

def Dm (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (uA L (-u))ᵀ.map (cA σ)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_D_i0i0 (u : Fin L.n → AE F E) : Dm L u L.i₀ L.i₀ = 1 := by
  simp [Dm, hz_uA_i0i0]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_D_i0em (u : Fin L.n → AE F E) (l : Fin L.n) : Dm L u L.i₀ (L.em l) = 0 := by
  simp [Dm, unipotent_block_embedded_zero]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem diagonal_block_embedded_neg_conj (u : Fin L.n → AE F E) (k : Fin L.n) : Dm L u (L.em k) L.i₀ = -cA σ (u k) := by
  simp [Dm, hz_uA_i0em]

/- English proof (translation)
Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hz_D_emem (u : Fin L.n → AE F E) (k l : Fin L.n) : Dm L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp only [Dm, Matrix.map_apply, Matrix.transpose_apply, hz_uA_emem]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_aB_i0i0 (x : AF F) : aB L δ x L.i₀ L.i₀ = x • inclR (F := F) (AF F) δ := by
  simp [aB, Matrix.single]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_aB_i0em (x : AF F) (l : Fin L.n) : aB L δ x L.i₀ (L.em l) = 0 := by
  simp [aB, Matrix.single, em_ne' L]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem centre_block_embedded_zero (x : AF F) (k : Fin L.n) : aB L δ x (L.em k) L.i₀ = 0 := by
  simp [aB, Matrix.single, em_ne' L]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hz_aB_emem (x : AF F) (k l : Fin L.n) : aB L δ x (L.em k) (L.em l) = 0 := by
  simp [aB, Matrix.single, em_ne' L]

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem hz_uA_add (u v : Fin L.n → AE F E) : uA L u * uA L v = uA L (u + v) := by
  have e := ComplexParameterFamilyContinuity.nilpotent_frame_mul_zero L u v
  change (1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L u) * (1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L v) = 1 + ComplexParameterFamilyContinuity.nilpotentFrameMatrix L (u + v)
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, e, add_zero]
  simp only [ComplexParameterFamilyContinuity.nilpotentFrameMatrix, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.

By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem heis' (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (sM R L b * cM (u, a)) = sM R L b * cM (u₀ + u, a₀ + a + Z u₀ b) := by
  classical
  let y : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AE F E := fun u₀ b =>
    ∑ l, b l * cA σ (u₀ l) - ∑ k, u₀ k * (eA R * cA σ (b k))
  refine ⟨fun u₀ b => ellA δ (y u₀ b), ?_, ?_, ?_⟩
  · have hl : Continuous (ellA (F := F) (E := E) δ) := IsModuleTopology.continuous_of_linearMap _
    have hc := GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ
    show Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => ellA δ (y p.1 p.2)
    refine hl.comp ((continuous_finset_sum _ fun l _ => ?_).sub (continuous_finset_sum _ fun k _ => ?_))
    · exact ((continuous_apply l).comp continuous_snd).mul (hc.comp ((continuous_apply l).comp continuous_fst))
    · exact ((continuous_apply k).comp continuous_fst).mul
        (continuous_const.mul (hc.comp ((continuous_apply k).comp continuous_snd)))
  · intro u₀ b hu hb
    obtain ⟨x0, rfl⟩ := ratV_incl hu
    obtain ⟨xb, rfl⟩ := ratV_incl hb
    have e : y (fun i => inclR (F := F) (AF F) (x0 i)) (fun i => inclR (F := F) (AF F) (xb i)) =
        inclR (F := F) (AF F) (∑ l, xb l * σ (x0 l) - ∑ k, x0 k * (((R.ε : ℤ) : E) * σ (xb k))) := by
      simp only [y, eA, map_sub, map_sum, map_mul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]
    show ellA δ (y _ _) ∈ _
    rw [e]
    exact ellA_inclR h _
  · intro u₀ a₀ b u a
    have hC : ∀ c, inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 (Dm L c.1) := inFrame_cM h
    have hM := inFrame_sM' (R := R) (L := L) b
    apply eq_of_upper
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hM]
      simp [bMat, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hM]
      simp [bMat, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      exact hz_uA_add u₀ u
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [bMat, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      have hZ : ellA δ (y u₀ b) • inclR (F := F) (AF F) δ = y u₀ b := by
        refine eig (R := R) h _ ?_
        have he := eps_mul R
        simp only [y, eA_eq, map_sub, map_sum, map_mul, map_intCast, cc d, mul_sub, Finset.mul_sum]
        simp only [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (-(u₀ l * cA σ (b l))) * he
      ext i j
      rcases idx L i with rfl | ⟨k, rfl⟩ <;> rcases idx L j with rfl | ⟨l, rfl⟩ <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, sum_split L, hz_uA_i0i0, hz_uA_i0em, unipotent_block_embedded_zero, hz_uA_emem,
          hz_D_i0i0, hz_D_i0em, diagonal_block_embedded_neg_conj, hz_D_emem, hz_aB_i0i0, hz_aB_i0em, centre_block_embedded_zero, hz_aB_emem, sB_i0i0,
          sB_i0em, siegel_block_embedded_row, sB_emem, Pi.add_apply, map_add, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
          mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      rw [add_smul, add_smul, hZ]
      simp only [y, mul_neg, mul_add, neg_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
      ring

end PositivityTheory.SiegelWeilFormula.Act.C5

end
