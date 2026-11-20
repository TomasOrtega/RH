import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.HomExtensionByZeroOrthDecompRational

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

/- English proof (translation)
Simplify using `[uA]`.
-/
theorem uA_zero : uA L 0 = 1 := by simp [uA]

/- English proof (translation)
Simplify using `[uA, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun k => (ComplexParameterFamilyContinuity.em_ne L k), fun k => (ComplexParameterFamilyContinuity.em_ne L k).symm]`.
-/
theorem uA_col (u : Fin L.n → AE F E) (j : Fin d.n) : uA L u j L.i₀ = if j = L.i₀ then 1 else 0 := by
  simp [uA, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun k => (ComplexParameterFamilyContinuity.em_ne L k),
    fun k => (ComplexParameterFamilyContinuity.em_ne L k).symm]

/- English proof (translation)
Simplify using `only [uA, aB, add_mul, one_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (ComplexParameterFamilyContinuity.em_ne L j) _, add_zero]`.
-/
theorem uA_mul_aB (u : Fin L.n → AE F E) (δ : E) (a : AF F) : uA L u * aB L δ a = aB L δ a := by
  simp only [uA, aB, add_mul, one_mul, Finset.sum_mul]
  rw [Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (ComplexParameterFamilyContinuity.em_ne L j) _, add_zero]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [aB, Matrix.mul_apply, Matrix.single_apply, Matrix.map_apply, Matrix.transpose_apply]`. Distinguish the cases in `hi : L.i₀ = i`. Substitute `hi` using the available equality. Distinguish the cases in `hj : j = L.i₀`.

Substitute `hj` using the available equality. Simplify using `[uA_col]`. Simplify using `[uA_col, hj, Ne.symm hj]`. Simplify using `[hi]`.
-/
theorem aB_mul_D (u : Fin L.n → AE F E) (δ : E) (a : AF F) : aB L δ a * (uA L u)ᵀ.map (cA σ) = aB L δ a := by
  ext i j
  simp only [aB, Matrix.mul_apply, Matrix.single_apply, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hi : L.i₀ = i
  · subst hi
    by_cases hj : j = L.i₀
    · subst hj; simp [uA_col]
    · simp [uA_col, hj, Ne.symm hj]
  · simp [hi]

/- English proof (translation)
Simplify using `only [aB, add_smul, Matrix.single_add]`.
-/
theorem aB_add (δ : E) (a a' : AF F) : aB L δ (a + a') = aB L δ a + aB L δ a' := by
  simp only [aB, add_smul, Matrix.single_add]

/- English proof (translation)
Simplify using `only [sB, Pi.add_apply, map_add, mul_add, neg_add, Matrix.single_add, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => by abel` and prove the remaining obligations.
-/
theorem sB_add (b b' : Fin L.n → AE F E) : sB R L (b + b') = sB R L b + sB R L b' := by
  simp only [sB, Pi.add_apply, map_add, mul_add, neg_add, Matrix.single_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by abel

/- English proof (translation)
Apply the tactic sequence `rcases r with i | i <;> rcases idx L i with rfl | ⟨k, rfl⟩`. Conclude with `Or.inl rfl`. Conclude with `Or.inr (Or.inr ⟨Sum.inl k, rfl⟩)`. Conclude with `Or.inr (Or.inl rfl)`. Conclude with `Or.inr (Or.inr ⟨Sum.inr k, rfl⟩)`.
-/
theorem idx2 (r : Fin d.n ⊕ Fin d.n) : r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ a, r = Sum.map L.em L.em a := by
  rcases r with i | i <;> rcases idx L i with rfl | ⟨k, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl k, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr k, rfl⟩)

def padB (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ k, ∑ l, Matrix.single (L.em k) (L.em l) (β k l)

/- English proof (translation)
Simplify using `[padB, Matrix.sum_apply, Matrix.single_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]`.
-/
theorem padB_apply_i0_eq_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (j : Fin d.n) : padB L β L.i₀ j = 0 := by
  simp [padB, Matrix.sum_apply, Matrix.single_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]

/- English proof (translation)
Simplify using `[padB, Matrix.sum_apply, Matrix.single_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]`.
-/
theorem pad_block_col_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i : Fin d.n) : padB L β i L.i₀ = 0 := by
  simp [padB, Matrix.sum_apply, Matrix.single_apply, fun k => ComplexParameterFamilyContinuity.em_ne L k]

/- English proof (translation)
Simplify using `[padB, Matrix.sum_apply, Matrix.single_apply, L.inj.eq_iff, ite_and, Finset.sum_ite_eq']`.
-/
theorem padB_em (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (k l : Fin L.n) : padB L β (L.em k) (L.em l) = β k l := by
  simp [padB, Matrix.sum_apply, Matrix.single_apply, L.inj.eq_iff, ite_and, Finset.sum_ite_eq']

/- English proof (translation)
Set `φ : (Fin L.n → E) →+ (Fin L.n → AE F E)` to `AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin L.n)`. Establish `hle : L.ratV ≤ φ.range` using `(AddSubgroup.closure_le _).2 (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)`. Take `⟨x, hx⟩` from `hle hb`. Conclude with `⟨x, hx.symm⟩`.
-/
theorem mem_ratV {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : ∃ x : Fin L.n → E, b = GlobalTheory.ThK.incV F x := by
  let φ : (Fin L.n → E) →+ (Fin L.n → AE F E) :=
    AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin L.n)
  have hle : L.ratV ≤ φ.range := (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
  obtain ⟨x, hx⟩ := hle hb
  exact ⟨x, hx.symm⟩

/- English proof (translation)
Use `show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (t • e) = algebraMap F (AF F) t • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) e`. Rewrite using `[map_smul, algebraMap_smul]`.
-/
theorem inclR_smul (t : F) (e : E) :
    inclR (F := F) (AF F) (t • e) = algebraMap F (AF F) t • inclR (F := F) (AF F) e := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (t • e) =
    algebraMap F (AF F) t • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) e
  rw [map_smul, algebraMap_smul]

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

/- English proof (translation)
Take `⟨a', ha⟩` from `h.uM u`. Rewrite using `[ha, lr_of ha (uA_mul_neg L u)]`.
-/
theorem inFrame_uM' (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 ((uA L (-u))ᵀ.map (cA σ)) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, lr_of ha (uA_mul_neg L u)]

/- English proof (translation)
Establish `hin : ∀ a b, inFrame d.b (L.j (nb' β)) (Sum.map L.em L.em a) (Sum.map L.em L.em b) = inFrame L.b (nb' β) a b` using `fun a b => congrFun (congrFun (L.j_in (nb' β)) a) b`. Use extensionality with `r c`. Break down `idx2 L r with rfl | rfl | ⟨a, rfl⟩` into its components or cases. Rewrite using `[(L.j_out _ _ (by simp) c).1]`. Apply the tactic sequence `rcases c with c | c <;> simp [Matrix.one_apply, padB_apply_i0_eq_zero]`.

Rewrite using `[(L.j_out _ _ (by simp) c).1]`. Apply the tactic sequence `rcases c with c | c <;> simp [Matrix.one_apply]`. Break down `idx2 L c with rfl | rfl | ⟨b, rfl⟩` into its components or cases. Rewrite using `[(L.j_out _ _ (by simp) _).2]`. Apply the tactic sequence `rcases a with a | a <;> simp [Matrix.one_apply, ComplexParameterFamilyContinuity.em_ne]`.

Rewrite using `[(L.j_out _ _ (by simp) _).2]`. Apply the tactic sequence `rcases a with a | a <;> simp [Matrix.one_apply, pad_block_col_zero, ComplexParameterFamilyContinuity.em_ne]`. Rewrite using `[hin, h.nb' β]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, padB_em, L.inj.eq_iff]`.
-/
theorem inFrame_jn (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ L.Y L.b) :
    inFrame d.b (L.j (nb' β)) = Matrix.fromBlocks 1 (padB L β.1) 0 1 := by
  have hin : ∀ a b, inFrame d.b (L.j (nb' β)) (Sum.map L.em L.em a) (Sum.map L.em L.em b) = inFrame L.b (nb' β) a b :=
    fun a b => congrFun (congrFun (L.j_in (nb' β)) a) b
  ext r c
  rcases idx2 L r with rfl | rfl | ⟨a, rfl⟩
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply, padB_apply_i0_eq_zero]
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply]
  · rcases idx2 L c with rfl | rfl | ⟨b, rfl⟩
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, ComplexParameterFamilyContinuity.em_ne]
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, pad_block_col_zero, ComplexParameterFamilyContinuity.em_ne]
    · rw [hin, h.nb' β]
      rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, padB_em, L.inj.eq_iff]

/- English proof (translation)
Rewrite using `[inFrame_cM h]`. Simplify using `[uA_zero, Matrix.transpose_one]`.
-/
theorem inFrame_centre_matrix (h : Hyp L nb uM nb' w₁ cM δ) (a : AF F) :
    inFrame d.b (cM (0, a)) = Matrix.fromBlocks 1 (aB L δ a) 0 1 := by
  rw [inFrame_cM h]
  simp [uA_zero, Matrix.transpose_one]

/- English proof (translation)
The claim follows from `inFrame_sM' b`.
-/
theorem inFrame_sM (b : Fin L.n → AE F E) : inFrame d.b (sM R L b) = bMat (sB R L b) :=
  inFrame_sM' b

/- English proof (translation)
Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, inFrame_sM', inFrame_sM', inFrame_sM', sB_add]`. Conclude with `(kfour.nM_mul _ _).symm`.
-/
theorem sM_add (b b' : Fin L.n → AE F E) : sM R L (b + b') = sM R L b * sM R L b' := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_sM', inFrame_sM', inFrame_sM', sB_add]
  exact (kfour.nM_mul _ _).symm

/- English proof (translation)
Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, inFrame_cM h, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply]`. Simplify using `[uA_mul_aB]`.
-/
theorem cM_split (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : cM (u, a) = uM u * cM (0, a) := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_cM h, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply]
  simp [uA_mul_aB]

/- English proof (translation)
Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, KAway.inFrame_mul, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[uA_mul_aB, aB_mul_D]`.
-/
theorem cM_comm (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : uM u * cM (0, a) = cM (0, a) * uM u := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_uM' h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [uA_mul_aB, aB_mul_D]

/- English proof (translation)
Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_centre_matrix h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply, aB_add]`. Simplify using `[add_comm]`.
-/
theorem centre_matrix_add (h : Hyp L nb uM nb' w₁ cM δ) (a a' : AF F) : cM (0, a + a') = cM (0, a) * cM (0, a') := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_centre_matrix h, inFrame_centre_matrix h, Matrix.fromBlocks_multiply, aB_add]
  simp [add_comm]

/- English proof (translation)
Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_sM', bMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[add_comm]`.
-/
theorem siegel_centre_commute (h : Hyp L nb uM nb' w₁ cM δ) (b : Fin L.n → AE F E) (a : AF F) : sM R L b * cM (0, a) = cM (0, a) * sM R L b := by
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_centre_matrix h, inFrame_sM', bMat, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [add_comm]

/- English proof (translation)
Establish `hc : β.1ᵀ = -((((R.ε : ℤ) : AE F E)) • β.1.map (cA σ))` using `(kfour.mem_nA_iff (sig2 d) R.hε β.1).1 β.2`. Establish `hcij : ∀ i j, β.1 j i = -(((R.ε : ℤ) : AE F E) * cA σ (β.1 i j))` using `fun i j => by`. Use `congrFun (congrFun hc i) j` as an intermediate fact. Simplify using `using this`. Establish `e2` using `eps_mul R`.

Apply `KAway.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[KAway.inFrame_mul, KAway.inFrame_mul, inFrame_jn h, inFrame_sM', inFrame_centre_matrix h, h.nb β, bMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Use `congr 1`. Use extensionality with `i j`.

Apply the tactic sequence `rcases idx L i with rfl | ⟨k, rfl⟩ <;> rcases idx L j with rfl | ⟨l, rfl⟩ <;>`. Simplify using `only [Matrix.add_apply, sB_i0i0, sB_i0em, siegel_block_embedded_row, sB_emem, padB_apply_i0_eq_zero, pad_block_col_zero, padB_em, aB, Matrix.single_apply, C4.prj_val, Matrix.submatrix_apply, pb, pa, eA_eq, fun k => ComplexParameterFamilyContinuity.em_ne L k, fun k => (ComplexPara …`. Establish `hy : cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * β.1 L.i₀ L.i₀`. Establish `e` using `hcij L.i₀ L.i₀`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[neg_mul_neg, ← mul_assoc, e2, one_mul]`. Use `_ = _ := by rw [← e]`. Conclude with `(eig h _ hy).symm`. Conclude with `hcij _ _`.
-/
theorem nb_split (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) :
    nb β = L.j (nb' (C4.prj L β)) * (sM R L (pb L β) * cM (0, pa L δ β)) := by
  have hc : β.1ᵀ = -((((R.ε : ℤ) : AE F E)) • β.1.map (cA σ)) := (kfour.mem_nA_iff (sig2 d) R.hε β.1).1 β.2
  have hcij : ∀ i j, β.1 j i = -(((R.ε : ℤ) : AE F E) * cA σ (β.1 i j)) := fun i j => by
    have := congrFun (congrFun hc i) j
    simpa using this
  have e2 := eps_mul R
  apply KAway.inFrame_inj d
  rw [KAway.inFrame_mul, KAway.inFrame_mul, inFrame_jn h, inFrame_sM', inFrame_centre_matrix h, h.nb β, bMat,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  rcases idx L i with rfl | ⟨k, rfl⟩ <;> rcases idx L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.add_apply, sB_i0i0, sB_i0em, siegel_block_embedded_row, sB_emem, padB_apply_i0_eq_zero, pad_block_col_zero, padB_em, aB,
      Matrix.single_apply, C4.prj_val, Matrix.submatrix_apply, pb, pa, eA_eq, fun k => ComplexParameterFamilyContinuity.em_ne L k,
      fun k => (ComplexParameterFamilyContinuity.em_ne L k).symm, and_self, and_false, false_and, if_true, if_false, add_zero, zero_add]
  · have hy : cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * β.1 L.i₀ L.i₀ := by
      have e := hcij L.i₀ L.i₀
      calc cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * -(((R.ε : ℤ) : AE F E) * cA σ (β.1 L.i₀ L.i₀)) := by
            rw [neg_mul_neg, ← mul_assoc, e2, one_mul]
        _ = _ := by rw [← e]
    exact (eig h _ hy).symm
  · exact hcij _ _

/- English proof (translation)
The claim follows from `j_move' h u β''`.
-/
theorem j_move (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (sM R L b * cM (u, a)) =
      sM R L (b + B) * cM (u, a + A) * L.j (nb' β'') :=
  j_move' h u β''

/- English proof (translation)
The claim follows from `j_conj' h γ'`.
-/
theorem j_conj (h : Hyp L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (sM R L b * cM (u, a)) = sM R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w, w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) :=
  j_conj' h γ'

/- English proof (translation)
The claim follows from `heis' h`.
-/
theorem Heisenberg₂ (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (sM R L b * cM (u, a)) = sM R L b * cM (u₀ + u, a₀ + a + Z u₀ b) :=
  heis' h

/- English proof (translation)
The claim follows from `section_w1_siegel_invariant_of_hyp h hf z b g`.
-/
theorem section_w1_siegel_invariant (h : Hyp L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : phz d f s₁ z (w₁ * (sM R L b * g)) = phz d f s₁ z (w₁ * g) :=
  section_w1_siegel_invariant_of_hyp h hf z b g

/- English proof (translation)
Take `⟨x, rfl⟩` from `mem_ratV L hb`. Use `kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (x j) + Matrix.single (L.em j) L.i₀ (-(((R.ε : ℤ) : E) * σ (x j))))) 0 1) ?_` and prove the remaining obligations. Rewrite using `[inFrame_sM']`. Use extensionality with `r c`. Apply the tactic sequence `rcases r with i | i <;> rcases c with j | j <;>`.

Simplify using `[bMat, incM, Matrix.map_apply, sB, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, eA, map_neg, map_mul, map_intCast]`.
-/
theorem sM_rat {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : sM R L b ∈ rat2 σ d.Y := by
  obtain ⟨x, rfl⟩ := mem_ratV L hb
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (x j) +
    Matrix.single (L.em j) L.i₀ (-(((R.ε : ℤ) : E) * σ (x j))))) 0 1) ?_
  rw [inFrame_sM']
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    simp [bMat, incM, Matrix.map_apply, sB, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, eA, map_neg, map_mul,
      map_intCast]

/- English proof (translation)
Take `⟨c1, c2⟩` from `c`. Take `⟨x, rfl⟩` from `mem_ratV L hu`. Take `⟨t, rfl⟩` from `ha`. Use `kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (x j)) (Matrix.single L.i₀ L.i₀ (t • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-(x j)))ᵀ.map σ)) ?_` and prove the remaining obligations. Rewrite using `[inFrame_cM h]`.

Use extensionality with `r c`. Apply the tactic sequence `rcases r with i | i <;> rcases c with j | j <;>`. Simplify using `[uA, aB, incM, Matrix.map_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Matrix.transpose_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), apply_ite (cA σ), apply_ite (⇑σ), GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRad …`.
-/
theorem cM_rat (h : Hyp L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨x, rfl⟩ := mem_ratV L hu
  obtain ⟨t, rfl⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (x j))
    (Matrix.single L.i₀ L.i₀ (t • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-(x j)))ᵀ.map σ)) ?_
  rw [inFrame_cM h]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    simp [uA, aB, incM, Matrix.map_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Matrix.transpose_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), apply_ite (cA σ), apply_ite (⇑σ), GlobalTheory.ThK.incV,
      GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_neg, inclR_smul]

/- English proof (translation)
The claim follows from `eisenstein_rational_invariant_reindex hf z hr hx g`.
-/
theorem eisenstein_rational_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : E2 L (phz d f s₁ z) (r * g) = E2 L (phz d f s₁ z) g :=
  eisenstein_rational_invariant_reindex hf z hr hx g

/- English proof (translation)
The claim follows from `eisenstein_norm_sum_reindex hf z hr hx g`.
-/
theorem eisenstein_norm_sum_rational_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (r * g))‖ₑ =
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * g)‖ₑ :=
  eisenstein_norm_sum_reindex hf z hr hx g

/- English proof (translation)
Rewrite using `[inFrame_sM']`. Apply the tactic sequence `rcases k with k | k <;> simp [bMat, Matrix.one_apply]`.
-/
theorem fix_sM (b : Fin L.n → AE F E) (k) :
    inFrame d.b (sM R L b) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [inFrame_sM']
  rcases k with k | k <;> simp [bMat, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[inFrame_cM h]`. Apply the tactic sequence `rcases k with k | k <;> simp [uA_col, Matrix.one_apply]`.
-/
theorem fix_cM (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k) :
    inFrame d.b (cM c) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [inFrame_cM h]
  rcases k with k | k <;> simp [uA_col, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[h.nb β]`. Apply the tactic sequence `rcases k with k | k <;> simp [Matrix.one_apply]`.
-/
theorem fix_nb (h : Hyp L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) (k) :
    inFrame d.b (nb β) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [h.nb β]
  rcases k with k | k <;> simp [Matrix.one_apply]

end PositivityTheory.SiegelWeilFormula.Act.C5

end
