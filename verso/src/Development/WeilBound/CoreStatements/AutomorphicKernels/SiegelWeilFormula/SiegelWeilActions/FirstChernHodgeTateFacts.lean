import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} {L : LD d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem _ h => obtain ⟨v, rfl⟩ := h`. Conclude with `⟨v, rfl⟩`. Consider the case `zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩`. Consider the case `add _ _ _ _ h h'`.

Take `⟨v, rfl⟩` from `h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩`. Consider the case `neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩`.
-/
theorem ratV_inc {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩

/- English proof (translation)
The claim follows from `funext fun i => by simp [GlobalTheory.ThK.incV]`.
-/
theorem neg_incV (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]

def A0 (L : LD d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Au, A0, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]`.
-/
theorem Au_inc (v : Fin L.n → E) : Au L (GlobalTheory.ThK.incV F v) = incM F (A0 L v) := by
  ext a b
  simp [Au, A0, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]

/- English proof (translation)
Establish `h1 : (Ap hU u).map (cA σ) * (Au L u)ᵀ = 1` using `mul_eq_one_comm.1 (frame_blk d (inFrame_uM hU u))`. Establish `h2 : (Au L u)ᵀ * (Au L (-u))ᵀ = 1` using `by rw [← Matrix.transpose_mul, Au_mul, neg_add_cancel, Au_zero, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Apc (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (Ap hU u).map (cA σ) = (Au L (-u))ᵀ := by
  have h1 : (Ap hU u).map (cA σ) * (Au L u)ᵀ = 1 := mul_eq_one_comm.1 (frame_blk d (inFrame_uM hU u))
  have h2 : (Au L u)ᵀ * (Au L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, Au_mul, neg_add_cancel, Au_zero, Matrix.transpose_one]
  calc (Ap hU u).map (cA σ) = (Ap hU u).map (cA σ) * ((Au L u)ᵀ * (Au L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (Au L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_basis d.bs`. Set `e` to `AlgEquiv.ofBijective σ (AlgHom.bijective σ)`. Use `⟨((A0 L (-v))ᵀ).map e.symm, Matrix.map_injective (cA_injective d) ?_⟩` and prove the remaining obligations. Use `show (Ap hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((A0 L (-v))ᵀ).map e.symm)).map (cA σ)`. Rewrite using `[Apc, kunf.incM_map_cA, Matrix.map_map, neg_incV, Au_inc]`.

Establish `h : (⇑σ ∘ ⇑e.symm) = id` using `funext fun x => e.apply_symm_apply x`. Rewrite using `[h, Matrix.map_id]`. Both sides reduce to the same expression.
-/
theorem Ap_inc (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    Ap hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((A0 L (-v))ᵀ).map e.symm, Matrix.map_injective (cA_injective d) ?_⟩
  show (Ap hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((A0 L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [Apc, kunf.incM_map_cA, Matrix.map_map, neg_incV, Au_inc]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl

/- English proof (translation)
Take `⟨v, rfl⟩` from `ratV_inc hu`. Take `⟨M, hM⟩` from `Ap_inc hU v`. Use `kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (A0 L v) 0 0 M) ?_` and prove the remaining obligations. Rewrite using `[inFrame_uM hU, Au_inc, hM]`. Simplify using `[incM, Matrix.fromBlocks_map]`.
-/
theorem uM_rat (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := ratV_inc hu
  obtain ⟨M, hM⟩ := Ap_inc hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (A0 L v) 0 0 M) ?_
  rw [inFrame_uM hU, Au_inc, hM]
  simp [incM, Matrix.fromBlocks_map]

/- English proof (translation)
Take `⟨v, rfl⟩` from `ratV_inc hu`. Take `⟨M, hM⟩` from `Ap_inc hU v`. Take `⟨T, hT⟩` from `kunf.mem_nF_iff.1 hβ`. Use `kunf.mem_nF_iff.2 ⟨A0 L (-v) * T * M, ?_⟩` and prove the remaining obligations. Rewrite using `[cj_val, neg_incV, Au_inc, hT, hM, kunf.incM_mul', kunf.incM_mul']`.
-/
theorem cj_rat (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : cj hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := ratV_inc hu
  obtain ⟨M, hM⟩ := Ap_inc hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨A0 L (-v) * T * M, ?_⟩
  rw [cj_val, neg_incV, Au_inc, hT, hM, kunf.incM_mul', kunf.incM_mul']

/- English proof (translation)
Establish `h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0` using `fun j => by`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[← h.1, hX, zero_mul]`. Conclude with `mul_zero _`. Simplify using `only [Au, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]`.
-/
theorem mul_Au (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * Au L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [Au, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Establish `h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0` using `fun j => by`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[← h.1, hX, mul_zero]`. Conclude with `zero_mul _`. Simplify using `only [Au, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul, Finset.sum_mul, h, Finset.sum_const_zero, add_zero]`.
-/
theorem AuT_mul (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (Au L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [Au, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Establish `h1 : T.1.1 * Au L (-u) = T.1.1` using `mul_Au _ (fun a => (hT.1 a).2) _`. Establish `h2 : Ap hU u * T.1.1 = T.1.1`. Apply `Matrix.map_injective (cA_injective d)` to reduce the goal to its premises. Use `show (Ap hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)`. Rewrite using `[kunf.map_cA_mul, Apc]`.

Conclude with `AuT_mul _ (fun b => by simp [(hT.1 b).1]) _`. Rewrite using `[cj_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]`.
-/
theorem trace_cj (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (cj hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * Au L (-u) = T.1.1 := mul_Au _ (fun a => (hT.1 a).2) _
  have h2 : Ap hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (cA_injective d)
    show (Ap hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, Apc]
    exact AuT_mul _ (fun b => by simp [(hT.1 b).1]) _
  rw [cj_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
