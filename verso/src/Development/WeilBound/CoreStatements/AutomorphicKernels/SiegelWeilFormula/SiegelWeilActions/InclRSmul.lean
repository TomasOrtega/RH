import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LinearFormAdelic
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousNilpotentFramePart
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (L : LD d)

def pre (r : Fin d.n) (h : r ≠ L.i₀) : Fin L.n := ((L.rng r).1 h).choose

/- English proof (translation)
The claim follows from `((L.rng r).1 h).choose_spec`.
-/
theorem em_pre (r : Fin d.n) (h : r ≠ L.i₀) : L.em (pre L r h) = r := ((L.rng r).1 h).choose_spec

/- English proof (translation)
The claim follows from `L.inj (em_pre L _ h)`.
-/
theorem pre_em (k : Fin L.n) (h : L.em k ≠ L.i₀) : pre L (L.em k) h = k := L.inj (em_pre L _ h)

/- English proof (translation)
Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.
-/
theorem eps_sq {R : Type} [Ring R] (ε : ℤˣ) : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

def padZ (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then 0 else if hc : c = L.i₀ then 0 else β (pre L r hr) (pre L c hc)

/- English proof (translation)
Simplify using `[Matrix.one_apply, L.inj.eq_iff]`.
-/
theorem one_em (k l : Fin L.n) :
    (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (L.em k) (L.em l) = (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) k l := by
  simp [Matrix.one_apply, L.inj.eq_iff]

/- English proof (translation)
Establish `hin` using `L.j_in x`. Rewrite `hin` using `[hx]`. Establish `emb : ∀ u v : Fin L.n ⊕ Fin L.n, inFrame d.b (L.j x) (Sum.map L.em L.em u) (Sum.map L.em L.em v) = Matrix.fromBlocks 1 β 0 1 u v` using `fun u v => by rw [← hin]; rfl`. Establish `kl : ∀ v, inFrame d.b (L.j x) (Sum.inl L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inl L.i₀) v ∧ inFrame d.b (L.j x) v (Sum.inl L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inl L.i₀)` using `fun v => L.j_out x _ (by simp) v`. Establish `kr : ∀ v, inFrame d.b (L.j x) (Sum.inr L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inr L.i₀) v ∧ inFrame d.b (L.j x) v (Sum.inr L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inr L.i₀)` using `fun v => L.j_out x _ (by simp) v`.

Use extensionality with `(r | r) (c | c)`. Break down `eq_or_ne r L.i₀ with rfl | hr` into its components or cases. Rewrite using `[(kl _).1]`. Simplify using `[Matrix.one_apply]`. Break down `eq_or_ne c L.i₀ with rfl | hc` into its components or cases.

Rewrite using `[(kl _).2]`. Simplify using `[Matrix.one_apply, hr]`. Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc`. Use `emb (Sum.inl k) (Sum.inl l)` as an intermediate fact.

Simplify using `only [Sum.map_inl, Matrix.fromBlocks_apply₁₁] at this ⊢`. Rewrite using `[this, one_em]`. Break down `eq_or_ne r L.i₀ with rfl | hr` into its components or cases. Rewrite using `[(kl _).1]`. Simplify using `[Matrix.one_apply, padZ]`.

Break down `eq_or_ne c L.i₀ with rfl | hc` into its components or cases. Rewrite using `[(kr _).2]`. Simplify using `[Matrix.one_apply, padZ]`. Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc`.

Use `emb (Sum.inl k) (Sum.inr l)` as an intermediate fact. Simplify using `only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₁₂] at this ⊢`. Rewrite using `[this]`. Simplify using `[padZ, ComplexParameterFamilyContinuity.em_ne, pre_em]`. Break down `eq_or_ne r L.i₀ with rfl | hr` into its components or cases.

Rewrite using `[(kr _).1]`. Simplify using `[Matrix.one_apply]`. Break down `eq_or_ne c L.i₀ with rfl | hc` into its components or cases. Rewrite using `[(kl _).2]`. Simplify using `[Matrix.one_apply]`.

Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc`. Use `emb (Sum.inr k) (Sum.inl l)` as an intermediate fact. Simplify using `only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₂₁] at this ⊢`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Break down `eq_or_ne r L.i₀ with rfl | hr` into its components or cases. Rewrite using `[(kr _).1]`. Simplify using `[Matrix.one_apply]`. Break down `eq_or_ne c L.i₀ with rfl | hc` into its components or cases.

Rewrite using `[(kr _).2]`. Simplify using `[Matrix.one_apply, hr]`. Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc`. Use `emb (Sum.inr k) (Sum.inr l)` as an intermediate fact.

Simplify using `only [Sum.map_inr, Matrix.fromBlocks_apply₂₂] at this ⊢`. Rewrite using `[this, one_em]`.
-/
theorem inFrame_j_nb {x : G2 σ L.Y} {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hx : inFrame L.b x = Matrix.fromBlocks 1 β 0 1) :
    inFrame d.b (L.j x) = Matrix.fromBlocks 1 (padZ L β) 0 1 := by
  have hin := L.j_in x
  rw [hx] at hin
  have emb : ∀ u v : Fin L.n ⊕ Fin L.n, inFrame d.b (L.j x) (Sum.map L.em L.em u) (Sum.map L.em L.em v) =
      Matrix.fromBlocks 1 β 0 1 u v := fun u v => by rw [← hin]; rfl
  have kl : ∀ v, inFrame d.b (L.j x) (Sum.inl L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inl L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inl L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inl L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  have kr : ∀ v, inFrame d.b (L.j x) (Sum.inr L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inr L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inr L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inr L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  ext (r | r) (c | c)
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp [Matrix.one_apply, hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inl l)
    simp only [Sum.map_inl, Matrix.fromBlocks_apply₁₁] at this ⊢
    rw [this, one_em]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [Matrix.one_apply, padZ]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [Matrix.one_apply, padZ]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inr l)
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₁₂] at this ⊢
    rw [this]
    simp [padZ, ComplexParameterFamilyContinuity.em_ne, pre_em]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp [Matrix.one_apply]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inl l)
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₂₁] at this ⊢
    rw [this]
    simp
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [Matrix.one_apply, hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inr l)
    simp only [Sum.map_inr, Matrix.fromBlocks_apply₂₂] at this ⊢
    rw [this, one_em]

/- English proof (translation)
Use `revert k l`. Proceed by induction on `hβ using AddSubgroup.closure_induction with`. Consider the case `mem β h`. Take `⟨x, hx⟩` from `h`. Establish `hmem : padZ L β ∈ nA σ d.Y d.b` using `AddSubgroup.subset_closure ⟨L.j x, inFrame_j_nb L hx⟩`.

Establish `hc` using `(kunf.mem_nA_iff hε _).1 hmem`. Introduce `k l`. Use `congrFun (congrFun hc (L.em k)) (L.em l)` as an intermediate fact. Simplify `this` using `[padZ, ComplexParameterFamilyContinuity.em_ne, pre_em, Matrix.transpose_apply, smul_eq_mul]`. Consider the case `zero => intro k l`.

Simplify using the standard rewrite rules. Consider the case `add β β' _ _ h h' => intro k l`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, h, h', map_add, mul_add, neg_add]`. Consider the case `neg β _ h => intro k l`. Rewrite using `[Matrix.neg_apply, Matrix.neg_apply, h, map_neg, mul_neg]`.
-/
theorem padCond {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {β : Matrix (Fin L.n) (Fin L.n) (AE F E)} (hβ : β ∈ nA σ L.Y L.b) (k l : Fin L.n) :
    β l k = -(((ε : ℤ) : AE F E) * cA σ (β k l)) := by
  revert k l
  induction hβ using AddSubgroup.closure_induction with
  | mem β h =>
    obtain ⟨x, hx⟩ := h
    have hmem : padZ L β ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨L.j x, inFrame_j_nb L hx⟩
    have hc := (kunf.mem_nA_iff hε _).1 hmem
    intro k l
    have := congrFun (congrFun hc (L.em k)) (L.em l)
    simpa [padZ, ComplexParameterFamilyContinuity.em_ne, pre_em, Matrix.transpose_apply, smul_eq_mul] using this
  | zero => intro k l; simp
  | add β β' _ _ h h' => intro k l; rw [Matrix.add_apply, Matrix.add_apply, h, h', map_add, mul_add, neg_add]
  | neg β _ h => intro k l; rw [Matrix.neg_apply, Matrix.neg_apply, h, map_neg, mul_neg]

/- English proof (translation)
Take `⟨x, A', hx⟩` from `hcf`. Establish `inv : ∀ z, cA σ (cA σ z) = z` using `GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (kunf.sigma_invol d.B hB)`. Establish `h` using `kunf.frame_eq hε x`. Rewrite `h` using `[hx]`. Establish `h1 : (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `h0 : (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 0` using `Matrix.map_zero _ (map_zero _)`. Simplify using `only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero, h1, h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add] at h`. Take `⟨-, h2, -, h4⟩` from `Matrix.fromBlocks_inj.1 h`. Establish `hA : A' = 1`. Use extensionality with `i j`.

Use `congrFun (congrFun h2 i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Rewrite using `[← inv (A' i j), this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite `h4` using `[hA, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`.

Establish `he` using `congrFun (congrFun h4 L.i₀) L.i₀`. Simplify using `[aB, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR] at he`. Establish `e2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1` using `eps_sq ε`. Establish `h5 : ((ε : ℤ) : E) * σ δ + δ = 0`. Apply `kfour.inclR_injective (F := F)` to reduce the goal to its premises.

Rewrite using `[map_add, map_mul, map_intCast, he, map_zero]`. Use `push_cast`. Take the linear combination `((ε : ℤ) : E) * h5 - σ δ * e2`.
-/
theorem sig_delta (hB : d.B.IsGood σ) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks 1 (aB L δ 1) 0 A') :
    σ δ = ((-(ε : ℤ) : ℤ) : E) * δ := by
  obtain ⟨x, A', hx⟩ := hcf
  have inv : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (kunf.sigma_invol d.B hB)
  have h := kunf.frame_eq hε x
  rw [hx] at h
  have h1 : (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, h1, h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add] at h
  obtain ⟨-, h2, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  have hA : A' = 1 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    rw [← inv (A' i j), this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hA, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h4
  have he := congrFun (congrFun h4 L.i₀) L.i₀
  simp [aB, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR] at he
  have e2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := eps_sq ε
  have h5 : ((ε : ℤ) : E) * σ δ + δ = 0 := by
    apply kfour.inclR_injective (F := F)
    rw [map_add, map_mul, map_intCast, he, map_zero]
  push_cast
  linear_combination ((ε : ℤ) : E) * h5 - σ δ * e2

def ins (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then (if hc : c = L.i₀ then x.1.2 • inclR (F := F) (AF F) δ else x.1.1 (pre L c hc))
  else (if hc : c = L.i₀ then -(e * cA σ (x.1.1 (pre L r hr))) else x.2 (pre L r hr) (pre L c hc))

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap`.
-/
theorem continuous_cA' : Continuous (cA σ : AE F E → AE F E) :=
  IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap

/- English proof (translation)
Use `continuous_pi fun r => continuous_pi fun c => ?_` and prove the remaining obligations. Unfold `ins`. Establish `hcA` using `continuous_cA' (σ := σ)`. Apply the tactic sequence `by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;> simp only [hr, hc, dite_true, dite_false] <;> fun_prop`.
-/
theorem continuous_ins (e : AE F E) (δ : E) : Continuous (ins L e δ) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  unfold ins
  have hcA := continuous_cA' (σ := σ)
  by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;> simp only [hr, hc, dite_true, dite_false] <;> fun_prop

/- English proof (translation)
Rewrite using `[kunf.mem_nA_iff hε]`. Establish `e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1` using `eps_sq ε`. Establish `cε : cA σ (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E)` using `map_intCast _ _`. Establish `inv : ∀ z, cA σ (cA σ z) = z` using `GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (kunf.sigma_invol d.B hB)`. Use extensionality with `r c`.

Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Apply the tactic sequence `rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc`. Simplify using `only [ins, dite_true]`. Rewrite using `[map_smul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, hδ, map_mul, map_intCast, Algebra.smul_def, Algebra.smul_def]`. Use `push_cast`.

Take the linear combination `(-(algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) δ)) * e2`. Simplify using `[ins, hc]`. Simplify using `only [ins, hr, dite_true, dite_false]`. Rewrite using `[map_neg, map_mul, cε, inv]`. Take the linear combination `(-(b (pre L r hr))) * e2`.

Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc`. Simplify using `only [ins, hr, hc, dite_false, pre_em]`. Conclude with `padCond L hε hβ k l`.
-/
theorem ins_mem (hB : d.B.IsGood σ) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (b : Fin L.n → AE F E) (a : AF F) {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hβ : β ∈ nA σ L.Y L.b) : ins L (((ε : ℤ) : AE F E)) δ ((b, a), β) ∈ nA σ d.Y d.b := by
  rw [kunf.mem_nA_iff hε]
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have cε : cA σ (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have inv : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (kunf.sigma_invol d.B hB)
  ext r c
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc
  · simp only [ins, dite_true]
    rw [map_smul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, hδ, map_mul, map_intCast, Algebra.smul_def, Algebra.smul_def]
    push_cast
    linear_combination (-(algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) δ)) * e2
  · simp [ins, hc]
  · simp only [ins, hr, dite_true, dite_false]
    rw [map_neg, map_mul, cε, inv]
    linear_combination (-(b (pre L r hr))) * e2
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    simp only [ins, hr, hc, dite_false, pre_em]
    exact padCond L hε hβ k l

/- English proof (translation)
Establish `hc` using `(kunf.mem_nA_iff hε β.1).1 β.2`. Establish `e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1` using `eps_sq ε`. Establish `hk : (-(ε : ℤ)) * (-(ε : ℤ)) = 1` using `by rw [neg_mul_neg]; exact eps_sq ε`. Use extensionality with `r c`. Apply the tactic sequence `rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc'`.

Simplify using `only [ins, dite_true]`. Establish `h0` using `congrFun (congrFun hc L.i₀) L.i₀`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0`. Use `(eig_AE d.ok.good hk hδ0 hδ ?_).symm` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `((ε : ℤ) : AE F E) * h0 - cA σ (β.1 L.i₀ L.i₀) * e2`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc'`. Simplify using `[ins, ComplexParameterFamilyContinuity.em_ne, pre_em]`. Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Establish `h0` using `congrFun (congrFun hc L.i₀) (L.em k)`.

Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0`. Simplify using `only [ins, hr, dite_true, dite_false, pre_em]`. Conclude with `h0.symm`. Take `⟨k, rfl⟩` from `(L.rng r).1 hr`. Take `⟨l, rfl⟩` from `(L.rng c).1 hc'`.

Simplify using `only [ins, hr, hc', dite_false, pre_em, C4.prj_val, Matrix.submatrix_apply]`.
-/
theorem ins_left (hB : d.B.IsGood σ) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (β : nA σ d.Y d.b) :
    ins L (((ε : ℤ) : AE F E)) δ (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), (C4.prj L β).1) =
      β.1 := by
  have hc := (kunf.mem_nA_iff hε β.1).1 β.2
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have hk : (-(ε : ℤ)) * (-(ε : ℤ)) = 1 := by rw [neg_mul_neg]; exact eps_sq ε
  ext r c
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc'
  · simp only [ins, dite_true]
    have h0 := congrFun (congrFun hc L.i₀) L.i₀
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    refine (eig_AE d.ok.good hk hδ0 hδ ?_).symm
    push_cast
    linear_combination ((ε : ℤ) : AE F E) * h0 - cA σ (β.1 L.i₀ L.i₀) * e2
  · obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp [ins, ComplexParameterFamilyContinuity.em_ne, pre_em]
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    have h0 := congrFun (congrFun hc L.i₀) (L.em k)
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    simp only [ins, hr, dite_true, dite_false, pre_em]
    exact h0.symm
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp only [ins, hr, hc', dite_false, pre_em, C4.prj_val, Matrix.submatrix_apply]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[ins, ComplexParameterFamilyContinuity.em_ne, pre_em]`.
-/
theorem ins_pb (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (fun j => ins L e δ x L.i₀ (L.em j)) = x.1.1 := by
  funext j
  simp [ins, ComplexParameterFamilyContinuity.em_ne, pre_em]

/- English proof (translation)
Simplify using `only [ins, dite_true]`. Conclude with `ellA_smul_inclR hδ0 _`.
-/
theorem ins_pa {δ : E} (hδ0 : δ ≠ 0) (e : AE F E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    linearFormAdelic (F := F) δ (ins L e δ x L.i₀ L.i₀) = x.1.2 := by
  simp only [ins, dite_true]
  exact ellA_smul_inclR hδ0 _

/- English proof (translation)
Use extensionality with `k l`. Simplify using `[ins, ComplexParameterFamilyContinuity.em_ne, pre_em]`.
-/
theorem ins_sub (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (ins L e δ x).submatrix L.em L.em = x.2 := by
  ext k l
  simp [ins, ComplexParameterFamilyContinuity.em_ne, pre_em]

/- English proof (translation)
Rewrite using `[inclR_eq', inclR_eq', TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]`.
-/
theorem inclR_smul' (f : F) (e : E) :
    inclR (F := F) (AF F) (f • e) = algebraMap F (AF F) f • inclR (F := F) (AF F) e := by
  rw [inclR_eq', inclR_eq', TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `hB` using `d.ok.good`. Take `⟨ε, hε⟩` from `d.ok.frame.1`. Establish `hδ` using `sig_delta L hB hε hcf`. Set `fwd : nA σ d.Y d.b → ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b` to `fun β => (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), C4.prj L β)`. Set `bwd : ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b → nA σ d.Y d.b` to `fun x => ⟨ins L (((ε : ℤ) : AE F E)) δ (x.1, x.2.1), ins_mem L hB hε hδ x.1.1 x.1.2 x.2.2⟩`.

Establish `hleft : ∀ β, bwd (fwd β) = β` using `fun β => Subtype.ext (ins_left L hB hε hδ0 hδ β)`. Establish `hright : ∀ x, fwd (bwd x) = x`. Introduce and unpack `⟨⟨b, a⟩, β''⟩`. Use `Prod.ext (Prod.ext (ins_pb L _ δ _) (ins_pa L hδ0 _ _)) (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[C4.prj_val]`.

Conclude with `ins_sub L _ δ _`. Set `P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)` to `{ toFun := fwd invFun := bwd left_inv := hleft right_inv := hright map_add' := fun β β' => by`. Use `Prod.ext (Prod.ext ?_ ?_) (map_add (C4.prj L) β β')` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Both sides reduce to the same expression.

Use `show linearFormAdelic (F := F) δ ((β + β').1 L.i₀ L.i₀) = linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) + linearFormAdelic (F := F) δ (β'.1 L.i₀ L.i₀)`. Rewrite using `[← map_add]`. Both sides reduce to the same expression. Use `continuous_toFun := by`. Use `Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_` and prove the remaining obligations.

Conclude with `continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)`. Conclude with `(continuous_ellA δ).comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val))`. Conclude with `continuous_induced_rng.2 (continuous_subtype_val.matrix_submatrix _ _)`. Use `continuous_invFun := by`. Use `Continuous.subtype_mk ((continuous_ins L _ δ).comp ?_) _` and prove the remaining obligations.

Conclude with `continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) }`. Use `⟨P, fun β => rfl, fun β => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hβ`. Take `⟨T, hT⟩` from `kunf.mem_nF_iff.1 hβ`.

Use `⟨⟨ComplexParameterFamilyContinuity.mem_ratVec.2 ⟨fun j => T L.i₀ (L.em j), ?_⟩, ?_⟩, kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[hT]`. Both sides reduce to the same expression. Take `⟨f, hf⟩` from `ellA_inclR (F := F) δ (T L.i₀ L.i₀)`.

Use `⟨f, ?_⟩` and prove the remaining obligations. Rewrite using `[hT]`. Conclude with `hf.symm`. Rewrite using `[C4.prj_val, hT]`. Both sides reduce to the same expression.

Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Take `⟨v, hv⟩` from `ComplexParameterFamilyContinuity.mem_ratVec.1 h1`. Take `⟨f, hf⟩` from `h2`. Take `⟨T'', hT''⟩` from `kunf.mem_nF_iff.1 h3`. Establish `hv' : ∀ j, β.1 L.i₀ (L.em j) = inclR (F` using `F) (AF F) (v j) := fun j => (congrFun hv j).symm`.

Establish `hT2 : ∀ k l, (C4.prj L β).1 k l = inclR (F` using `F) (AF F) (T'' k l) := fun k l => by rw [hT'']; rfl`. Use `kunf.mem_nF_iff.2 ⟨Matrix.of fun r c => if hr : r = L.i₀ then (if hc : c = L.i₀ then f • δ else v (pre L c hc)) else (if hc : c = L.i₀ then -(((ε : ℤ) : E) * σ (v (pre L r hr))) else T'' (pre L r hr) (pre L c hc)), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← ins_left L hB hε hδ0 hδ β]`. Use extensionality with `r c`. Apply the tactic sequence `by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;>`.

Simplify using `only [ins, incM, Matrix.map_apply, Matrix.of_apply, hr, hc, dite_true, dite_false]`. Rewrite using `[inclR_smul', ← hf]`. Conclude with `hv' _`. Rewrite using `[hv', map_neg, map_mul, map_intCast, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]`. Conclude with `hT2 _ _`.
-/
theorem pEquiv0 {δ : E} (hδ0 : δ ≠ 0)
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks 1 (aB L δ 1) 0 A') :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), C4.prj L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (((fun j => β.1 L.i₀ (L.em j)) ∈ L.ratV ∧
        linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) ∈ (algebraMap F (AF F)).range.toAddSubgroup) ∧ C4.prj L β ∈ nF σ L.Y L.b) := by
  have hB := d.ok.good
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hδ := sig_delta L hB hε hcf
  let fwd : nA σ d.Y d.b → ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b :=
    fun β => (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), C4.prj L β)
  let bwd : ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b → nA σ d.Y d.b :=
    fun x => ⟨ins L (((ε : ℤ) : AE F E)) δ (x.1, x.2.1), ins_mem L hB hε hδ x.1.1 x.1.2 x.2.2⟩
  have hleft : ∀ β, bwd (fwd β) = β := fun β => Subtype.ext (ins_left L hB hε hδ0 hδ β)
  have hright : ∀ x, fwd (bwd x) = x := by
    rintro ⟨⟨b, a⟩, β''⟩
    refine Prod.ext (Prod.ext (ins_pb L _ δ _) (ins_pa L hδ0 _ _)) (Subtype.ext ?_)
    rw [C4.prj_val]
    exact ins_sub L _ δ _
  let P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_add' := fun β β' => by
        refine Prod.ext (Prod.ext ?_ ?_) (map_add (C4.prj L) β β')
        · funext j
          rfl
        · show linearFormAdelic (F := F) δ ((β + β').1 L.i₀ L.i₀) = linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) + linearFormAdelic (F := F) δ (β'.1 L.i₀ L.i₀)
          rw [← map_add]
          rfl
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_
        · exact continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
        · exact (continuous_ellA δ).comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val))
        · exact continuous_induced_rng.2 (continuous_subtype_val.matrix_submatrix _ _)
      continuous_invFun := by
        refine Continuous.subtype_mk ((continuous_ins L _ δ).comp ?_) _
        exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) }
  refine ⟨P, fun β => rfl, fun β => ?_⟩
  constructor
  · intro hβ
    obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
    refine ⟨⟨ComplexParameterFamilyContinuity.mem_ratVec.2 ⟨fun j => T L.i₀ (L.em j), ?_⟩, ?_⟩, kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩⟩
    · funext j
      rw [hT]
      rfl
    · obtain ⟨f, hf⟩ := ellA_inclR (F := F) δ (T L.i₀ L.i₀)
      refine ⟨f, ?_⟩
      rw [hT]
      exact hf.symm
    · rw [C4.prj_val, hT]
      rfl
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨v, hv⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 h1
    obtain ⟨f, hf⟩ := h2
    obtain ⟨T'', hT''⟩ := kunf.mem_nF_iff.1 h3
    have hv' : ∀ j, β.1 L.i₀ (L.em j) = inclR (F := F) (AF F) (v j) := fun j => (congrFun hv j).symm
    have hT2 : ∀ k l, (C4.prj L β).1 k l = inclR (F := F) (AF F) (T'' k l) := fun k l => by rw [hT'']; rfl
    refine kunf.mem_nF_iff.2 ⟨Matrix.of fun r c => if hr : r = L.i₀ then (if hc : c = L.i₀ then f • δ else v (pre L c hc))
      else (if hc : c = L.i₀ then -(((ε : ℤ) : E) * σ (v (pre L r hr))) else T'' (pre L r hr) (pre L c hc)), ?_⟩
    conv_lhs => rw [← ins_left L hB hε hδ0 hδ β]
    ext r c
    by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;>
      simp only [ins, incM, Matrix.map_apply, Matrix.of_apply, hr, hc, dite_true, dite_false]
    · rw [inclR_smul', ← hf]
    · exact hv' _
    · rw [hv', map_neg, map_mul, map_intCast, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]
    · exact hT2 _ _

end PositivityTheory.SiegelWeilFormula.Act.C5.Meas

end
