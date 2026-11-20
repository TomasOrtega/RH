import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames

section gen

variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}

/- English proof (translation)
Introduce `a b c d`. Use extensionality with `x`. Establish `hx` using `G.comm a b c d x`. Apply the tactic sequence `split_ifs at hx ⊢ <;> simpa using hx`.
-/
theorem glRel_ofT (G : GlW K V n) : GlRel G.E := by
  intro a b c d
  ext x
  have hx := G.comm a b c d x
  split_ifs at hx ⊢ <;> simpa using hx

def pr0 (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) : Module.End K (U →ₗ[K] V) :=
  ∑ ν ∈ S, postC (G₂.comp ν) * preC (G₁.comp ν)

/- English proof (translation)
Simplify using `[pr0, postC_apply, preC_apply]`.
-/
theorem scalar_projection_apply (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (φ : U →ₗ[K] V) (x : U) :
    pr0 G₁ G₂ S φ x = ∑ ν ∈ S, G₂.comp ν (φ (G₁.comp ν x)) := by
  simp [pr0, postC_apply, preC_apply]

/- English proof (translation)
Use extensionality with `x`. Establish `hd : dl c c = 0` using `sub_self _`. Express the relevant statement in the definitionally equal form `G₂.E c c (pr0 G₁ G₂ S φ x) - pr0 G₁ G₂ S φ (G₁.E c c x) = 0`. Rewrite using `[scalar_projection_apply, scalar_projection_apply, map_sum, sub_eq_zero]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations.

Rewrite using `[G₂.diag, G₁.shift, hd, sub_zero, G₁.diag, map_smul, map_smul]`.
-/
theorem weightZeroProj_weight (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (φ : U →ₗ[K] V) (c : Fin n) :
    homAct G₁.E G₂.E c c (pr0 G₁ G₂ S φ) = 0 := by
  ext x
  have hd : dl c c = 0 := sub_self _
  change G₂.E c c (pr0 G₁ G₂ S φ x) - pr0 G₁ G₂ S φ (G₁.E c c x) = 0
  rw [scalar_projection_apply, scalar_projection_apply, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [G₂.diag, G₁.shift, hd, sub_zero, G₁.diag, map_smul, map_smul]

/- English proof (translation)
Rewrite using `[scalar_projection_apply]`. Conclude with `Submodule.sum_mem _ fun ν _ => hW ν _ (hφ _)`.
-/
theorem weightZeroProj_mem (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {W : Submodule K V} (hW : G₂.Graded W)
    {φ : U →ₗ[K] V} (hφ : ∀ x, φ x ∈ W) (x : U) : pr0 G₁ G₂ S φ x ∈ W := by
  rw [scalar_projection_apply]
  exact Submodule.sum_mem _ fun ν _ => hW ν _ (hφ _)

/- English proof (translation)
Establish `hφ' : ∀ x ∈ L, φ x ∈ M` using `hφ`. Use `show ∀ x ∈ L, pr0 G₁ G₂ S φ x ∈ M`. Introduce `x hx`. Rewrite using `[scalar_projection_apply]`. Conclude with `AddSubgroup.sum_mem _ fun ν _ => hM ν _ (hφ' _ (hL ν x hx))`.
-/
theorem weightZeroProj_mem_homLat (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {L : AddSubgroup U} {M : AddSubgroup V}
    (hL : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L) (hM : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M)
    {φ : U →ₗ[K] V} (hφ : φ ∈ HomLat (K := K) L M) : pr0 G₁ G₂ S φ ∈ HomLat (K := K) L M := by
  have hφ' : ∀ x ∈ L, φ x ∈ M := hφ
  show ∀ x ∈ L, pr0 G₁ G₂ S φ x ∈ M
  intro x hx
  rw [scalar_projection_apply]
  exact AddSubgroup.sum_mem _ fun ν _ => hM ν _ (hφ' _ (hL ν x hx))

/- English proof (translation)
Establish `hw : ∀ ν, G₂.comp ν (θ (G₁.comp ν x)) = θ (G₁.comp ν x)` using `fun ν => GlX.isWt_of_eig (G := G₂) (fun c => by rw [← hθ, G₁.diag, map_smul])`. Take `⟨S, hS⟩` from `G₁.dec x`. Establish `hx : ∑ ν ∈ insert μ S, G₁.comp ν x = x` using `G₁.sum_comp x _ (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))`. Use `conv_rhs => rw [← hx]`. Rewrite using `[map_sum, map_sum, Finset.sum_eq_single μ]`.

Conclude with `(hw μ).symm`. Introduce `ν _ hne`. Rewrite using `[← hw ν, G₂.idem, if_neg (Ne.symm hne)]`. Introduce `h`. Conclude with `absurd (Finset.mem_insert_self μ S) h`.
-/
theorem comp_comm2 (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  have hw : ∀ ν, G₂.comp ν (θ (G₁.comp ν x)) = θ (G₁.comp ν x) := fun ν =>
    GlX.isWt_of_eig (G := G₂) (fun c => by rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx : ∑ ν ∈ insert μ S, G₁.comp ν x = x :=
    G₁.sum_comp x _ (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx]
  rw [map_sum, map_sum, Finset.sum_eq_single μ]
  · exact (hw μ).symm
  · intro ν _ hne
    rw [← hw ν, G₂.idem, if_neg (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_insert_self μ S) h

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, scalar_projection_apply, map_sum, hθ]`.
-/
theorem weightZeroProj_comp (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (θ : U →ₗ[K] V)
    (hθ : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x)) (φ : U →ₗ[K] U) :
    pr0 G₁ G₂ S (θ ∘ₗ φ) = θ ∘ₗ pr0 G₁ G₁ S φ := by
  ext x
  simp only [LinearMap.comp_apply, scalar_projection_apply, map_sum, hθ]

/- English proof (translation)
Establish `hsum : ∑ ν ∈ S, G₁.comp ν = 1`. Use extensionality with `x`. Simplify using `using G₁.sum_comp x S (hS x)`. Establish `hidem : ∀ ν, G₁.comp ν * G₁.comp ν = G₁.comp ν`. Introduce `ν`.

Use extensionality with `x`. Simplify using `[G₁.idem]`. Establish `hp : pr0 G₁ G₁ S φ = ∑ ν ∈ S, G₁.comp ν * (φ * G₁.comp ν)`. Use extensionality with `x`. Simplify using `[scalar_projection_apply]`.

Rewrite using `[hp, map_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.trace_mul_comm, mul_assoc, hidem ν]`. Use `_ = LinearMap.trace K U φ := by`.

Rewrite using `[← map_sum, ← Finset.mul_sum, hsum, mul_one]`.
-/
theorem weightZeroProj_trace (G₁ : GlW K U n) (S : Finset (Fin n → ℤ)) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0) (φ : U →ₗ[K] U) :
    LinearMap.trace K U (pr0 G₁ G₁ S φ) = LinearMap.trace K U φ := by
  classical
  have hsum : ∑ ν ∈ S, G₁.comp ν = 1 := by
    ext x
    simpa using G₁.sum_comp x S (hS x)
  have hidem : ∀ ν, G₁.comp ν * G₁.comp ν = G₁.comp ν := by
    intro ν
    ext x
    simp [G₁.idem]
  have hp : pr0 G₁ G₁ S φ = ∑ ν ∈ S, G₁.comp ν * (φ * G₁.comp ν) := by
    ext x
    simp [scalar_projection_apply]
  rw [hp, map_sum]
  calc ∑ ν ∈ S, LinearMap.trace K U (G₁.comp ν * (φ * G₁.comp ν))
      = ∑ ν ∈ S, LinearMap.trace K U (φ * G₁.comp ν) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [LinearMap.trace_mul_comm, mul_assoc, hidem ν]
    _ = LinearMap.trace K U φ := by
        rw [← map_sum, ← Finset.mul_sum, hsum, mul_one]

def Psi (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) : Module.End K (U →ₗ[K] V) :=
  InvOp (homAct G₁.E G₂.E) l (List.finRange n) * pr0 G₁ G₂ S

noncomputable def QQ (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) : V →ₗ[K] V :=
  (k : K) • ∑ i, LinearMap.applyₗ (b i) ∘ₗ Psi G₁ G₂ S l ∘ₗ LinearMap.smulRightₗ (b.coord i)

/- English proof (translation)
Simplify using `only [QQ, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smulRightₗ_apply, LinearMap.applyₗ_apply_apply]`.
-/
theorem QQ_apply (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) (m : V) :
    QQ G₁ G₂ S l b m = (k : K) • ∑ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) := by
  simp only [QQ, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.smulRightₗ_apply, LinearMap.applyₗ_apply_apply]

/- English proof (translation)
Rewrite using `[QQ_apply]`. Establish `hWg : G₂.Graded W` using `G₂.graded_of hW`. Establish `hz : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) = 0`. Introduce `i`. Establish `hφW : ∀ x, pr0 G₁ G₂ S ((b.coord i).smulRight m) x ∈ W` using `fun x => weightZeroProj_mem G₁ G₂ S hWg (fun y => by rw [LinearMap.smulRight_apply]; exact W.smul_mem _ hm) x`.

Take `⟨h1, h2, -⟩` from `hHom K U V n G₁ G₂ W l hW hb _ hφW (weightZeroProj_weight G₁ G₂ S _)`. Conclude with `h0 _ h1 h2`. Simplify using `[hz]`.
-/
theorem QQ_zero (hHom : HomInv) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) {W : Submodule K V} (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l)
    (h0 : ∀ ψ : U →ₗ[K] V, (∀ a b x, ψ (G₁.E a b x) = G₂.E a b (ψ x)) → (∀ x, ψ x ∈ W) → ψ = 0)
    {m : V} (hm : m ∈ W) : QQ G₁ G₂ S l b m = 0 := by
  rw [QQ_apply]
  have hWg : G₂.Graded W := G₂.graded_of hW
  have hz : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) = 0 := by
    intro i
    have hφW : ∀ x, pr0 G₁ G₂ S ((b.coord i).smulRight m) x ∈ W := fun x =>
      weightZeroProj_mem G₁ G₂ S hWg (fun y => by rw [LinearMap.smulRight_apply]; exact W.smul_mem _ hm) x
    obtain ⟨h1, h2, -⟩ := hHom K U V n G₁ G₂ W l hW hb _ hφW (weightZeroProj_weight G₁ G₂ S _)
    exact h0 _ h1 h2
  simp [hz]

/- English proof (translation)
Establish `hk' : (k : K) ≠ 0` using `Nat.cast_ne_zero.mpr hk`. Establish `hθc : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x)` using `fun μ x => comp_comm2 G₁ G₂ θ (fun c x => hθ c c x) μ x`. Set `θ' : (U →ₗ[K] U) →ₗ[K] (U →ₗ[K] V)` to `{ toFun := fun χ => θ ∘ₗ χ map_add' := fun χ ψ => by ext x; simp map_smul' := fun c χ => by ext x; simp }`. Establish `hθ'a : ∀ χ, θ' χ = θ ∘ₗ χ` using `fun χ => rfl`. Establish `hcomm : ∀ a b χ, θ' (homAct G₁.E G₁.E a b χ) = homAct G₁.E G₂.E a b (θ' χ)` using `fun a b χ => by`.

Rewrite using `[hθ'a, hθ'a]`. Conclude with `homAct_postcomp G₁.E G₁.E G₂.E θ hθ a b χ`. Establish `htr : ∀ i, LinearMap.trace K U ((b.coord i).smulRight y) = b.coord i y`. Introduce `i`. Rewrite using `[LinearMap.trace_eq_matrix_trace K b, Matrix.trace]`.

Simplify using `[LinearMap.toMatrix_apply, Finsupp.single_apply]`. Simplify using `[Matrix.vecMulVec_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Establish `key : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight (θ y)) (b i) = (b.coord i y / (k : K)) • θ (b i)`. Introduce `i`. Establish `h1 : (b.coord i).smulRight (θ y) = θ' ((b.coord i).smulRight y)`.

Use extensionality with `x`. Simplify using `[hθ'a]`. Establish `h2 : Psi G₁ G₂ S l (θ' ((b.coord i).smulRight y)) = θ' (InvOp (homAct G₁.E G₁.E) l (List.finRange n) (pr0 G₁ G₁ S ((b.coord i).smulRight y)))`. Establish `hp : pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y)) = θ' (pr0 G₁ G₁ S ((b.coord i).smulRight y))` using `weightZeroProj_comp G₁ G₂ S θ hθc _`. Use `show InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y))) = _`.

Rewrite using `[hp]`. Conclude with `(hNat K _ _ (Fin n) (homAct G₁.E G₁.E) (homAct G₁.E G₂.E) θ' hcomm l (List.finRange n) _).symm`. Rewrite using `[h1, h2, hSch _ (weightZeroProj_weight G₁ G₁ S _), weightZeroProj_trace G₁ S hS, hθ'a, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, htr]`. Establish `hsc : ∀ i, (k : K) • ((b.coord i y / (k : K)) • θ (b i)) = θ (b.repr y i • b i)`. Introduce `i`.

Establish `hc : (k : K) * (b.coord i y / (k : K)) = b.repr y i`. Rewrite using `[Module.Basis.coord_apply]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[smul_smul, hc, map_smul]`. Rewrite using `[QQ_apply, Finset.smul_sum]`.

Repeatedly rewrite using `[key, hsc]`. Rewrite using `[← map_sum, b.sum_repr]`.
-/
theorem QQ_id (hNat : InvNat) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0)
    (hSch : ∀ φ : U →ₗ[K] U, (∀ c, homAct G₁.E G₁.E c c φ = 0) →
      InvOp (homAct G₁.E G₁.E) l (List.finRange n) φ = (LinearMap.trace K U φ / (k : K)) • LinearMap.id)
    (hk : k ≠ 0) (θ : U →ₗ[K] V) (hθ : ∀ a b x, θ (G₁.E a b x) = G₂.E a b (θ x)) (y : U) :
    QQ G₁ G₂ S l b (θ y) = θ y := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hθc : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x) := fun μ x =>
    comp_comm2 G₁ G₂ θ (fun c x => hθ c c x) μ x
  let θ' : (U →ₗ[K] U) →ₗ[K] (U →ₗ[K] V) :=
    { toFun := fun χ => θ ∘ₗ χ
      map_add' := fun χ ψ => by ext x; simp
      map_smul' := fun c χ => by ext x; simp }
  have hθ'a : ∀ χ, θ' χ = θ ∘ₗ χ := fun χ => rfl
  have hcomm : ∀ a b χ, θ' (homAct G₁.E G₁.E a b χ) = homAct G₁.E G₂.E a b (θ' χ) := fun a b χ => by
    rw [hθ'a, hθ'a]
    exact homAct_postcomp G₁.E G₁.E G₂.E θ hθ a b χ
  have htr : ∀ i, LinearMap.trace K U ((b.coord i).smulRight y) = b.coord i y := by
    intro i
    rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
    simp [LinearMap.toMatrix_apply, Finsupp.single_apply]
    simp [Matrix.vecMulVec_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have key : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight (θ y)) (b i) = (b.coord i y / (k : K)) • θ (b i) := by
    intro i
    have h1 : (b.coord i).smulRight (θ y) = θ' ((b.coord i).smulRight y) := by
      ext x
      simp [hθ'a]
    have h2 : Psi G₁ G₂ S l (θ' ((b.coord i).smulRight y)) =
        θ' (InvOp (homAct G₁.E G₁.E) l (List.finRange n) (pr0 G₁ G₁ S ((b.coord i).smulRight y))) := by
      have hp : pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y)) = θ' (pr0 G₁ G₁ S ((b.coord i).smulRight y)) :=
        weightZeroProj_comp G₁ G₂ S θ hθc _
      show InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y))) = _
      rw [hp]
      exact (hNat K _ _ (Fin n) (homAct G₁.E G₁.E) (homAct G₁.E G₂.E) θ' hcomm l (List.finRange n) _).symm
    rw [h1, h2, hSch _ (weightZeroProj_weight G₁ G₁ S _), weightZeroProj_trace G₁ S hS, hθ'a, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, htr]
  have hsc : ∀ i, (k : K) • ((b.coord i y / (k : K)) • θ (b i)) = θ (b.repr y i • b i) := by
    intro i
    have hc : (k : K) * (b.coord i y / (k : K)) = b.repr y i := by
      rw [Module.Basis.coord_apply]
      field_simp
    rw [smul_smul, hc, map_smul]
  rw [QQ_apply, Finset.smul_sum]
  simp_rw [key, hsc]
  rw [← map_sum, b.sum_repr]

end gen

section iso

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem res_E_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (x : U) :
    (((res G U hU).E a b x : U) : V) = G.E a b (x : V) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem res_comp_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (μ : Fin n → ℤ) (x : U) :
    (((res G U hU).comp μ x : U) : V) = G.comp μ (x : V) := rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[pow_succ', pow_succ']`. Use `show (((res G U hU).E a b (((res G U hU).E a b ^ k) x) : U) : V) = G.E a b ((G.E a b ^ k) (x : V))`.

Rewrite using `[res_E_coe, ih]`.
-/
theorem res_pow_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (k : ℕ) (x : U) :
    ((((res G U hU).E a b ^ k) x : U) : V) = (G.E a b ^ k) (x : V) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    show (((res G U hU).E a b (((res G U hU).E a b ^ k) x) : U) : V) = G.E a b ((G.E a b ^ k) (x : V))
    rw [res_E_coe, ih]

/- English proof (translation)
The claim follows from `G.gS_le (fun v hv => (show G.IsHW la v ∧ v ∈ W from hv).2) hW`.
-/
theorem IsoW_le (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (la : Fin n → ℤ) : IsoW G W la ≤ W := G.gS_le (fun v hv => (show G.IsHW la v ∧ v ∈ W from hv).2) hW

/- English proof (translation)
Use `G.gS_le (fun v hv => ?_) ?_` and prove the remaining obligations. Conclude with `(le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) ⟨v, hv⟩) (G.subset_gS _ (Set.mem_singleton v))`. Introduce `a b x hx`. Establish `hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}).comap (G.E a b)` using `iSup_le fun i y hy => (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) i) (G.gS_stable _ a b y hy)`. Conclude with `hle hx`.
-/
theorem IsoW_le_iSup (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} := by
  refine G.gS_le (fun v hv => ?_) ?_
  · exact (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) ⟨v, hv⟩)
      (G.subset_gS _ (Set.mem_singleton v))
  · intro a b x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}).comap (G.E a b) :=
      iSup_le fun i y hy =>
        (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) i) (G.gS_stable _ a b y hy)
    exact hle hx

/- English proof (translation)
Assume the negation of the conclusion as `hx0`. Establish `hxw : G.comp la x = x ∧ ∀ a b, a < b → G.E a b x = 0` using `hx`. Establish `hbot : G.Stable (⊥ : Submodule K V)`. Introduce `a b y hy`. Rewrite `hy`, the goal using `[Submodule.mem_bot]`.

Rewrite using `[hy, map_zero]`. Establish `hr : ∀ a b, a < b → G.E a b x ∈ (⊥ : Submodule K V)` using `fun a b hab => by`. Rewrite using `[hxw.2 a b hab]`. Conclude with `Submodule.zero_mem _`. Establish `hxW : x ∈ W` using `IsoW_le G hW mu hxI`.

Establish `hdom : DomW la` using `G.dom_of_hwmod hbot hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1 hr`. Take `⟨S, hS⟩` from `hWf`. Establish `hkill : ∀ y ∈ IsoW G W mu, G.cprod (GlX.qlist S (GlW.casI la)) (G.comp la y) = 0`. Introduce `y hy`. Establish `hle : (⨆ v : {v : V // G.IsHW mu v ∧ v ∈ W}, G.gS {(v : V)}) ≤ LinearMap.ker ((G.cprod (GlX.qlist S (GlW.casI la))) ∘ₗ G.comp la)`.

Use `iSup_le fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv0 : (v : V) = 0`. Introduce `z hz`. Establish `hz0 : z ∈ (⊥ : Submodule K V)` using `G.gS_le (by`. Introduce `w hw`.

Rewrite `hw` using `[Set.mem_singleton_iff]`. Rewrite using `[hw, hv0]`. Conclude with `Submodule.zero_mem _) hbot hz`. Rewrite `hz0` using `[Submodule.mem_bot]`. Rewrite using `[hz0]`.

Conclude with `Submodule.zero_mem _`. Introduce `z hz`. Conclude with `LinearMap.mem_ker.mpr (GlX.gen_kill (G := G) hW hS v.2.1 v.2.2 hv0 hdom ⟨fun _ => le_refl _, rfl⟩ (fun _ => hne) z hz)`. Conclude with `LinearMap.mem_ker.mp (hle (IsoW_le_iSup G W mu hy))`. Establish `h1` using `hkill x hxI`.

Rewrite `h1` using `[hxw.1]`. Establish `h2` using `GlX.cprod_mod (G := G) (μ := la) hbot hxw.1 hr (GlX.qlist S (GlW.casI la))`. Rewrite `h2` using `[h1, zero_sub, neg_mem_iff, Submodule.mem_bot]`. Establish `hprod : ((GlX.qlist S (GlW.casI la)).map (fun c => ((GlW.casI la - c : ℤ) : K))).prod ≠ 0`. Use `List.prod_ne_zero ?_` and prove the remaining obligations.

Introduce `hmem`. Take `⟨c, hc, hc0⟩` from `List.mem_map.mp hmem`. Establish `hc1 : GlW.casI la - c = 0` using `by exact_mod_cast hc0`. Establish `hc2 : c ∈ (S.image GlW.casI).erase (GlW.casI la)` using `Finset.mem_toList.mp hc`. Conclude with `(Finset.mem_erase.mp hc2).1 (by omega)`.

Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `hprod h`. Conclude with `hx0 h`.
-/
theorem hw_IsoW_zero (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la mu : Fin n → ℤ}
    (hne : mu ≠ la) {x : V} (hx : G.IsHW la x) (hxI : x ∈ IsoW G W mu) : x = 0 := by
  by_contra hx0
  have hxw : G.comp la x = x ∧ ∀ a b, a < b → G.E a b x = 0 := hx
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  have hr : ∀ a b, a < b → G.E a b x ∈ (⊥ : Submodule K V) := fun a b hab => by
    rw [hxw.2 a b hab]
    exact Submodule.zero_mem _
  have hxW : x ∈ W := IsoW_le G hW mu hxI
  have hdom : DomW la := G.dom_of_hwmod hbot hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1 hr
  obtain ⟨S, hS⟩ := hWf
  have hkill : ∀ y ∈ IsoW G W mu, G.cprod (GlX.qlist S (GlW.casI la)) (G.comp la y) = 0 := by
    intro y hy
    have hle : (⨆ v : {v : V // G.IsHW mu v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        LinearMap.ker ((G.cprod (GlX.qlist S (GlW.casI la))) ∘ₗ G.comp la) := by
      refine iSup_le fun v => ?_
      by_cases hv0 : (v : V) = 0
      · intro z hz
        have hz0 : z ∈ (⊥ : Submodule K V) := G.gS_le (by
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw, hv0]
          exact Submodule.zero_mem _) hbot hz
        rw [Submodule.mem_bot] at hz0
        rw [hz0]
        exact Submodule.zero_mem _
      · intro z hz
        exact LinearMap.mem_ker.mpr (GlX.gen_kill (G := G) hW hS v.2.1 v.2.2 hv0 hdom
          ⟨fun _ => le_refl _, rfl⟩ (fun _ => hne) z hz)
    exact LinearMap.mem_ker.mp (hle (IsoW_le_iSup G W mu hy))
  have h1 := hkill x hxI
  rw [hxw.1] at h1
  have h2 := GlX.cprod_mod (G := G) (μ := la) hbot hxw.1 hr (GlX.qlist S (GlW.casI la))
  rw [h1, zero_sub, neg_mem_iff, Submodule.mem_bot] at h2
  have hprod : ((GlX.qlist S (GlW.casI la)).map (fun c => ((GlW.casI la - c : ℤ) : K))).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro hmem
    obtain ⟨c, hc, hc0⟩ := List.mem_map.mp hmem
    have hc1 : GlW.casI la - c = 0 := by exact_mod_cast hc0
    have hc2 : c ∈ (S.image GlW.casI).erase (GlW.casI la) := Finset.mem_toList.mp hc
    exact (Finset.mem_erase.mp hc2).1 (by omega)
  rcases smul_eq_zero.mp h2 with h | h
  · exact hprod h
  · exact hx0 h

/- English proof (translation)
Establish `key : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker ψ)`. Use `G.gS_le ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv` using `[Set.mem_singleton_iff]`. Rewrite using `[hv]`.

Conclude with `Submodule.mem_map.mpr ⟨⟨h, G.subset_gS _ (Set.mem_singleton h)⟩, LinearMap.mem_ker.mpr h0, rfl⟩`. Introduce `a b y hy`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hy`. Use `Submodule.mem_map.mpr ⟨(res G _ (G.gS_stable {h})).E a b z, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, hψ, LinearMap.mem_ker.mp hz, map_zero]`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨z, hz, hzx⟩` from `Submodule.mem_map.mp (key x.2)`. Establish `hzx' : z = x` using `Subtype.ext hzx`. Rewrite using `[← hzx', LinearMap.zero_apply]`. Conclude with `LinearMap.mem_ker.mp hz`.
-/
theorem equiv_zero (G : GlW K V n) (h : V) (ψ : G.gS {h} →ₗ[K] V)
    (hψ : ∀ a b x, ψ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (ψ x))
    (h0 : ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0) : ψ = 0 := by
  have key : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker ψ) := by
    refine G.gS_le ?_ ?_
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Submodule.mem_map.mpr ⟨⟨h, G.subset_gS _ (Set.mem_singleton h)⟩, LinearMap.mem_ker.mpr h0, rfl⟩
    · intro a b y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      refine Submodule.mem_map.mpr ⟨(res G _ (G.gS_stable {h})).E a b z, ?_, rfl⟩
      rw [LinearMap.mem_ker, hψ, LinearMap.mem_ker.mp hz, map_zero]
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (key x.2)
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx', LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp hz

/- English proof (translation)
Establish `hbot : G.Stable (⊥ : Submodule K V)`. Introduce `a b y hy`. Rewrite `hy`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hy, map_zero]`. Distinguish the cases in `h0' : h' = 0`.

Use `⟨0, fun a b x => by simp, fun m hm => ⟨0, ?_⟩⟩` and prove the remaining obligations. Establish `hm0 : m ∈ (⊥ : Submodule K V)` using `G.gS_le (by`. Introduce `w hw`. Rewrite `hw` using `[Set.mem_singleton_iff]`. Rewrite using `[hw, h0']`.

Conclude with `Submodule.zero_mem _) hbot hm`. Rewrite `hm0` using `[Submodule.mem_bot]`. Rewrite using `[hm0, map_zero]`. Establish `hUW : G.gS {h} ≤ W` using `G.gS_le (Set.singleton_subset_iff.mpr hhW) hW`. Establish `hU'W : G.gS {h'} ≤ W` using `G.gS_le (Set.singleton_subset_iff.mpr hh'W) hW`.

Take `⟨S, hS⟩` from `hWf`. Distinguish the cases in `hdis : G.gS {h} ⊓ G.gS {h'} = ⊥`. Establish `hind : iSupIndep (fun i : Bool => if i then G.gS {h'} else G.gS {h})`. Apply the tactic sequence `rw [iSupIndep_pair (i := true) (j := false) (by decide) (fun k => by cases k <;> simp), disjoint_iff]`. Use `show G.gS {h'} ⊓ G.gS {h} = ⊥`.

Rewrite using `[inf_comm]`. Conclude with `hdis`. Establish `hRW : ∀ i : Bool, (if i then G.gS {h'} else G.gS {h}) ≤ G.gS {h} ⊔ G.gS {h'}`. Introduce `i`. Apply the tactic sequence `cases i <;> simp`.

Establish `hWR : G.gS {h} ⊔ G.gS {h'} ≤ ⨆ i : Bool, (if i then G.gS {h'} else G.gS {h})` using `sup_le (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) false) (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) true)`. Take `⟨π, hπ1, hπ2, hπ3⟩` from `proj_exists (W := G.gS {h} ⊔ G.gS {h'}) (fun i : Bool => if i then G.gS {h'} else G.gS {h}) hind hRW hWR`. Establish `hEq : ∀ i, ∀ x ∈ G.gS {h} ⊔ G.gS {h'}, ∀ c d, π i (G.E c d x) = G.E c d (π i x)`. Introduce `i x hx c d`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`.

Establish `hy' : G.E c d y ∈ G.gS {h}` using `G.gS_stable _ c d y hy`. Establish `hz' : G.E c d z ∈ G.gS {h'}` using `G.gS_stable _ c d z hz`. Simplify using `only [map_add]`. Consider the cases of `i`. Rewrite using `[hπ2 false _ hy', hπ2 false _ hy, hπ3 false true (by decide) _ hz', hπ3 false true (by decide) _ hz, map_zero]`.

Rewrite using `[hπ3 true false (by decide) _ hy', hπ3 true false (by decide) _ hy, hπ2 true _ hz', hπ2 true _ hz, map_zero]`. Establish `hW' : G.Stable (G.gS {h} ⊔ G.gS {h'})`. Introduce `a b x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (G.gS_stable _ a b y hy)) (Submodule.mem_sup_right (G.gS_stable _ a b z hz))`. Establish `hWf' : G.FinW (G.gS {h} ⊔ G.gS {h'})` using `⟨S, fun x hx => hS x (sup_le hUW hU'W hx)⟩`. Take `⟨θ₁, θ₁', hθ1, -, -, hθE', hinv⟩` from `GlX.exists_theta G (W := G.gS {h} ⊔ G.gS {h'}) hW' hWf' (h := h') (h' := h) hh' hh (Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton h'))) (Submodule.mem_sup_left (G.subset_gS _ (Set.mem_singleton h))) h0' h0 (π true) (π false) (hπ1 true) (hπ2 true) (hEq true) (hπ1 false …`. Use `⟨θ₁' ∘ₗ (G.gS {h}).subtype, fun a b x => ?_, fun m hm => ⟨⟨θ₁ m, hθ1 m⟩, hinv m hm⟩⟩` and prove the remaining obligations. Use `show θ₁' (G.E a b (x : V)) = G.E a b (θ₁' (x : V))`.

Conclude with `hθE' _ (Submodule.mem_sup_left x.2) a b`. Establish `hI : G.Stable (G.gS {h} ⊓ G.gS {h'})`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[Submodule.mem_inf]`. Conclude with `⟨G.gS_stable _ a b x hx.1, G.gS_stable _ a b x hx.2⟩`.

Take `⟨v, hvI, hv0, μ, hvw, hvr⟩` from `G.exists_hwmod (U := ⊥) (G.graded_of hI) (fun a b _ x hx => hI a b x hx) ⟨S, fun x hx => hS x (hUW (Submodule.mem_inf.mp hx).1)⟩ (fun hle => hdis (le_bot_iff.mp hle))`. Establish `hvHW : G.comp μ v = v ∧ ∀ a b, a < b → G.E a b v = 0` using `⟨hvw, fun a b hab => by`. Establish `hq` using `hvr a b hab`. Rewrite using `[Submodule.mem_bot] at hq⟩` and apply the resulting hypothesis. Establish `hv0' : v ≠ 0` using `fun hq => hv0 (by rw [hq]; exact Submodule.zero_mem _)`.

Take `⟨-, c', hc'⟩` from `G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W (Submodule.mem_inf.mp hvI).2 hvHW hv0'`. Establish `hc'0 : c' ≠ 0`. Introduce and unpack `rfl`. Apply `hv0'` to reduce the goal to its premises. Rewrite using `[hc', zero_smul]`.

Establish `hmem : h' ∈ G.gS {h}`. Establish `hq : h' = c'⁻¹ • v` using `by rw [hc', smul_smul, inv_mul_cancel₀ hc'0, one_smul]`. Rewrite using `[hq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_inf.mp hvI).1`. Establish `hle : G.gS {h'} ≤ G.gS {h}` using `G.gS_le (Set.singleton_subset_iff.mpr hmem) (G.gS_stable _)`.

Conclude with `⟨(G.gS {h}).subtype, fun a b x => rfl, fun m hm => ⟨⟨m, hle hm⟩, rfl⟩⟩`.
-/
theorem exists_transport (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  by_cases h0' : h' = 0
  · refine ⟨0, fun a b x => by simp, fun m hm => ⟨0, ?_⟩⟩
    have hm0 : m ∈ (⊥ : Submodule K V) := G.gS_le (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw, h0']
      exact Submodule.zero_mem _) hbot hm
    rw [Submodule.mem_bot] at hm0
    rw [hm0, map_zero]
  have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hW
  have hU'W : G.gS {h'} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  by_cases hdis : G.gS {h} ⊓ G.gS {h'} = ⊥
  · have hind : iSupIndep (fun i : Bool => if i then G.gS {h'} else G.gS {h}) := by
      rw [iSupIndep_pair (i := true) (j := false) (by decide) (fun k => by cases k <;> simp), disjoint_iff]
      show G.gS {h'} ⊓ G.gS {h} = ⊥
      rw [inf_comm]
      exact hdis
    have hRW : ∀ i : Bool, (if i then G.gS {h'} else G.gS {h}) ≤ G.gS {h} ⊔ G.gS {h'} := by
      intro i
      cases i <;> simp
    have hWR : G.gS {h} ⊔ G.gS {h'} ≤ ⨆ i : Bool, (if i then G.gS {h'} else G.gS {h}) :=
      sup_le (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) false)
        (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) true)
    obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (W := G.gS {h} ⊔ G.gS {h'})
      (fun i : Bool => if i then G.gS {h'} else G.gS {h}) hind hRW hWR
    have hEq : ∀ i, ∀ x ∈ G.gS {h} ⊔ G.gS {h'}, ∀ c d, π i (G.E c d x) = G.E c d (π i x) := by
      intro i x hx c d
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      have hy' : G.E c d y ∈ G.gS {h} := G.gS_stable _ c d y hy
      have hz' : G.E c d z ∈ G.gS {h'} := G.gS_stable _ c d z hz
      simp only [map_add]
      cases i
      · rw [hπ2 false _ hy', hπ2 false _ hy, hπ3 false true (by decide) _ hz', hπ3 false true (by decide) _ hz,
          map_zero]
      · rw [hπ3 true false (by decide) _ hy', hπ3 true false (by decide) _ hy, hπ2 true _ hz', hπ2 true _ hz,
          map_zero]
    have hW' : G.Stable (G.gS {h} ⊔ G.gS {h'}) := by
      intro a b x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (G.gS_stable _ a b y hy))
        (Submodule.mem_sup_right (G.gS_stable _ a b z hz))
    have hWf' : G.FinW (G.gS {h} ⊔ G.gS {h'}) := ⟨S, fun x hx => hS x (sup_le hUW hU'W hx)⟩
    obtain ⟨θ₁, θ₁', hθ1, -, -, hθE', hinv⟩ := GlX.exists_theta G (W := G.gS {h} ⊔ G.gS {h'}) hW' hWf'
      (h := h') (h' := h) hh' hh (Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton h')))
      (Submodule.mem_sup_left (G.subset_gS _ (Set.mem_singleton h))) h0' h0 (π true) (π false)
      (hπ1 true) (hπ2 true) (hEq true) (hπ1 false) (hπ2 false) (hEq false)
    refine ⟨θ₁' ∘ₗ (G.gS {h}).subtype, fun a b x => ?_, fun m hm => ⟨⟨θ₁ m, hθ1 m⟩, hinv m hm⟩⟩
    show θ₁' (G.E a b (x : V)) = G.E a b (θ₁' (x : V))
    exact hθE' _ (Submodule.mem_sup_left x.2) a b
  · have hI : G.Stable (G.gS {h} ⊓ G.gS {h'}) := by
      intro a b x hx
      rw [Submodule.mem_inf] at hx ⊢
      exact ⟨G.gS_stable _ a b x hx.1, G.gS_stable _ a b x hx.2⟩
    obtain ⟨v, hvI, hv0, μ, hvw, hvr⟩ := G.exists_hwmod (U := ⊥) (G.graded_of hI)
      (fun a b _ x hx => hI a b x hx) ⟨S, fun x hx => hS x (hUW (Submodule.mem_inf.mp hx).1)⟩
      (fun hle => hdis (le_bot_iff.mp hle))
    have hvHW : G.comp μ v = v ∧ ∀ a b, a < b → G.E a b v = 0 := ⟨hvw, fun a b hab => by
      have hq := hvr a b hab
      rwa [Submodule.mem_bot] at hq⟩
    have hv0' : v ≠ 0 := fun hq => hv0 (by rw [hq]; exact Submodule.zero_mem _)
    obtain ⟨-, c', hc'⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W (Submodule.mem_inf.mp hvI).2 hvHW hv0'
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      apply hv0'
      rw [hc', zero_smul]
    have hmem : h' ∈ G.gS {h} := by
      have hq : h' = c'⁻¹ • v := by rw [hc', smul_smul, inv_mul_cancel₀ hc'0, one_smul]
      rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.mem_inf.mp hvI).1
    have hle : G.gS {h'} ≤ G.gS {h} := G.gS_le (Set.singleton_subset_iff.mpr hmem) (G.gS_stable _)
    exact ⟨(G.gS {h}).subtype, fun a b x => rfl, fun m hm => ⟨⟨m, hle hm⟩, rfl⟩⟩

end iso

section padic

variable (p : ℕ) [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup V] [Module ℚ_[p] V]
  {n : ℕ}

/- English proof (translation)
Take `⟨hZH, hDH⟩` from `hom_divided_holds p U V (Fin n) G₁.E G₂.E L M hZ hLd hMd`. Establish `hrel : GlRel (homAct G₁.E G₂.E)` using `hom_relation_holds ℚ_[p] U V (Fin n) G₁.E G₂.E (glRel_ofT G₁) (glRel_ofT G₂)`. Establish `hterm : ∀ i, ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) ∈ M`. Introduce `i`. Establish `hφ : (b.coord i).smulRight m ∈ HomLat (K` using `ℚ_[p]) L M := by show ∀ x ∈ L, (b.coord i).smulRight m x ∈ M`.

Introduce `x hx`. Rewrite using `[LinearMap.smulRight_apply]`. Conclude with `hZ _ (by rw [Module.Basis.coord_apply]; exact hbi x hx i) m hm`. Establish `hp` using `weightZeroProj_mem_homLat G₁ G₂ S hLg hMg hφ`. Establish `hI` using `invariant_integral_holds p (U →ₗ[ℚ_[p]] V) (Fin n) (homAct G₁.E G₂.E) hrel _ hZH hDH l (List.finRange n) (List.nodup_finRange n) _ hp`.

Rewrite `hI` using `[List.length_finRange]`. Establish `hI' : ∀ x ∈ L, (((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S ((b.coord i).smulRight m))) x ∈ M` using `hI`. Conclude with `hI' (b i) (hbL i)`. Rewrite using `[QQ_apply, smul_comm, Finset.smul_sum, Nat.cast_smul_eq_nsmul]`. Conclude with `AddSubgroup.nsmul_mem _ (AddSubgroup.sum_mem _ fun i _ => hterm i) _`.
-/
theorem QQ_int (G₁ : GlW ℚ_[p] U n) (G₂ : GlW ℚ_[p] V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) ℚ_[p] U) {L : AddSubgroup U} {M : AddSubgroup V} (hZ : ZpClosed p M)
    (hLd : DivStable G₁.E L) (hMd : DivStable G₂.E M) (hLg : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L)
    (hMg : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M) (hbL : ∀ i, b i ∈ L) (hbi : ∀ x ∈ L, ∀ i, ‖b.repr x i‖ ≤ 1)
    {m : V} (hm : m ∈ M) :
    ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • QQ G₁ G₂ S l b m ∈ M := by
  obtain ⟨hZH, hDH⟩ := hom_divided_holds p U V (Fin n) G₁.E G₂.E L M hZ hLd hMd
  have hrel : GlRel (homAct G₁.E G₂.E) :=
    hom_relation_holds ℚ_[p] U V (Fin n) G₁.E G₂.E (glRel_ofT G₁) (glRel_ofT G₂)
  have hterm : ∀ i, ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
      Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) ∈ M := by
    intro i
    have hφ : (b.coord i).smulRight m ∈ HomLat (K := ℚ_[p]) L M := by
      show ∀ x ∈ L, (b.coord i).smulRight m x ∈ M
      intro x hx
      rw [LinearMap.smulRight_apply]
      exact hZ _ (by rw [Module.Basis.coord_apply]; exact hbi x hx i) m hm
    have hp := weightZeroProj_mem_homLat G₁ G₂ S hLg hMg hφ
    have hI := invariant_integral_holds p (U →ₗ[ℚ_[p]] V) (Fin n) (homAct G₁.E G₂.E) hrel _ hZH hDH l (List.finRange n)
      (List.nodup_finRange n) _ hp
    rw [List.length_finRange] at hI
    have hI' : ∀ x ∈ L, (((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
        InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S ((b.coord i).smulRight m))) x ∈ M := hI
    exact hI' (b i) (hbL i)
  rw [QQ_apply, smul_comm, Finset.smul_sum, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.sum_mem _ fun i _ => hterm i) _

end padic

/- English proof (translation)
Introduce `p _ V _ _ n G W M l hD la`. Distinguish the cases in `hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0`. Take `⟨h, hhw, hhW, h0⟩` from `hex`. Establish `hhw' : G.comp la h = h ∧ ∀ a b, a < b → G.E a b h = 0` using `hhw`. Establish `hUW : G.gS {h} ≤ W` using `G.gS_le (Set.singleton_subset_iff.mpr hhW) hD.stable`.

Take `⟨S, hS⟩` from `hD.finW`. Take `⟨k, b, hbM, hbi⟩` from `hD.basis (G.gS {h}) hUW`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Apply `h0` to reduce the goal to its premises.

Establish `h1 : (⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ : G.gS {h}) = 0` using `b.ext_elem (fun i => i.elim0)`. Conclude with `congrArg Subtype.val h1`. Establish `hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) = (k : ℚ_[p])`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `hSch : ∀ φ : (G.gS {h}) →ₗ[ℚ_[p]] (G.gS {h}), (∀ c, homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E c c φ = 0) → InvOp (homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E) l (List.finRange n) φ = (LinearMap.tr …` using `fun φ hφ => by`.

Rewrite using `[hSchur ℚ_[p] V n G W l hD.stable hD.fd hD.finW hD.bound la h hhw hhW h0 φ hφ, hfr]`. Establish `hS' : ∀ (x : G.gS {h}) (μ : Fin n → ℤ), μ ∉ S → (res G (G.gS {h}) (G.gS_stable {h})).comp μ x = 0` using `fun x μ hμ => Subtype.ext (by rw [res_comp_coe]; exact hS _ (hUW x.2) μ hμ)`. Use `⟨QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ LinearMap.eqLocus (QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b) LinearMap.id`.

Use `iSup_le fun v => ?_` and prove the remaining obligations. Take `⟨θ, hθ, hsurj⟩` from `exists_transport G hD.stable hD.finW hhw v.2.1 hhW v.2.2 h0`. Introduce `m hm`. Take `⟨y, rfl⟩` from `hsurj m hm`. Conclude with `LinearMap.mem_eqLocus.mpr (QQ_id hNat (res G (G.gS {h}) (G.gS_stable {h})) G S l b hS' hSch hk θ hθ y)`.

Conclude with `LinearMap.mem_eqLocus.mp (hle (IsoW_le_iSup G W la hx))`. Introduce `mu hmu x hx`. Use `QQ_zero hHom (res G (G.gS {h}) (G.gS_stable {h})) G S l b (W := IsoW G W mu) (G.gS_stable _) ?_ ?_ hx` and prove the remaining obligations. Introduce `μ ν x' y hx0 hy0 hyI hxw hyw c`. Establish `hxw'` using `congrArg Subtype.val hxw`.

Rewrite `hxw'` using `[res_comp_coe]`. Conclude with `hD.bound μ ν (x' : V) y (fun h' => hx0 (Subtype.ext h')) hy0 (hUW x'.2) (IsoW_le G hD.stable mu hyI) hxw' hyw c`. Introduce `ψ hψ hψW`. Use `equiv_zero G h ψ hψ ?_` and prove the remaining obligations. Establish `hc : (res G (G.gS {h}) (G.gS_stable {h})).comp la ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩` using `Subtype.ext (by rw [res_comp_coe]; exact hhw'.1)`.

Establish `hE : ∀ a b, a < b → (res G (G.gS {h}) (G.gS_stable {h})).E a b ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0` using `fun a b hab => Subtype.ext (by rw [res_E_coe]; exact hhw'.2 a b hab)`. Establish `hHW : G.comp la (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ ∧ ∀ a b, a < b → G.E a b (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = 0` using `⟨by rw [← comp_comm2 (res G (G.gS {h}) (G.gS_stable {h})) G ψ (fun c x => hψ c c x) la, hc], fun a b hab => by rw [← hψ, hE a b hab, map_zero]⟩`. Conclude with `hw_IsoW_zero G hD.stable hD.finW hmu hHW (hψW _)`. Introduce `m hm _`. Use `QQ_int p (res G (G.gS {h}) (G.gS_stable {h})) G S l b (L := M.comap (G.gS {h}).subtype.toAddMonoidHom) hD.closed ?_ hD.div ?_ hD.graded hbM hbi hm` and prove the remaining obligations.

Introduce `a c hac j x hx show ((((j.factorial : ℚ_[p]))⁻¹ • (((res G (G.gS {h}) (G.gS_stable {h})).E a c ^ j) x) : G.gS {h}) : V) ∈ M`. Rewrite using `[Submodule.coe_smul, res_pow_coe]`. Conclude with `hD.div a c hac j _ hx`. Introduce `μ x hx show (((res G (G.gS {h}) (G.gS_stable {h})).comp μ x : G.gS {h}) : V) ∈ M`. Rewrite using `[res_comp_coe]`.

Conclude with `hD.graded μ _ hx`. Use `push_neg at hex`. Use `⟨0, ?_, fun _ _ _ _ => rfl, fun m _ _ => by simp⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ ⊥`.

Use `iSup_le fun v => G.gS_le ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Rewrite using `[hy, hex _ v.2.1 v.2.2]`. Conclude with `Submodule.zero_mem _`.

Introduce `a b y hy`. Rewrite `hy`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hy, map_zero]`. Establish `hx0` using `hle (IsoW_le_iSup G W la hx)`. Rewrite `hx0` using `[Submodule.mem_bot]`.

Rewrite using `[hx0, map_zero]`.
-/
theorem typeInt_of (hNat : InvNat) (hHom : HomInv) (hSchur : SchurTrace) : TypeInt := by
  intro p _ V _ _ n G W M l hD la
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  · obtain ⟨h, hhw, hhW, h0⟩ := hex
    have hhw' : G.comp la h = h ∧ ∀ a b, a < b → G.E a b h = 0 := hhw
    have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hD.stable
    obtain ⟨S, hS⟩ := hD.finW
    obtain ⟨k, b, hbM, hbi⟩ := hD.basis (G.gS {h}) hUW
    have hk : k ≠ 0 := by
      rintro rfl
      apply h0
      have h1 : (⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ : G.gS {h}) = 0 := b.ext_elem (fun i => i.elim0)
      exact congrArg Subtype.val h1
    have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) = (k : ℚ_[p]) := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hSch : ∀ φ : (G.gS {h}) →ₗ[ℚ_[p]] (G.gS {h}),
        (∀ c, homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E c c φ = 0) →
        InvOp (homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E) l (List.finRange n) φ =
          (LinearMap.trace ℚ_[p] _ φ / (k : ℚ_[p])) • LinearMap.id := fun φ hφ => by
      rw [hSchur ℚ_[p] V n G W l hD.stable hD.fd hD.finW hD.bound la h hhw hhW h0 φ hφ, hfr]
    have hS' : ∀ (x : G.gS {h}) (μ : Fin n → ℤ), μ ∉ S → (res G (G.gS {h}) (G.gS_stable {h})).comp μ x = 0 :=
      fun x μ hμ => Subtype.ext (by rw [res_comp_coe]; exact hS _ (hUW x.2) μ hμ)
    refine ⟨QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b, ?_, ?_, ?_⟩
    · intro x hx
      have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
          LinearMap.eqLocus (QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b) LinearMap.id := by
        refine iSup_le fun v => ?_
        obtain ⟨θ, hθ, hsurj⟩ := exists_transport G hD.stable hD.finW hhw v.2.1 hhW v.2.2 h0
        intro m hm
        obtain ⟨y, rfl⟩ := hsurj m hm
        exact LinearMap.mem_eqLocus.mpr (QQ_id hNat (res G (G.gS {h}) (G.gS_stable {h})) G S l b hS' hSch hk θ hθ y)
      exact LinearMap.mem_eqLocus.mp (hle (IsoW_le_iSup G W la hx))
    · intro mu hmu x hx
      refine QQ_zero hHom (res G (G.gS {h}) (G.gS_stable {h})) G S l b (W := IsoW G W mu) (G.gS_stable _) ?_ ?_ hx
      · intro μ ν x' y hx0 hy0 hyI hxw hyw c
        have hxw' := congrArg Subtype.val hxw
        rw [res_comp_coe] at hxw'
        exact hD.bound μ ν (x' : V) y (fun h' => hx0 (Subtype.ext h')) hy0 (hUW x'.2) (IsoW_le G hD.stable mu hyI)
          hxw' hyw c
      · intro ψ hψ hψW
        refine equiv_zero G h ψ hψ ?_
        have hc : (res G (G.gS {h}) (G.gS_stable {h})).comp la ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ =
            ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ :=
          Subtype.ext (by rw [res_comp_coe]; exact hhw'.1)
        have hE : ∀ a b, a < b → (res G (G.gS {h}) (G.gS_stable {h})).E a b ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0 :=
          fun a b hab => Subtype.ext (by rw [res_E_coe]; exact hhw'.2 a b hab)
        have hHW : G.comp la (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ ∧
            ∀ a b, a < b → G.E a b (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = 0 :=
          ⟨by rw [← comp_comm2 (res G (G.gS {h}) (G.gS_stable {h})) G ψ (fun c x => hψ c c x) la, hc],
            fun a b hab => by rw [← hψ, hE a b hab, map_zero]⟩
        exact hw_IsoW_zero G hD.stable hD.finW hmu hHW (hψW _)
    · intro m hm _
      refine QQ_int p (res G (G.gS {h}) (G.gS_stable {h})) G S l b (L := M.comap (G.gS {h}).subtype.toAddMonoidHom) hD.closed ?_ hD.div ?_
        hD.graded hbM hbi hm
      · intro a c hac j x hx
        show ((((j.factorial : ℚ_[p]))⁻¹ • (((res G (G.gS {h}) (G.gS_stable {h})).E a c ^ j) x) : G.gS {h}) : V) ∈ M
        rw [Submodule.coe_smul, res_pow_coe]
        exact hD.div a c hac j _ hx
      · intro μ x hx
        show (((res G (G.gS {h}) (G.gS_stable {h})).comp μ x : G.gS {h}) : V) ∈ M
        rw [res_comp_coe]
        exact hD.graded μ _ hx
  · push_neg at hex
    refine ⟨0, ?_, fun _ _ _ _ => rfl, fun m _ _ => by simp⟩
    intro x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ ⊥ := by
      refine iSup_le fun v => G.gS_le ?_ ?_
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy, hex _ v.2.1 v.2.2]
        exact Submodule.zero_mem _
      · intro a b y hy
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero]
    have hx0 := hle (IsoW_le_iSup G W la hx)
    rw [Submodule.mem_bot] at hx0
    rw [hx0, map_zero]

end Formalism.InvariantFactorPaths.PW
