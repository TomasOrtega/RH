import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefHomGenHomMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotential

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWt GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD
open scoped TensorProduct

namespace GlobalTheory.HighWtEmb

section AtFactor

variable {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem atFactor_tprod' (τ : ι) (p : Nb τ →ₗ[O] Nb τ) (x : ∀ τ, Nb τ) :
    atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ))) := by
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

def atHom (τ : ι) : Module.End O (Nb τ) →ₐ[O] Module.End O (⨂[O] τ, Nb τ) :=
  AlgHom.ofLinearMap
    { toFun := atFactor τ
      map_add' := fun p q => by ext x; simp [atFactor_tprod']
      map_smul' := fun c p => by ext x; simp [atFactor_tprod'] }
    (by ext x; simp [atFactor_tprod']) (fun p q => by ext x; simp [atFactor_tprod'])

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atHom_tprod (τ : ι) (p : Module.End O (Nb τ)) (x : ∀ τ, Nb τ) :
    atHom τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ))) := atFactor_tprod' τ p x

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem atHom_comm {τ σ : ι} (h : τ ≠ σ) (p : Module.End O (Nb τ)) (q : Module.End O (Nb σ)) :
    atHom τ p * atHom σ q = atHom σ q * atHom τ p := by
  ext x
  simp [atHom_tprod, Function.update_of_ne h, Function.update_of_ne h.symm, Function.update_comm h]

end AtFactor

variable (O : Type) [CommRing O] (N : ℕ)

def coefEnd (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) : Module.End O (dualWeyl O N N ν) :=
  (((lcoeff (MvPolynomial (Fin N × Fin N) O) m).restrictScalars O) ∘ₗ (genHom O N).toLinearMap).restrict
    (fun x hx => coeff_genHom_mem O N ν x hx m)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_coefEnd (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) (f : dualWeyl O N N ν) :
    (coefEnd O N ν m f : MvPolynomial (Fin N × Fin N) O) = coeff m (genHom O N f) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_rowProj (ν v : Fin N → ℕ) (f : dualWeyl O N N ν) :
    (rowProj O N ν v f : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) v f := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem coefEnd_mul_rowProj (ν v : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    coefEnd O N ν m * rowProj O N ν v = if Finsupp.weight (rowW N N) m = v then coefEnd O N ν m else 0 := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_coefEnd, coe_rowProj, genHom_component, coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem rowProj_mul_coefEnd (ν v : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    rowProj O N ν v * coefEnd O N ν m = if Finsupp.weight (colW N N) m = v then coefEnd O N ν m else 0 := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_rowProj, coe_coefEnd, weightedHomogeneousComponent_of_mem (coeff_genHom_row O N f m)]
  by_cases h : Finsupp.weight (colW N N) m = v
  · rw [if_pos h, if_pos h.symm]; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rowProj_mul_self (ν v : Fin N → ℕ) : rowProj O N ν v * rowProj O N ν v = rowProj O N ν v := by
  ext1 f
  apply Subtype.ext
  rw [Module.End.mul_apply, coe_rowProj, coe_rowProj,
    weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous v _), if_pos rfl]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)

abbrev atN (τ : ι) : Module.End O (dualWeyl O N N (res N (lam τ))) →ₐ[O] Module.End O (NablaT O N lam) :=
  atHom (Nb := fun τ => dualWeyl O N N (res N (lam τ))) τ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isProj_iff (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) :
    IsProj O N lam τ v a ↔ a = atN O N lam τ (rowProj O N _ v) := by
  constructor
  · intro h
    ext x
    exact (h x _ rfl).trans (atHom_tprod τ _ x).symm
  · rintro rfl x y hy
    rw [atHom_tprod, show y = rowProj O N _ v (x τ) from Subtype.ext hy]

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem eq_of_isCoef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (a : Module.End O (NablaT O N lam)) (h : IsCoef O N lam τ m a) :
    a = atN O N lam τ (coefEnd O N _ m) := by
  ext x
  exact (h x _ rfl).trans (atHom_tprod τ _ x).symm

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem grp_mulSingle (τ : ι) (h : GL (Fin N) O) :
    grp O N lam (Pi.mulSingle τ h) = atN O N lam τ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) h) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply]
  rw [grp_tprod, atHom_tprod]
  congr 1
  funext σ
  by_cases hσ : σ = τ
  · subst hσ; simp
  · simp [Function.update_of_ne hσ, Pi.mulSingle_eq_of_ne hσ]

def projA (τ : ι) (v : Fin N → ℕ) : alg O N lam :=
  ⟨atN O N lam τ (rowProj O N _ v), Algebra.subset_adjoin (Or.inr ⟨τ, v, (isProj_iff O N lam τ v _).2 rfl⟩)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isProj_projA (τ : ι) (v : Fin N → ℕ) : IsProj O N lam τ v (projA O N lam τ v) := (isProj_iff O N lam τ v _).2 rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eq_projA {τ : ι} {v : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ v a) : a = projA O N lam τ v :=
  Subtype.ext ((isProj_iff O N lam τ v _).1 h)

variable {O N lam} {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm] {R : Type} [CommRing R] [Algebra O R]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem sum_expand {Z I : Type} (θ : MvPolynomial Z O →ₐ[O] R) (ψ : Gm →+ R)
    (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z) (s : Finset I) (p : I → MvPolynomial Z O)
    (a : I → alg O N lam) (U : Finset (Z →₀ ℕ)) (hU : ∀ i ∈ s, (p i).support ⊆ U) (z : Gm) :
    ∑ i ∈ s, θ (p i) * ψ (a i • z) = ∑ μ ∈ U, θ (monomial μ 1) * ψ ((∑ i ∈ s, coeff μ (p i) • a i) • z) := by
  simp only [Finset.sum_smul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : p i = ∑ μ ∈ U, coeff μ (p i) • monomial μ 1 := by
    conv_lhs => rw [(p i).as_sum]
    simp only [smul_monomial, smul_eq_mul, mul_one]
    exact Finset.sum_subset (hU i hi) fun m _ hm => by rw [notMem_support_iff.1 hm, map_zero]
  conv_lhs => rw [this]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Algebra.smul_def (A := alg O N lam), mul_smul, hψ, map_smul, Algebra.smul_def]
  ring

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
theorem transfer {Z I J : Type} (θ : MvPolynomial Z O →ₐ[O] R) (ψ : Gm →+ R)
    (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z) (τ : ι) (s : Finset I) (t : Finset J)
    (p : I → MvPolynomial Z O) (q : J → MvPolynomial Z O) (a : I → alg O N lam) (a' : J → alg O N lam)
    (b : I → Module.End O (dualWeyl O N N (res N (lam τ)))) (b' : J → Module.End O (dualWeyl O N N (res N (lam τ))))
    (hb : ∀ i, (a i : Module.End O (NablaT O N lam)) = atN O N lam τ (b i))
    (hb' : ∀ j, (a' j : Module.End O (NablaT O N lam)) = atN O N lam τ (b' j))
    (H : ∀ f : dualWeyl O N N (res N (lam τ)), ∑ i ∈ s, map C (p i) * C (b i f : MvPolynomial (Fin N × Fin N) O) =
      ∑ j ∈ t, map C (q j) * C (b' j f : MvPolynomial (Fin N × Fin N) O)) (z : Gm) :
    ∑ i ∈ s, θ (p i) * ψ (a i • z) = ∑ j ∈ t, θ (q j) * ψ (a' j • z) := by
  classical
  let U := s.biUnion (fun i => (p i).support) ∪ t.biUnion fun j => (q j).support
  rw [sum_expand θ ψ hψ s p a U (fun i hi => (Finset.subset_biUnion_of_mem (fun i => (p i).support) hi).trans Finset.subset_union_left),
    sum_expand θ ψ hψ t q a' U (fun i hi => (Finset.subset_biUnion_of_mem (fun i => (q i).support) hi).trans Finset.subset_union_right)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : ∑ i ∈ s, coeff μ (p i) • b i = ∑ j ∈ t, coeff μ (q j) • b' j := by
    ext1 f
    apply Subtype.ext
    have := congrArg (coeff μ) (H f)
    simp only [coeff_sum, mul_comm _ (C _), coeff_C_mul, coeff_map] at this
    simpa [smul_eq_C_mul, mul_comm] using this
  have h2 : ∑ i ∈ s, coeff μ (p i) • a i = ∑ j ∈ t, coeff μ (q j) • a' j := by
    apply Subtype.ext
    have := congrArg (atN O N lam τ) h1
    simpa [hb, hb'] using this
  rw [h2]

variable (c : ι → (Fin N × Fin N →₀ ℕ) → alg O N lam)
  (hc : ∀ τ m, (c τ m : Module.End O (NablaT O N lam)) = atN O N lam τ (coefEnd O N _ m))
  (ψ : Gm →+ R) (hψ : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = algebraMap O R c * ψ z)
include hc

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem coef_mul_proj (τ : ι) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    c τ m * projA O N lam τ v = if Finsupp.weight (rowW N N) m = v then c τ m else 0 := by
  apply Subtype.ext
  have := congrArg (atN O N lam τ) (coefEnd_mul_rowProj O N _ v m)
  rw [map_mul] at this
  split_ifs at this ⊢
  · simpa [hc, projA] using this
  · simpa [hc, projA] using this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem proj_mul_coef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    projA O N lam τ v * c τ m = if Finsupp.weight (colW N N) m = v then c τ m else 0 := by
  apply Subtype.ext
  have := congrArg (atN O N lam τ) (rowProj_mul_coefEnd O N _ v m)
  rw [map_mul] at this
  split_ifs at this ⊢
  · simpa [hc, projA] using this
  · simpa [hc, projA] using this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coef_comm {τ σ : ι} (h : τ ≠ σ) (m m' : Fin N × Fin N →₀ ℕ) : c τ m * c σ m' = c σ m' * c τ m := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, hc]
  exact atHom_comm h _ _

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coef_proj_comm {τ σ : ι} (h : τ ≠ σ) (m : Fin N × Fin N →₀ ℕ) (v : Fin N → ℕ) :
    c τ m * projA O N lam σ v = projA O N lam σ v * c τ m := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, hc]
  exact atHom_comm h _ _

omit hc in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem proj_comm {τ σ : ι} (h : τ ≠ σ) (u v : Fin N → ℕ) :
    projA O N lam τ u * projA O N lam σ v = projA O N lam σ v * projA O N lam τ u :=
  Subtype.ext (atHom_comm h _ _)

omit hc in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem proj_mul_self (τ : ι) (v : Fin N → ℕ) : projA O N lam τ v * projA O N lam τ v = projA O N lam τ v :=
  Subtype.ext (by
    show atN O N lam τ _ * atN O N lam τ _ = atN O N lam τ _
    rw [← map_mul, rowProj_mul_self])

include hψ

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem sum_unit {Z : Type} (θ : MvPolynomial Z O →ₐ[O] R) (τ : ι) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (unitHom O N Z (monomial m 1)) * ψ (c τ m • z) = ψ z := by
  have := transfer θ ψ hψ τ (expSet N (res N (lam τ))) {()} (fun m => unitHom O N Z (monomial m 1)) (fun _ => 1) (c τ) (fun _ => 1)
    _ (fun _ => 1) (hc τ) (fun _ => by simp) (fun f => by
      simp only [coe_coefEnd]
      rw [← extHom_genHom O N _ _ _ f.2, extHom_unit]
      simp) z
  simpa using this

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_grp (θ : MvPolynomial (Fin N × Fin N) O →ₐ[O] R) (τ : ι) (h : GL (Fin N) O) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (monomial m 1) * ψ (c τ m • grpA O N lam (Pi.mulSingle τ h) • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rowAct O ((h⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O) (monomial m 1)) * ψ (c τ m • z) := by
  simp only [smul_smul]
  refine transfer θ ψ hψ τ _ _ _ _ (fun m => c τ m * grpA O N lam (Pi.mulSingle τ h)) (c τ)
    (fun m => coefEnd O N _ m * Formalism.UG.dualWeylRep O N N (res N (lam τ)) h) _
    (fun m => by rw [map_mul, ← hc, ← grp_mulSingle]; rfl) (hc τ) (fun f => ?_) z
  simp only [coe_coefEnd, Module.End.mul_apply]
  rw [← extHom_genHom O N _ _ _ f.2, ← genHom_rowAct]
  have := extHom_genHom O N (AlgHom.id O _) _ _ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) h f).2
  rw [extHom_id] at this
  exact this.symm

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem sum_col (θ : MvPolynomial (Option (Fin N × Fin N)) O →ₐ[O] R) (τ : ι) (l j : Fin N) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (colAddGen O l j (monomial m 1)) * ψ (c τ m • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rename some (monomial m 1)) *
        ∑ m' ∈ expSet N (res N (lam τ)), θ (elemHom O N l j (monomial m' 1)) * ψ (c τ m' • c τ m • z) := by
  rw [transfer θ ψ hψ τ _ (expSet N (res N (lam τ)) ×ˢ expSet N (res N (lam τ))) _
    (fun p => rename some (monomial p.1 1) * elemHom O N l j (monomial p.2 1)) (c τ) (fun p => c τ p.2 * c τ p.1)
    _ (fun p => coefEnd O N _ p.2 * coefEnd O N _ p.1) (hc τ) (fun m => by rw [map_mul, ← hc, ← hc]; rfl) (fun f => ?_) z]
  · rw [Finset.sum_product]
    simp only [Finset.mul_sum, map_mul, mul_smul, mul_assoc]
  · simp only [coe_coefEnd, Module.End.mul_apply]
    rw [← extHom_genHom O N _ _ _ f.2, extHom_colAddGen O N l j _ _ f.2]

omit hψ in
/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem apply_coef_eq_zero_of_col (τ : ι) (w : Fin N → ℕ) (h0 : ∀ v, v ≠ w → ∀ z, ψ (projA O N lam τ v • z) = 0)
    (m : Fin N × Fin N →₀ ℕ) (hm : Finsupp.weight (colW N N) m ≠ w) (z : Gm) : ψ (c τ m • z) = 0 := by
  have := proj_mul_coef c hc τ m (Finsupp.weight (colW N N) m)
  rw [if_pos rfl] at this
  rw [← this, mul_smul, h0 _ hm]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem apply_proj (τ : ι) (w : Fin N → ℕ) (h0 : ∀ v, v ≠ w → ∀ z, ψ (projA O N lam τ v • z) = 0) (z : Gm) :
    ψ (projA O N lam τ w • z) = ψ z := by
  let θ : MvPolynomial Empty O →ₐ[O] R := aeval fun _ => 0
  have h1 := sum_unit c hc (ψ.comp (DistribMulAction.toAddMonoidHom Gm (projA O N lam τ w))) (fun r z => by
    simp only [AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply]
    rw [smul_smul, ← Algebra.commutes, mul_smul, hψ]) θ τ z
  refine h1.symm.trans ((Finset.sum_congr rfl fun m _ => ?_).trans (sum_unit c hc ψ hψ θ τ z))
  refine congrArg (_ * ·) ?_
  simp only [AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply]
  rw [smul_smul, proj_mul_coef c hc]
  split_ifs with h
  · rfl
  · rw [zero_smul, map_zero, apply_coef_eq_zero_of_col c hc ψ τ w h0 m h]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. It suffices to derive a contradiction. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem apply_coef_eq_zero_of_lt (w : ι → Fin N → ℕ) (hmax : ∀ w' : ι → Fin N → ℕ, JointWt O N lam Gm w' → pot N w' ≤ pot N w)
    (h0 : ∀ τ v, v ≠ w τ → ∀ z, ψ (projA O N lam τ v • z) = 0) (τ : ι) (m : Fin N × Fin N →₀ ℕ)
    (hm : ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v) (z : Gm) : ψ (c τ m • z) = 0 := by
  by_cases hcol : Finsupp.weight (colW N N) m = w τ
  swap
  · exact apply_coef_eq_zero_of_col c hc ψ τ _ (h0 τ) m hcol z
  set w' := Function.update w τ (Finsupp.weight (rowW N N) m) with hw'
  have key : ∀ s : Finset ι, ∃ z' : Gm, ψ (c τ m • z) = ψ (c τ m • z') ∧ ∀ σ ∈ s, projA O N lam σ (w' σ) • z' = z' := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨z, rfl, by simp⟩
    | insert σ s hσ ih =>
      obtain ⟨z', h1, h2⟩ := ih
      refine ⟨projA O N lam σ (w' σ) • z', h1.trans ?_, fun ρ hρ => ?_⟩
      · by_cases h : σ = τ
        · subst h
          rw [smul_smul, coef_mul_proj c hc, if_pos (by simp [hw'])]
        · rw [smul_smul, coef_proj_comm c hc (Ne.symm h), mul_smul, hw', Function.update_of_ne h, apply_proj c hc ψ hψ σ _ (h0 σ)]
      · rcases Finset.mem_insert.1 hρ with rfl | hρ'
        · rw [smul_smul, proj_mul_self]
        · rw [smul_smul, proj_comm (by rintro rfl; exact hσ hρ'), mul_smul, h2 ρ hρ']
  obtain ⟨z', h1, h2⟩ := key Finset.univ
  by_cases hz : z' = 0
  · rw [h1, hz, smul_zero, map_zero]
  exfalso
  have h3 := hmax w' ⟨z', hz, fun σ a ha => by rw [eq_projA O N lam ha]; exact h2 σ (Finset.mem_univ _)⟩
  refine absurd h3 (not_le.2 ?_)
  unfold pot
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = τ
    · subst hi
      rw [hw', Function.update_self, ← hcol, sum_mul_weight_rowW N (fun a => N - (a : ℕ)), sum_mul_weight_colW N (fun a => N - (a : ℕ))]
      exact hm.le
    · rw [hw', Function.update_of_ne hi]
  · refine ⟨τ, Finset.mem_univ _, ?_⟩
    rw [hw', Function.update_self, ← hcol, sum_mul_weight_rowW N (fun a => N - (a : ℕ)), sum_mul_weight_colW N (fun a => N - (a : ℕ))]
    exact hm

omit hc hψ in
/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem elemHom_eq_or_lt (l j : Fin N) (hlj : l < j) (m : Fin N × Fin N →₀ ℕ) :
    elemHom O N l j (monomial m 1) = unitHom O N _ (monomial m 1) ∨
      ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v := by
  by_cases h1 : m (l, j) = 0
  · left
    simp only [elemHom, unitHom, aeval_monomial, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_neg (show ¬ v = (l, j) by rintro rfl; exact Finsupp.mem_support_iff.1 hv h1), add_zero]
  by_cases h2 : ∃ v ∈ m.support, v.1 ≠ v.2 ∧ v ≠ (l, j)
  · left
    obtain ⟨v, hv, hv1, hv2⟩ := h2
    simp only [elemHom, unitHom, aeval_monomial, Finsupp.prod]
    rw [Finset.prod_eq_zero hv, Finset.prod_eq_zero hv] <;> simp [hv1, hv2, Finsupp.mem_support_iff.1 hv]
  right
  push_neg at h2
  have hl : N - (j : ℕ) < N - (l : ℕ) := by have := j.isLt; have : (l : ℕ) < j := hlj; omega
  apply Finset.sum_lt_sum
  · intro v _
    by_cases hv : m v = 0
    · simp [hv]
    by_cases h : v.1 = v.2
    · rw [h]
    · rw [h2 v (Finsupp.mem_support_iff.2 hv) h]
      exact Nat.mul_le_mul_right _ hl.le
  · exact ⟨(l, j), Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right hl (Nat.pos_of_ne_zero h1)⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem sum_col_eq (θ : MvPolynomial (Option (Fin N × Fin N)) O →ₐ[O] R) (τ : ι) (l j : Fin N) (hlj : l < j)
    (h0 : ∀ m : Fin N × Fin N →₀ ℕ, ∑ v : Fin N × Fin N, (N - (v.2 : ℕ)) * m v < ∑ v : Fin N × Fin N, (N - (v.1 : ℕ)) * m v →
      ∀ z, ψ (c τ m • z) = 0) (z : Gm) :
    ∑ m ∈ expSet N (res N (lam τ)), θ (colAddGen O l j (monomial m 1)) * ψ (c τ m • z) =
      ∑ m ∈ expSet N (res N (lam τ)), θ (rename some (monomial m 1)) * ψ (c τ m • z) := by
  rw [sum_col c hc ψ hψ]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine congrArg (_ * ·) (Eq.trans ?_ (sum_unit c hc ψ hψ θ τ (c τ m • z)))
  refine Finset.sum_congr rfl fun m' _ => ?_
  rcases elemHom_eq_or_lt (O := O) l j hlj m' with h | h
  · rw [h]
  · rw [h0 m' h, mul_zero, mul_zero]

end GlobalTheory.HighWtEmb

end
