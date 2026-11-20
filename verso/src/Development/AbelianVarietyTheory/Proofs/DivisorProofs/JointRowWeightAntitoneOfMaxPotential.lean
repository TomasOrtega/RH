import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.HighWt

def permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) O :=
  Matrix.of fun i j => if σ i = j then 1 else 0

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [permMat, Matrix.mul_apply, Matrix.of_apply, Equiv.trans_apply]`. Rewrite using `[Finset.sum_eq_single (σ i)]`. Apply the tactic sequence `by_cases h : ρ (σ i) = k <;> simp [h]`. Introduce `j _ hj`.

Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
theorem permMat_mul {O : Type} [CommRing O] {N : ℕ} (σ ρ : Equiv.Perm (Fin N)) :
    (permMat σ : Matrix (Fin N) (Fin N) O) * permMat ρ = permMat (σ.trans ρ) := by
  ext i k
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, Equiv.trans_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : ρ (σ i) = k <;> simp [h]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/- English proof (translation)
Use extensionality with `i k`. Apply the tactic sequence `by_cases h : i = k <;> simp [permMat, Matrix.one_apply, h]`.
-/
theorem permMat_refl {O : Type} [CommRing O] {N : ℕ} :
    (permMat (Equiv.refl (Fin N)) : Matrix (Fin N) (Fin N) O) = 1 := by
  ext i k
  by_cases h : i = k <;> simp [permMat, Matrix.one_apply, h]

def permGL {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) O :=
  ⟨permMat σ, permMat σ.symm, by rw [permMat_mul, Equiv.self_trans_symm, permMat_refl],
    by rw [permMat_mul, Equiv.symm_trans_self, permMat_refl]⟩

/- English proof (translation)
Establish `: Formalism.GradedWeylDivisibility.rowAct O (n` using `N) (permMat σ) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, permMat, rename_X]`. Rewrite using `[this]`.
-/
theorem rowAct_permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) O) :
    Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f := by
  have : Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, permMat, rename_X]
  rw [this]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hf, hg]`. Consider the case `single v c`. Rewrite using `[Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]`.

Simplify using `only [Pi.smul_apply, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, σ.injective.eq_iff]`.
-/
theorem weight_mapDomain_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) (σ a) =
      Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hf, hg]
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    simp only [Pi.smul_apply, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, σ.injective.eq_iff]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial d c`. Rewrite using `[rename_monomial]`. Establish `key : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) = u ↔ Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use function extensionality and compare the values at `a`. Rewrite using `[Function.comp_apply, ← h, weight_mapDomain_perm]`. Introduce `h`. Use function extensionality and compare the values at `b`.

Take `⟨a, rfl⟩` from `σ.surjective b`. Rewrite using `[weight_mapDomain_perm, h, Function.comp_apply]`. Rewrite using `[weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl), weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]`. Distinguish the cases in `h : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ`. Rewrite using `[if_pos (Eq.symm (key.2 h)), if_pos h.symm, rename_monomial]`.

Rewrite using `[if_neg (fun h' => h (key.1 h'.symm)), if_neg (fun h' => h h'.symm), map_zero]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]`.
-/
theorem rowComp_rename_perm {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f) =
      rename (fun v : Fin N × Fin N => (σ v.1, v.2)) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (u ∘ σ) f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]
    have key : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) = u ↔
        Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ := by
      constructor
      · intro h
        funext a
        rw [Function.comp_apply, ← h, weight_mapDomain_perm]
      · intro h
        funext b
        obtain ⟨a, rfl⟩ := σ.surjective b
        rw [weight_mapDomain_perm, h, Function.comp_apply]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    by_cases h : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ
    · rw [if_pos (Eq.symm (key.2 h)), if_pos h.symm, rename_monomial]
    · rw [if_neg (fun h' => h (key.1 h'.symm)), if_neg (fun h' => h h'.symm), map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

/- English proof (translation)
Simplify using `only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, MonoidHom.coe_comp, Function.comp_apply]`. Rewrite using `[PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]`. Both sides reduce to the same expression.
-/
theorem grp_tprod (g : ι → GL (Fin N) O) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) :
    grp O N lam g (PiTensorProduct.tprod O x) =
      PiTensorProduct.tprod O (fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ) (x τ)) := by
  simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, MonoidHom.coe_comp, Function.comp_apply]
  rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

/- English proof (translation)
Simplify using `only [grp]`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`.
-/
theorem grp_inv_mul (g : ι → GL (Fin N) O) : grp O N lam g⁻¹ * grp O N lam g = 1 := by
  simp only [grp]
  rw [← map_mul, inv_mul_cancel, map_one]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem dualWeylRep_mul_inv (ν : Fin N → ℕ) (h : GL (Fin N) O) (v : Formalism.GradedWeylDivisibility.dualWeyl O N N ν) :
    Formalism.UG.dualWeylRep O N N ν h (Formalism.UG.dualWeylRep O N N ν h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Introduce `x y hy`. Use `set x'' : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)) := fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ)⁻¹ (x τ) with hx''`. Establish `h1 : grp O N lam g⁻¹ (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O x''`. Rewrite using `[grp_tprod]`. Both sides reduce to the same expression.

Establish `hy'' : ((Formalism.UG.dualWeylRep O N N (res N (lam τ')) (g τ')⁻¹ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ'))) : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (x'' τ' : MvPolynomial (Fin N × F …`. Rewrite using `[Formalism.UG.dualWeylRep_apply, hy, ← h, hx'', Formalism.UG.dualWeylRep_apply]`. Establish `h2` using `hb x'' _ hy''`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, h1, h2, grp_tprod]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = τ'`. Substitute `hi` using the available equality. Rewrite using `[Function.update_self, Function.update_self, dualWeylRep_mul_inv]`. Rewrite using `[Function.update_of_ne hi, Function.update_of_ne hi, hx'', dualWeylRep_mul_inv]`.
-/
theorem isProj_conj (g : ι → GL (Fin N) O) (τ' : ι) (u u' : Fin N → ℕ)
    (h : ∀ f, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (Formalism.UG.dwAct O N N (g τ')⁻¹ f) =
      Formalism.UG.dwAct O N N (g τ')⁻¹ (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u' f))
    (b : Module.End O (NablaT O N lam)) (hb : IsProj O N lam τ' u b) :
    IsProj O N lam τ' u' (grp O N lam g * b * grp O N lam g⁻¹) := by
  intro x y hy
  set x'' : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)) := fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ)⁻¹ (x τ) with hx''
  have h1 : grp O N lam g⁻¹ (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O x'' := by
    rw [grp_tprod]; rfl
  have hy'' : ((Formalism.UG.dualWeylRep O N N (res N (lam τ')) (g τ')⁻¹ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ'))) :
      MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (x'' τ' : MvPolynomial (Fin N × Fin N) O) := by
    rw [Formalism.UG.dualWeylRep_apply, hy, ← h, hx'', Formalism.UG.dualWeylRep_apply]
  have h2 := hb x'' _ hy''
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2, grp_tprod]
  congr 1
  funext i
  by_cases hi : i = τ'
  · subst hi
    rw [Function.update_self, Function.update_self, dualWeylRep_mul_inv]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi, hx'', dualWeylRep_mul_inv]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

/- English proof (translation)
The claim follows from `Subtype.ext (grp_inv_mul O N lam g)`.
-/
theorem grpA_inv_mul (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (g : ι → GL (Fin N) O) :
    grpA O N lam g⁻¹ * grpA O N lam g = 1 :=
  Subtype.ext (grp_inv_mul O N lam g)

/- English proof (translation)
Take `⟨z, hz0, hz⟩` from `hw`. Use `set g : ι → GL (Fin N) O := Pi.mulSingle τ (permGL σ) with hg`. Use `⟨grpA O N lam g • z, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hz0` to reduce the goal to its premises.

Use `congrArg (fun t => grpA O N lam g⁻¹ • t) h0` as an intermediate fact. Simplify using `only [smul_smul, grpA_inv_mul, one_smul, smul_zero] at this`. Conclude with `this`. Introduce `τ' a ha`. Take `⟨b0, hb0, -⟩` from `GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (w τ')`.

Take `⟨c, -, huniq⟩` from `GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (Function.update w τ (w τ ∘ σ) τ')`. Establish `hconj : IsProj O N lam τ' (Function.update w τ (w τ ∘ σ) τ') (grp O N lam g * b0 * grp O N lam g⁻¹)`. Apply `isProj_conj O N lam g τ' (w τ') _ _ b0 hb0` to reduce the goal to its premises. Introduce `f`. Distinguish the cases in `hτ : τ' = τ`.

Substitute `hτ` using the available equality. Establish `hgt : g τ' = permGL σ` using `by rw [hg, Pi.mulSingle_eq_same]`. Rewrite using `[hgt, Function.update_self]`. Simplify using `only [Formalism.UG.dwAct, inv_inv]`. Use `show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ') (Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f) = Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility …`.

Rewrite using `[rowAct_permMat, rowAct_permMat, rowComp_rename_perm]`. Establish `hgt : g τ' = 1` using `by rw [hg, Pi.mulSingle_eq_of_ne hτ]`. Rewrite using `[hgt, Function.update_of_ne hτ, inv_one, (Formalism.UG.P.dual_weyl_action_mul O N N 1 1).2]`. Both sides reduce to the same expression. Establish `haeq : (a : Module.End O (NablaT O N lam)) = grp O N lam g * b0 * grp O N lam g⁻¹` using `(huniq _ ha).trans (huniq _ hconj).symm`.

Use `set b : alg O N lam := ⟨b0, Algebra.subset_adjoin (Or.inr ⟨τ', w τ', hb0⟩)⟩ with hbdef`. Establish `haeq' : a = grpA O N lam g * b * grpA O N lam g⁻¹` using `Subtype.ext haeq`. Rewrite using `[haeq', smul_smul, mul_assoc, grpA_inv_mul, mul_one, mul_smul, hz τ' b hb0]`.
-/
theorem jointWt_perm (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (hw : JointWt O N lam Gm w)
    (τ : ι) (σ : Equiv.Perm (Fin N)) : JointWt O N lam Gm (Function.update w τ (w τ ∘ σ)) := by
  obtain ⟨z, hz0, hz⟩ := hw
  set g : ι → GL (Fin N) O := Pi.mulSingle τ (permGL σ) with hg
  refine ⟨grpA O N lam g • z, ?_, ?_⟩
  · intro h0
    apply hz0
    have := congrArg (fun t => grpA O N lam g⁻¹ • t) h0
    simp only [smul_smul, grpA_inv_mul, one_smul, smul_zero] at this
    exact this
  · intro τ' a ha
    obtain ⟨b0, hb0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (w τ')
    obtain ⟨c, -, huniq⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (Function.update w τ (w τ ∘ σ) τ')
    have hconj : IsProj O N lam τ' (Function.update w τ (w τ ∘ σ) τ') (grp O N lam g * b0 * grp O N lam g⁻¹) := by
      apply isProj_conj O N lam g τ' (w τ') _ _ b0 hb0
      intro f
      by_cases hτ : τ' = τ
      · subst hτ
        have hgt : g τ' = permGL σ := by rw [hg, Pi.mulSingle_eq_same]
        rw [hgt, Function.update_self]
        simp only [Formalism.UG.dwAct, inv_inv]
        show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ') (Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f) =
          Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ' ∘ σ) f)
        rw [rowAct_permMat, rowAct_permMat, rowComp_rename_perm]
      · have hgt : g τ' = 1 := by rw [hg, Pi.mulSingle_eq_of_ne hτ]
        rw [hgt, Function.update_of_ne hτ, inv_one, (Formalism.UG.P.dual_weyl_action_mul O N N 1 1).2]
        rfl
    have haeq : (a : Module.End O (NablaT O N lam)) = grp O N lam g * b0 * grp O N lam g⁻¹ :=
      (huniq _ ha).trans (huniq _ hconj).symm
    set b : alg O N lam := ⟨b0, Algebra.subset_adjoin (Or.inr ⟨τ', w τ', hb0⟩)⟩ with hbdef
    have haeq' : a = grpA O N lam g * b * grpA O N lam g⁻¹ := Subtype.ext haeq
    rw [haeq', smul_smul, mul_assoc, grpA_inv_mul, mul_one, mul_smul, hz τ' b hb0]

/- English proof (translation)
Establish `hne : a ≠ b` using `fun e => by rw [e] at hab; omega`. Rewrite using `[← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b} (fun c : Fin N => (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c)]`. Establish `hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * v c = ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c hc`.

Simplify using `only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc`. Rewrite using `[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]`. Rewrite using `[hrest, Finset.sum_pair hne, Finset.sum_pair hne]`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Establish `hb : (b : ℕ) < N` using `b.isLt`.

Establish `hk : N - (a : ℕ) = (N - (b : ℕ)) + 1` using `by omega`. Rewrite using `[hk]`. Establish `: (N - (b : ℕ) + 1) * v a + (N - b) * v b < (N - (b : ℕ) + 1) * v b + (N - b) * v a` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_lt_swap {N : ℕ} (v : Fin N → ℕ) (a b : Fin N) (hab : (b : ℕ) = a + 1) (h : v a < v b) :
    ∑ c : Fin N, (N - (c : ℕ)) * v c < ∑ c : Fin N, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
  classical
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b} (fun c : Fin N => (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * v c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hb : (b : ℕ) < N := b.isLt
  have hk : N - (a : ℕ) = (N - (b : ℕ)) + 1 := by omega
  rw [hk]
  have : (N - (b : ℕ) + 1) * v a + (N - b) * v b < (N - (b : ℕ) + 1) * v b + (N - b) * v a := by nlinarith
  omega

/- English proof (translation)
Unfold `pot`. Apply `Finset.sum_lt_sum` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : i = τ`. Substitute `hi` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `(sum_lt_swap _ a b hab h).le`. Rewrite using `[Function.update_of_ne hi]`. Conclude with `⟨τ, Finset.mem_univ _, by rw [Function.update_self]; exact sum_lt_swap _ a b hab h⟩`.
-/
theorem pot_lt_swap {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → Fin N → ℕ) (τ : ι) (a b : Fin N)
    (hab : (b : ℕ) = a + 1) (h : w τ a < w τ b) : pot N w < pot N (Function.update w τ (w τ ∘ Equiv.swap a b)) := by
  unfold pot
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      exact (sum_lt_swap _ a b hab h).le
    · rw [Function.update_of_ne hi]
  · exact ⟨τ, Finset.mem_univ _, by rw [Function.update_self]; exact sum_lt_swap _ a b hab h⟩

/- English proof (translation)
Consider the cases of `N with`. Consider the case `zero => intro a`. Conclude with `a.elim0`. Consider the case `succ n => exact Fin.antitone_iff_succ_le.2 fun i => h i.castSucc i.succ (by simp)`.
-/
theorem antitone_of_adj {N : ℕ} (v : Fin N → ℕ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b ≤ v a) : Antitone v := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n => exact Fin.antitone_iff_succ_le.2 fun i => h i.castSucc i.succ (by simp)

/- English proof (translation)
Introduce `O _ _ _ _ N ι _ _ lam Gm _ _ w hw hmax τ`. Apply `antitone_of_adj` to reduce the goal to its premises. Introduce `a b hab`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `h1` using `hmax _ (jointWt_perm O N lam Gm w hw τ (Equiv.swap a b))`. Establish `h2` using `pot_lt_swap w τ a b hab hlt`. Use linear arithmetic over natural numbers and integers.
-/
theorem antitone_of_pot_max : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ),
    GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) →
    ∀ τ, Antitone (w τ) := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ w hw hmax τ
  apply antitone_of_adj
  intro a b hab
  by_contra hlt
  push_neg at hlt
  have h1 := hmax _ (jointWt_perm O N lam Gm w hw τ (Equiv.swap a b))
  have h2 := pot_lt_swap w τ a b hab hlt
  omega

end GlobalTheory.HighWt
