import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SignedActionTensor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {A : Fin n → Fin n → Module.End ℂ X}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `T _ _ hT`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hT`. Conclude with `⟨w, hw, hw0, 0, by simp⟩`.

Consider the case `insert a s ha ih`. Introduce `T hfd hst hT`. Establish `: Nontrivial T` using `Submodule.nontrivial_iff_ne_bot.mpr hT`. Set `f : Module.End ℂ T` to `(A a a).restrict (fun v hv => hst a v hv)`. Take `⟨lam, hlam⟩` from `Module.End.exists_eigenvalue f`.

Take `⟨v, hv⟩` from `hlam.exists_hasEigenvector`. Establish `hv1 : f v = lam • v` using `Module.End.mem_eigenspace_iff.mp hv.1`. Establish `hv2 : (v : X) ≠ 0` using `fun h => hv.2 (Subtype.ext h)`. Establish `hv3 : A a a v = lam • (v : X)`. Use `congrArg Subtype.val hv1` as an intermediate fact.

Simplify `this` using `[f]`. Set `T' : Submodule ℂ X` to `T ⊓ Module.End.eigenspace (A a a) lam`. Establish `hfd' : FiniteDimensional ℂ T'` using `Submodule.finiteDimensional_of_le inf_le_left`. Establish `hst' : ∀ c, ∀ u ∈ T', A c c u ∈ T'`. Introduce `c u hu`.

Use `⟨hst c u hu.1, ?_⟩` and prove the remaining obligations. Establish `h2 : A a a u = lam • u` using `Module.End.mem_eigenspace_iff.mp hu.2`. Use `show A c c u ∈ Module.End.eigenspace (A a a) lam`. Rewrite using `[Module.End.mem_eigenspace_iff, hcomm a c u, h2, map_smul]`. Establish `hT' : T' ≠ ⊥`.

Introduce `h`. Establish `: (v : X) ∈ T'` using `⟨v.2, Module.End.mem_eigenspace_iff.mpr hv3⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hv2 this`. Take `⟨w, hw, hw0, μ, hμ⟩` from `ih T' hfd' hst' hT'`.

Use `⟨w, hw.1, hw0, Function.update μ a lam, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Break down `Finset.mem_insert.mp hc with rfl | hc` into its components or cases. Rewrite using `[Function.update_self]`. Conclude with `Module.End.mem_eigenspace_iff.mp hw.2`.

Establish `hca : c ≠ a` using `fun h => ha (h ▸ hc)`. Rewrite using `[Function.update_of_ne hca]`. Conclude with `hμ c hc`.
-/
theorem exists_joint_eigenvector_alt (hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v)) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro T _ _ hT
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    exact ⟨w, hw, hw0, 0, by simp⟩
  | insert a s ha ih =>
    intro T hfd hst hT
    have : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hT
    let f : Module.End ℂ T := (A a a).restrict (fun v hv => hst a v hv)
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue f
    obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
    have hv1 : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hv2 : (v : X) ≠ 0 := fun h => hv.2 (Subtype.ext h)
    have hv3 : A a a v = lam • (v : X) := by
      have := congrArg Subtype.val hv1
      simpa [f] using this
    let T' : Submodule ℂ X := T ⊓ Module.End.eigenspace (A a a) lam
    have hfd' : FiniteDimensional ℂ T' := Submodule.finiteDimensional_of_le inf_le_left
    have hst' : ∀ c, ∀ u ∈ T', A c c u ∈ T' := by
      intro c u hu
      refine ⟨hst c u hu.1, ?_⟩
      have h2 : A a a u = lam • u := Module.End.mem_eigenspace_iff.mp hu.2
      show A c c u ∈ Module.End.eigenspace (A a a) lam
      rw [Module.End.mem_eigenspace_iff, hcomm a c u, h2, map_smul]
    have hT' : T' ≠ ⊥ := by
      intro h
      have : (v : X) ∈ T' := ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv3⟩
      rw [h, Submodule.mem_bot] at this
      exact hv2 this
    obtain ⟨w, hw, hw0, μ, hμ⟩ := ih T' hfd' hst' hT'
    refine ⟨w, hw.1, hw0, Function.update μ a lam, ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [Function.update_self]
      exact Module.End.mem_eigenspace_iff.mp hw.2
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      rw [Function.update_of_ne hca]
      exact hμ c hc

/- English proof (translation)
Establish `hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v)`. Introduce `a c v`. Establish `h` using `LinearMap.congr_fun (hK a a c c rfl rfl) v`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Distinguish the cases in `hac : a = c`.

Substitute `hac` using the available equality. Both sides reduce to the same expression. Simplify using `only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h`. Conclude with `h`. Establish `hshift : ∀ {μ : Fin n → ℝ} {w : X}, (∀ c, A c c w = (μ c : ℂ) • w) → ∀ {a b : Fin n}, a ≠ b → ε a = ε b → ∀ c, A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w`.

Introduce `μ w hw a b hab hεab c`. Establish `h` using `LinearMap.congr_fun (hK c c a b rfl hεab) w`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality.

Simplify using `[hab, Ne.symm hab] at h ⊢`. Take the linear combination `(norm := module) h`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Simplify using `[hca] at h ⊢`.

Take the linear combination `(norm := module) h`. Simplify using `[hca, hcb, Ne.symm hcb] at h ⊢`. Take the linear combination `(norm := module) h`. Establish `hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S` using `fun c => hS c c rfl`. Set `P : Set (Fin n → ℝ)` to `{μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}`.

Establish `hPfin : P.Finite`. Use `(Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)}) (fun c => (Module.End.finite_hasEigenvalue _).preimage (Complex.ofReal_injective.injOn))).subset ?_` and prove the remaining obligations. Introduce and unpack `μ ⟨w, hw, hw0, hμ⟩ c -`. Use `show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)`. Use `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `Subtype.ext (by simpa using hμ c)`. Introduce `h`. Conclude with `hw0 (congrArg Subtype.val h)`. Establish `hPne : P.Nonempty`.

Take `⟨w, hw, hw0, z, hz⟩` from `exists_joint_eigenvector_alt hcomm Finset.univ S hfd hSc hne`. Use `⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[hz c (Finset.mem_univ c)]`. Use `congr 1`. Conclude with `hreal c w (z c) hw0 (hz c (Finset.mem_univ c))`.

Take `⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩` from `Set.exists_max_image P kUnitWtLin hPfin hPne`. Use `⟨w, hw, hw0, μ, hμ, ?_⟩` and prove the remaining obligations. Introduce `a b hab hεab`. Assume the negation of the conclusion as `h`. Establish `hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P` using `⟨A a b w, hS a b hεab w hw, h, fun c => hshift hμ (ne_of_lt hab) hεab c⟩`.

Conclude with `absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))`.
-/
theorem exists_highestWeight_general (ε : Fin n → Bool)
    (hK : ∀ a b c d, ε a = ε b → ε c = ε d →
      A a b * A c d - A c d * A a b = (if b = c then A a d else 0) - (if d = a then A c b else 0))
    (hreal : ∀ c (w : X) (z : ℂ), w ≠ 0 → A c c w = z • w → z = ((z.re : ℝ) : ℂ))
    {S : Submodule ℂ X} (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v) := by
    intro a c v
    have h := LinearMap.congr_fun (hK a a c c rfl rfl) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    by_cases hac : a = c
    · subst hac; rfl
    · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
      exact h
  have hshift : ∀ {μ : Fin n → ℝ} {w : X}, (∀ c, A c c w = (μ c : ℂ) • w) → ∀ {a b : Fin n}, a ≠ b → ε a = ε b →
      ∀ c, A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
    intro μ w hw a b hab hεab c
    have h := LinearMap.congr_fun (hK c c a b rfl hεab) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
    by_cases hca : c = a
    · subst hca
      simp [hab, Ne.symm hab] at h ⊢
      linear_combination (norm := module) h
    · by_cases hcb : c = b
      · subst hcb
        simp [hca] at h ⊢
        linear_combination (norm := module) h
      · simp [hca, hcb, Ne.symm hcb] at h ⊢
        linear_combination (norm := module) h
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := exists_joint_eigenvector_alt hcomm Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact hreal c w (z c) hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => hshift hμ (ne_of_lt hab) hεab c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

end Gen

section Alg

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/- English proof (translation)
Establish `e1` using `hE a b c d`. Establish `e2` using `sgE_comm hC ε a b c d hab hcd`. Establish `h1` using `E_comm_sgE hEC ε a b c d`. Establish `h2` using `E_comm_sgE hEC ε c d a b`. Establish `key : (E a b + sgE ε cp cm a b) * (E c d + sgE ε cp cm c d) - (E c d + sgE ε cp cm c d) * (E a b + sgE ε cp cm a b) = (E a b * E c d - E c d * E a b) + (sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b)`.

Simplify using `only [add_mul, mul_add]`. Rewrite using `[h1, ← h2]`. Normalize the expressions using the abelian group laws. Unfold `diagE`. Rewrite using `[key, e1, e2]`.

Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem diagAction_commutator {W : Type*} [AddCommGroup W] [Module ℂ W] {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hE : IsGlRep E) (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    diagE ε E cp cm a b * diagE ε E cp cm c d - diagE ε E cp cm c d * diagE ε E cp cm a b =
      (if b = c then diagE ε E cp cm a d else 0) - (if d = a then diagE ε E cp cm c b else 0) := by
  have e1 := hE a b c d
  have e2 := sgE_comm hC ε a b c d hab hcd
  have h1 := E_comm_sgE hEC ε a b c d
  have h2 := E_comm_sgE hEC ε c d a b
  have key : (E a b + sgE ε cp cm a b) * (E c d + sgE ε cp cm c d) -
      (E c d + sgE ε cp cm c d) * (E a b + sgE ε cp cm a b) =
      (E a b * E c d - E c d * E a b) + (sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b) := by
    simp only [add_mul, mul_add]
    rw [h1, ← h2]
    abel
  unfold diagE
  rw [key, e1, e2]
  split_ifs <;> abel

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨v, hv⟩ ⊗ₜ f, by simp [TensorProduct.map_tmul]⟩`.
-/
theorem tmul_mem_tensorFock {S : Submodule ℂ N} {v : N} (hv : v ∈ S) (f : Fock n) :
    v ⊗ₜ f ∈ tensFock (n := n) S :=
  ⟨⟨v, hv⟩ ⊗ₜ f, by simp [TensorProduct.map_tmul]⟩

/- English proof (translation)
Rewrite using `[tcoef_expand y]`. Conclude with `Submodule.sum_mem _ fun s _ => tmul_mem_tensorFock (hy s) _`.
-/
theorem mem_tensorFock_of_coeffs {S : Submodule ℂ N} {y : TensorProduct ℂ N (Fock n)}
    (hy : ∀ s, tcoef ((fockBasis n).coord s) y ∈ S) : y ∈ tensFock S := by
  rw [tcoef_expand y]
  exact Submodule.sum_mem _ fun s _ => tmul_mem_tensorFock (hy s) _

/- English proof (translation)
Establish `: Module.Finite ℂ (Fock n)` using `Module.Finite.of_basis (fockBasis n)`. Conclude with `LinearMap.finiteDimensional_range _`.
-/
theorem tensorFock_finiteDimensional {S : Submodule ℂ N} (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (tensFock (n := n) S) := by
  have : Module.Finite ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  exact LinearMap.finiteDimensional_range _

/- English proof (translation)
Introduce `y hy`. Conclude with `mem_tensorFock_of_coeffs fun s => h (tcoef_mem hy _)`.
-/
theorem tensorFock_mono {S T : Submodule ℂ N} (h : S ≤ T) : tensFock (n := n) S ≤ tensFock T := by
  intro y hy
  exact mem_tensorFock_of_coeffs fun s => h (tcoef_mem hy _)

/- English proof (translation)
Take `⟨x, rfl⟩` from `hy`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v f`. Rewrite using `[diagE, LinearMap.add_apply, signedAction_tensor]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Simplify using `only [eT, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]`. Conclude with `tmul_mem_tensorFock (hS a b hab _ v.2) f`. Simplify using `only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, LinearMap.lTensor_tmul]`. Conclude with `tmul_mem_tensorFock v.2 _`.

Consider the case `add x x' hx hx'`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem hx hx'`.
-/
theorem tensorFock_diagAction_stable (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {S : Submodule ℂ N}
    (hS : IsKStableSub ε E S) {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ tensFock S) : diagE ε (eT E) cpT cmT a b y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v f =>
    rw [diagE, LinearMap.add_apply, signedAction_tensor]
    refine add_mem ?_ ?_
    · simp only [eT, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      exact tmul_mem_tensorFock (hS a b hab _ v.2) f
    · simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, LinearMap.lTensor_tmul]
      exact tmul_mem_tensorFock v.2 _
  | add x x' hx hx' =>
    rw [map_add, map_add]
    exact add_mem hx hx'

end Alg

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

/- English proof (translation)
Rewrite using `[← tform_conj y' (c • y), tform_smul_right, star_mul', tform_conj]`.
-/
theorem tensorForm_smul_left (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (c • y) y' = star c * tform y y' := by
  rw [← tform_conj y' (c • y), tform_smul_right, star_mul', tform_conj]

/- English proof (translation)
Unfold `sgE`. Establish `s1 : (ε b = true ∧ ε a = true) ↔ (ε a = true ∧ ε b = true)` using `and_comm`. Establish `s2 : (ε b = false ∧ ε a = false) ↔ (ε a = false ∧ ε b = false)` using `and_comm`. Simplify using `only [s1, s2]`. Use `split_ifs with h1 h2`.

Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, tform_sum_left, tform_sum_right]`. Use `sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[tform_cpT, tform_cmT]`. Simplify using `only [LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply, tform_neg_left, tform_neg_right, tform_sum_left, tform_sum_right]`. Use `congr 1`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tform_cpT, tform_cmT]`. Simplify using `[tform]`.
-/
theorem tensorForm_signedAction_adjoint (ε : Fin n → Bool) (a b : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (sgE ε cpT cmT a b y) y' = tform y (sgE ε cpT cmT b a y') := by
  unfold sgE
  have s1 : (ε b = true ∧ ε a = true) ↔ (ε a = true ∧ ε b = true) := and_comm
  have s2 : (ε b = false ∧ ε a = false) ↔ (ε a = false ∧ ε b = false) := and_comm
  simp only [s1, s2]
  split_ifs with h1 h2
  · simp only [LinearMap.sum_apply, Module.End.mul_apply, tform_sum_left, tform_sum_right]
    refine sum_congr rfl fun x _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp only [LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply, tform_neg_left,
      tform_neg_right, tform_sum_left, tform_sum_right]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp [tform]

/- English proof (translation)
Simplify using `only [diagE, LinearMap.add_apply, tform_add_left, tform_add_right, tform_eT hU, tensorForm_signedAction_adjoint]`. Simplify using `[adjSign, hab]`.
-/
theorem tensorForm_diagAction_adjoint {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {a b : Fin n} (hab : ε a = ε b) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (diagE ε (eT E) cpT cmT a b y) y' = tform y (diagE ε (eT E) cpT cmT b a y') := by
  simp only [diagE, LinearMap.add_apply, tform_add_left, tform_add_right, tform_eT hU, tensorForm_signedAction_adjoint]
  simp [adjSign, hab]

/- English proof (translation)
Use `exists_highestWeight_general ε (fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd) ?_ hfd hS hne` and prove the remaining obligations. Introduce `c w z hw0 hw`. Establish `h` using `tensorForm_diagAction_adjoint hU (a := c) (b := c) rfl w w`. Rewrite `h` using `[hw, tensorForm_smul_left, tform_smul_right]`. Establish `hne : tform w w ≠ 0` using `fun h0 => by`.

Use `tform_self_re_pos hw0` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `h2 : star z = z` using `mul_right_cancel₀ hne h`. Conclude with `(Complex.conj_eq_iff_re.mp h2).symm`.
-/
theorem exists_highestWeight_in_stable {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) {S : Submodule ℂ (TensorProduct ℂ M (Fock n))} (hfd : FiniteDimensional ℂ S)
    (hS : IsKStableSub ε (diagE ε (eT E) cpT cmT) S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε (diagE ε (eT E) cpT cmT) μ w := by
  refine exists_highestWeight_general ε (fun a b c d hab hcd =>
    diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd) ?_ hfd hS hne
  intro c w z hw0 hw
  have h := tensorForm_diagAction_adjoint hU (a := c) (b := c) rfl w w
  rw [hw, tensorForm_smul_left, tform_smul_right] at h
  have hne : tform w w ≠ 0 := fun h0 => by
    have := tform_self_re_pos hw0
    rw [h0] at this
    simp at this
  have h2 : star z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

end Form

end ReciprocityTheory.ChartRestriction.DS.TRGap
