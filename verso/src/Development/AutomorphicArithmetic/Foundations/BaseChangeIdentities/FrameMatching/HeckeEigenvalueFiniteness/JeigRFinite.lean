import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinearIndependentEigenvectors

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.HeckeLevelFrameExistence.Ev

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem fix_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) {v : V}
    (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem hk_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) (f : G → ℂ) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem hk_lin (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ∃ T : V →ₗ[ℂ] V, ∀ v, hkG ρ K f v = T v := by
  by_cases h : (Function.support fun q : G ⧸ K => f q.out).Finite
  · refine ⟨∑ q ∈ h.toFinset, f q.out • ρ q.out, fun v => ?_⟩
    unfold hkG
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset), LinearMap.sum_apply]
    · rfl
    · intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp only [h0, zero_smul]
  · refine ⟨0, fun v => ?_⟩
    unfold hkG
    by_cases hv : v = 0
    · simp [hv]
    · refine finsum_of_infinite_support fun hfin => h (hfin.subset fun q hq h0 => ?_)
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hq h1
      · apply hv
        have := congrArg (ρ q.out⁻¹) h1
        rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem li_eig {Ξ P : Type} (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ) (hinj : Function.Injective ev) (v : Ξ → V)
    (h0 : ∀ ξ, v ξ ≠ 0) (hv : ∀ ξ p, T p (v ξ) = ev ξ p • v ξ) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fin_eig {Ξ P : Type} (U : Submodule ℂ V) [FiniteDimensional ℂ U] (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ)
    (hinj : Function.Injective ev) : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}.Finite := by
  choose v hU h0 hv using fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ξ.2
  have h := li_eig T (fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ev ξ.1)
    (hinj.comp Subtype.val_injective) v h0 hv
  have h' : LinearIndependent ℂ fun ξ => (⟨v ξ, hU ξ⟩ : U) := LinearIndependent.of_comp U.subtype h
  haveI := h'.finite_of_isNoetherian
  exact Set.toFinite _

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def JEigR {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V)
    (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem jeigR_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {w : Pl E}
    {ρ : Representation ℂ (GLw a w × GLw b w) V} {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ)
    {ϖ : (w.adicCompletion E)ˣ} {ξa : Fin a → ℂˣ} {ξb : Fin b → ℂˣ} (h : JEigR w ρ ϖ ξa ξb) :
    JEigR w σ ϖ ξa ξb := by
  obtain ⟨v, hv, hv0, he⟩ := h
  refine ⟨φ.toLinearEquiv v, fix_map φ _ hv, fun h0 => hv0 (φ.toLinearEquiv.injective (by rw [h0, map_zero])),
    fun x y hx hy => ?_⟩
  rw [← hk_map, he x y hx hy, map_smul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem qh_ne_zero (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  have hq : qV E w ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero hq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pw_ne_zero {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) : pw y x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => Units.ne_zero _

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem pw_shift {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) (i : Fin m) :
    pw y (fun j => x j + if j = i then 1 else 0) = pw y x * (y i : ℂ) := by
  have key : ∀ j, (((y j ^ (x j + if j = i then 1 else 0) : ℂˣ)) : ℂ) =
      ((y j ^ x j : ℂˣ) : ℂ) * (if j = i then (y i : ℂ) else 1) := by
    intro j
    by_cases h : j = i
    · subst h
      simp [_root_.zpow_add]
    · simp [h]
  simp only [pw, key, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

def g0 (m : ℕ) : Fin m → ℤ := fun i => 2 * ((m : ℤ) - (i : ℕ))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem gap0 (m : ℕ) : Gap (g0 m) := by
  intro i j hij
  have := Fin.lt_def.1 hij
  simp only [g0]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gap1 (m : ℕ) (i : Fin m) : Gap (fun j => g0 m j + if j = i then 1 else 0) := by
  intro j l hjl
  have := Fin.lt_def.1 hjl
  simp only [g0]
  split_ifs <;> omega

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem ev2_inj (w : Pl E) : Function.Injective (fun (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ))
    (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) => ev2 w ξ.1 ξ.2 p.1.1 p.1.2) := by
  rintro ⟨ξa, ξb⟩ ⟨ξa', ξb'⟩ h
  have hx : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ), Gap x → Gap y → ev2 w ξa ξb x y = ev2 w ξa' ξb' x y :=
    fun x y hx hy => congrFun h ⟨(x, y), hx, hy⟩
  have hd : ∀ {N : ℕ} (x : Fin N → ℤ), dl w x ≠ 0 := fun _ => zpow_ne_zero _ (qh_ne_zero w)
  have h0 := hx (g0 a) (g0 b) (gap0 a) (gap0 b)
  simp only [ev2] at h0
  have hM : pw ξa (g0 a) * pw ξb (g0 b) = pw ξa' (g0 a) * pw ξb' (g0 b) := by
    refine mul_left_cancel₀ (mul_ne_zero (hd (g0 a)) (hd (g0 b))) ?_
    linear_combination h0
  have hM0 : pw ξa' (g0 a) * pw ξb' (g0 b) ≠ 0 := mul_ne_zero (pw_ne_zero _ _) (pw_ne_zero _ _)
  refine Prod.ext (funext fun i => Units.ext ?_) (funext fun i => Units.ext ?_)
  · have h1 := hx _ (g0 b) (gap1 a i) (gap0 b)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (fun j => g0 a j + if j = i then 1 else 0))
      (hd (g0 b))) hM0) ?_
    linear_combination h1 - (dl w (fun j => g0 a j + if j = i then 1 else 0) * dl w (g0 b) * (ξa i : ℂ)) * hM
  · have h1 := hx (g0 a) _ (gap0 a) (gap1 b i)
    simp only [ev2, pw_shift] at h1
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (g0 a))
      (hd (fun j => g0 b j + if j = i then 1 else 0))) hM0) ?_
    linear_combination h1 - (dl w (g0 a) * dl w (fun j => g0 b j + if j = i then 1 else 0) * (ξb i : ℂ)) * hM

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem jeigR_finite {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E)
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ϖ : (w.adicCompletion E)ˣ)
    [FiniteDimensional ℂ (fixed ρ (I2 a b w))] :
    {ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JEigR w ρ ϖ ξ.1 ξ.2}.Finite := by
  choose T hT using fun (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) =>
    hk_lin ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2)
  refine (fin_eig (fixed ρ (I2 a b w)) T _ (ev2_inj w)).subset ?_
  rintro ⟨ξa, ξb⟩ ⟨v, hv, hv0, he⟩
  exact ⟨v, hv, hv0, fun p => by rw [← hT]; exact he _ _ p.2.1 p.2.2⟩

end UpperTheory.HeckeLevelFrameExistence.Ev

end
