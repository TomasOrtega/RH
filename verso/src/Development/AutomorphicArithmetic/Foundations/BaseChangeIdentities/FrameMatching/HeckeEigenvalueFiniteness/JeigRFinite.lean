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
Introduce `h`. Establish `h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v` using `hv h`. Rewrite using `[Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining, ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]`. Both sides reduce to the same expression.
-/
theorem fix_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) {v : V}
    (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

/- English proof (translation)
Unfold `hkG`. Use `(φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)`. Rewrite using `[map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply, φ.toIntertwiningMap.isIntertwining]`.
-/
theorem hk_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) (f : G → ℂ) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

/- English proof (translation)
Distinguish the cases in `h : (Function.support fun q : G ⧸ K => f q.out).Finite`. Use `⟨∑ q ∈ h.toFinset, f q.out • ρ q.out, fun v => ?_⟩` and prove the remaining obligations. Unfold `hkG`. Rewrite using `[finsum_eq_sum_of_support_subset (s := h.toFinset), LinearMap.sum_apply]`. Both sides reduce to the same expression.

Introduce `q hq`. Rewrite using `[Set.Finite.coe_toFinset]`. Introduce `h0`. Apply `hq` to reduce the goal to its premises. Simplify using `only [h0, zero_smul]`.

Use `⟨0, fun v => ?_⟩` and prove the remaining obligations. Unfold `hkG`. Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Use `finsum_of_infinite_support fun hfin => h (hfin.subset fun q hq h0 => ?_)` and prove the remaining obligations.

Break down `smul_eq_zero.1 h0 with h1 | h1` into its components or cases. Conclude with `hq h1`. Apply `hv` to reduce the goal to its premises. Use `congrArg (ρ q.out⁻¹) h1` as an intermediate fact. Rewrite `this` using `[map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis.
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
The claim follows from `_root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv`.
-/
theorem li_eig {Ξ P : Type} (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ) (hinj : Function.Injective ev) (v : Ξ → V)
    (h0 : ∀ ξ, v ξ ≠ 0) (hv : ∀ ξ p, T p (v ξ) = ev ξ p • v ξ) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv

/- English proof (translation)
Use `choose v hU h0 hv using fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ξ.2`. Establish `h` using `li_eig T (fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ev ξ.1) (hinj.comp Subtype.val_injective) v h0 hv`. Establish `h' : LinearIndependent ℂ fun ξ => (⟨v ξ, hU ξ⟩ : U)` using `LinearIndependent.of_comp U.subtype h`. Use `haveI := h'.finite_of_isNoetherian`. Conclude with `Set.toFinite _`.
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
Take `⟨v, hv, hv0, he⟩` from `h`. Use `⟨φ.toLinearEquiv v, fix_map φ _ hv, fun h0 => hv0 (φ.toLinearEquiv.injective (by rw [h0, map_zero])), fun x y hx hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← hk_map, he x y hx hy, map_smul]`.
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
Unfold `qh`. Rewrite using `[Complex.ofReal_ne_zero, Real.sqrt_ne_zero']`. Establish `hq : qV E w ≠ 0`. Conclude with `Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot`. Conclude with `Nat.pos_of_ne_zero hq` after adjusting the coercions.
-/
theorem qh_ne_zero (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  have hq : qV E w ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero hq

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun j _ => Units.ne_zero _`.
-/
theorem pw_ne_zero {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) : pw y x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => Units.ne_zero _

/- English proof (translation)
Establish `key : ∀ j, (((y j ^ (x j + if j = i then 1 else 0) : ℂˣ)) : ℂ) = ((y j ^ x j : ℂˣ) : ℂ) * (if j = i then (y i : ℂ) else 1)`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[_root_.zpow_add]`.

Simplify using `[h]`. Simplify using `only [pw, key, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]`.
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
Introduce `i j hij`. Use `Fin.lt_def.1 hij` as an intermediate fact. Simplify using `only [g0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gap0 (m : ℕ) : Gap (g0 m) := by
  intro i j hij
  have := Fin.lt_def.1 hij
  simp only [g0]
  omega

/- English proof (translation)
Introduce `j l hjl`. Use `Fin.lt_def.1 hjl` as an intermediate fact. Simplify using `only [g0]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem gap1 (m : ℕ) (i : Fin m) : Gap (fun j => g0 m j + if j = i then 1 else 0) := by
  intro j l hjl
  have := Fin.lt_def.1 hjl
  simp only [g0]
  split_ifs <;> omega

/- English proof (translation)
Introduce and unpack `⟨ξa, ξb⟩ ⟨ξa', ξb'⟩ h`. Establish `hx : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ), Gap x → Gap y → ev2 w ξa ξb x y = ev2 w ξa' ξb' x y` using `fun x y hx hy => congrFun h ⟨(x, y), hx, hy⟩`. Establish `hd : ∀ {N : ℕ} (x : Fin N → ℤ), dl w x ≠ 0` using `fun _ => zpow_ne_zero _ (qh_ne_zero w)`. Establish `h0` using `hx (g0 a) (g0 b) (gap0 a) (gap0 b)`. Simplify using `only [ev2] at h0`.

Establish `hM : pw ξa (g0 a) * pw ξb (g0 b) = pw ξa' (g0 a) * pw ξb' (g0 b)`. Use `mul_left_cancel₀ (mul_ne_zero (hd (g0 a)) (hd (g0 b))) ?_` and prove the remaining obligations. Take the linear combination `h0`. Establish `hM0 : pw ξa' (g0 a) * pw ξb' (g0 b) ≠ 0` using `mul_ne_zero (pw_ne_zero _ _) (pw_ne_zero _ _)`. Use `Prod.ext (funext fun i => Units.ext ?_) (funext fun i => Units.ext ?_)` and prove the remaining obligations.

Establish `h1` using `hx _ (g0 b) (gap1 a i) (gap0 b)`. Simplify using `only [ev2, pw_shift] at h1`. Use `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (fun j => g0 a j + if j = i then 1 else 0)) (hd (g0 b))) hM0) ?_` and prove the remaining obligations. Take the linear combination `h1 - (dl w (fun j => g0 a j + if j = i then 1 else 0) * dl w (g0 b) * (ξa i : ℂ)) * hM`. Establish `h1` using `hx (g0 a) _ (gap0 a) (gap1 b i)`.

Simplify using `only [ev2, pw_shift] at h1`. Use `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hd (g0 a)) (hd (fun j => g0 b j + if j = i then 1 else 0))) hM0) ?_` and prove the remaining obligations. Take the linear combination `h1 - (dl w (g0 a) * dl w (fun j => g0 b j + if j = i then 1 else 0) * (ξb i : ℂ)) * hM`.
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
Use `choose T hT using fun (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) => hk_lin ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2)`. Use `(fin_eig (fixed ρ (I2 a b w)) T _ (ev2_inj w)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨ξa, ξb⟩ ⟨v, hv, hv0, he⟩`. Conclude with `⟨v, hv, hv0, fun p => by rw [← hT]; exact he _ _ p.2.1 p.2.2⟩`.
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
