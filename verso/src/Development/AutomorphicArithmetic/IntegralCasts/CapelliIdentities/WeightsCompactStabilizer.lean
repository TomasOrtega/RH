import Mathlib

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b = (if b = c then E a d else (0 : A)) - if d = a then E c b else (0 : A)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit :
    {n : ℕ} →
      {V : Type} →
        [inst : NormedAddCommGroup V] →
          [inst_1 : InnerProductSpace ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Prop :=
    fun {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
        (E : Fin n → Fin n → Module.End ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ (x y : V), Inner.inner ℂ ((E a b : V → V) x) y = Inner.inner ℂ x ((E b a : V → V) y)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Submodule ℂ V → Prop :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
        (S : Submodule ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ v ∈ S, (E a b : V → V) v ∈ S

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight.{u_1} :
    {V : Type u_1} →
      [inst : AddCommGroup V] →
        [inst_1 : _root_.Module ℂ V] → {n : ℕ} → (Fin n → Fin n → Module.End ℂ V) → (Fin n → ℝ) → V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ)
        (w : V) ↦
      ∀ (a : Fin n), (E a a : V → V) w = (↑(μ a) : ℂ) • w

/- English proof (translation)
Introduce `n ε V _ _ E hG hU Q _ hS hQ`. Set `T : Fin n → Module.End ℂ Q` to `fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)`. Establish `hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x` using `fun a x => rfl`. Establish `hsym : ∀ a, (T a).IsSymmetric`. Introduce `a x y`.

Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, hT, hT]`. Conclude with `hU a a rfl x y`. Establish `hcomm : Pairwise (Function.onFun Commute T)`. Introduce `a b hab`. Establish `h` using `hG a a b b`.

Rewrite `h` using `[if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `T a * T b = T b * T a`. Use extensionality with `x`. Use `congrArg (fun f : Module.End ℂ V => f x) h` as an intermediate fact. Simplify `this` using `[hT]`.

Establish `htop` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm`. Establish `hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Rewrite `htop` using `[iSup_eq_bot.mpr hcon]`.

Establish `: Nontrivial Q` using `Submodule.nontrivial_iff_ne_bot.mpr hQ`. Conclude with `bot_ne_top htop`. Take `⟨α, hα⟩` from `hex`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hα`. Establish `hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a)` using `fun a => (Submodule.mem_iInf _).mp hx a`.

Establish `hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a` using `fun a => Complex.conj_eq_iff_re.mp ((hsym a).conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))`. Use `⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))`. Rewrite `h` using `[hT]`. Rewrite using `[hre a, h]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight :
    ∀ {n : ℕ} {ε : Fin n → Bool} {V : Type} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℂ V]
      {E : Fin n → Fin n → Module.End ℂ V},
      UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel E →
        UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit ε E →
          ∀ {Q : Submodule ℂ V} [FiniteDimensional ℂ ↥Q],
            UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab ε E Q → Q ≠ ⊥ → ∃ (ν : Fin n → ℝ), ∃ x ∈ Q, x ≠ (0 : V) ∧ UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight E ν x := by
  intro n ε V _ _ E hG hU Q _ hS hQ
  classical
  let T : Fin n → Module.End ℂ Q := fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)
  have hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x := fun a x => rfl
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT]
    exact hU a a rfl x y
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a b hab
    have h := hG a a b b
    rw [if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero] at h
    change T a * T b = T b * T a
    ext x
    have := congrArg (fun f : Module.End ℂ V => f x) h
    simpa [hT] using this
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact bot_ne_top htop
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a) := fun a =>
    (Submodule.mem_iInf _).mp hx a
  have hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a := fun a =>
    Complex.conj_eq_iff_re.mp
      ((hsym a).conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))
  refine ⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩
  have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))
  rw [hT] at h
  rw [hre a, h]
  rfl
