import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

/- English proof (translation)
Use `set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef`. Set `e : E ≃+* T.F` to `{ toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩ invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl map_add' := fun _ _ => rfl }`. Use `haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm`. Establish `hEM : E ≤ maximalRealSubfield T.L` using `IsTotallyReal.le_maximalRealSubfield E`. Establish `hdE : Module.finrank ℚ E = Module.finrank ℚ T.F` using `(RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq`.

Establish `hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2`. Establish `h1` using `IntermediateField.finrank_sup_le T.F T.K`. Rewrite `h1` using `[T.degK, ← T.hL]`. Conclude with `h1`. Establish `hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L`.

Rewrite using `[← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]`. Conclude with `Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L`. Establish `hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L` using `Module.finrank_mul_finrank ℚ E T.L`. Establish `hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L)` using `LinearMap.finrank_le_finrank_of_injective (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective`. Establish `hpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`.

Establish `hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L)` using `Module.finrank_pos`. Establish `hdeg : Module.finrank E T.L = 2`. Apply `le_antisymm` to reduce the goal to its premises. Establish `: Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2`. Rewrite using `[hE2, hdE]`.

Conclude with `hsup`. Conclude with `Nat.le_of_mul_le_mul_left this hpos`. Establish `: Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤ Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L`. Rewrite using `[hM, ← hE2]`. Conclude with `Nat.mul_le_mul_right _ hle`.

Conclude with `Nat.le_of_mul_le_mul_left this hposM`. Use `haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }`. Establish `hEq : E = maximalRealSubfield T.L` using `NumberField.CMExtension.eq_maximalRealSubfield T.L E`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L`. Rewrite using `[← hEq]`. Conclude with `hx`. Conclude with `⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`.

Establish `hy : (y : T.L) ∈ E` using `by rw [hEq]; exact y.2`. Conclude with `hy`.
-/
private theorem plus_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (x : Ω) : x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x := by
  classical
  set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef
  let e : E ≃+* T.F :=
    { toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩
      invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm
  have hEM : E ≤ maximalRealSubfield T.L := IsTotallyReal.le_maximalRealSubfield E
  have hdE : Module.finrank ℚ E = Module.finrank ℚ T.F :=
    (RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq
  have hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2 := by
    have h1 := IntermediateField.finrank_sup_le T.F T.K
    rw [T.degK, ← T.hL] at h1
    exact h1
  have hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]
    exact Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L
  have hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L :=
    Module.finrank_mul_finrank ℚ E T.L
  have hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L) := Module.finrank_pos
  have hdeg : Module.finrank E T.L = 2 := by
    apply le_antisymm
    · have : Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2 := by
        rw [hE2, hdE]; exact hsup
      exact Nat.le_of_mul_le_mul_left this hpos
    · have : Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤
          Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L := by
        rw [hM, ← hE2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left this hposM
  haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }
  have hEq : E = maximalRealSubfield T.L := NumberField.CMExtension.eq_maximalRealSubfield T.L E
  constructor
  · intro hx
    have hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L := by
      rw [← hEq]; exact hx
    exact ⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : T.L) ∈ E := by rw [hEq]; exact y.2
    exact hy

/- English proof (translation)
Establish `hF : resQ T.F τ ∈ T.F.fixingSubgroup`. Rewrite using `[IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]`. Introduce `y hy`. Conclude with `τ.commutes ⟨y, hy⟩`. Unfold `Tower.GalL`.

Rewrite using `[Subgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Establish `hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup`. Rewrite using `[IntermediateField.fixingSubgroup_sup]`.

Conclude with `⟨hF, h⟩`. Rewrite `hsup` using `[← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]`. Conclude with `hsup x x.2`. Introduce `h`. Rewrite using `[IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]`.

Introduce `y hy`. Conclude with `h ⟨y, Lk.K_le T hy⟩`.
-/
private theorem fix_L {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (τ : G T.F Ω) : τ ∈ T.GalL ↔ ∀ x : T.L, τ (x : Ω) = x := by
  have hF : resQ T.F τ ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  unfold Tower.GalL
  rw [Subgroup.mem_comap]
  constructor
  · intro h x
    have hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, h⟩
    rw [← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hsup
    exact hsup x x.2
  · intro h
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact h ⟨y, Lk.K_le T hy⟩

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T`. Establish `hP` using `plus_eq T`. Use `⟨hP, ?_, ?_⟩` and prove the remaining obligations. Set `φ : G (W.Lp T.L) Ω ≃* G T.F Ω` to `{ toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by`. Take `⟨y, hy⟩` from `(hP (x : Ω)).1 x.2`.

Express the relevant statement in the definitionally equal form `σ (x : Ω) = (x : Ω)`. Rewrite using `[← hy]`. Conclude with `σ.commutes y)`. Use `invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by`. Establish `hx` using `(hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩`.

Conclude with `σ.commutes ⟨_, hx⟩)`. Use `left_inv := fun σ => by ext; rfl`. Use `right_inv := fun σ => by ext; rfl`. Use the proof step `map_mul' := fun σ τ => by ext; rfl }`. Use `⟨φ, fun σ x => rfl, fun σ => ?_⟩` and prove the remaining obligations.

Rewrite using `[fix_L, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩`. Introduce and unpack `⟨ρ, rfl⟩ x`.

Conclude with `ρ.commutes x`. Introduce `τ`. Rewrite using `[fix_L, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩`. Introduce and unpack `⟨ρ, rfl⟩ x`. Conclude with `ρ.commutes x`.
-/
theorem UpperTheory.V.Ws.Lk.galEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), (∀ x : Ω, x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x) ∧ (∃ φ : G (W.Lp T.L) Ω ≃* G T.F Ω, (∀ σ x, φ σ x = σ x) ∧ ∀ σ, φ σ ∈ T.GalL ↔ σ ∈ (W.resP T.L Ω).range) ∧ ∀ τ : G T.F Ω, τ ∈ T.GalL ↔ τ ∈ (resLe T.F_le).range := by
  intro Ω _ _ _ l _ c D T
  have hP := plus_eq T
  refine ⟨hP, ?_, ?_⟩
  · let φ : G (W.Lp T.L) Ω ≃* G T.F Ω :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by
            obtain ⟨y, hy⟩ := (hP (x : Ω)).1 x.2
            change σ (x : Ω) = (x : Ω)
            rw [← hy]
            exact σ.commutes y)
        invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by
            have hx := (hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
            exact σ.commutes ⟨_, hx⟩)
        left_inv := fun σ => by ext; rfl
        right_inv := fun σ => by ext; rfl
        map_mul' := fun σ τ => by ext; rfl }
    refine ⟨φ, fun σ x => rfl, fun σ => ?_⟩
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
  · intro τ
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
