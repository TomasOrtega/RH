import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

/- English proof (translation)
Introduce `Γ k _ _ _ n ρ hss g htr`. Set `σ : Γ →* Module.End k (Fin n → k)` to `(Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp ρ)`. Establish `hσ : ∀ h, σ h = Matrix.toLin' (ρ h : Matrix (Fin n) (Fin n) k)` using `fun h => rfl`. Set `A : Subalgebra k (Module.End k (Fin n → k))` to `Algebra.adjoin k (Set.range σ)`. Establish `hspan : ∀ a ∈ A, a ∈ Submodule.span k (Set.range σ)`.

Introduce `a ha`. Establish `h1 : a ∈ Subalgebra.toSubmodule A` using `ha`. Rewrite `h1` using `[Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]`. Conclude with `h1`. Establish `hinv : ∀ W : Submodule k (Fin n → k), Formalism.MainNotions.N.IsInv ρ W → ∀ a ∈ A, ∀ v ∈ W, a v ∈ W`.

Introduce `W hW a ha v hv`. It suffices to establish `H : ∀ b ∈ Submodule.span k (Set.range σ), b v ∈ W from H a (hspan a ha)`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b' hb'`.

Take `⟨h, rfl⟩` from `hb'`. Rewrite using `[hσ, Matrix.toLin'_apply]`. Conclude with `hW h v hv`. Consider the case `zero => simpa using W.zero_mem`. Consider the case `add b c _ _ hb hc => simpa using W.add_mem hb hc`.

Consider the case `smul c b _ hb => simpa using W.smul_mem c hb`. Establish `hssA : IsSemisimpleModule A (Fin n → k)`. Use `{ exists_isCompl := fun W => ?_ }` and prove the remaining obligations. Establish `hW : Formalism.MainNotions.N.IsInv ρ (W.restrictScalars k)`. Introduce `h v hv`.

Establish `hmem : σ h ∈ A` using `Algebra.subset_adjoin ⟨h, rfl⟩`. Use `W.smul_mem (⟨σ h, hmem⟩ : A) hv` as an intermediate fact. Conclude with `this`. Take `⟨W', hW'inv, hc⟩` from `hss _ hW`. Set `W'' : Submodule A (Fin n → k)` to `{ carrier := W' add_mem' := W'.add_mem zero_mem' := W'.zero_mem smul_mem' := fun a v hv => hinv W' hW'inv a a.2 v hv }`.

Use `⟨W'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `v hv hv'`. Conclude with `(Submodule.disjoint_def.mp hc.disjoint) v hv hv'`. Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`.

Introduce `v`. Establish `hv : v ∈ W.restrictScalars k ⊔ W'` using `by rw [hc.sup_eq_top]; trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hv`. Conclude with `Submodule.add_mem_sup hy hz`. Set `φ : A →ₗ[A] (Fin n → (Fin n → k))` to `{ toFun := fun a i => (a : Module.End k (Fin n → k)) (Pi.single i 1) map_add' := fun a b => by ext i j; simp map_smul' := fun a b => by ext i j; rfl }`.

Establish `hφ : Function.Injective φ`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(Pi.basisFun k (Fin n)).ext` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[Pi.basisFun_apply]`. Conclude with `congrFun hab i`. Establish `hssAA : IsSemisimpleModule A A` using `IsSemisimpleModule.of_injective φ hφ`. Establish `hgA : σ g ∈ A` using `Algebra.subset_adjoin ⟨g, rfl⟩`. Establish `hxA : σ g - 1 ∈ A` using `A.sub_mem hgA A.one_mem`.

Establish `htrace : ∀ a ∈ A, LinearMap.trace k (Fin n → k) (a * (σ g - 1)) = 0`. Introduce `a ha`. It suffices to establish `H : ∀ b ∈ Submodule.span k (Set.range σ), LinearMap.trace k (Fin n → k) (b * (σ g - 1)) = 0 from H a (hspan a ha)`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem b' hb'`. Take `⟨h, rfl⟩` from `hb'`. Rewrite using `[mul_sub, mul_one, ← map_mul, map_sub, hσ, hσ, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, htr, sub_self]`. Consider the case `zero => simp`. Consider the case `add b c _ _ hb hc => rw [add_mul, map_add, hb, hc, add_zero]`.

Consider the case `smul c b _ hb => rw [smul_mul_assoc, map_smul, hb, smul_zero]`. Set `x' : A` to `⟨σ g - 1, hxA⟩`. Take `⟨L', hL⟩` from `exists_isCompl (Submodule.span A {x'})`. Establish `h1 : (1 : A) ∈ Submodule.span A {x'} ⊔ L'` using `by rw [hL.sup_eq_top]; trivial`. Take `⟨e, he, e', he', hee⟩` from `Submodule.mem_sup.mp h1`.

Establish `he'eq : e' = 1 - e` using `by rw [← hee]; abel`. Establish `key : ∀ l ∈ Submodule.span A {x'}, l * e = l`. Introduce `l hl`. Establish `h2 : l * e' ∈ L'` using `L'.smul_mem l he'`. Establish `h5 : l * e' = l - l * e` using `by rw [he'eq, mul_sub, mul_one]`.

Establish `h3 : l * e' ∈ Submodule.span A {x'}`. Rewrite using `[h5]`. Conclude with `Submodule.sub_mem _ hl (Submodule.smul_mem _ l he)`. Establish `h4` using `(Submodule.disjoint_def.mp hL.disjoint) _ h3 h2`. Rewrite `h4` using `[h5, sub_eq_zero]`.

Conclude with `h4.symm`. Establish `hidem : e * e = e` using `key e he`. Take `⟨y, hy⟩` from `Submodule.mem_span_singleton.mp he`. Establish `htr_e : LinearMap.trace k (Fin n → k) (e : Module.End k (Fin n → k)) = 0`. Rewrite using `[← hy]`.

Conclude with `htrace _ y.2`. Establish `hI : IsIdempotentElem (e : Module.End k (Fin n → k))` using `congrArg Subtype.val hidem`. Establish `he0 : (e : Module.End k (Fin n → k)) = 0` using `by first`. Consider the case `exact (LinearMap.IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e`. Consider the case `exact (IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e`.

Establish `he0' : e = 0` using `Subtype.ext he0`. Establish `hx0 : x' = 0`. Rewrite using `[← key x' (Submodule.mem_span_singleton_self x'), he0', mul_zero]`. Establish `hx1 : σ g - 1 = 0` using `congrArg Subtype.val hx0`. Apply `Units.ext` to reduce the goal to its premises.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Units.val_one, Matrix.toLin'_one, ← hσ]`. Conclude with `sub_eq_zero.mp hx1`.
-/
theorem UpperTheory.eq_one_of_trace_translation_invariant_semisimple :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ : Γ →* GL (Fin n) k), Formalism.MainNotions.N.IsSSRep ρ → ∀ g : Γ, (∀ h : Γ, (ρ (h * g) : Matrix (Fin n) (Fin n) k).trace = (ρ h : Matrix (Fin n) (Fin n) k).trace) → ρ g = 1 := by
  intro Γ k _ _ _ n ρ hss g htr
  classical
  let σ : Γ →* Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp ρ)
  have hσ : ∀ h, σ h = Matrix.toLin' (ρ h : Matrix (Fin n) (Fin n) k) := fun h => rfl
  let A : Subalgebra k (Module.End k (Fin n → k)) := Algebra.adjoin k (Set.range σ)
  have hspan : ∀ a ∈ A, a ∈ Submodule.span k (Set.range σ) := by
    intro a ha
    have h1 : a ∈ Subalgebra.toSubmodule A := ha
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq] at h1
    exact h1
  have hinv : ∀ W : Submodule k (Fin n → k), Formalism.MainNotions.N.IsInv ρ W →
      ∀ a ∈ A, ∀ v ∈ W, a v ∈ W := by
    intro W hW a ha v hv
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ), b v ∈ W from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [hσ, Matrix.toLin'_apply]
      exact hW h v hv
    | zero => simpa using W.zero_mem
    | add b c _ _ hb hc => simpa using W.add_mem hb hc
    | smul c b _ hb => simpa using W.smul_mem c hb
  have hssA : IsSemisimpleModule A (Fin n → k) := by
    refine { exists_isCompl := fun W => ?_ }
    have hW : Formalism.MainNotions.N.IsInv ρ (W.restrictScalars k) := by
      intro h v hv
      have hmem : σ h ∈ A := Algebra.subset_adjoin ⟨h, rfl⟩
      have := W.smul_mem (⟨σ h, hmem⟩ : A) hv
      exact this
    obtain ⟨W', hW'inv, hc⟩ := hss _ hW
    let W'' : Submodule A (Fin n → k) :=
      { carrier := W'
        add_mem' := W'.add_mem
        zero_mem' := W'.zero_mem
        smul_mem' := fun a v hv => hinv W' hW'inv a a.2 v hv }
    refine ⟨W'', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro v hv hv'
      exact (Submodule.disjoint_def.mp hc.disjoint) v hv hv'
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      have hv : v ∈ W.restrictScalars k ⊔ W' := by rw [hc.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      exact Submodule.add_mem_sup hy hz
  let φ : A →ₗ[A] (Fin n → (Fin n → k)) :=
    { toFun := fun a i => (a : Module.End k (Fin n → k)) (Pi.single i 1)
      map_add' := fun a b => by ext i j; simp
      map_smul' := fun a b => by ext i j; rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply (Pi.basisFun k (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact congrFun hab i
  have hssAA : IsSemisimpleModule A A := IsSemisimpleModule.of_injective φ hφ
  have hgA : σ g ∈ A := Algebra.subset_adjoin ⟨g, rfl⟩
  have hxA : σ g - 1 ∈ A := A.sub_mem hgA A.one_mem
  have htrace : ∀ a ∈ A, LinearMap.trace k (Fin n → k) (a * (σ g - 1)) = 0 := by
    intro a ha
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ),
        LinearMap.trace k (Fin n → k) (b * (σ g - 1)) = 0 from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [mul_sub, mul_one, ← map_mul, map_sub, hσ, hσ, Matrix.trace_toLin'_eq,
        Matrix.trace_toLin'_eq, htr, sub_self]
    | zero => simp
    | add b c _ _ hb hc => rw [add_mul, map_add, hb, hc, add_zero]
    | smul c b _ hb => rw [smul_mul_assoc, map_smul, hb, smul_zero]
  let x' : A := ⟨σ g - 1, hxA⟩
  obtain ⟨L', hL⟩ := exists_isCompl (Submodule.span A {x'})
  have h1 : (1 : A) ∈ Submodule.span A {x'} ⊔ L' := by rw [hL.sup_eq_top]; trivial
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp h1
  have he'eq : e' = 1 - e := by rw [← hee]; abel
  have key : ∀ l ∈ Submodule.span A {x'}, l * e = l := by
    intro l hl
    have h2 : l * e' ∈ L' := L'.smul_mem l he'
    have h5 : l * e' = l - l * e := by rw [he'eq, mul_sub, mul_one]
    have h3 : l * e' ∈ Submodule.span A {x'} := by
      rw [h5]
      exact Submodule.sub_mem _ hl (Submodule.smul_mem _ l he)
    have h4 := (Submodule.disjoint_def.mp hL.disjoint) _ h3 h2
    rw [h5, sub_eq_zero] at h4
    exact h4.symm
  have hidem : e * e = e := key e he
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp he
  have htr_e : LinearMap.trace k (Fin n → k) (e : Module.End k (Fin n → k)) = 0 := by
    rw [← hy]
    exact htrace _ y.2
  have hI : IsIdempotentElem (e : Module.End k (Fin n → k)) := congrArg Subtype.val hidem
  have he0 : (e : Module.End k (Fin n → k)) = 0 := by
    first
    | exact (LinearMap.IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
    | exact (IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
  have he0' : e = 0 := Subtype.ext he0
  have hx0 : x' = 0 := by
    rw [← key x' (Submodule.mem_span_singleton_self x'), he0', mul_zero]
  have hx1 : σ g - 1 = 0 := congrArg Subtype.val hx0
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one, ← hσ]
  exact sub_eq_zero.mp hx1
