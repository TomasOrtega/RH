import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Apply the tactic sequence `first | exact Iff.rfl | simp [Data.Λp, Data.hermL]`.
-/
lemma mem_orthogonal_lattice_iff {r : ℕ} (X : Data E r) (ξ v : Fin r → E) :
    v ∈ X.Λp ξ ↔ v ∈ X.Λ ∧ herm X.Gm v ξ = 0 := by first | exact Iff.rfl | simp [Data.Λp, Data.hermL]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(funext i; simp [Algebra.smul_def])`.
-/
lemma integer_smul_eq_coe_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  first
    | rfl
    | (funext i; simp [Algebra.smul_def])

/- English proof (translation)
Unfold `EFf herm`. Rewrite using `[integer_smul_eq_coe_smul]`. Use `congr 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma trace_form_integer_smul {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E)
    (β : 𝓞 E) :
    EFf ξ0 G x (β • y) = Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) := by
  unfold EFf herm
  rw [integer_smul_eq_coe_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0` using `fun β => (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)`. Establish `hinv : ∀ a : E, cc (cc a) = a`. Establish `h2` using `pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)`. Rewrite `h2` using `[NumberField.IsCMField.orderOf_complexConj, pow_two]`. Introduce `a`.

Use `congrArg (fun σ => σ a) h2` as an intermediate fact. Simplify `this` using `[cc]`. Establish `hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0`. Introduce `w`. Rewrite using `[← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]`.

Simplify using `only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[NumberField.integralBasis_apply]`. Use `hb ((NumberField.RingOfIntegers.basis E) i)` as an intermediate fact. Simplify using `only [cc] at this`.

Rewrite using `[smul_eq_zero]`. Conclude with `Or.inr this`. Establish `hz : -ξ0 * herm G x y = 0`. Establish `hnd` using `traceForm_nondegenerate ℚ E`. Establish `hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0` using `fun w => by`.

Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `hw w`. Use `first`. Consider the case `exact hnd _ hw'`. Consider the case `exact hnd.1 _ hw'`.

Break down `mul_eq_zero.1 hz with h1 | h1` into its components or cases. Conclude with `absurd (neg_eq_zero.1 h1) hξ0`. Conclude with `h1`.
-/
lemma herm_eq_zero_of_trace_form_vanish {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by
  have hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0 := fun β =>
    (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)
  have hinv : ∀ a : E, cc (cc a) = a := by
    have h2 := pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)
    rw [NumberField.IsCMField.orderOf_complexConj, pow_two] at h2
    intro a
    have := congrArg (fun σ => σ a) h2
    simpa [cc] using this
  have hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0 := by
    intro w
    rw [← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]
    simp only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [NumberField.integralBasis_apply]
    have := hb ((NumberField.RingOfIntegers.basis E) i)
    simp only [cc] at this
    rw [smul_eq_zero]
    exact Or.inr this
  have hz : -ξ0 * herm G x y = 0 := by
    have hnd := traceForm_nondegenerate ℚ E
    have hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0 := fun w => by
      rw [Algebra.traceForm_apply, mul_comm]
      exact hw w
    first
      | exact hnd _ hw'
      | exact hnd.1 _ hw'
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (neg_eq_zero.1 h1) hξ0
  · exact h1

/- English proof (translation)
Introduce `r X ξ hξ`. Take `⟨hξΛ, hξξ, hξ0⟩` from `hξ`. Establish `hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ`. Introduce `β v hv`. Rewrite `hv`, the goal using `[mem_orthogonal_lattice_iff]`.

Use `⟨X.Λ.smul_mem β hv.1, ?_⟩` and prove the remaining obligations. Rewrite using `[integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]`. Establish `hξp : ξ ∈ X.Λp ξ` using `(mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩`. Prove the components needed by the constructor for the conclusion. Introduce `φ hφ`.

Establish `: Module.Finite (𝓞 E) ↥X.Λ` using `Module.Finite.iff_fg.mpr X.Λ_fg`. Establish `: Module.Finite ℤ ↥X.Λ` using `Module.Finite.trans (𝓞 E) ↥X.Λ`. Set `f : ↥X.Λ →ₗ[ℤ] E` to `((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap`. Establish `hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ` using `fun m => rfl`. Set `P` to `LinearMap.ker f`.

Establish `: Module.IsTorsionFree ℤ (↥X.Λ ⧸ P)`. Rewrite using `[Module.isTorsionFree_iff_smul_eq_zero]`. Introduce `n q hq`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective P q`. Rewrite `hq` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker, map_zsmul]`.

Break down `smul_eq_zero.mp hq with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))`. Take `⟨s, hs⟩` from `Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective`. Establish `hsq : ∀ q, P.mkQ (s q) = q` using `fun q => LinearMap.congr_fun hs q`.

Establish `hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P`. Introduce `m`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]`. Express the relevant statement in the definitionally equal form `P.mkQ m - P.mkQ (s (P.mkQ m)) = 0`. Rewrite using `[hsq, sub_self]`.

Set `ψ : ↥X.Λ →+ ℤ` to `{ toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E), (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩ map_zero' := by`. Rewrite using `[← map_zero φ]`. Use `congr 1`. Use `ext1`. Simplify using the standard rewrite rules.

Use the proof step `map_add' := by`. Introduce `a b`. Rewrite using `[← map_add φ]`. Use `congr 1`. Use `ext1`.

Simplify using `only [map_add]`. Use `push_cast`. Use `abel }`. Take `⟨x, hxΛ, hx⟩` from `X.EF_perf ψ`. Establish `hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν`.

Introduce `ν`. Establish `hν` using `(mem_orthogonal_lattice_iff _ _ _).mp ν.2`. Establish `hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P` using `by rw [LinearMap.mem_ker, hf]; exact hν.2`. Establish `hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0` using `(Submodule.Quotient.mk_eq_zero P).mpr hP`. Establish `hψ : ψ ⟨ν, hν.1⟩ = φ ν` using `by show φ _ = φ ν`.

Use `congr 1`. Use `ext1`. Simplify using `[hmk]`. Rewrite using `[← hψ]`. Conclude with `hx ⟨ν, hν.1⟩`.

Establish `hxξ : herm X.Gm x ξ = 0`. Apply `herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne` to reduce the goal to its premises. Introduce `β`. Establish `hmem` using `hsm β ξ hξp`. Establish `h0` using `hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩`.

Establish `h1` using `hval ⟨β • ξ, hmem⟩`. Rewrite `h1` using `[h0]`. Simplify using `using h1.symm`. Conclude with `⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩`. Introduce `μ hμ`.

Apply `exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0` to reduce the goal to its premises. Introduce `y hy`. Establish `horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0`. Introduce `ν hν`. Apply `herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne` to reduce the goal to its premises.

Introduce `β`. Conclude with `hμ ⟨β • ν, hsm β ν hν⟩`. Take `⟨d, hd, hdy⟩` from `exists_smul_mem (F := E) X.Λ (x := y) (by rw [X.Λ_span]; exact Submodule.mem_top)`. Establish `hdyp : d • y ∈ X.Λp ξ`. Rewrite using `[mem_orthogonal_lattice_iff]`.

Use `⟨hdy, ?_⟩` and prove the remaining obligations. Rewrite using `[integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]`. Establish `h2` using `horth _ hdyp`. Rewrite `h2` using `[integer_smul_eq_coe_smul, herm_smul_right]`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases.

Conclude with `absurd h (by simpa using hd)`. Conclude with `h`.
-/
theorem hermitian_dual_lattice_identity : PerfectPairingQuotient (E := E) := by
  intro r X ξ hξ
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ := by
    intro β v hv
    rw [mem_orthogonal_lattice_iff] at hv ⊢
    refine ⟨X.Λ.smul_mem β hv.1, ?_⟩
    rw [integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]
  have hξp : ξ ∈ X.Λp ξ := (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩
  constructor
  · intro φ hφ
    have : Module.Finite (𝓞 E) ↥X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
    have : Module.Finite ℤ ↥X.Λ := Module.Finite.trans (𝓞 E) ↥X.Λ
    let f : ↥X.Λ →ₗ[ℤ] E := ((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap
    have hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ := fun m => rfl
    let P := LinearMap.ker f
    have : Module.IsTorsionFree ℤ (↥X.Λ ⧸ P) := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro n q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker,
        map_zsmul] at hq
      rcases smul_eq_zero.mp hq with h | h
      · exact Or.inl h
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))
    obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
    have hsq : ∀ q, P.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
    have hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P := by
      intro m
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change P.mkQ m - P.mkQ (s (P.mkQ m)) = 0
      rw [hsq, sub_self]
    let ψ : ↥X.Λ →+ ℤ :=
      { toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E),
          (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩
        map_zero' := by
          rw [← map_zero φ]; congr 1; ext1; simp
        map_add' := by
          intro a b
          rw [← map_add φ]; congr 1; ext1
          simp only [map_add]
          push_cast
          abel }
    obtain ⟨x, hxΛ, hx⟩ := X.EF_perf ψ
    have hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν := by
      intro ν
      have hν := (mem_orthogonal_lattice_iff _ _ _).mp ν.2
      have hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P := by rw [LinearMap.mem_ker, hf]; exact hν.2
      have hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hP
      have hψ : ψ ⟨ν, hν.1⟩ = φ ν := by
        show φ _ = φ ν
        congr 1; ext1
        simp [hmk]
      rw [← hψ]; exact hx ⟨ν, hν.1⟩
    have hxξ : herm X.Gm x ξ = 0 := by
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      have hmem := hsm β ξ hξp
      have h0 := hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩
      have h1 := hval ⟨β • ξ, hmem⟩
      rw [h0] at h1
      simpa using h1.symm
    exact ⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩
  · intro μ hμ
    apply exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0
    intro y hy
    have horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0 := by
      intro ν hν
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      exact hμ ⟨β • ν, hsm β ν hν⟩
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem (F := E) X.Λ (x := y)
      (by rw [X.Λ_span]; exact Submodule.mem_top)
    have hdyp : d • y ∈ X.Λp ξ := by
      rw [mem_orthogonal_lattice_iff]
      refine ⟨hdy, ?_⟩
      rw [integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]
    have h2 := horth _ hdyp
    rw [integer_smul_eq_coe_smul, herm_smul_right] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by simpa using hd)
    · exact h

end ReciprocityTheory.ChartRestriction.G.FD
