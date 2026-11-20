import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.ThetaGL.DualPair

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def ev (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) :
    V ⊗[ℂ] smoothPart π.dual →ₗ[ℂ] W →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (v : V) (l : smoothPart π.dual) => (l : Module.Dual ℂ W).smulRight v)
    (fun v v' l => by ext w; simp)
    (fun c v l => by
      ext w
      show (l : Module.Dual ℂ W) w • c • v = c • (l : Module.Dual ℂ W) w • v
      exact smul_comm _ _ _)
    (fun v l l' => by ext w; simp [add_smul])
    (fun c v l => by ext w; simp [smul_smul]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ev_tmul (π : Representation ℂ G W) (v : V) (l : smoothPart π.dual) (w : W) :
    ev V π (v ⊗ₜ l) w = (l : Module.Dual ℂ W) w • v := rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun t ht => ?_` and prove the remaining obligations. Set `b` to `Module.Basis.ofVectorSpace ℂ V`. Take `⟨c, rfl⟩` from `TensorProduct.eq_repr_basis_left b t`. Establish `hc : ∀ i ∈ c.support, c i = 0`. Introduce `i hi`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Establish `h0 : ev V π (c.sum fun i n => b i ⊗ₜ[ℂ] n) w = 0` using `by rw [ht]; rfl`. Establish `h1 : ∑ j ∈ c.support, ((c j : Module.Dual ℂ W) w) • b j = 0`. Rewrite using `[← h0, Finsupp.sum, map_sum, LinearMap.sum_apply]`.

Both sides reduce to the same expression. Conclude with `linearIndependent_iff'.1 b.linearIndependent c.support _ h1 i hi`. Rewrite using `[Finsupp.sum]`. Conclude with `Finset.sum_eq_zero fun i hi => by rw [hc i hi, TensorProduct.tmul_zero]`.
-/
theorem ev_injective (π : Representation ℂ G W) : Function.Injective (ev V π) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  let b := Module.Basis.ofVectorSpace ℂ V
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ i ∈ c.support, c i = 0 := by
    intro i hi
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    have h0 : ev V π (c.sum fun i n => b i ⊗ₜ[ℂ] n) w = 0 := by rw [ht]; rfl
    have h1 : ∑ j ∈ c.support, ((c j : Module.Dual ℂ W) w) • b j = 0 := by
      rw [← h0, Finsupp.sum, map_sum, LinearMap.sum_apply]
      rfl
    exact linearIndependent_iff'.1 b.linearIndependent c.support _ h1 i hi
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun i hi => by rw [hc i hi, TensorProduct.tmul_zero]

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Set `S : Subgroup K` to `{ carrier := {k | π (k : G) w = w} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Establish `hS : IsOpen (S : Set K)` using `(hπ w).preimage continuous_subtype_val`.

Use `haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS`. Use `haveI : Fintype (K ⧸ S) := Fintype.ofFinite _`. Set `φ : K ⧸ S → W` to `fun q => Quotient.liftOn' q (fun k : K => π (k : G) w) (fun a b h => by`. Establish `h' : a⁻¹ * b ∈ S` using `QuotientGroup.leftRel_apply.1 h`. Establish `h2 : π ((a⁻¹ * b : K) : G) w = w` using `h'`.

Establish `h3 : π (b : G) w = π (a : G) w` using `by conv_rhs => rw [← h2]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Conclude with `h3.symm)`. Establish `hφ : ∀ (k : K) (q : K ⧸ S), φ (k • q) = π (k : G) (φ q)`.

Introduce `k q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H a => show π ((k * a : K) : G) w = π (k : G) (π (a : G) w)`. Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Establish `hcard : ((Fintype.card (K ⧸ S) : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Use `⟨((Fintype.card (K ⧸ S) : ℕ) : ℂ)⁻¹ • ∑ q, φ q, ?_, fun T hT => ?_⟩` and prove the remaining obligations. Introduce `k`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Rewrite using `[map_smul, map_sum]`. Use `congr 1`.

Repeatedly rewrite using `[← hφ]`. Conclude with `Equiv.sum_comp (MulAction.toPerm k) φ`. Establish `h1 : ∀ q, T (φ q) = T w`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H a => exact hT _ a.2 w`. Rewrite using `[map_smul, map_sum]`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]`.
-/
theorem exists_fixed (π : Representation ℂ G W) (hπ : IsSmooth π) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : W) :
    ∃ w' ∈ fixed π K, ∀ T : W →ₗ[ℂ] V, (∀ k ∈ K, ∀ x, T (π k x) = T x) → T w = T w' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : Subgroup K :=
    { carrier := {k | π (k : G) w = w}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hS : IsOpen (S : Set K) := (hπ w).preimage continuous_subtype_val
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
  haveI : Fintype (K ⧸ S) := Fintype.ofFinite _
  let φ : K ⧸ S → W := fun q => Quotient.liftOn' q (fun k : K => π (k : G) w) (fun a b h => by
    have h' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 h
    have h2 : π ((a⁻¹ * b : K) : G) w = w := h'
    have h3 : π (b : G) w = π (a : G) w := by
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    exact h3.symm)
  have hφ : ∀ (k : K) (q : K ⧸ S), φ (k • q) = π (k : G) (φ q) := by
    intro k q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show π ((k * a : K) : G) w = π (k : G) (π (a : G) w)
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hcard : ((Fintype.card (K ⧸ S) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (K ⧸ S) : ℕ) : ℂ)⁻¹ • ∑ q, φ q, ?_, fun T hT => ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [map_smul, map_sum]
    congr 1
    simp_rw [← hφ]
    exact Equiv.sum_comp (MulAction.toPerm k) φ
  · have h1 : ∀ q, T (φ q) = T w := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a => exact hT _ a.2 w
    rw [map_smul, map_sum]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hKo hKc`. Establish `hle : LinearMap.range T ≤ (fixed π K).map T`. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨w', hw', h⟩` from `exists_fixed (V := V) π hπ.1 K hKc w`. Conclude with `⟨w', hw', (h T hT).symm⟩`.

Use `haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hle`. Set `b` to `Module.finBasis ℂ (LinearMap.range T)`. Set `l : _ → Module.Dual ℂ W` to `fun i => b.coord i ∘ₗ T.rangeRestrict`. Establish `hl : ∀ i, l i ∈ smoothPart π.dual` using `fun i => mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem K)) fun g hg => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Use `show l i (π g⁻¹ x) = l i x`. Establish `: T.rangeRestrict (π g⁻¹ x) = T.rangeRestrict x` using `Subtype.ext (hT _ (inv_mem hg) x)`. Simplify using `only [l, LinearMap.comp_apply, this])`. Use `⟨∑ i, (b i : V) ⊗ₜ[ℂ] (⟨l i, hl i⟩ : smoothPart π.dual), LinearMap.ext fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, LinearMap.sum_apply]`.

Establish `h2 : ((∑ i, b.repr (T.rangeRestrict w) i • b i : LinearMap.range T) : V) = T w`. Rewrite using `[b.sum_repr]`. Both sides reduce to the same expression. Rewrite `h2` using `[Submodule.coe_sum]`. Conclude with `h2`.
-/
theorem exists_ev_eq (π : Representation ℂ G W) (hπ : IsAdmissible π) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (T : W →ₗ[ℂ] V)
    (hT : ∀ k ∈ K, ∀ x, T (π k x) = T x) : ∃ t, ev V π t = T := by
  haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hKo hKc
  have hle : LinearMap.range T ≤ (fixed π K).map T := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', h⟩ := exists_fixed (V := V) π hπ.1 K hKc w
    exact ⟨w', hw', (h T hT).symm⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hle
  let b := Module.finBasis ℂ (LinearMap.range T)
  let l : _ → Module.Dual ℂ W := fun i => b.coord i ∘ₗ T.rangeRestrict
  have hl : ∀ i, l i ∈ smoothPart π.dual := fun i =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem K)) fun g hg => by
      refine LinearMap.ext fun x => ?_
      show l i (π g⁻¹ x) = l i x
      have : T.rangeRestrict (π g⁻¹ x) = T.rangeRestrict x :=
        Subtype.ext (hT _ (inv_mem hg) x)
      simp only [l, LinearMap.comp_apply, this])
  refine ⟨∑ i, (b i : V) ⊗ₜ[ℂ] (⟨l i, hl i⟩ : smoothPart π.dual), LinearMap.ext fun w => ?_⟩
  rw [map_sum, LinearMap.sum_apply]
  have h2 : ((∑ i, b.repr (T.rangeRestrict w) i • b i : LinearMap.range T) : V) = T w := by
    rw [b.sum_repr]
    rfl
  rw [Submodule.coe_sum] at h2
  exact h2

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul v l => simp`.
-/
theorem ev_map {H : Type} [Group H] (σ : Representation ℂ H V) (π : Representation ℂ G W) (g : H) (h : G)
    (t : V ⊗[ℂ] smoothPart π.dual) (w : W) :
    ev V π (TensorProduct.map (σ g) (contra π h) t) w = σ g (ev V π t (π h⁻¹ w)) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul v l => simp
end General

end GlobalTheory.ThetaGL.DualPair

open GlobalTheory.ThetaGL.DualPair in

/- English proof (translation)
Introduce `k _ _ _ _ r n μ V _ _ W _ _ σ π hμ hπ ⟨B, hB0, hB⟩`. Take `⟨-, hmul, -, -, hop⟩` from `om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ`. Establish `hone` using `(om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ).1`. Establish `hmem : ∀ Φ, B Φ ∈ LinearMap.range (ev V π)`. Introduce `Φ`.

Set `S : Subgroup (GL (Fin n) k)` to `{ carrier := {h | om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1} one_mem' := hone _ mul_mem' := fun {x y} hx hy => by show om μ (1 : GL (Fin r) k) (x * y) Φ.1 = Φ.1`. Use `hmul 1 1 x y Φ.1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by show om μ (1 : GL (Fin r) k) x⁻¹ Φ.1 = Φ.1`.

Establish `hx' : om μ (1 : GL (Fin r) k) x Φ.1 = Φ.1` using `hx`. Use `conv_lhs => rw [← hx']`. Use `hmul 1 1 x⁻¹ x Φ.1` as an intermediate fact. Rewrite `this` using `[mul_one, inv_mul_cancel, hone]`. Conclude with `this.symm }`.

Establish `hSo : IsOpen (S : Set (GL (Fin n) k))` using `(hop Φ.1 Φ.2).preimage (Continuous.prodMk continuous_const continuous_id)`. Establish `hKo : IsOpen ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k))` using `hSo.inter SplitFlip.isOpen_KO`. Establish `hKc : IsCompact ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k))` using `SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) Set.inter_subset_right`. Take `⟨t, ht⟩` from `exists_ev_eq π hπ _ hKo hKc (B Φ) fun h hh x => by`. Use `hB 1 h Φ Φ (hh.1 : om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1).symm x` as an intermediate fact.

Simplify using `using this`. Conclude with `⟨t, ht⟩`. Set `e` to `LinearEquiv.ofInjective (ev V π) (ev_injective π)`. Set `f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] smoothPart π.dual` to `e.symm.toLinearMap ∘ₗ B.codRestrict _ hmem`. Establish `hf : ∀ Φ, ev V π (f Φ) = B Φ` using `fun Φ => by`.

Use `e.apply_symm_apply (B.codRestrict _ hmem Φ)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Use `⟨f, fun h0 => hB0 (LinearMap.ext fun Φ => ?_), fun g h Φ Φ' hΦ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf, h0]`. Simplify using the standard rewrite rules.

Apply `ev_injective π` to reduce the goal to its premises. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[ev_map, hf, hf, ← hB g h Φ Φ' hΦ (π h⁻¹ w), ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsSmoothChar μ → IsAdmissible π → ThetaPair μ σ π → OmQuot μ σ (contra π) := by
  intro k _ _ _ _ r n μ V _ _ W _ _ σ π hμ hπ ⟨B, hB0, hB⟩
  obtain ⟨-, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ
  have hone := (om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ).1
  have hmem : ∀ Φ, B Φ ∈ LinearMap.range (ev V π) := by
    intro Φ
    let S : Subgroup (GL (Fin n) k) :=
      { carrier := {h | om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1}
        one_mem' := hone _
        mul_mem' := fun {x y} hx hy => by
          show om μ (1 : GL (Fin r) k) (x * y) Φ.1 = Φ.1
          have := hmul 1 1 x y Φ.1
          rw [mul_one] at this
          rw [this, hy, hx]
        inv_mem' := fun {x} hx => by
          show om μ (1 : GL (Fin r) k) x⁻¹ Φ.1 = Φ.1
          have hx' : om μ (1 : GL (Fin r) k) x Φ.1 = Φ.1 := hx
          conv_lhs => rw [← hx']
          have := hmul 1 1 x⁻¹ x Φ.1
          rw [mul_one, inv_mul_cancel, hone] at this
          exact this.symm }
    have hSo : IsOpen (S : Set (GL (Fin n) k)) :=
      (hop Φ.1 Φ.2).preimage (Continuous.prodMk continuous_const continuous_id)
    have hKo : IsOpen ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      hSo.inter SplitFlip.isOpen_KO
    have hKc : IsCompact ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      SplitFlip.isCompact_KO.of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ hKo) Set.inter_subset_right
    obtain ⟨t, ht⟩ := exists_ev_eq π hπ _ hKo hKc (B Φ) fun h hh x => by
      have := hB 1 h Φ Φ (hh.1 : om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1).symm x
      simpa using this
    exact ⟨t, ht⟩
  let e := LinearEquiv.ofInjective (ev V π) (ev_injective π)
  let f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] smoothPart π.dual :=
    e.symm.toLinearMap ∘ₗ B.codRestrict _ hmem
  have hf : ∀ Φ, ev V π (f Φ) = B Φ := fun Φ => by
    have := e.apply_symm_apply (B.codRestrict _ hmem Φ)
    exact congrArg Subtype.val this
  refine ⟨f, fun h0 => hB0 (LinearMap.ext fun Φ => ?_), fun g h Φ Φ' hΦ => ?_⟩
  · rw [← hf, h0]
    simp
  · apply ev_injective π
    refine LinearMap.ext fun w => ?_
    rw [ev_map, hf, hf, ← hB g h Φ Φ' hΦ (π h⁻¹ w), ← Module.End.mul_apply, ← map_mul]
    simp
