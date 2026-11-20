import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatticeCard

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_span_singleton_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : R) (x : M) : x ∈ (Ideal.span {b} • ⊤ : Submodule R M) ↔ ∃ y : M, b • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_quot_pow_succ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (k : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ (k + 1)} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) *
      Nat.card (M ⧸ (Ideal.span {a ^ k} • ⊤ : Submodule R M)) := by
  set S : Submodule R M := Ideal.span {a ^ (k + 1)} • ⊤ with hS
  set T : Submodule R M := Ideal.span {a ^ k} • ⊤ with hT
  have hST : S ≤ T := by
    intro x hx
    rw [hS, mem_span_singleton_smul_top] at hx
    rw [hT, mem_span_singleton_smul_top]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [smul_smul, ← pow_succ]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (T.map S.mkQ)
  rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient S T hST).toEquiv] at h1
  rw [h1]
  congr 1
  have hmem : ∀ x : M, S.mkQ (a ^ k • x) ∈ T.map S.mkQ := fun x =>
    ⟨a ^ k • x, SetLike.mem_coe.2 ((mem_span_singleton_smul_top _ _).2 ⟨x, rfl⟩), rfl⟩
  let φ : M →ₗ[R] ↥(T.map S.mkQ) :=
    LinearMap.codRestrict (T.map S.mkQ) (S.mkQ ∘ₗ (a ^ k • LinearMap.id)) (fun x => hmem x)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_span_singleton_smul_top] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker φ = (Ideal.span {a} • ⊤ : Submodule R M) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    have hφ : φ x = 0 ↔ a ^ k • x ∈ S := by
      rw [← Subtype.coe_inj]
      change S.mkQ (a ^ k • x) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [hφ, hS, mem_span_singleton_smul_top]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (ha.pow k) ?_⟩
      change a ^ k • (a • y) = a ^ k • x
      rw [smul_smul, ← pow_succ]; exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_smul, ← pow_succ]⟩
  rw [← Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hsurj).toEquiv,
    Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Proceed by induction.

Proceed by induction. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Treat this case separately.
-/
theorem card_quot_pow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (r : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    rw [Submodule.Quotient.eq, mem_span_singleton_smul_top]
    exact ⟨x - y, one_smul _ _⟩
  | succ k ih => rw [card_quot_pow_succ a ha k, ih, pow_succ, mul_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Assume the hypotheses and unpack their components.
-/
theorem card_quot_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (b : R) :
    Nat.card (M ⧸ (Ideal.span {b} • ⊤ : Submodule R M)) =
      Nat.card (N ⧸ (Ideal.span {b} • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv
  ext y
  rw [Submodule.mem_map_equiv, mem_span_singleton_smul_top, mem_span_singleton_smul_top]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨e x, by rw [← map_smul, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩; exact ⟨e.symm x, by rw [map_smul]⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_quot_fun {ι O : Type*} [Fintype ι] [CommRing O] (b : O) :
    Nat.card ((ι → O) ⧸ (Ideal.span {b} • ⊤ : Submodule O (ι → O))) =
      Nat.card (O ⧸ Ideal.span {b}) ^ Fintype.card ι := by
  let π : (ι → O) →ₗ[O] (ι → O ⧸ Ideal.span {b}) :=
    LinearMap.pi (fun i => (Ideal.Quotient.mkₐ O (Ideal.span {b})).toLinearMap ∘ₗ LinearMap.proj i)
  have hπ : ∀ x i, π x i = Ideal.Quotient.mk _ (x i) := fun x i => rfl
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨fun i => (y i).out, funext fun i => ?_⟩
    rw [hπ, Ideal.Quotient.mk_out]
  have hker : LinearMap.ker π = (Ideal.span {b} • ⊤ : Submodule O (ι → O)) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    constructor
    · intro hx
      have : ∀ i, ∃ c, b * c = x i := fun i => by
        have h := congrFun hx i
        rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
        obtain ⟨c, hc⟩ := h
        exact ⟨c, hc.symm⟩
      choose c hc using this
      exact ⟨c, funext fun i => by simp [hc]⟩
    · rintro ⟨y, rfl⟩
      funext i
      rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y i, by simp⟩
  rw [← Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective π hsurj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

end GlobalTheory.LatticeCard

namespace GlobalTheory.LatticeCard

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem card_lattice_quot_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r
  obtain ⟨⟨hD, -, hFr⟩, -, -, -, -⟩ := hG
  haveI := hD
  haveI := hFr
  haveI : Module.Free O LA.T := LA.free
  haveI : Module.Finite O LA.T := Module.Finite.iff_fg.2 LA.fg
  let b := Module.Free.chooseBasis O LA.T
  have hli : LinearIndependent LL (fun i => (b i : A.V)) := by
    rw [← LinearIndependent.iff_fractionRing O LL]
    exact b.linearIndependent.map' LA.T.subtype (Submodule.ker_subtype _)
  have hT : (LA.T : Set A.V) ⊆ Submodule.span LL (Set.range fun i => (b i : A.V)) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : LA.T) ∈ Submodule.span O (Set.range b) := by
      rw [b.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span LA.T.subtype hx'
    rw [← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O LL _ h2
  have hsp : ⊤ ≤ Submodule.span LL (Set.range fun i => (b i : A.V)) :=
    calc ⊤ = Submodule.span LL (LA.T : Set A.V) := LA.span.symm
      _ ≤ _ := Submodule.span_le.2 hT
  have hn : finrank LL A.V = Fintype.card (Module.Free.ChooseBasisIndex O LA.T) :=
    finrank_eq_card_basis (Basis.mk hli hsp)
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    have h := (algebraMap ℚ_[l] LL).injective.ne
      (show ((l : ℕ) : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using h
  have hreg : IsSMulRegular LA.T ((l : ℕ) : O) := by
    intro x y hxy
    have h1 : ((l : ℕ) : O) • (x : A.V) = ((l : ℕ) : O) • (y : A.V) := by
      have := congrArg (fun z : LA.T => (z : A.V)) hxy
      simpa only [Submodule.coe_smul] using this
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul LL,
      ← Nat.cast_smul_eq_nsmul LL l (y : A.V)] at h1
    exact Subtype.ext (smul_right_injective A.V hl h1)
  rw [card_quot_pow _ hreg, card_quot_equiv b.equivFun, card_quot_fun, hn, ← pow_mul, mul_comm]

end GlobalTheory.LatticeCard
