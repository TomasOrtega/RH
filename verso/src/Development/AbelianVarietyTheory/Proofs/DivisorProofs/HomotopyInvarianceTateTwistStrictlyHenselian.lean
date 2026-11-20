import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosurStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

/- English proof (translation)
Introduce `q _ A _ _ hq`. Establish `hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `R _ _ _ hd`. Apply `GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton` to reduce the goal to its premises. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_subsingleton_iff_nontrivial]`. Conclude with `absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))`.

Consider the case `succ d ih`. Introduce `R _ _ hR hd`. Establish `hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D`. Introduce `D _ _ _ hD hDd`. Use `GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)` and prove the remaining obligations.

Introduce `x hx`. Establish `hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D)))`. Rewrite using `[IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]`. Conclude with `(algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))`. Establish `h0 : x = 0`.

Apply `hinj` to reduce the goal to its premises. Use `congrArg Subtype.val (RingHom.mem_ker.mp hx)` as an intermediate fact. Simplify using `using this`. Rewrite using `[h0]`. Conclude with `zero_mem _`.

Use `GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_` and prove the remaining obligations. Use `revert hd`. Proceed by induction on `ringKrullDim R with`. Consider the case `bot => intro _`. Conclude with `bot_le`.

Consider the case `coe n`. Introduce `h`. Establish `h' : n < ((d + 1 : ℕ) : ℕ∞)` using `WithBot.coe_lt_coe.mp h`. Conclude with `WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))`. Set `S : Finset A → Subalgebra ℤ A` to `fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))`.

Establish `hmono : Monotone S` using `fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))`. Establish `hcov : ∀ a, ∃ s, a ∈ S s` using `fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩`. Establish `hunit : ∀ s, IsUnit (q : S s)`. Introduce `s`. Establish `hm : (↑(hq.unit⁻¹) : A) ∈ S s` using `Algebra.subset_adjoin (Set.mem_insert _ _)`.

Use `isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `hinv : ∀ s, HInv q (S s)`. Introduce `s`.

Establish `: Algebra.FiniteType ℤ (S s)`. Establish `hfg' : (S s).FG`. Establish `: (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A)` using `by simp`. Rewrite using `[show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]`. Conclude with `Subalgebra.fg_adjoin_finset _`.

Conclude with `Subalgebra.fg_iff_finiteType _ |>.mp hfg'`. Establish `hlt` using `GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)`. Take `⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d` from `by revert hlt`. Proceed by induction on `ringKrullDim (S s) with`. Consider the case `bot => intro _`.

Conclude with `⟨0, bot_le⟩`. Consider the case `coe n`. Introduce `h`. Proceed by induction on `n with`. Consider the case `top => exact absurd h (lt_irrefl _)`.

Consider the case `coe m => exact ⟨m, le_rfl⟩`. Conclude with `hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))`. Introduce `i`. Conclude with `GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i`.
-/
theorem GlobalTheory.homotopyInvariance_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  classical
  intro q _ A _ _ hq
  have hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R := by
    intro d
    induction d with
    | zero =>
      intro R _ _ _ hd
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
    | succ d ih =>
      intro R _ _ hR hd
      have hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D := by
        intro D _ _ _ hD hDd
        refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)
        intro x hx
        have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
          rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
          exact (algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))
        have h0 : x = 0 := by
          apply hinj
          have := congrArg Subtype.val (RingHom.mem_ker.mp hx)
          simpa using this
        rw [h0]; exact zero_mem _
      refine GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_
      revert hd
      induction ringKrullDim R with
      | bot => intro _; exact bot_le
      | coe n =>
        intro h
        have h' : n < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))
  let S : Finset A → Subalgebra ℤ A := fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))
  have hmono : Monotone S := fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))
  have hcov : ∀ a, ∃ s, a ∈ S s := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  have hunit : ∀ s, IsUnit (q : S s) := by
    intro s
    have hm : (↑(hq.unit⁻¹) : A) ∈ S s := Algebra.subset_adjoin (Set.mem_insert _ _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    simp
  have hinv : ∀ s, HInv q (S s) := by
    intro s
    have : Algebra.FiniteType ℤ (S s) := by
      have hfg' : (S s).FG := by
        have : (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A) := by simp
        rw [show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]
        exact Subalgebra.fg_adjoin_finset _
      exact Subalgebra.fg_iff_finiteType _ |>.mp hfg'
    have hlt := GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d := by
      revert hlt
      induction ringKrullDim (S s) with
      | bot => intro _; exact ⟨0, bot_le⟩
      | coe n =>
        intro h
        induction n with
        | top => exact absurd h (lt_irrefl _)
        | coe m => exact ⟨m, le_rfl⟩
    exact hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  intro i
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i
