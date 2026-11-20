import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

section Clopen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace (R ⊗[F] E)] [IsTopologicalRing (R ⊗[F] E)]

/- English proof (translation)
Establish `: tupIn (M` using `M) (n := n) R L = ⋂ i, ⋂ k, {X | X i k ∈ L} := by`. Use extensionality with `X`. Simplify using `[tupIn]`. Rewrite using `[this]`. Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_` and prove the remaining obligations.

Conclude with `hL.preimage ((continuous_apply k).comp (continuous_apply i))`.
-/
theorem isOpen_tupIn_of_isOpen {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsOpen L) :
    IsOpen (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = ⋂ i, ⋂ k, {X | X i k ∈ L} := by
    ext X
    simp [tupIn]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
  exact hL.preimage ((continuous_apply k).comp (continuous_apply i))

/- English proof (translation)
Establish `: (fun x => (t : R ⊗[F] E) ^ j * x) '' L = (fun x => ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) ⁻¹' L`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `h : ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * ((t : R ⊗[F] E) ^ j * y) = y`.

Rewrite using `[← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]`. Simplify `hy` using `only [Set.mem_preimage, h]`. Introduce `hx`. Use `⟨_, hx, ?_⟩` and prove the remaining obligations. Use `show (t : R ⊗[F] E) ^ j * (((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) = x`.

Rewrite using `[← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one, one_mul]`. Rewrite using `[this]`. Conclude with `hL.preimage (continuous_const.mul continuous_id)`.
-/
theorem isOpen_unit_pow_image {L : Set (R ⊗[F] E)} (hL : IsOpen L) (t : (R ⊗[F] E)ˣ) (j : ℕ) :
    IsOpen ((fun x => (t : R ⊗[F] E) ^ j * x) '' L) := by
  have : (fun x => (t : R ⊗[F] E) ^ j * x) '' L =
      (fun x => ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) ⁻¹' L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * ((t : R ⊗[F] E) ^ j * y) = y := by
        rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel,
          Units.val_one, one_mul]
      simpa only [Set.mem_preimage, h] using hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      show (t : R ⊗[F] E) ^ j * (((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) = x
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, mul_inv_cancel,
        Units.val_one, one_mul]
  rw [this]
  exact hL.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Establish `hT` using `isOpen_unit_pow_image R hL t j`. Establish `: nearNF (M` using `M) (n := n) R O L (t : R ⊗[F] E) j = tupIn R L ∩ ⋃ (l : Fin n), ⋃ (a : Fin n → R ⊗[F] E), ⋃ (_ : (∀ i, a i ∈ O) ∧ a l = 1), ⋂ k, {X : Fin n → Fin M → R ⊗[F] E | ∑ i, X i k * a i ∈ (fun x => (t : R ⊗[F] E) ^ j * x) '' L} := by`. Use extensionality with `X`. Simplify using `only [nearNF, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, l, a, h2, h3, h4⟩`. Conclude with `⟨h1, l, a, ⟨h2, h3⟩, h4⟩`. Introduce and unpack `⟨h1, l, a, ⟨h2, h3⟩, h4⟩`. Conclude with `⟨h1, l, a, h2, h3, h4⟩`. Rewrite using `[this]`.

Use `(isOpen_tupIn_of_isOpen R hL).inter ?_` and prove the remaining obligations. Use `isOpen_iUnion fun l => isOpen_iUnion fun a => isOpen_iUnion fun _ => ?_` and prove the remaining obligations. Use `isOpen_iInter_of_finite fun k => hT.preimage ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(continuous_apply_apply i k).mul continuous_const`.
-/
theorem isOpen_nearNF {M n : ℕ} (O : Set (R ⊗[F] E)) {L : Set (R ⊗[F] E)} (hL : IsOpen L)
    (t : (R ⊗[F] E)ˣ) (j : ℕ) :
    IsOpen (nearNF (M := M) (n := n) R O L (t : R ⊗[F] E) j) := by
  have hT := isOpen_unit_pow_image R hL t j
  have : nearNF (M := M) (n := n) R O L (t : R ⊗[F] E) j =
      tupIn R L ∩ ⋃ (l : Fin n), ⋃ (a : Fin n → R ⊗[F] E), ⋃ (_ : (∀ i, a i ∈ O) ∧ a l = 1),
        ⋂ k, {X : Fin n → Fin M → R ⊗[F] E | ∑ i, X i k * a i ∈
          (fun x => (t : R ⊗[F] E) ^ j * x) '' L} := by
    ext X
    simp only [nearNF, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      exists_prop]
    constructor
    · rintro ⟨h1, l, a, h2, h3, h4⟩
      exact ⟨h1, l, a, ⟨h2, h3⟩, h4⟩
    · rintro ⟨h1, l, a, ⟨h2, h3⟩, h4⟩
      exact ⟨h1, l, a, h2, h3, h4⟩
  rw [this]
  refine (isOpen_tupIn_of_isOpen R hL).inter ?_
  refine isOpen_iUnion fun l => isOpen_iUnion fun a => isOpen_iUnion fun _ => ?_
  refine isOpen_iInter_of_finite fun k => hT.preimage ?_
  refine continuous_finset_sum _ fun i _ => ?_
  exact (continuous_apply_apply i k).mul continuous_const

/- English proof (translation)
Establish `hT : IsClosed ((fun x => t ^ j * x) '' L)` using `(hL.image (continuous_const.mul continuous_id)).isClosed`. Set `C : Fin n → Set ((Fin n → Fin M → R ⊗[F] E) × (Fin n → R ⊗[F] E))` to `fun l => (tupIn R L ×ˢ Set.pi Set.univ fun _ => O) ∩ ({p | p.2 l = 1} ∩ ⋂ k, {p | ∑ i, p.1 i k * p.2 i ∈ (fun x => t ^ j * x) '' L})`. Establish `hC : ∀ l, IsCompact (C l)`. Introduce `l`. Use `((isCompact_tupIn R hL).prod (isCompact_univ_pi fun _ => hO)).inter_right ?_` and prove the remaining obligations.

Use `(isClosed_eq ?_ continuous_const).inter (isClosed_iInter fun k => hT.preimage ?_)` and prove the remaining obligations. Conclude with `(continuous_apply l).comp continuous_snd`. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply_apply i k).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)`. Establish `: nearNF (M` using `M) (n := n) R O L t j = ⋃ l, Prod.fst '' C l := by`.

Use extensionality with `X`. Simplify using `only [nearNF, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, l, a, h2, h3, h4⟩`. Use `⟨l, (X, a), ⟨⟨h1, fun i _ => h2 i⟩, h3, ?_⟩, rfl⟩` and prove the remaining obligations.

Conclude with `Set.mem_iInter.2 h4`. Introduce and unpack `⟨l, ⟨X', a⟩, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩`. Conclude with `⟨h1, l, a, fun i => h2 i trivial, h3, Set.mem_iInter.1 h4⟩`. Rewrite using `[this]`. Conclude with `(isCompact_iUnion fun l => (hC l).image continuous_fst).isClosed`.
-/
theorem isClosed_nearNF [T2Space (R ⊗[F] E)] {M n : ℕ} {O L : Set (R ⊗[F] E)} (hO : IsCompact O)
    (hL : IsCompact L) (t : R ⊗[F] E) (j : ℕ) :
    IsClosed (nearNF (M := M) (n := n) R O L t j) := by
  have hT : IsClosed ((fun x => t ^ j * x) '' L) :=
    (hL.image (continuous_const.mul continuous_id)).isClosed
  let C : Fin n → Set ((Fin n → Fin M → R ⊗[F] E) × (Fin n → R ⊗[F] E)) := fun l =>
    (tupIn R L ×ˢ Set.pi Set.univ fun _ => O) ∩
      ({p | p.2 l = 1} ∩ ⋂ k, {p | ∑ i, p.1 i k * p.2 i ∈ (fun x => t ^ j * x) '' L})
  have hC : ∀ l, IsCompact (C l) := by
    intro l
    refine ((isCompact_tupIn R hL).prod (isCompact_univ_pi fun _ => hO)).inter_right ?_
    refine (isClosed_eq ?_ continuous_const).inter (isClosed_iInter fun k => hT.preimage ?_)
    · exact (continuous_apply l).comp continuous_snd
    · refine continuous_finset_sum _ fun i _ => ?_
      exact ((continuous_apply_apply i k).comp continuous_fst).mul
        ((continuous_apply i).comp continuous_snd)
  have : nearNF (M := M) (n := n) R O L t j = ⋃ l, Prod.fst '' C l := by
    ext X
    simp only [nearNF, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨h1, l, a, h2, h3, h4⟩
      refine ⟨l, (X, a), ⟨⟨h1, fun i _ => h2 i⟩, h3, ?_⟩, rfl⟩
      exact Set.mem_iInter.2 h4
    · rintro ⟨l, ⟨X', a⟩, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
      exact ⟨h1, l, a, fun i => h2 i trivial, h3, Set.mem_iInter.1 h4⟩
  rw [this]
  exact (isCompact_iUnion fun l => (hC l).image continuous_fst).isClosed

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `(isCompact_tupIn R hLc).diff ?_` and prove the remaining obligations. Conclude with `isOpen_biUnion fun p _ => isOpen_nearNF R O hLo p.1 j`. Use `(isOpen_tupIn_of_isOpen R hLo).sdiff ?_` and prove the remaining obligations. Conclude with `S.finite_toSet.isClosed_biUnion fun p _ => isClosed_nearNF R hO hLc _ j`.
-/
theorem goodT_compact_open [T2Space (R ⊗[F] E)] {M n : ℕ} {O L : Set (R ⊗[F] E)} (hO : IsCompact O)
    (hLc : IsCompact L) (hLo : IsOpen L) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    IsCompact (goodT (M := M) (n := n) R O L S j) ∧ IsOpen (goodT (M := M) (n := n) R O L S j) := by
  constructor
  · refine (isCompact_tupIn R hLc).diff ?_
    exact isOpen_biUnion fun p _ => isOpen_nearNF R O hLo p.1 j
  · refine (isOpen_tupIn_of_isOpen R hLo).sdiff ?_
    exact S.finite_toSet.isClosed_biUnion fun p _ => isClosed_nearNF R hO hLc _ j

end Clopen

end GlobalTheory.CompanionTheory.AvgFree

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b v lv hlv O S hOS L hLc hLo n M j`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Take `⟨a1, -, -, a4, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`. Use `haveI := a4`. Conclude with `goodT_compact_open (Fv F v) hOS.1 hLc hLo S j`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M j : ℕ), IsCompact (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∧ IsOpen (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O S hOS L hLc hLo n M j
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -, -, a4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a4
  exact goodT_compact_open (Fv F v) hOS.1 hLc hLo S j
