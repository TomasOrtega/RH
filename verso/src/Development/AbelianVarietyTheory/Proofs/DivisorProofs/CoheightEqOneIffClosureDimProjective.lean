import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.FieldDimCoheight

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[add_comm] haveI : QuasiSober (closure ({z} : Set X)) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober`. Conclude with `DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _ fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)`. Take `⟨_, ⟨U, hU, rfl⟩, hzU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU`.

Establish `hne : Nonempty U` using `⟨⟨z, hzU⟩⟩`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = z := by`. Establish `: z ∈ Set.range hU.fromSpec` using `by rw [hU.range_fromSpec]; exact hzU`. Conclude with `this`. Set `φ` to `Spec.preimage (hU.fromSpec ≫ p)`.

Establish `hφ : Spec.map φ = hU.fromSpec ≫ p` using `Spec.map_preimage _`. Set `_ : Algebra F Γ(X, U)` to `φ.hom.toAlgebra`. Establish `hft : Algebra.FiniteType F Γ(X, U)` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)`. Establish `: Nonempty (Spec Γ(X, U))` using `⟨P⟩`. Establish `hA : ringKrullDim Γ(X, U) = topologicalKrullDim X`.

Rewrite using `[← OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X _ p hU.fromSpec]`. Conclude with `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm`. Establish `h2` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F P.asIdeal`. Set `x : Spec Γ(X, U)` to `P`. Establish `eS` using `(asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(X, U) x).commRingCatIsoToRingEquiv`.

Establish `hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z`. Rewrite using `[← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal), ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]`. Rewrite using `[← hP]`. Establish `h3 : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ topologicalKrullDim (closure ({z} : Set X))`. Rewrite using `[← topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec P, hP]`.

Conclude with `(Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le`. Rewrite using `[← hA, ← h2, hPh]`. Conclude with `add_le_add le_rfl h3`.
-/
theorem coheight_add_dim_closure_eq (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) [LocallyOfFiniteType p] (z : X) :
    (Order.coheight z : WithBot ℕ∞) + topologicalKrullDim (closure ({z} : Set X)) =
      topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [add_comm]
    haveI : QuasiSober (closure ({z} : Set X)) :=
      isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  let φ := Spec.preimage (hU.fromSpec ≫ p)
  have hφ : Spec.map φ = hU.fromSpec ≫ p := Spec.map_preimage _
  let _ : Algebra F Γ(X, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have : Nonempty (Spec Γ(X, U)) := ⟨P⟩
  have hA : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
    rw [← OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X _ p hU.fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
  have h2 := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F P.asIdeal
  let x : Spec Γ(X, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(X, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]
  have h3 : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ topologicalKrullDim (closure ({z} : Set X)) := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec P, hP]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [← hA, ← h2, hPh]
  exact add_le_add le_rfl h3

/- English proof (translation)
Proceed by induction on `t using WithBot.recBotCoe with`. Consider the case `bot => rw [WithBot.add_bot] at h`. Conclude with `absurd h.symm (WithBot.natCast_ne_bot _)`. Consider the case `coe t`. Establish `h' : c + t = ((e + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast h`.

Establish `hc : c ≠ ⊤` using `by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm`. Establish `ht : t ≠ ⊤` using `by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm`. Use `lift c to ℕ using hc`. Use `lift t to ℕ using ht`. Establish `h'' : c + t = e + 1` using `by exact_mod_cast h'`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Establish `: c = 1` using `by exact_mod_cast h1`. Establish `: t = e` using `by omega`. Conclude with `this` after adjusting the coercions.

Introduce `h1`. Establish `: t = e` using `by exact_mod_cast h1`. Establish `: c = 1` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem eq_one_iff_of_add_eq {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h' : c + t = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have hc : c ≠ ⊤ := by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm
    lift c to ℕ using hc
    lift t to ℕ using ht
    have h'' : c + t = e + 1 := by exact_mod_cast h'
    constructor
    · intro h1
      have : c = 1 := by exact_mod_cast h1
      have : t = e := by omega
      exact_mod_cast this
    · intro h1
      have : t = e := by exact_mod_cast h1
      have : c = 1 := by omega
      exact_mod_cast this

/- English proof (translation)
Introduce `F _ X _ p e hp hd z`. Establish `: IsProper p`. Take `⟨N, c, hc, rfl⟩` from `hp`. Use `isProper_str F N` as an intermediate fact. Use `infer_instance`.

Conclude with `eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)`.
-/
theorem coheight_eq_one_iff : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  intro F _ X _ p e hp hd z
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  exact eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)

end GlobalTheory.FieldDimCoheight
