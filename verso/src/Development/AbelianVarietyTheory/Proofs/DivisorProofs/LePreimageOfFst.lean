import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Points

namespace GlobalTheory.UnifImmersive

/- English proof (translation)
Establish `H (p : PrimeSpectrum (DualNumber ℂ)) : Ideal.span {DualNumber.eps} = p.asIdeal` using `DualNumber.isMaximal_span_singleton_eps.eq_of_le p.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 (p.isPrime.mem_of_pow_mem 2 (by simp [sq])))`. Conclude with `PrimeSpectrum.ext ((H x).symm.trans (H x'))`.
-/
theorem primeSpectrum_eq (x x' : PrimeSpectrum (DualNumber ℂ)) : x = x' := by
  have H (p : PrimeSpectrum (DualNumber ℂ)) : Ideal.span {DualNumber.eps} = p.asIdeal :=
    DualNumber.isMaximal_span_singleton_eps.eq_of_le p.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).2 (p.isPrime.mem_of_pow_mem 2 (by simp [sq])))
  exact PrimeSpectrum.ext ((H x).symm.trans (H x'))

/- English proof (translation)
Introduce `x _`. Establish `hx` using `h (x := IsLocalRing.closedPoint ℂ) trivial`. Establish `e : x = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ)` using `primeSpectrum_eq _ _`. Rewrite using `[e]`. Conclude with `hx`.
-/
theorem le_preimage_of_fst {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t) ⁻¹ᵁ U) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro x _
  have hx := h (x := IsLocalRing.closedPoint ℂ) trivial
  have e : x = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) :=
    primeSpectrum_eq _ _
  rw [e]
  exact hx

/- English proof (translation)
Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (x := o (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial`. Establish `h₀ : ⊤ ≤ o ⁻¹ᵁ U` using `fun z _ => by`. Rewrite using `[show z = IsLocalRing.closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]` and apply the resulting hypothesis. Establish `h₁ : ⊤ ≤ t ⁻¹ᵁ U` using `le_preimage_of_fst t U (ho ▸ h₀)`. Use `ext_of_valR hU h₁ (le_preimage_comp _ o h₀ le_top) fun f => ?_` and prove the remaining obligations.

Rewrite using `[valR_spMap_comp _ o U h₀, ← ho, valR_spMap_comp _ t U h₁]`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl, H U f h₀]`.
-/
theorem eq_const {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (o : Sp ℂ ⟶ X)
    (ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = o)
    (H : ∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ o ⁻¹ᵁ U → TrivSqZeroExt.snd (valR t U f) = 0) :
    t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ o := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := o (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  have h₀ : ⊤ ≤ o ⁻¹ᵁ U := fun z _ => by
    rwa [show z = IsLocalRing.closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  have h₁ : ⊤ ≤ t ⁻¹ᵁ U := le_preimage_of_fst t U (ho ▸ h₀)
  refine ext_of_valR hU h₁ (le_preimage_comp _ o h₀ le_top) fun f => ?_
  rw [valR_spMap_comp _ o U h₀, ← ho, valR_spMap_comp _ t U h₁]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, H U f h₀]

/- English proof (translation)
Introduce `S P y d ⟨h₁, h₂⟩ w hw`. Take `⟨v, ⟨hv, hd⟩, -⟩` from `h₂ w`. Set `t : Sp (DualNumber ℂ) ⟶ d.B.left` to `v.left`. Establish `ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = LieVB.unitSec d.B` using `hv`. Establish `hb : t ≫ d.B.hom = spMap (algebraMap ℂ (DualNumber ℂ))` using `Over.w v`.

Establish `hu : LieVB.unitSec d.B ≫ d.φ = y ≫ LieVB.unitSec P.A` using `LieVB.unitSec_comp d.isPull`. Establish `ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t ≫ d.φ = y ≫ LieVB.unitSec P.A`. Rewrite using `[← Category.assoc, ht, hu]`. Establish `e₁` using `eq_const (t ≫ d.φ) _ ho fun W f hW => by`. Establish `hW' : ⊤ ≤ t ⁻¹ᵁ d.φ ⁻¹ᵁ W` using `le_preimage_of_fst (t ≫ d.φ) W (ho ▸ hW)`.

Rewrite using `[valR_comp, valR_eq _ _ hW']`. Use `(hd (d.φ ⁻¹ᵁ W) hW' (d.φ.app W f)).trans (Eq.trans ?_ (hw W f hW))` and prove the remaining obligations. Establish `e : (fun z => valAt' (d.u.ex z).left (d.φ ⁻¹ᵁ W) (d.φ.app W f)) = d.fn W f`. Use function extensionality and compare the values at `fun z => (valR_comp _ _ _ _).symm`. Rewrite using `[e]`.

Use `conv_lhs => rw [← Finset.univ_sum_single w]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[show (Pi.single a (w a) : Fin P.g → ℂ) = w a • Pi.single a 1 by`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]`.

Both sides reduce to the same expression. Establish `e₂ : t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ LieVB.unitSec d.B`. Use `d.isPull.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[e₁, Category.assoc, hu]`. Rewrite using `[hb, Category.assoc, LieVB.sec_hom, Category.comp_id]`.

Use `(h₁ v hv).unique hd fun U h f => ?_` and prove the remaining obligations. Establish `h₀ : ⊤ ≤ LieVB.unitSec d.B ⁻¹ᵁ U` using `ht ▸ le_preimage_comp _ t h le_top`. Rewrite using `[map_zero]`. Use `(congrArg TrivSqZeroExt.snd (valR_eq t U h f)).symm.trans ?_` and prove the remaining obligations. Rewrite using `[e₂, valR_spMap_comp _ _ U h₀]`.

Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem eq_zero_of_cov : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y),
    ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧
      (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) →
    ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)),
      ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0 := by
  intro S P y d ⟨h₁, h₂⟩ w hw
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  let t : Sp (DualNumber ℂ) ⟶ d.B.left := v.left
  have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = LieVB.unitSec d.B := hv
  have hb : t ≫ d.B.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  have hu : LieVB.unitSec d.B ≫ d.φ = y ≫ LieVB.unitSec P.A := LieVB.unitSec_comp d.isPull
  have ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t ≫ d.φ = y ≫ LieVB.unitSec P.A := by
    rw [← Category.assoc, ht, hu]
  have e₁ := eq_const (t ≫ d.φ) _ ho fun W f hW => by
    have hW' : ⊤ ≤ t ⁻¹ᵁ d.φ ⁻¹ᵁ W := le_preimage_of_fst (t ≫ d.φ) W (ho ▸ hW)
    rw [valR_comp, valR_eq _ _ hW']
    refine (hd (d.φ ⁻¹ᵁ W) hW' (d.φ.app W f)).trans (Eq.trans ?_ (hw W f hW))
    have e : (fun z => valAt' (d.u.ex z).left (d.φ ⁻¹ᵁ W) (d.φ.app W f)) = d.fn W f :=
      funext fun z => (valR_comp _ _ _ _).symm
    rw [e]
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Pi.single a (w a) : Fin P.g → ℂ) = w a • Pi.single a 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    rfl
  have e₂ : t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ LieVB.unitSec d.B := by
    refine d.isPull.1.hom_ext ?_ ?_
    · rw [e₁, Category.assoc, hu]
    · rw [hb, Category.assoc, LieVB.sec_hom, Category.comp_id]
  refine (h₁ v hv).unique hd fun U h f => ?_
  have h₀ : ⊤ ≤ LieVB.unitSec d.B ⁻¹ᵁ U := ht ▸ le_preimage_comp _ t h le_top
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd (valR_eq t U h f)).symm.trans ?_
  rw [e₂, valR_spMap_comp _ _ U h₀]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.UnifImmersive
