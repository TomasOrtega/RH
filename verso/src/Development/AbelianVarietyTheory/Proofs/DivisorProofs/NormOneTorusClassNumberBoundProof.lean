import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddNsmul

noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

/- English proof (translation)
Introduce `E _ _ _ r M G Λ hr hM hE hΛ`. Use `set c := IsCMField.complexConj E`. Take `⟨S, hS, hS'⟩` from `GlobalTheory.UCls.normOne_classes_le_classNumber E hE`. Take `⟨S', hS₂, hS₂'⟩` from `GlobalTheory.UCls.NormOneMod.normOne_mod E M hM`. Set `T : Finset (RA (maximalRealSubfield E) E)` to `(S ×ˢ S').image fun p => p.1 * p.2`.

Establish `hT : T.card ≤ classNumber E * M ^ (2 * fdeg E)` using `Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))`. Establish `hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b)`. Introduce `a b ha hb`. Unfold `IsTA at *`. Rewrite using `[map_mul, mul_mul_mul_comm, ha, hb, one_mul]`.

Establish `hone : IsTA c (1 : RA (maximalRealSubfield E) E)` using `by simp [IsTA]`. Set `Q` to `Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1`. Set `φ : T → Q` to `fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩`. Establish `hφ : Function.Surjective φ`. Introduce and unpack `⟨t, ht⟩`.

Take `⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩` from `hS' t ht`. Take `⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩` from `hS₂' k hk hkint`. Take `⟨g, hg, hdet⟩` from `GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1`. Establish `hmem : s * s' ∈ T` using `Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩`. Use `⟨⟨s * s', hmem⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [φ, dif_pos (hTA s s' hsTA hs'TA)]`. Use `Quot.sound ⟨u, hu, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[hdet]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
