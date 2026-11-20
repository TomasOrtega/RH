import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteProjectiveRankAtStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

/- English proof (translation)
Simplify using `only [mul_zpow, ← zpow_mul, zpow_add]`. Conclude with `_root_.mul_mul_mul_comm _ _ _ _`.
-/
theorem zpow_two_var {G : Type*} [CommGroup G] (x y : G) (a b c d a' b' : ℤ) :
    (x ^ a * y ^ b) ^ a' * (x ^ c * y ^ d) ^ b' = x ^ (a * a' + c * b') * y ^ (b * a' + d * b') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  exact _root_.mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, comp_pow]`. Consider the case `negSucc n => simp only [zpow_negSucc, GrpObj.comp_inv, comp_pow]`.
-/
theorem comp_zpow_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X Y : C} [GrpObj G]
    (f : X ⟶ Y) (g : Y ⟶ G) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, comp_pow]
  | negSucc n => simp only [zpow_negSucc, GrpObj.comp_inv, comp_pow]

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, psiMap_fst, psiMap_fst, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst, psiMap_snd, zpow_two_var]`. Rewrite using `[Category.assoc, psiMap_snd, psiMap_snd, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst, psiMap_snd, zpow_two_var]`.
-/
theorem psiMap_comp {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (a b c d a' b' c' d' : ℤ) :
    psiMap A a b c d ≫ psiMap A a' b' c' d' =
      psiMap A (a * a' + c * b') (b * a' + d * b') (a * c' + c * d') (b * c' + d * d') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, psiMap_fst, psiMap_fst, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]
  · rw [Category.assoc, psiMap_snd, psiMap_snd, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[psiMap_fst, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.mul_one, zpow_natCast]`. Rewrite using `[psiMap_snd, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.one_mul, zpow_natCast]`.
-/
theorem psiMap_diag {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (n : ℕ) :
    psiMap A n 0 0 n = Out.mulA (A ⊗ A) n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [psiMap_fst, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.mul_one, zpow_natCast]
  · rw [psiMap_snd, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.one_mul, zpow_natCast]

/- English proof (translation)
Establish `hgs : IsSeparated g` using `MorphismProperty.of_postcomp (W' := ⊤) @IsSeparated g p trivial (by rw [hg]; infer_instance)`. Use `haveI : LocallyOfFiniteType (g ≫ p) := by rw [hg]; infer_instance`. Use `haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p`. Use `haveI : FormallyUnramified (g ≫ f) := by rw [h2]; infer_instance`. Use `haveI : FormallyUnramified g := FormallyUnramified.of_comp g f`.

Use `haveI : Etale (f ≫ g) := by rw [h1]; infer_instance`. Use `haveI : IsFinite (f ≫ g) := by rw [h1]; infer_instance`. Conclude with `⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g hgs inferInstance, Etale.of_comp f g⟩`.
-/
theorem finite_etale_of_comp_eq {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] (f g m : X ⟶ X) [IsFinite m] [Etale m] (hg : g ≫ p = p)
    (h1 : f ≫ g = m) (h2 : g ≫ f = m) : IsFinite f ∧ Etale f := by
  have hgs : IsSeparated g :=
    MorphismProperty.of_postcomp (W' := ⊤) @IsSeparated g p trivial (by rw [hg]; infer_instance)
  haveI : LocallyOfFiniteType (g ≫ p) := by rw [hg]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  haveI : FormallyUnramified (g ≫ f) := by rw [h2]; infer_instance
  haveI : FormallyUnramified g := FormallyUnramified.of_comp g f
  haveI : Etale (f ≫ g) := by rw [h1]; infer_instance
  haveI : IsFinite (f ≫ g) := by rw [h1]; infer_instance
  exact ⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g hgs inferInstance,
    Etale.of_comp f g⟩

/- English proof (translation)
Break down `Int.natAbs_eq d with h | h` into its components or cases. Conclude with `⟨1, by rw [_root_.one_mul]; exact h⟩`. Conclude with `⟨-1, by rw [h]; ring_nf; simp⟩`.
-/
theorem exists_sign_mul (d : ℤ) : ∃ s : ℤ, s * d = (d.natAbs : ℤ) := by
  rcases Int.natAbs_eq d with h | h
  · exact ⟨1, by rw [_root_.one_mul]; exact h⟩
  · exact ⟨-1, by rw [h]; ring_nf; simp⟩

/- English proof (translation)
Introduce `K _ _ A _ hA a₁ b₁ a₂ b₂ hd`. Use `haveI := hA.comm`. Use `set n := (a₁ * b₂ - b₁ * a₂).natAbs with hn_def`. Establish `hn : (n : K) ≠ 0`. Break down `Int.natAbs_eq (a₁ * b₂ - b₁ * a₂) with h | h` into its components or cases.

Rewrite `hd` using `[h, Int.cast_natCast]`. Conclude with `hd`. Rewrite `hd` using `[h, Int.cast_neg, Int.cast_natCast, neg_ne_zero]`. Conclude with `hd`. Use `haveI hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA`.

Take `⟨hfin, -, het, r, hr0, -, hall, -⟩` from `GlobalTheory.AbelianMulFin.mulA_finite_locallyFree K (A ⊗ A) n hn`. Take `⟨s, hs⟩` from `exists_sign_mul (a₁ * b₂ - b₁ * a₂)`. Rewrite `hs` using `[← hn_def]`. Use `set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ`. Use `set ψ' := psiMap A (s * b₂) (-(s * b₁)) (-(s * a₂)) (s * a₁) with hψ'`.

Establish `h1 : ψ ≫ ψ' = Out.mulA (A ⊗ A) n`. Rewrite using `[hψ, hψ', psiMap_comp, ← psiMap_diag]`. Apply the tactic sequence `congr 1 <;> push_cast <;> first | ring1 | linear_combination hs`. Establish `h2 : ψ' ≫ ψ = Out.mulA (A ⊗ A) n`. Rewrite using `[hψ, hψ', psiMap_comp, ← psiMap_diag]`.

Apply the tactic sequence `congr 1 <;> push_cast <;> first | ring1 | linear_combination hs`. Establish `h1' : ψ.left ≫ ψ'.left = (Out.mulA (A ⊗ A) n).left` using `by rw [← Over.comp_left, h1]`. Establish `h2' : ψ'.left ≫ ψ.left = (Out.mulA (A ⊗ A) n).left` using `by rw [← Over.comp_left, h2]`. Use `haveI := hAA.proper`. Use `haveI := hAA.smooth`.

Use `haveI := hAA.geomConnected`. Take `⟨hψfin, hψet⟩` from `finite_etale_of_comp_eq (A ⊗ A).hom ψ.left ψ'.left _ (Over.w ψ') h1' h2'`. Take `⟨hψ'fin, hψ'et⟩` from `finite_etale_of_comp_eq (A ⊗ A).hom ψ'.left ψ.left _ (Over.w ψ) h2' h1'`. Use `haveI : ConnectedSpace (A ⊗ A).left := GeometricallyConnected.connectedSpace (A ⊗ A).hom (A ⊗ A).hom.isOpenMap`. Set `o : (A ⊗ A).left` to `Classical.arbitrary _`.

Use `set r' := ψ.left.finrank o with hr'`. Establish `hall' : ∀ y, ψ.left.finrank y = r'` using `fun y => (Scheme.Hom.isLocallyConstant_finrank ψ.left).apply_eq_of_preconnectedSpace y o`. Use `⟨hψfin, inferInstance, inferInstance, r', hall', fun h0 => hr0 ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.FinrankComp.finrank_comp_of_const ψ.left ψ'.left r' hall' o`. Rewrite `e` using `[h1', hall o]`.

Rewrite using `[e, Nat.cast_mul, h0, zero_mul]`.
-/
theorem psiMap_finite_locallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K))
    [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 →
    IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧
      LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧
      ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  intro K _ _ A _ hA a₁ b₁ a₂ b₂ hd
  haveI := hA.comm
  set n := (a₁ * b₂ - b₁ * a₂).natAbs with hn_def
  have hn : (n : K) ≠ 0 := by
    rcases Int.natAbs_eq (a₁ * b₂ - b₁ * a₂) with h | h
    · rw [h, Int.cast_natCast] at hd; exact hd
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_ne_zero] at hd; exact hd
  haveI hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨hfin, -, het, r, hr0, -, hall, -⟩ :=
    GlobalTheory.AbelianMulFin.mulA_finite_locallyFree K (A ⊗ A) n hn
  obtain ⟨s, hs⟩ := exists_sign_mul (a₁ * b₂ - b₁ * a₂)
  rw [← hn_def] at hs
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set ψ' := psiMap A (s * b₂) (-(s * b₁)) (-(s * a₂)) (s * a₁) with hψ'
  have h1 : ψ ≫ ψ' = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h2 : ψ' ≫ ψ = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h1' : ψ.left ≫ ψ'.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h1]
  have h2' : ψ'.left ≫ ψ.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h2]
  haveI := hAA.proper
  haveI := hAA.smooth
  haveI := hAA.geomConnected
  obtain ⟨hψfin, hψet⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ.left ψ'.left _ (Over.w ψ') h1' h2'
  obtain ⟨hψ'fin, hψ'et⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ'.left ψ.left _ (Over.w ψ) h2' h1'
  haveI : ConnectedSpace (A ⊗ A).left :=
    GeometricallyConnected.connectedSpace (A ⊗ A).hom (A ⊗ A).hom.isOpenMap
  let o : (A ⊗ A).left := Classical.arbitrary _
  set r' := ψ.left.finrank o with hr'
  have hall' : ∀ y, ψ.left.finrank y = r' := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank ψ.left).apply_eq_of_preconnectedSpace y o
  refine ⟨hψfin, inferInstance, inferInstance, r', hall', fun h0 => hr0 ?_⟩
  have e := GlobalTheory.FinrankComp.finrank_comp_of_const ψ.left ψ'.left r' hall' o
  rw [h1', hall o] at e
  rw [e, Nat.cast_mul, h0, zero_mul]

end GlobalTheory.AmpleGen
