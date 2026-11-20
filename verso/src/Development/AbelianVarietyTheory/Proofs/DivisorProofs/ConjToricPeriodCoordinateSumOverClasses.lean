import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ConjCoordToric

/- English proof (translation)
Unfold `lamF`. Rewrite using `[map_mul, Units.val_mul, IdeleModule.modF_mul, mul_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamF_mul {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y y' : (Af E)ˣ) :
    lamF s χ (y * y') = lamF s χ y * lamF s χ y' := by
  unfold lamF
  rw [map_mul, Units.val_mul, IdeleModule.modF_mul, mul_pow]
  push_cast
  ring

/- English proof (translation)
Unfold `GlobalTheory.ToricTransport.coordIn`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coordIn_eq_mul {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold GlobalTheory.ToricTransport.coordIn
  ring

/- English proof (translation)
Take `⟨q, hq⟩ : ∃ q : PicO c, q = QuotientGroup.mk y` from `⟨_, rfl⟩`. Take `⟨S, hS⟩` from `h q`. Establish `hq' : (QuotientGroup.mk q.out : PicO c) = QuotientGroup.mk y` using `by rw [QuotientGroup.out_eq', hq]`. Take `⟨a, ⟨α, rfl⟩, u, hu, hau⟩` from `Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq')`. Establish `hy : y = Units.map (algebraMap E (Af E)).toMonoidHom α * q.out * u`.

Establish `: y = q.out * (Units.map (algebraMap E (Af E)).toMonoidHom α * u)` using `by rw [hau]; group`. Rewrite using `[this]`. The two sides agree by associativity and commutativity. Rewrite using `[hy, GlobalTheory.ClassInv.lattice_princ_mul_unit _ α hu]`. Conclude with `⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).1⟩`.
-/
theorem exists_latSum {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E))
    (h : ∀ q : PicO c, ∃ S, IsLatSum φ (2 * s) κ (lattice c q.out) S) (y : (Af E)ˣ) :
    ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : PicO c, q = QuotientGroup.mk y := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := h q
  have hq' : (QuotientGroup.mk q.out : PicO c) = QuotientGroup.mk y := by rw [QuotientGroup.out_eq', hq]
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq')
  have hy : y = Units.map (algebraMap E (Af E)).toMonoidHom α * q.out * u := by
    have : y = q.out * (Units.map (algebraMap E (Af E)).toMonoidHom α * u) := by rw [hau]; group
    rw [this]
    ac_rfl
  rw [hy, GlobalTheory.ClassInv.lattice_princ_mul_unit _ α hu]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).1⟩

/- English proof (translation)
Introduce `hC K _ _ d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hE hφ hφK s hs κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'`. Take `⟨hAux, hVal, -, S, hS, rfl⟩` from `hV`. Take `⟨⟨hlam, hInf'⟩, hfin', S'', hS'', rfl⟩` from `hV'`. Use `haveI : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _`. Establish `hunit' : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ' u = 1`.

Introduce `u hu`. Establish `h1 : lamF s χ' u = 1`. Rewrite using `[hlam]`. Unfold `lamF`. Rewrite using `[GlobalTheory.ClassInv.finPart_unit hVal hu, ObjModel.modF_unit hu]`.

Simplify using the standard rewrite rules. Unfold `lamF at h1`. Rewrite `h1` using `[ObjModel.modF_unit hu]`. Simplify using `at h1`. Conclude with `h1`.

Establish `hex : ∀ q : PicO (condQ 𝔣 Q), ∃ S', IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (q.out * (upIdele K E t)⁻¹)) S'` using `fun q => exists_latSum hφ s κ' (condQ 𝔣 Q) (fun q => ⟨S'' q, hS'' q⟩) _`. Use `choose S' hS' using hex`. Establish `hLC : ∀ q : PicO (condQ 𝔣 Q), g (coordIn E d s κ Ω₀ 1 * S q 0) = coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)` using `fun q => by`. Rewrite using `[← coordIn_eq_mul, ← coordIn_eq_mul]`. Conclude with `hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hAux⟩ κ κ' hκ' q.out (S q) (S' q) (hS q) (hS' q)`.

Establish `hCI : ∀ q : PicO (condQ 𝔣 Q), (lamF s χ' (q.out * (upIdele K E t)⁻¹))⁻¹ * S' q 0 = (lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0`. Introduce `q`. Use `GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hInf' hunit' _ _ (S' q) (S'' _) ?_ (hS' q) (hS'' _)` and prove the remaining obligations. Rewrite using `[QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Establish `hsum : ∀ (ψ : HChar E) (R : PicO (condQ 𝔣 Q) → ℂ → ℂ), (∑ᶠ q : PicO (condQ 𝔣 Q), ((finPart ψ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * R q 0) = ∑ q, (lamF s ψ q.out)⁻¹ * R q 0` using `fun ψ R => by`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression. Rewrite using `[hsum, hsum, coordIn_eq_mul (E := E) d s κ Ω₀, coordIn_eq_mul (E := E) d s κ Ω₁]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[show coordIn E d s κ Ω₀ 1 * ((lamF s χ q.out)⁻¹ * S q 0) = (lamF s χ q.out)⁻¹ * (coordIn E d s κ Ω₀ 1 * S q 0) by ring, map_mul, map_inv₀]`. Use `_ = ∑ q, (lamF s χ' q.out)⁻¹ * (coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)) := by`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hlam, hLC]`.

Use `_ = ∑ q, coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * ((lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0) := by`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← hCI q]`. Establish `hm : lamF s χ' q.out = lamF s χ' (q.out * (upIdele K E t)⁻¹) * lamF s χ' (upIdele K E t)`. Rewrite using `[← lamF_mul, inv_mul_cancel_right]`.

Rewrite using `[hm, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * ∑ q, (lamF s χ' q.out)⁻¹ * S'' q 0 := by`. Rewrite using `[Finset.mul_sum]`. Conclude with `Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (upIdele K E t)⁻¹ : PicO (condQ 𝔣 Q))) _ _ fun q => rfl`.

Use `_ = _ := by ring`.
-/
theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  intro hC K _ _ d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hE hφ hφK s hs κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  classical
  obtain ⟨hAux, hVal, -, S, hS, rfl⟩ := hV
  obtain ⟨⟨hlam, hInf'⟩, hfin', S'', hS'', rfl⟩ := hV'
  haveI : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  have hunit' : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ' u = 1 := by
    intro u hu
    have h1 : lamF s χ' u = 1 := by
      rw [hlam]
      unfold lamF
      rw [GlobalTheory.ClassInv.finPart_unit hVal hu, ObjModel.modF_unit hu]
      simp
    unfold lamF at h1
    rw [ObjModel.modF_unit hu] at h1
    simp at h1
    exact h1
  have hex : ∀ q : PicO (condQ 𝔣 Q), ∃ S', IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (q.out * (upIdele K E t)⁻¹)) S' :=
    fun q => exists_latSum hφ s κ' (condQ 𝔣 Q) (fun q => ⟨S'' q, hS'' q⟩) _
  choose S' hS' using hex
  have hLC : ∀ q : PicO (condQ 𝔣 Q), g (coordIn E d s κ Ω₀ 1 * S q 0) =
      coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0) := fun q => by
    rw [← coordIn_eq_mul, ← coordIn_eq_mul]
    exact hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hAux⟩ κ κ' hκ' q.out (S q) (S' q)
      (hS q) (hS' q)
  have hCI : ∀ q : PicO (condQ 𝔣 Q), (lamF s χ' (q.out * (upIdele K E t)⁻¹))⁻¹ * S' q 0 =
      (lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0 := by
    intro q
    refine GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hInf' hunit' _ _ (S' q) (S'' _) ?_
      (hS' q) (hS'' _)
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  have hsum : ∀ (ψ : HChar E) (R : PicO (condQ 𝔣 Q) → ℂ → ℂ),
      (∑ᶠ q : PicO (condQ 𝔣 Q), ((finPart ψ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * R q 0) =
        ∑ q, (lamF s ψ q.out)⁻¹ * R q 0 := fun ψ R => by
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [hsum, hsum, coordIn_eq_mul (E := E) d s κ Ω₀, coordIn_eq_mul (E := E) d s κ Ω₁]
  calc g (coordIn E d s κ Ω₀ 1 * ∑ q, (lamF s χ q.out)⁻¹ * S q 0)
      = ∑ q, (g (lamF s χ q.out))⁻¹ * g (coordIn E d s κ Ω₀ 1 * S q 0) := by
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show coordIn E d s κ Ω₀ 1 * ((lamF s χ q.out)⁻¹ * S q 0) =
          (lamF s χ q.out)⁻¹ * (coordIn E d s κ Ω₀ 1 * S q 0) by ring, map_mul, map_inv₀]
    _ = ∑ q, (lamF s χ' q.out)⁻¹ * (coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hlam, hLC]
    _ = ∑ q, coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ((lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← hCI q]
        have hm : lamF s χ' q.out = lamF s χ' (q.out * (upIdele K E t)⁻¹) * lamF s χ' (upIdele K E t) := by
          rw [← lamF_mul, inv_mul_cancel_right]
        rw [hm, mul_inv]
        ring
    _ = coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ∑ q, (lamF s χ' q.out)⁻¹ * S'' q 0 := by
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (upIdele K E t)⁻¹ : PicO (condQ 𝔣 Q))) _ _ fun q => rfl
    _ = _ := by ring

end GlobalTheory.ConjCoordToric
