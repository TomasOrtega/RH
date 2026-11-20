import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectivePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSummandUnitSmul

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord defTerm)
open GlobalTheory.CMVal (modUnits unitRel)

namespace GlobalTheory.HilbFam.BrVal

/- English proof (translation)
Rewrite using `[← NumberField.Embeddings.card F ℂ]`. Use `Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `τ τ' hτ`. Use extensionality with `y`. Use `DFunLike.congr_fun hτ y` as an intermediate fact.

Simplify using `using this`. Introduce `φ`. Establish `hr : NumberField.ComplexEmbedding.IsReal φ` using `IsTotallyReal.complexEmbedding_isReal φ`. Conclude with `⟨hr.embedding, by ext y; simp⟩`.
-/
theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]`.
-/
theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

/- English proof (translation)
Unfold `defTerm`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod, prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]`.
-/
theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

/- English proof (translation)
Simplify using `only [defCoord, map_mul, ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

end GlobalTheory.HilbFam.BrVal

namespace GlobalTheory.HilbFam.BrVal

/- English proof (translation)
Introduce `E _ _ _ I _ _ φ e θ τ Λ L n k z G hI hk hφ hθ hn hL hG`. Take `⟨i0⟩` from `hI`. Use `set T : (Fin 2 → FR E) → E := fun x ↦ (x 0 : E) * θ + (x 1 : E) with hT`. Establish `hTb : Function.Bijective T` using `GlobalTheory.HilbFam.EBasis.bijective_pair E (φ i0) θ (by`. Rewrite using `[hθ i0, UpperHalfPlane.coe_im]`.

Conclude with `(UpperHalfPlane.im_pos τ).ne')`. Establish `hnE : (n : E) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Use `set B : (Fin 2 → FR E) → E := fun x ↦ (n : E)⁻¹ * T x with hB`. Establish `hBinj : Function.Injective B` using `fun x y h ↦ hTb.1 (mul_left_cancel₀ (inv_ne_zero hnE) h)`. Establish `hB0 : B 0 = 0` using `by simp [hB, hT]`.

Establish `hLB : ∀ x, x ∈ L ↔ B x ∈ Λ`. Introduce `x`. Rewrite using `[hL x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hny⟩`.

Establish `: B x = y` using `by show (n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E)) = y`. Rewrite using `[← hny, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]`. Rewrite using `[this]`. Conclude with `hy`. Introduce `h`.

Conclude with `⟨B x, h, by show (n : E) * ((n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E))) = _`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hnE, one_mul]⟩`. Establish `hBu : ∀ (u : (OF E)ˣ) (x : Fin 2 → FR E), B (u • x) = algebraMap (OF E) E (u : OF E) * B x`. Introduce `u x`. Establish `h0 : ∀ j, (((u • x) j : FR E) : E) = (((u : OF E) : FR E) : E) * ((x j : FR E) : E)`.

Introduce `j`. Rewrite using `[Pi.smul_apply, Units.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `only [hB, hT, h0]`. Use `show _ = (((u : OF E) : FR E) : E) * _`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcoord : ∀ (x : Fin 2 → FR E) (i : I), coord (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) x (e i) = (n : ℂ) * defCoord φ z (B x) i`. Introduce `x i`. Establish `h1 : T x = (n : E) * B x` using `by simp only [hB]; rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]`. Establish `h2 : defCoord φ z (T x) i = (n : ℂ) * defCoord φ z (B x) i`.

Rewrite using `[h1, defCoord_mul φ z _ _ i (by simp)]; simp`. Rewrite using `[← h2]`. Simplify using `only [coord, defCoord, hT, map_add, map_mul, hφ, hθ, Equiv.symm_apply_apply, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Use `set b : Emb (FR E) → ℂ := fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ)) with hb`.

Use `set a : Emb (FR E) → ℂ := fun j ↦ 1 + z (e.symm j) * 1 with ha`. Use `set d := Module.finrank ℚ (FR E) with hd`. Establish `hcard : Fintype.card I = d`. Rewrite using `[Fintype.card_congr e, hd, ← card_realEmb (FR E)]`. Establish `hprod : ∀ x, ∏ j, coord b a x j = ((n : ℂ) ^ d) * ∏ i, defCoord φ z (B x) i`.

Introduce `x`. Rewrite using `[← Equiv.prod_comp e]`. Simplify using `only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]`. Use `set c : ℂ → ℂ := fun σ ↦ (((n : ℂ) ^ d)⁻¹) ^ k * ((((n : ℝ) ^ d : ℝ)) : ℂ) ^ (-2 * σ) with hc`. Establish `hterm : ∀ σ x, gTerm k σ b a x = c σ * defTerm φ k z σ (B x)`.

Introduce `σ x`. Rewrite using `[defTerm_eq, gTerm, hprod, hc]`. Simplify using `only`. Rewrite using `[_root_.mul_inv, _root_.mul_pow, norm_mul, norm_pow, Complex.norm_natCast, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hBne : ∀ x, x ≠ 0 → B x ≠ 0` using `fun x hx h ↦ hx (hBinj (h.trans hB0.symm))`. Set `ι : cls L → modUnits Λ` to `fun q ↦ ⟨Quotient.mk _ (B q.1.out), B q.1.out, (hLB _).1 q.2.1, hBne _ q.2.2, rfl⟩`. Establish `hinj : Function.Injective ι`. Introduce `q1 q2 h`. Establish `h' : Quotient.mk (unitRel (E` using `E)) (B q1.1.out) = Quotient.mk _ (B q2.1.out) := congrArg Subtype.val h`.

Take `⟨u, hu⟩` from `Quotient.exact h'`. Rewrite `hu` using `[← hBu]`. Establish `hx` using `hBinj hu`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]`.

Conclude with `(Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u, hx.symm⟩)).symm`. Establish `hsurj : Function.Surjective ι`. Introduce and unpack `⟨p, y, hy, hy0, hp⟩`. Take `⟨x, hx⟩` from `hTb.2 ((n : E) * y)`. Establish `hBx : B x = y` using `by show (n : E)⁻¹ * T x = y`.

Rewrite using `[hx, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]`. Establish `hxL : x ∈ L` using `(hLB x).2 (hBx ▸ hy)`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hy0 (hBx ▸ hB0)`. Take `⟨g, hg⟩` from `MulAction.mem_orbit_iff.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x)))`. Use `set q0 := Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x with hq0`.

Establish `hmem : q0 ∈ cls L`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg, Units.smul_def]`. Conclude with `L.smul_mem _ hxL`. Rewrite using `[← hg]`.

Introduce `h0`. Conclude with `hx0 ((smul_eq_zero_iff_eq g).1 h0)`. Use `⟨⟨q0, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Quotient.mk _ (B q0.out) = p`.

Rewrite using `[← hp, ← hg, hBu g x, hBx]`. Conclude with `(Quotient.sound (show (unitRel (E := E)).r y (algebraMap (OF E) E (g : OF E) * y) from ⟨g, rfl⟩)).symm`. Establish `hval : ∀ σ (q : cls L), gTerm k σ b a q.1.out = c σ * defTerm φ k z σ (ι q).1.out`. Introduce `σ q`. Take `⟨u, hu⟩ : (unitRel (E` from `E)).r (B q.1.out) (ι q).1.out := Quotient.exact (Quotient.out_eq (ι q).1).symm`.

Rewrite using `[hu, ← hBu, ← hterm, GlobalTheory.HilbFam.gTerm_unit_smul (FR E) k σ b a u q.1.out hk]`. Establish `hsum : ∀ σ S, HasSum (fun p : modUnits Λ ↦ defTerm φ k z σ p.1.out) S → HasSum (fun q : cls L ↦ gTerm k σ b a q.1.out) (c σ * S)`. Introduce `σ S h`. Simplify using `only [hval]`. Conclude with `((Equiv.hasSum_iff (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).2 h).mul_left (c σ)`.

Establish `hc0 : c 0 = (((n : ℂ) ^ d)⁻¹) ^ k` using `by simp [hc]`. Use `⟨fun hk2 ↦ ?_, fun hk2 ↦ ?_⟩` and prove the remaining obligations. Establish `hd0 : ∀ x : E, defTerm φ k z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ k`. Introduce `x`. Simplify using `[defTerm]`.

Rewrite using `[← hc0]`. Use `hsum 0 G ?_` and prove the remaining obligations. Simplify using `only [hd0]`. Conclude with `hG.1 hk2`. Take `⟨H, hHd, hHs, hH0⟩` from `hG.2 hk2`.

Substitute `hk2` using the available equality. Establish `hn' : ((((n : ℝ) ^ d : ℝ)) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (by positivity)`. Establish `hcd : Differentiable ℂ c` using `fun σ ↦ (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn'))`. Use `⟨fun σ ↦ c σ * H σ, hcd.differentiableOn.mul hHd, fun σ hσ ↦ hsum σ _ (hHs σ hσ), ?_⟩` and prove the remaining obligations. Rewrite using `[hH0, ← hc0]`.
-/
theorem isGVal_of_isEisValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (k : ℕ) (z : I → ℂ) (G : ℂ), Nonempty I → Even k → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsEisValue φ k Λ z G → IsGVal k L (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) ((((n : ℂ) ^ Module.finrank ℚ (FR E))⁻¹) ^ k * G) := by
  intro E _ _ _ I _ _ φ e θ τ Λ L n k z G hI hk hφ hθ hn hL hG
  obtain ⟨i0⟩ := hI
  set T : (Fin 2 → FR E) → E := fun x ↦ (x 0 : E) * θ + (x 1 : E) with hT
  have hTb : Function.Bijective T := GlobalTheory.HilbFam.EBasis.bijective_pair E (φ i0) θ (by
    rw [hθ i0, UpperHalfPlane.coe_im]; exact (UpperHalfPlane.im_pos τ).ne')
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set B : (Fin 2 → FR E) → E := fun x ↦ (n : E)⁻¹ * T x with hB
  have hBinj : Function.Injective B := fun x y h ↦ hTb.1 (mul_left_cancel₀ (inv_ne_zero hnE) h)
  have hB0 : B 0 = 0 := by simp [hB, hT]
  have hLB : ∀ x, x ∈ L ↔ B x ∈ Λ := by
    intro x
    rw [hL x]
    constructor
    · rintro ⟨y, hy, hny⟩
      have : B x = y := by
        show (n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E)) = y
        rw [← hny, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
      rw [this]; exact hy
    · intro h
      exact ⟨B x, h, by
        show (n : E) * ((n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E))) = _
        rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]⟩
  have hBu : ∀ (u : (OF E)ˣ) (x : Fin 2 → FR E), B (u • x) = algebraMap (OF E) E (u : OF E) * B x := by
    intro u x
    have h0 : ∀ j, (((u • x) j : FR E) : E) = (((u : OF E) : FR E) : E) * ((x j : FR E) : E) := by
      intro j
      rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]
      rfl
    simp only [hB, hT, h0]
    show _ = (((u : OF E) : FR E) : E) * _
    ring
  have hcoord : ∀ (x : Fin 2 → FR E) (i : I),
      coord (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) x (e i)
        = (n : ℂ) * defCoord φ z (B x) i := by
    intro x i
    have h1 : T x = (n : E) * B x := by simp only [hB]; rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]
    have h2 : defCoord φ z (T x) i = (n : ℂ) * defCoord φ z (B x) i := by
      rw [h1, defCoord_mul φ z _ _ i (by simp)]; simp
    rw [← h2]
    simp only [coord, defCoord, hT, map_add, map_mul, hφ, hθ, Equiv.symm_apply_apply, Complex.conj_ofReal]
    ring
  set b : Emb (FR E) → ℂ := fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ)) with hb
  set a : Emb (FR E) → ℂ := fun j ↦ 1 + z (e.symm j) * 1 with ha
  set d := Module.finrank ℚ (FR E) with hd
  have hcard : Fintype.card I = d := by
    rw [Fintype.card_congr e, hd, ← card_realEmb (FR E)]
  have hprod : ∀ x, ∏ j, coord b a x j = ((n : ℂ) ^ d) * ∏ i, defCoord φ z (B x) i := by
    intro x
    rw [← Equiv.prod_comp e]
    simp only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  set c : ℂ → ℂ := fun σ ↦ (((n : ℂ) ^ d)⁻¹) ^ k * ((((n : ℝ) ^ d : ℝ)) : ℂ) ^ (-2 * σ) with hc
  have hterm : ∀ σ x, gTerm k σ b a x = c σ * defTerm φ k z σ (B x) := by
    intro σ x
    rw [defTerm_eq, gTerm, hprod, hc]
    simp only
    rw [_root_.mul_inv, _root_.mul_pow, norm_mul, norm_pow, Complex.norm_natCast, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
    ring
  have hBne : ∀ x, x ≠ 0 → B x ≠ 0 := fun x hx h ↦ hx (hBinj (h.trans hB0.symm))
  let ι : cls L → modUnits Λ := fun q ↦ ⟨Quotient.mk _ (B q.1.out), B q.1.out, (hLB _).1 q.2.1, hBne _ q.2.2, rfl⟩
  have hinj : Function.Injective ι := by
    intro q1 q2 h
    have h' : Quotient.mk (unitRel (E := E)) (B q1.1.out) = Quotient.mk _ (B q2.1.out) := congrArg Subtype.val h
    obtain ⟨u, hu⟩ := Quotient.exact h'
    rw [← hBu] at hu
    have hx := hBinj hu
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact (Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u, hx.symm⟩)).symm
  have hsurj : Function.Surjective ι := by
    rintro ⟨p, y, hy, hy0, hp⟩
    obtain ⟨x, hx⟩ := hTb.2 ((n : E) * y)
    have hBx : B x = y := by
      show (n : E)⁻¹ * T x = y
      rw [hx, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
    have hxL : x ∈ L := (hLB x).2 (hBx ▸ hy)
    have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (hBx ▸ hB0)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x)))
    set q0 := Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x with hq0
    have hmem : q0 ∈ cls L := by
      refine ⟨?_, ?_⟩
      · rw [← hg, Units.smul_def]; exact L.smul_mem _ hxL
      · rw [← hg]; intro h0; exact hx0 ((smul_eq_zero_iff_eq g).1 h0)
    refine ⟨⟨q0, hmem⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (B q0.out) = p
    rw [← hp, ← hg, hBu g x, hBx]
    exact (Quotient.sound (show (unitRel (E := E)).r y (algebraMap (OF E) E (g : OF E) * y) from ⟨g, rfl⟩)).symm
  have hval : ∀ σ (q : cls L), gTerm k σ b a q.1.out = c σ * defTerm φ k z σ (ι q).1.out := by
    intro σ q
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r (B q.1.out) (ι q).1.out :=
      Quotient.exact (Quotient.out_eq (ι q).1).symm
    rw [hu, ← hBu, ← hterm, GlobalTheory.HilbFam.gTerm_unit_smul (FR E) k σ b a u q.1.out hk]
  have hsum : ∀ σ S, HasSum (fun p : modUnits Λ ↦ defTerm φ k z σ p.1.out) S →
      HasSum (fun q : cls L ↦ gTerm k σ b a q.1.out) (c σ * S) := by
    intro σ S h
    simp only [hval]
    exact ((Equiv.hasSum_iff (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).2 h).mul_left (c σ)
  have hc0 : c 0 = (((n : ℂ) ^ d)⁻¹) ^ k := by simp [hc]
  refine ⟨fun hk2 ↦ ?_, fun hk2 ↦ ?_⟩
  · have hd0 : ∀ x : E, defTerm φ k z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
      intro x; simp [defTerm]
    rw [← hc0]
    refine hsum 0 G ?_
    simp only [hd0]
    exact hG.1 hk2
  · obtain ⟨H, hHd, hHs, hH0⟩ := hG.2 hk2
    subst hk2
    have hn' : ((((n : ℝ) ^ d : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
    have hcd : Differentiable ℂ c := fun σ ↦
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn'))
    refine ⟨fun σ ↦ c σ * H σ, hcd.differentiableOn.mul hHd, fun σ hσ ↦ hsum σ _ (hHs σ hσ), ?_⟩
    rw [hH0, ← hc0]

end GlobalTheory.HilbFam.BrVal
