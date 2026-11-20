import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewLocalPlaceData
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.UnipShiftEv

open Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC hB hG e' he u hu Ψ hΨ`. Establish `hH` using `hC.hH`. Establish `hH'` using `hC.hH'`. Establish `hY` using `hG.hV'`. Use `set X := incV F H.x with hX`.

Use `set Y := incV F H.y with hYdef`. Use `set X' := incV F H'.x with hX'`. Use `set I := incM F H.ι with hI`. Take `⟨hux, -⟩` from `GlobalTheory.StabNormal.prop_of_mem_unip' H hu`. Establish `hspan : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (w : Fin b → E), v = s • H.x + H.ι *ᵥ w + t • H.y`.

Introduce `v`. Establish `hv : v ∈ Submodule.span E (G.V'.L : Set (Fin (b + 2) → E))`. Rewrite using `[hY.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨s, t, w, -, -, -, hz⟩` from `hH.split z hz`. Conclude with `⟨s, t, w, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨s, t, w, rfl⟩` from `hy`. Take `⟨s', t', w', rfl⟩` from `hz`. Conclude with `⟨s + s', t + t', w + w', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul c y _ hy`. Take `⟨s, t, w, rfl⟩` from `hy`.

Conclude with `⟨c * s, c * t, c • w, by rw [Matrix.mulVec_smul]; module⟩`. Use `set c₀ : Fin (b + 2) → E := G.V'.J *ᵥ fun i => σ (H.x i) with hc₀`. Establish `hιc : ∀ w, (H.ι *ᵥ w) ⬝ᵥ c₀ = 0` using `fun w => (hH.orth w).1`. Establish `hxc : H.x ⬝ᵥ c₀ = 0` using `hH.xx`. Establish `hyx : H.y ⬝ᵥ c₀ ≠ 0`.

Introduce `h0`. Establish `hall : ∀ w : Fin (b + 2) → E, w ⬝ᵥ c₀ = 0`. Introduce `w`. Take `⟨s, t, v, rfl⟩` from `hspan w`. Rewrite using `[add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hxc, h0, hιc]`.

Simplify using the standard rewrite rules. Establish `hc0 : ∀ i, c₀ i = 0` using `fun i => by simpa using hall (Pi.single i 1)`. Establish `hxJ : H.x ᵥ* G.V'.J = 0`. Use function extensionality and compare the values at `i`. Establish `hσinj : Function.Injective σ` using `σ.toRingHom.injective`.

Apply `hσinj` to reduce the goal to its premises. Rewrite using `[Pi.zero_apply, map_zero, ← hc0 i]`. Simplify using `only [vecMul, mulVec, dotProduct, map_sum, map_mul, hc₀, Pi.zero_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hY.herm, mul_comm]`.

Establish `h1` using `hH.xy`. Unfold `form at h1`. Rewrite `h1` using `[dotProduct_mulVec, hxJ, zero_dotProduct]`. Conclude with `zero_ne_one h1`. Use `set C : Fin (b + 2) → AE F E := incM F G.V'.J *ᵥ fun i => cA σ (X i) with hC'`.

Establish `hCe : C = incV F c₀`. Rewrite using `[hC', hc₀, GlobalTheory.StabNormal.incM_mulVec]`. Use `congr 1`. Establish `hIC : ∀ z, (I *ᵥ z) ⬝ᵥ C = 0`. Introduce `z`.

Establish `h0 : c₀ ᵥ* H.ι = 0`. Use function extensionality and compare the values at `j`. Use `hιc (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[mulVec_single_one, dotProduct_comm]`. Conclude with `this`.

Rewrite using `[dotProduct_comm, dotProduct_mulVec, hCe, hI, ← GlobalTheory.StabNormal.incV_vecMul, h0]`. Simplify using `[incV, dotProduct]`. Establish `hXC : X ⬝ᵥ C = 0` using `by rw [hCe, hX, GlobalTheory.StabNormal.incV_dot, hxc, map_zero]`. Establish `hYC : IsUnit (Y ⬝ᵥ C)`. Rewrite using `[hCe, hYdef, GlobalTheory.StabNormal.incV_dot]`.

Conclude with `(isUnit_iff_ne_zero.2 hyx).map (inclR (F := F) (E := E) (AF F))`. Take `⟨s, t, w, hv⟩` from `GlobalTheory.StabNormal.decompA H.x H.y H.ι hspan (mat u *ᵥ Y)`. Rewrite `hv` using `[← hX, ← hI, ← hYdef]`. Establish `ht : t = 1`. Establish `h0` using `GlobalTheory.StabNormal.dot_invariant u X hux Y`.

Rewrite `h0` using `[← hC', hv, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hXC, hIC]`. Simplify using `only [smul_eq_mul, mul_zero, zero_add] at h0`. Establish `h2 : (t - 1) * (Y ⬝ᵥ C) = 0` using `by rw [sub_mul, h0, one_mul, sub_self]`. Conclude with `sub_eq_zero.1 ((hYC.mul_left_eq_zero).1 h2)`. Rewrite `hv` using `[ht, one_smul]`.

Establish `hww` using `GlobalTheory.IsoBLoc.pair_zero_of_form (F := F) σ G.W.J H'.x H'.x hH'.xx`. Establish `hiso : ∀ p q : Fin (b + 2) → AE F E, symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (vecMulVec p X') (vecMulVec q X') = 0`. Introduce `p q`. Rewrite using `[symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hww, mul_zero, mul_zero, map_zero]`. Establish `hadd : ∀ (p q : Fin (b + 2) → AE F E) (φ : Fn F (b + 2) (a + (b + 2))), G.M'.co.rho B.ψ (vecMulVec p X' + vecMulVec q X') φ = G.M'.co.rho B.ψ (vecMulVec p X') (G.M'.co.rho B.ψ (vecMulVec q X') φ)`.

Introduce `p q φ`. Use `GlobalTheory.DblSiegel.rho_add G.M'.co B.ψ ?_ φ` and prove the remaining obligations. Use `(G.M'.co.form _ _).symm.trans (hiso p q)` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Establish `hshift : shiftB σ H H' 1 = vecMulVec Y X'`.

Simplify using `[shiftB, hYdef, hX']`. Establish `hmove : mat u * shiftB σ H H' 1 = vecMulVec (s • X) X' + (vecMulVec (I *ᵥ w) X' + vecMulVec Y X')`. Rewrite using `[hshift, Matrix.mul_vecMulVec, hv, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_assoc]`. Establish `hS : ∀ (γ : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) φ, φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) → G.M'.co.rho B.ψ γ φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))` using `fun γ φ hφ => GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hB.std γ φ hφ`. Establish `h1 : vecMulVec (s • X) X' ∈ isoB (F` using `F) H H' := by left`.

Use `⟨s • X', ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hX]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : vecMulVec (I *ᵥ w) X' ∈ isoB (F` using `F) H H' := Or.inr ⟨w, rfl⟩`.

Rewrite using `[hmove, ← Matrix.add_vecMulVec (I *ᵥ w) Y, hadd, he.inv _ h1 _ (hS _ _ hΨ), Matrix.add_vecMulVec, hadd, he.inv _ h2 _ (hS _ _ hΨ), hshift]`.
-/
theorem ev_rho_unip_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    B.IsGood σ → G.IsGood B → ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ u ∈ unip σ G.V' H, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      e' (G.M'.co.rho B.ψ (mat u * shiftB σ H H' 1) Ψ) = e' (G.M'.co.rho B.ψ (shiftB σ H H' 1) Ψ) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC hB hG e' he u hu Ψ hΨ
  have hH := hC.hH
  have hH' := hC.hH'
  have hY := hG.hV'
  set X := incV F H.x with hX
  set Y := incV F H.y with hYdef
  set X' := incV F H'.x with hX'
  set I := incM F H.ι with hI
  obtain ⟨hux, -⟩ := GlobalTheory.StabNormal.prop_of_mem_unip' H hu

  have hspan : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (w : Fin b → E), v = s • H.x + H.ι *ᵥ w + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (G.V'.L : Set (Fin (b + 2) → E)) := by
      rw [hY.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, w, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, w, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, w, rfl⟩ := hy
      obtain ⟨s', t', w', rfl⟩ := hz
      exact ⟨s + s', t + t', w + w', by rw [Matrix.mulVec_add]; module⟩
    | smul c y _ hy =>
      obtain ⟨s, t, w, rfl⟩ := hy
      exact ⟨c * s, c * t, c • w, by rw [Matrix.mulVec_smul]; module⟩

  set c₀ : Fin (b + 2) → E := G.V'.J *ᵥ fun i => σ (H.x i) with hc₀
  have hιc : ∀ w, (H.ι *ᵥ w) ⬝ᵥ c₀ = 0 := fun w => (hH.orth w).1
  have hxc : H.x ⬝ᵥ c₀ = 0 := hH.xx
  have hyx : H.y ⬝ᵥ c₀ ≠ 0 := by
    intro h0
    have hall : ∀ w : Fin (b + 2) → E, w ⬝ᵥ c₀ = 0 := by
      intro w
      obtain ⟨s, t, v, rfl⟩ := hspan w
      rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hxc, h0, hιc]
      simp
    have hc0 : ∀ i, c₀ i = 0 := fun i => by simpa using hall (Pi.single i 1)
    have hxJ : H.x ᵥ* G.V'.J = 0 := by
      funext i
      have hσinj : Function.Injective σ := σ.toRingHom.injective
      apply hσinj
      rw [Pi.zero_apply, map_zero, ← hc0 i]
      simp only [vecMul, mulVec, dotProduct, map_sum, map_mul, hc₀, Pi.zero_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hY.herm, mul_comm]
    have h1 := hH.xy
    unfold form at h1
    rw [dotProduct_mulVec, hxJ, zero_dotProduct] at h1
    exact zero_ne_one h1

  set C : Fin (b + 2) → AE F E := incM F G.V'.J *ᵥ fun i => cA σ (X i) with hC'
  have hCe : C = incV F c₀ := by
    rw [hC', hc₀, GlobalTheory.StabNormal.incM_mulVec]
    congr 1
  have hIC : ∀ z, (I *ᵥ z) ⬝ᵥ C = 0 := by
    intro z
    have h0 : c₀ ᵥ* H.ι = 0 := by
      funext j
      have := hιc (Pi.single j 1)
      rw [mulVec_single_one, dotProduct_comm] at this
      exact this
    rw [dotProduct_comm, dotProduct_mulVec, hCe, hI, ← GlobalTheory.StabNormal.incV_vecMul, h0]
    simp [incV, dotProduct]
  have hXC : X ⬝ᵥ C = 0 := by rw [hCe, hX, GlobalTheory.StabNormal.incV_dot, hxc, map_zero]
  have hYC : IsUnit (Y ⬝ᵥ C) := by
    rw [hCe, hYdef, GlobalTheory.StabNormal.incV_dot]
    exact (isUnit_iff_ne_zero.2 hyx).map (inclR (F := F) (E := E) (AF F))

  obtain ⟨s, t, w, hv⟩ := GlobalTheory.StabNormal.decompA H.x H.y H.ι hspan (mat u *ᵥ Y)
  rw [← hX, ← hI, ← hYdef] at hv
  have ht : t = 1 := by
    have h0 := GlobalTheory.StabNormal.dot_invariant u X hux Y
    rw [← hC', hv, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hXC, hIC] at h0
    simp only [smul_eq_mul, mul_zero, zero_add] at h0
    have h2 : (t - 1) * (Y ⬝ᵥ C) = 0 := by rw [sub_mul, h0, one_mul, sub_self]
    exact sub_eq_zero.1 ((hYC.mul_left_eq_zero).1 h2)
  rw [ht, one_smul] at hv

  have hww := GlobalTheory.IsoBLoc.pair_zero_of_form (F := F) σ G.W.J H'.x H'.x hH'.xx
  have hiso : ∀ p q : Fin (b + 2) → AE F E,
      symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (vecMulVec p X') (vecMulVec q X') = 0 := by
    intro p q
    rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hww, mul_zero, mul_zero, map_zero]
  have hadd : ∀ (p q : Fin (b + 2) → AE F E) (φ : Fn F (b + 2) (a + (b + 2))),
      G.M'.co.rho B.ψ (vecMulVec p X' + vecMulVec q X') φ =
        G.M'.co.rho B.ψ (vecMulVec p X') (G.M'.co.rho B.ψ (vecMulVec q X') φ) := by
    intro p q φ
    refine GlobalTheory.DblSiegel.rho_add G.M'.co B.ψ ?_ φ
    have := (G.M'.co.form _ _).symm.trans (hiso p q)
    exact sub_eq_zero.1 this
  have hshift : shiftB σ H H' 1 = vecMulVec Y X' := by
    simp [shiftB, hYdef, hX']
  have hmove : mat u * shiftB σ H H' 1 = vecMulVec (s • X) X' + (vecMulVec (I *ᵥ w) X' + vecMulVec Y X') := by
    rw [hshift, Matrix.mul_vecMulVec, hv, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_assoc]
  have hS : ∀ (γ : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) φ, φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) →
      G.M'.co.rho B.ψ γ φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun γ φ hφ => GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hB.std γ φ hφ
  have h1 : vecMulVec (s • X) X' ∈ isoB (F := F) H H' := by
    left
    refine ⟨s • X', ?_⟩
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hX]
    ring
  have h2 : vecMulVec (I *ᵥ w) X' ∈ isoB (F := F) H H' := Or.inr ⟨w, rfl⟩
  rw [hmove, ← Matrix.add_vecMulVec (I *ᵥ w) Y, hadd, he.inv _ h1 _ (hS _ _ hΨ), Matrix.add_vecMulVec, hadd,
    he.inv _ h2 _ (hS _ _ hΨ), hshift]

end GlobalTheory.UnipShiftEv
