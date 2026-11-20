import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModels
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviRat

open GlobalTheory.AdaptedMove GlobalTheory.FlagConj GlobalTheory.PointEquivariance

/- English proof (translation)
Establish `hk` using `GlobalTheory.PointEquivariance.lamX_mul_eq_iff I ((1 : I.Ginf), x) (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x))`. Establish `hcx : ((1 : I.Ginf), x) * (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x)) = c * ((1 : I.Ginf), x)` using `by group`. Rewrite `hk` using `[hcx, GlobalTheory.PointEquivariance.lamX_rat I ((1 : I.Ginf), x) c γ hc]`. Conclude with `hk`.
-/
theorem mem_conj_iff (I : AutInst) (x : I.Gf) (c : I.GA) (γ : GL (Fin I.n) I.E)
    (hc : I.fmat c.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    x⁻¹ * c.2 * x ∈ I.Kset ↔ ratIso I γ (lamX I (1, x)) = lamX I (1, x) := by
  have hk := GlobalTheory.PointEquivariance.lamX_mul_eq_iff I ((1 : I.Ginf), x) (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x))
  have hcx : ((1 : I.Ginf), x) * (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x)) = c * ((1 : I.Ginf), x) := by
    group
  rw [hcx, GlobalTheory.PointEquivariance.lamX_rat I ((1 : I.Ginf), x) c γ hc] at hk
  exact hk

/- English proof (translation)
Establish `key : ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ = (g : Matrix (Fin m) (Fin m) E)ᴴ`. Use extensionality with `r s`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]`. Both sides reduce to the same expression. Use `show ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ * J * g = J ↔ _`.

Rewrite using `[key]`.
-/
private theorem mem_UJ_iff_flag_measures {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (g : GL (Fin m) E) :
    g ∈ Formalism.UG.UJ (starRingEnd E) J ↔ (g : Matrix (Fin m) (Fin m) E)ᴴ * J * g = J := by
  have key : ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ = (g : Matrix (Fin m) (Fin m) E)ᴴ := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  show ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ * J * g = J ↔ _
  rw [key]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem inv_mul_eq_mul_inv_of_mul_eq_mul {R : Type} [CommRing R] {m p : ℕ} (G G' : Matrix (Fin m) (Fin m) R)
    (C C' : Matrix (Fin p) (Fin p) R) (X : Matrix (Fin m) (Fin p) R) (hG : G' * G = 1) (hC : C * C' = 1)
    (h : G * X = X * C) : G' * X = X * C' := by
  calc G' * X = G' * (X * C) * C' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hC, Matrix.mul_one]
    _ = X * C' := by rw [← h, ← Matrix.mul_assoc, hG, Matrix.one_mul]

/- English proof (translation)
Introduce `z hz`. Take `⟨u, u', y, hu, hu', hy, rfl⟩` from `(hlat z).1 hz`. Use `(hlat _).2 ⟨fun i => c i *ᵥ u i, fun i => (A i)ᴴ *ᵥ u' i, d *ᵥ y, fun i => hc i _ (hu i), ?_, hd y hy, ?_⟩` and prove the remaining obligations. Introduce `i t ht`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`.

Conclude with `hu' i _ (hA i t ht)`. Use `beta_reduce`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]`. Use `congr 1`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hT i, ← Matrix.mulVec_mulVec]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hT' i, ← Matrix.mulVec_mulVec]`. Rewrite using `[Matrix.mulVec_mulVec, h₀, ← Matrix.mulVec_mulVec]`.

Use `congr 1`. Use function extensionality and compare the values at `l`. Conclude with `(RingHom.map_mulVec (e : I₀.E →+* I.E) d y l).symm`.
-/
private theorem lat_mulVec_lemma_3 (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf)
    (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hlat : ∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l))
    (G : Matrix (Fin I.n) (Fin I.n) I.E) (c A : ∀ i, Matrix (Fin (j i)) (Fin (j i)) I.E)
    (d : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)
    (hc : ∀ i, ∀ u ∈ Λ i, c i *ᵥ u ∈ Λ i) (hA : ∀ i, ∀ u ∈ Λ i, A i *ᵥ u ∈ Λ i)
    (hd : ∀ y ∈ lamX I₀ (1, x₀), d *ᵥ y ∈ lamX I₀ (1, x₀))
    (hT : ∀ i, G * T i = T i * c i) (hT' : ∀ i, G * T' i = T' i * (A i)ᴴ) (h₀ : G * T₀ = T₀ * d.map e) :
    ∀ z ∈ lamX I (1, xf), G *ᵥ z ∈ lamX I (1, xf) := by
  intro z hz
  obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := (hlat z).1 hz
  refine (hlat _).2 ⟨fun i => c i *ᵥ u i, fun i => (A i)ᴴ *ᵥ u' i, d *ᵥ y, fun i => hc i _ (hu i), ?_, hd y hy, ?_⟩
  · intro i t ht
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact hu' i _ (hA i t ht)
  · beta_reduce
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT i, ← Matrix.mulVec_mulVec]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT' i, ← Matrix.mulVec_mulVec]
    · rw [Matrix.mulVec_mulVec, h₀, ← Matrix.mulVec_mulVec]
      congr 1
      funext l
      exact (RingHom.map_mulVec (e : I₀.E →+* I.E) d y l).symm

/- English proof (translation)
Introduce `I I₀ e xf a j S Λ x₀ T T' T₀ hAd γ hγ g₀ hg₀`. Take `⟨he, hn, -, h1, h2, h3, hlat, -⟩` from `hAd`. Take `⟨c₀, ⟨δ, hδU, hδP, hδf⟩, rfl, hc₀K⟩` from `hg₀`. Establish `hδL` using `(mem_conj_iff I₀ x₀ c₀ δ hδf).1 hc₀K`. Establish `hJ : I.Jᴴ = I.J`.

Establish `hH : (I.J.map (starRingEnd I.E))ᵀ = I.J` using `I.J_herm`. Use extensionality with `r s`. Use `congrArg (fun M => M r s) hH` as an intermediate fact. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply] at this`. Rewrite using `[Matrix.conjTranspose_apply, ← this]`.

Both sides reduce to the same expression. Establish `hJ₀ : (I₀.J.map e).det ≠ 0`. Introduce `h`. Apply `I₀.J_det` to reduce the goal to its premises. Establish `h' : (e : I₀.E →+* I.E) I₀.J.det = 0`.

Rewrite using `[RingHom.map_det]`. Conclude with `h`. Simplify using `using h'`. Establish `hsemi : Function.Semiconj e star star` using `he`. Establish `hδU'` using `(mem_UJ_iff_flag_measures I₀.J δ).1 hδU`.

Take `⟨U, hU⟩ : ∃ U : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E, ∀ i, U i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)` from `⟨_, fun _ => rfl⟩`. Take `⟨U', hU'⟩ : ∃ U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E, ∀ i, U' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ` from `⟨_, fun _ => rfl⟩`. Take `⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E, U₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e` from `⟨_, rfl⟩`. Establish `g1 : ∀ i k, (U i)ᴴ * I.J * U k = 0 ∧ (U' i)ᴴ * I.J * U' k = 0 ∧ (i ≠ k → (U i)ᴴ * I.J * U' k = 0)`. Introduce `i k`.

Take `⟨a1, a2, a3⟩` from `h1 i k`. Use `⟨?_, ?_, fun hik => ?_⟩` and prove the remaining obligations. Rewrite using `[hU, hU, GlobalTheory.AdaptedMove.gram_mul, a1, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[hU', hU', GlobalTheory.AdaptedMove.gram_mul, a2, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[hU, hU', GlobalTheory.AdaptedMove.gram_mul, a3 hik, Matrix.mul_zero, Matrix.zero_mul]`.

Establish `g2 : ∀ i, (U i)ᴴ * I.J * U' i = 1 ∧ (U i)ᴴ * I.J * U₀ = 0 ∧ (U' i)ᴴ * I.J * U₀ = 0`. Introduce `i`. Take `⟨b1, b2, b3⟩` from `h2 i`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hU, hU', GlobalTheory.AdaptedMove.gram_mul, b1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]`.

Rewrite using `[hU, hU₀, GlobalTheory.AdaptedMove.gram_mul, b2, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[hU', hU₀, GlobalTheory.AdaptedMove.gram_mul, b3, Matrix.mul_zero, Matrix.zero_mul]`. Establish `g3 : U₀ᴴ * I.J * U₀ = I₀.J.map e`. Rewrite using `[hU₀, GlobalTheory.AdaptedMove.gram_mul, h3, ← Matrix.conjTranspose_map _ hsemi]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Use `_ = I₀.J.map e := by`. Rewrite using `[hδU']`. Both sides reduce to the same expression.

Take `⟨Γ, hΓJ, hΓT, hΓT', hΓ₀⟩` from `GlobalTheory.FlagConj.exists_unitary_adapted hn I.J hJ (I₀.J.map e) hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3`. Establish `hΓU : Γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J` using `(mem_UJ_iff_flag_measures I.J Γ).2 hΓJ`. Take `⟨c, hc1, hc2⟩` from `GlobalTheory.FlagConj.exists_point I Γ hΓU`. Establish `hγf : ∀ i, ∀ u ∈ Λ i, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i` using `fun i u hu => (hγ i u).2 hu`. Establish `hγb : ∀ i, ∀ u ∈ Λ i, (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i`.

Introduce `i u hu`. Apply `(hγ i _).1` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `hu`. Establish `hδf' : ∀ y ∈ lamX I₀ (1, x₀), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀)`.

Introduce `y hy`. Rewrite using `[← hδL, GlobalTheory.FlagConj.mem_ratIso]`. Conclude with `⟨y, hy, rfl⟩`. Establish `hδb : ∀ y ∈ lamX I₀ (1, x₀), ((δ⁻¹ : GL (Fin I₀.n) I₀.E) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀)`. Introduce `y hy`.

Rewrite `hy` using `[← hδL, GlobalTheory.FlagConj.mem_ratIso]`. Take `⟨y', hy', rfl⟩` from `hy`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Conclude with `hy'`. Establish `hT : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)` using `fun i => (hΓT i).trans (hU i)`.

Establish `hT' : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ` using `fun i => (hΓT' i).trans (hU' i)`. Establish `hT₀ : (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e` using `hΓ₀.trans hU₀`. Establish `hΓi : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * Γ = 1` using `Units.inv_mul Γ`. Establish `hTb : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)` using `fun i => inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi (Units.mul_inv (γ i)) (hT i)`. Establish `hT'b : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T' i = T' i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ`.

Introduce `i`. Use `inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ (hT' i)` and prove the remaining obligations. Rewrite using `[← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]`. Establish `hT₀b : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e`. Use `inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ hT₀` and prove the remaining obligations.

Establish `hm : (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e = ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)).map (e : I₀.E →+* I.E)` using `(Matrix.map_mul).symm`. Rewrite using `[hm, Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero e) (map_one e)`. Establish `hfw` using `lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat Γ (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) δ hγf hγb hδf' hT hT' hT₀`. Establish `hbw` using `lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Ma …`.

Establish `hLat : ratIso I Γ (lamX I (1, xf)) = lamX I (1, xf)`. Use extensionality with `z`. Rewrite using `[GlobalTheory.FlagConj.mem_ratIso]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `hfw y hy`. Introduce `hz`. Use `⟨(((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, hbw z hz, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `⟨c.1, ⟨c, ⟨Γ, hΓU, hc1, hc2⟩, rfl, (mem_conj_iff I xf c Γ hc2).2 hLat⟩, (Γ : Matrix (Fin I.n) (Fin I.n) I.E), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), hc1, hδP, hT, hT₀⟩`.
-/
theorem exists_rat_block : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hAd γ hγ g₀ hg₀
  obtain ⟨he, hn, -, h1, h2, h3, hlat, -⟩ := hAd
  obtain ⟨c₀, ⟨δ, hδU, hδP, hδf⟩, rfl, hc₀K⟩ := hg₀
  have hδL := (mem_conj_iff I₀ x₀ c₀ δ hδf).1 hc₀K
  have hJ : I.Jᴴ = I.J := by
    have hH : (I.J.map (starRingEnd I.E))ᵀ = I.J := I.J_herm
    ext r s
    have := congrArg (fun M => M r s) hH
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this
    rw [Matrix.conjTranspose_apply, ← this]
    rfl
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    intro h
    apply I₀.J_det
    have h' : (e : I₀.E →+* I.E) I₀.J.det = 0 := by
      rw [RingHom.map_det]
      exact h
    simpa using h'
  have hsemi : Function.Semiconj e star star := he
  have hδU' := (mem_UJ_iff_flag_measures I₀.J δ).1 hδU
  obtain ⟨U, hU⟩ : ∃ U : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) := ⟨_, fun _ => rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E,
      U₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := ⟨_, rfl⟩
  have g1 : ∀ i k, (U i)ᴴ * I.J * U k = 0 ∧ (U' i)ᴴ * I.J * U' k = 0 ∧
      (i ≠ k → (U i)ᴴ * I.J * U' k = 0) := by
    intro i k
    obtain ⟨a1, a2, a3⟩ := h1 i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [hU, hU, GlobalTheory.AdaptedMove.gram_mul, a1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU', GlobalTheory.AdaptedMove.gram_mul, a2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, a3 hik, Matrix.mul_zero, Matrix.zero_mul]
  have g2 : ∀ i, (U i)ᴴ * I.J * U' i = 1 ∧ (U i)ᴴ * I.J * U₀ = 0 ∧ (U' i)ᴴ * I.J * U₀ = 0 := by
    intro i
    obtain ⟨b1, b2, b3⟩ := h2 i
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, b1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.inv_mul,
        Matrix.conjTranspose_one]
    · rw [hU, hU₀, GlobalTheory.AdaptedMove.gram_mul, b2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU₀, GlobalTheory.AdaptedMove.gram_mul, b3, Matrix.mul_zero, Matrix.zero_mul]
  have g3 : U₀ᴴ * I.J * U₀ = I₀.J.map e := by
    rw [hU₀, GlobalTheory.AdaptedMove.gram_mul, h3, ← Matrix.conjTranspose_map _ hsemi]
    calc ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ).map e * I₀.J.map e * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e
        = ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ * I₀.J * δ).map (e : I₀.E →+* I.E) := by
          rw [Matrix.map_mul, Matrix.map_mul]
          rfl
      _ = I₀.J.map e := by
          rw [hδU']
          rfl
  obtain ⟨Γ, hΓJ, hΓT, hΓT', hΓ₀⟩ :=
    GlobalTheory.FlagConj.exists_unitary_adapted hn I.J hJ (I₀.J.map e) hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hΓU : Γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := (mem_UJ_iff_flag_measures I.J Γ).2 hΓJ
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.FlagConj.exists_point I Γ hΓU
  have hγf : ∀ i, ∀ u ∈ Λ i, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i :=
    fun i u hu => (hγ i u).2 hu
  have hγb : ∀ i, ∀ u ∈ Λ i, (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i := by
    intro i u hu
    apply (hγ i _).1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hu
  have hδf' : ∀ y ∈ lamX I₀ (1, x₀), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso]
    exact ⟨y, hy, rfl⟩
  have hδb : ∀ y ∈ lamX I₀ (1, x₀),
      ((δ⁻¹ : GL (Fin I₀.n) I₀.E) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy'
  have hT : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => (hΓT i).trans (hU i)
  have hT' : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    fun i => (hΓT' i).trans (hU' i)
  have hT₀ : (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e :=
    hΓ₀.trans hU₀
  have hΓi : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * Γ = 1 := Units.inv_mul Γ
  have hTb : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T i =
      T i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi (Units.mul_inv (γ i)) (hT i)
  have hT'b : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ := by
    intro i
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ (hT' i)
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hT₀b : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ =
      T₀ * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := by
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ hT₀
    have hm : (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e *
        (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e =
        ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *
          (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)).map (e : I₀.E →+* I.E) :=
      (Matrix.map_mul).symm
    rw [hm, Units.mul_inv]
    exact Matrix.map_one _ (map_zero e) (map_one e)
  have hfw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat Γ
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) δ hγf hγb hδf' hT hT' hT₀
  have hbw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E)
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) hγb hγf hδb hTb hT'b hT₀b
  have hLat : ratIso I Γ (lamX I (1, xf)) = lamX I (1, xf) := by
    ext z
    rw [GlobalTheory.FlagConj.mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfw y hy
    · intro hz
      refine ⟨(((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, hbw z hz, ?_⟩
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨c.1, ⟨c, ⟨Γ, hΓU, hc1, hc2⟩, rfl, (mem_conj_iff I xf c Γ hc2).2 hLat⟩,
    (Γ : Matrix (Fin I.n) (Fin I.n) I.E), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), hc1, hδP, hT, hT₀⟩

end GlobalTheory.LeviRat
