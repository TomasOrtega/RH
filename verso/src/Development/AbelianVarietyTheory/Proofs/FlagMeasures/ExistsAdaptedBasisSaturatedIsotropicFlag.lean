import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

/- English proof (translation)
Establish `he' : ∀ y, e.symm (star y) = star (e.symm y)` using `fun y => e.injective (by simp [he])`. Use `set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG`. Establish `hGe : Bᴴ * I.J * B = G.map e` using `by ext r s; exact (e.apply_symm_apply _).symm`. Establish `hGd : G.det ≠ 0` using `fun h => h6 (by`. Rewrite using `[hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))`.

Establish `hGh : Gᴴ = G`. Rewrite using `[hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]`. Take `⟨L, hL, -, hLd⟩` from `exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛ hdual h7`. Take `⟨γ, hγ⟩` from `GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL, hLd⟩ ⟨I₀.L, ⟨I₀.L_fg, I₀.L_span⟩, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by`. Use `⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩` and prove the remaining obligations.

Use `set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom`. Establish `hψ : ∀ x, ψ (star x) = star (ψ x)` using `I.cm.cmUnram.2.1 ψ`. Establish `hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ` using `by rw [map_gram ψ hψ]; rfl`. Rewrite using `[hm]`. Use `hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.conjTranspose_map _ hψ, J_herm]`. Rewrite using `[map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]`. Rewrite using `[map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]`. Rewrite using `[map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]`. Rewrite using `[map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]`.

Rewrite using `[map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]`. Rewrite using `[← hm]`. Conclude with `fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))`. Use `set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ`. Establish `hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E)` using `rfl`.

Establish `hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e`. Use `map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1` as an intermediate fact. Rewrite `this` using `[hγ, ← hγ']`. Use `Eq.trans ?_ this` and prove the remaining obligations. Rewrite using `[show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Take `⟨L', hL', hm, hLd'⟩` from `exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛ hdual fun z hz => by`. Take `⟨y, hy, hy'⟩` from `h7 z hz`. Establish `: (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y`. Rewrite using `[mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`.

Use `⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩` and prove the remaining obligations. Rewrite using `[this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]`. Take `⟨x₀, hx₀⟩` from `GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL' (by simpa only [hform_eq] using hLd')`. Conclude with `⟨γ', x₀, hT, by rwa [hx₀]⟩`.
-/
theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛ hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL, hLd⟩
    ⟨I₀.L, ⟨I₀.L_fg, I₀.L_span⟩, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛ hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL' (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

/- English proof (translation)
Introduce `I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩`. Take `⟨-, hfg, hspan, hdual, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I (1, xf)`. Simplify using `only [hform_eq] at hdual hiso`. Establish `hn : I.n = I₀.n + 2 * ∑ i, j i`. Establish `h1` using `(GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI`.

Establish `h2` using `(GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀`. Use linear arithmetic over natural numbers and integers. Establish `hle : ∀ k, S k ≤ lamX I (1, xf)` using `fun k y hy => ((hsat k y).1 hy).1`. Establish `hSfg : (S (Fin.last a)).FG` using `hfg.of_le (hle _)`. Take `⟨A, hA⟩` from `GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩`.

Take `⟨Λ, Ti, hΛ, hS⟩` from `exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA`. Use `set κ := Σ i, Fin (j i)`. Establish `hκ : Fintype.card κ = ∑ i, j i` using `by simp [κ]`. Establish `hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E), M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩` using `fun M u => by`. Use extensionality with `r`.

Simplify using `[mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]`. Take `⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i)` from `⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩`. Establish `hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u` using `fun z => by`. Rewrite using `[hS]`. Use `⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩, fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩` and prove the remaining obligations.

Establish `hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a)` using `fun i t ht => by`. Use `(hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `using ht`.

Simplify using `[h]`. Apply the tactic sequence `rw [Finset.sum_eq_single i] <;> simp +contextual`. Use `set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW`. Establish `hrange : LinearMap.range T.mulVecLin = W`. Use `le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[mulVecLin_apply, hsum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin` using `Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)`. Rewrite using `[← hT]`.

Conclude with `this ((hΛ i).span_eq_top ▸ Submodule.mem_top)`. Take `⟨u, -, rfl⟩` from `(hlast z).1 hz`. Conclude with `⟨u, rfl⟩`. Establish `hdim : Module.finrank I.E W = Fintype.card κ`. Use `telescope a j (fun k => Formalism.HN.rkK (S k)) hrk` as an intermediate fact.

Simplify using `only [h0] at this`. Rewrite using `[hκ]`. Rewrite using `[show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by`. Rewrite `this` using `[Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add]`. Conclude with `this`.

Establish `hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0` using `fun x hx y hy => by`. Proceed by induction on `hx, hy using Submodule.span_induction₂ with`. Consider the case `mem_mem x y hx hy => exact hiso x hx y hy`. Consider the case `zero_left => simp`. Consider the case `zero_right => simp`.

Consider the case `add_left x y z _ _ _ h h' => simp [h, h']`. Consider the case `add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']`. Consider the case `smul_left c x y _ _ h => simp [h]`. Consider the case `smul_right c x y _ _ h => simp [mulVec_smul, h]`. Take `⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩` from `GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _ ⟨hfg, hspan⟩ hdual W hWiso`.

Take `⟨T', B, hrange', h3, h6, hB⟩` from `exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim (hW'dim.trans hdim) hWiso hW'iso hW'nd`. Establish `mT : ∀ u, T *ᵥ u ∈ W` using `fun u => hrange ▸ ⟨u, rfl⟩`. Establish `mT' : ∀ u, T' *ᵥ u ∈ W'` using `fun u => hrange' ▸ ⟨u, rfl⟩`. Establish `h1 : Tᴴ * I.J * T = 0` using `gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)`. Establish `h2 : T'ᴴ * I.J * T' = 0` using `gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)`.

Establish `h4 : Tᴴ * I.J * B = 0` using `gram_eq_zero _ _ _ fun x y => (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))`. Establish `h5 : T'ᴴ * I.J * B = 0` using `gram_eq_zero _ _ _ fun x y => (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))`. Establish `hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧ B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y` using `fun z hz => by`. Take `⟨x, hx, y, hy, hxW, hyW, h⟩` from `hsplit z hz`. Take `⟨w, hw⟩` from `(hB _).2 h`.

Establish `hxS` using `(hsat _ x).2 ⟨hx, hxW⟩`. Rewrite `hxW` using `[← hrange]`. Rewrite `hyW` using `[← hrange']`. Take `⟨u, rfl⟩` from `hxW`. Take `⟨u', rfl⟩` from `hyW`.

Simplify using `only [mulVecLin_apply] at hw hx hy hxS`. Conclude with `⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩`. Take `⟨γ, x₀, hG, hx₀⟩` from `exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ ⟨hfg, hspan⟩ hdual T T' B h1 h2 h3 h4 h5 h6 fun z hz => by`. Take `⟨u, u', y, -, -, hy, rfl⟩` from `hdec z hz`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T, gram_swap (J_herm I) T', h4, h5]`. Simplify using the standard rewrite rules. Establish `hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type} (f : k₁ → κ) (g : k₂ → l), (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g` using `fun M N _ _ f g => by`. Use extensionality with `r s`. Simplify using `[Matrix.mul_apply]`.

Establish `hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩` using `fun i t u' => by`. Rewrite using `[form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]`. Use `congr 1`. Use extensionality with `s`. Simplify using `[mulVec, dotProduct, Matrix.one_apply]`.

Use `⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩, fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩` and prove the remaining obligations. Rewrite using `[hT, hT, hsub, h1]`. Both sides reduce to the same expression. Rewrite using `[hsub, h2]`. Both sides reduce to the same expression.

Rewrite using `[hT, hsub, h3]`. Use extensionality with `r s`. Simplify using `[h]`. Rewrite using `[hT, hsub, h3]`. Use extensionality with `r s`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]`. Simplify using the standard rewrite rules. Rewrite using `[← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]`. Simplify using the standard rewrite rules.

Take `⟨u, u', y, hu, hu', hy, rfl⟩` from `hdec z hz`. Take `⟨v, hv, hv'⟩` from `(hlast _).1 hu`. Establish `hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y`. Simplify using `only [e.apply_symm_apply]`. Rewrite using `[mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`.

Use `⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_, (hx₀ _).2 (hy' ▸ hy), ?_⟩` and prove the remaining obligations. Rewrite using `[← hpair]`. Conclude with `(hdual _).1 hu' _ (hle _ (hone i t ht))`. Rewrite using `[hy', hv', hsum T, hsum T']`. Simplify using `only [hT]`.

Introduce and unpack `⟨u, u', y, hu, hu', hy, rfl⟩`. Use `add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)` and prove the remaining obligations. Establish `e1` using `hsum T' fun s => u' s.1 s.2`. Use `e1 ▸ (hdual _).2 fun w hw => ?_` and prove the remaining obligations. Take `⟨v, v', y', hv, -, -, rfl⟩` from `hdec w hw`.

Take `⟨t, ht, ht'⟩` from `(hlast _).1 hv`. Rewrite using `[star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2, gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]`. Simplify using `only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]`. Conclude with `Subring.sum_mem _ fun i _ => hu' i _ (ht i)`.
-/
theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      exact this ((hΛ i).span_eq_top ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    ⟨hfg, hspan⟩ hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ ⟨hfg, hspan⟩ hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
