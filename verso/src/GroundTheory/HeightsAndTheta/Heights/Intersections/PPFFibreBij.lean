import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Loc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

/- English proof (translation)
Establish `h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom = (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]`. Introduce `p`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]`. Unfold `baseSubst`. Rewrite using `[eval₂Hom_X']`. Establish `h1 : (v p).1 ∈ Set.range κ` using `⟨p.1, (hv.2.2.1 p).symm⟩`. Establish `h2 : v p ∈ Set.range v` using `⟨p, rfl⟩`.

Rewrite using `[dif_pos h1, dif_pos h2, hv.2.1 h2.choose_spec]`. Conclude with `DFunLike.congr_fun h g`.
-/
theorem baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRing ι) :
    baseSubst κ G (rename v g) = C (aeval G.x g) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dif_pos h1, dif_pos h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h g

/- English proof (translation)
Unfold `baseSubst`. Rewrite using `[eval₂Hom_X', dif_neg q.1.2]`.
-/
theorem baseSubst_X_fibre (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dif_neg q.1.2]

/- English proof (translation)
Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, hf, map_zero]`.
-/
theorem mem_of_baseSubst_eq_zero (hv : IsBlockMap κ v) (G : GenFibre v P') {f : MRing ι'}
    (hf : baseSubst κ G f = 0) : f ∈ P' := by
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, hf, map_zero]

/- English proof (translation)
Rewrite using `[fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]`.
-/
theorem baseSubst_mem_fibreIdeal (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    baseSubst κ G f ∈ fibreIdeal κ G ↔ f ∈ P' := by
  rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]

/- English proof (translation)
Proceed by induction on `c using MvPolynomial.induction_on with`. Consider the case `C a`. Take `⟨f, g, hg, rfl⟩` from `G.gen a`. Use `⟨rename v f, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[baseSubst_rename hv, ← C_mul, div_mul_cancel₀ _ hg]`.

Consider the case `add c₁ c₂ ih₁ ih₂`. Take `⟨F₁, g₁, h₁, e₁⟩` from `ih₁`. Take `⟨F₂, g₂, h₂, e₂⟩` from `ih₂`. Use `⟨F₁ * rename v g₂ + F₂ * rename v g₁, g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, baseSubst_rename hv]`.

Rewrite using `[← e₁, ← e₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X c q ih`. Take `⟨F, g, hg, e⟩` from `ih`. Use `⟨F * X ⟨q.1.1, q.2⟩, g, hg, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← e, baseSubst_X_fibre]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_eq_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (c : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (F : MRing ι') (g : MRing ι), aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G F := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, g, hg, rfl⟩ := G.gen a
    refine ⟨rename v f, g, hg, ?_⟩
    rw [baseSubst_rename hv, ← C_mul, div_mul_cancel₀ _ hg]
  | add c₁ c₂ ih₁ ih₂ =>
    obtain ⟨F₁, g₁, h₁, e₁⟩ := ih₁
    obtain ⟨F₂, g₂, h₂, e₂⟩ := ih₂
    refine ⟨F₁ * rename v g₂ + F₂ * rename v g₁, g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hv]
    rw [← e₁, ← e₂]
    ring
  | mul_X c q ih =>
    obtain ⟨F, g, hg, e⟩ := ih
    refine ⟨F * X ⟨q.1.1, q.2⟩, g, hg, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fibre]
    ring

/- English proof (translation)
Establish `: c = baseSubst κ G F * C (aeval G.x g)⁻¹`. Rewrite using `[← e, mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, mul_one]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hF)`.
-/
theorem mem_fibreOf_of_mul_eq (G : GenFibre v P') {I : Ideal (MRing ι')} {c : MRingOver G.Φ (fibreIdx ι' κ)}
    {F : MRing ι'} {g : MRing ι} (hg : aeval G.x g ≠ 0) (e : c * C (aeval G.x g) = baseSubst κ G F) (hF : F ∈ I) :
    c ∈ fibreOf κ G I := by
  have : c = baseSubst κ G F * C (aeval G.x g)⁻¹ := by
    rw [← e, mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hF)

/- English proof (translation)
Use `le_antisymm Ideal.map_comap_le fun c hc => ?_` and prove the remaining obligations. Take `⟨F, g, hg, e⟩` from `exists_mul_eq_baseSubst hv G c`. Use `mem_fibreOf_of_mul_eq G hg e ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, ← e]`. Conclude with `Q.mul_mem_right _ hc`.
-/
theorem fibreOf_comap (hv : IsBlockMap κ v) (G : GenFibre v P') (Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))) :
    fibreOf κ G (Q.comap (baseSubst κ G)) = Q := by
  refine le_antisymm Ideal.map_comap_le fun c hc => ?_
  obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
  refine mem_fibreOf_of_mul_eq G hg e ?_
  rw [Ideal.mem_comap, ← e]
  exact Q.mul_mem_right _ hc

/- English proof (translation)
Use `le_antisymm (fun f hf => ?_) Ideal.le_comap_map` and prove the remaining obligations. Establish `key : ∀ c ∈ fibreOf κ G W, ∃ w ∈ W, ∃ g : MRing ι, aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G w`. Introduce `c hc`. Unfold `fibreOf Ideal.map Ideal.span at hc`. Proceed by induction on `hc using Submodule.span_induction with`.

Consider the case `mem c hc`. Take `⟨w, hw, rfl⟩` from `hc`. Conclude with `⟨w, hw, 1, by simp, by simp⟩`. Consider the case `zero => exact ⟨0, W.zero_mem, 1, by simp, by simp⟩`. Consider the case `add c₁ c₂ _ _ ih₁ ih₂`.

Take `⟨w₁, hw₁, g₁, h₁, e₁⟩` from `ih₁`. Take `⟨w₂, hw₂, g₂, h₂, e₂⟩` from `ih₂`. Use `⟨w₁ * rename v g₂ + w₂ * rename v g₁, W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_right _ hw₂), g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, baseSubst_rename hv]`. Rewrite using `[← e₁, ← e₂]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a c _ ih`. Take `⟨w, hw, g, h, e⟩` from `ih`. Take `⟨F, g', h', e'⟩` from `exists_mul_eq_baseSubst hv G a`. Use `⟨F * w, W.mul_mem_left _ hw, g' * g, by rw [map_mul]; exact mul_ne_zero h' h, ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_eq_mul, map_mul]`. Rewrite using `[← e', ← e]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw, g, hg, e⟩` from `key _ hf`. Establish `h0 : f * rename v g - w ∈ P'` using `mem_of_baseSubst_eq_zero hv G (by rw [map_sub, map_mul, baseSubst_rename hv, e, sub_self])`.

Establish `h1 : f * rename v g ∈ W` using `by simpa using W.add_mem (hPW h0) hw`. Break down `hW.mem_or_mem h1 with h | h` into its components or cases. Conclude with `h`. Use `absurd ?_ hg` and prove the remaining obligations. Establish `hg' : g ∈ imageZ v W` using `h`.

Rewrite `hg'` using `[hI, ← G.ker_x]`. Conclude with `hg'`.
-/
theorem comap_fibreOf (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).comap (baseSubst κ G) = W := by
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  have key : ∀ c ∈ fibreOf κ G W, ∃ w ∈ W, ∃ g : MRing ι, aeval G.x g ≠ 0 ∧
      c * C (aeval G.x g) = baseSubst κ G w := by
    intro c hc
    unfold fibreOf Ideal.map Ideal.span at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨w, hw, rfl⟩ := hc
      exact ⟨w, hw, 1, by simp, by simp⟩
    | zero => exact ⟨0, W.zero_mem, 1, by simp, by simp⟩
    | add c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁, g₁, h₁, e₁⟩ := ih₁
      obtain ⟨w₂, hw₂, g₂, h₂, e₂⟩ := ih₂
      refine ⟨w₁ * rename v g₂ + w₂ * rename v g₁, W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_right _ hw₂),
        g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
      simp only [map_add, map_mul, baseSubst_rename hv]
      rw [← e₁, ← e₂]
      ring
    | smul a c _ ih =>
      obtain ⟨w, hw, g, h, e⟩ := ih
      obtain ⟨F, g', h', e'⟩ := exists_mul_eq_baseSubst hv G a
      refine ⟨F * w, W.mul_mem_left _ hw, g' * g, by rw [map_mul]; exact mul_ne_zero h' h, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [← e', ← e]
      ring
  obtain ⟨w, hw, g, hg, e⟩ := key _ hf
  have h0 : f * rename v g - w ∈ P' :=
    mem_of_baseSubst_eq_zero hv G (by rw [map_sub, map_mul, baseSubst_rename hv, e, sub_self])
  have h1 : f * rename v g ∈ W := by simpa using W.add_mem (hPW h0) hw
  rcases hW.mem_or_mem h1 with h | h
  · exact h
  · refine absurd ?_ hg
    have hg' : g ∈ imageZ v W := h
    rw [hI, ← G.ker_x] at hg'
    exact hg'

/- English proof (translation)
Establish `hc` using `comap_fibreOf hv G hW hPW hI`. Use `⟨fun h => hW.ne_top ?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, h, Ideal.comap_top]`. Take `⟨F, g, hg, e⟩` from `exists_mul_eq_baseSubst hv G a`. Take `⟨H, g', hg', e'⟩` from `exists_mul_eq_baseSubst hv G b`.

Establish `hFH : F * H ∈ W`. Rewrite using `[← hc, Ideal.mem_comap, map_mul, ← e, ← e']`. Establish `: a * C (aeval G.x g) * (b * C (aeval G.x g')) = a * b * (C (aeval G.x g) * C (aeval G.x g'))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_right _ _ hab`. Break down `hW.mem_or_mem hFH with h | h` into its components or cases. Conclude with `Or.inl (mem_fibreOf_of_mul_eq G hg e h)`. Conclude with `Or.inr (mem_fibreOf_of_mul_eq G hg' e' h)`.
-/
theorem fibreOf_isPrime (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).IsPrime := by
  have hc := comap_fibreOf hv G hW hPW hI
  refine ⟨fun h => hW.ne_top ?_, fun {a b} hab => ?_⟩
  · rw [← hc, h, Ideal.comap_top]
  · obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G a
    obtain ⟨H, g', hg', e'⟩ := exists_mul_eq_baseSubst hv G b
    have hFH : F * H ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e, ← e']
      have : a * C (aeval G.x g) * (b * C (aeval G.x g')) = a * b * (C (aeval G.x g) * C (aeval G.x g')) := by
        ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hab
    rcases hW.mem_or_mem hFH with h | h
    · exact Or.inl (mem_fibreOf_of_mul_eq G hg e h)
    · exact Or.inr (mem_fibreOf_of_mul_eq G hg' e' h)

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[← G.ker_x, RingHom.mem_ker, imageZ, Ideal.mem_comap, Ideal.mem_comap]`. Use `show baseSubst κ G (rename v g) ∈ Q ↔ _`. Rewrite using `[baseSubst_rename hv]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Assume the negation of the conclusion as `hne`. Conclude with `hQ (Q.eq_top_of_isUnit_mem h ((isUnit_iff_ne_zero.mpr hne).map C))`. Introduce `h`. Rewrite using `[h, map_zero]`.

Conclude with `Q.zero_mem`.
-/
theorem imageZ_comap (hv : IsBlockMap κ v) (G : GenFibre v P') {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}
    (hQ : Q ≠ ⊤) : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := by
  ext g
  rw [← G.ker_x, RingHom.mem_ker, imageZ, Ideal.mem_comap, Ideal.mem_comap]
  show baseSubst κ G (rename v g) ∈ Q ↔ _
  rw [baseSubst_rename hv]
  constructor
  · intro h
    by_contra hne
    exact hQ (Q.eq_top_of_isUnit_mem h ((isUnit_iff_ne_zero.mpr hne).map C))
  · intro h
    rw [h, map_zero]
    exact Q.zero_mem

end Loc

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' d e G s hv hP' hP`. Establish `hPrel : IsRelevant (imageZ v P')` using `hP.2.1.2.2`. Establish `hPhor : IsHorizontal (imageZ v P')` using `hP.2.2.1`. Establish `hfib : ∀ {W : Ideal (MRing ι')}, P' ≤ W → fibreIdeal κ G ≤ fibreOf κ G W`. Introduce `W hW c hc`.

Take `⟨F, g, hg, e⟩` from `exists_mul_eq_baseSubst hv G c`. Use `mem_fibreOf_of_mul_eq G hg e (hW ?_)` and prove the remaining obligations. Rewrite using `[← baseSubst_mem_fibreIdeal hv G, ← e]`. Conclude with `Ideal.mul_mem_right _ _ hc`. Establish `hle : ∀ {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}, fibreIdeal κ G ≤ Q → P' ≤ Q.comap (baseSubst κ G)` using `fun hQ f hf => hQ ((baseSubst_mem_fibreIdeal hv G f).mpr hf)`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `W ⟨⟨⟨⟨hWp, hWle⟩, hWmin⟩, hWrel⟩, -, hWI⟩`. Establish `hPW` using `(sup_le_iff.mp hWle).1`. Establish `hsW` using `(Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hWle).2`. Establish `hcW` using `comap_fibreOf hv G hWp hPW hWI`.

Use `⟨⟨⟨fibreOf_isPrime hv G hWp hPW hWI, sup_le (hfib hPW) ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW))⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q' ⟨hQ'p, hQ'le⟩ hQ'Q`. Establish `hsQ'` using `(Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQ'le).2`. Establish `hm` using `hWmin ⟨Ideal.IsPrime.comap _ (hK := hQ'p), sup_le (hle (sup_le_iff.mp hQ'le).1) ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_comap.mpr hsQ'))⟩ (by rw [← hcW]; exact Ideal.comap_mono hQ'Q)`. Combine the equalities or inequalities in the displayed calculation.

Introduce `k`. Take `⟨i, hi⟩` from `hWrel k.1`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hcW, Ideal.mem_comap, baseSubst_X_fibre G ⟨k, i⟩]`. Conclude with `h`.

Introduce and unpack `W₁ ⟨⟨⟨⟨h1p, h1le⟩, -⟩, -⟩, -, h1I⟩ W₂ ⟨⟨⟨⟨h2p, h2le⟩, -⟩, -⟩, -, h2I⟩ heq`. Rewrite using `[← comap_fibreOf hv G h1p (sup_le_iff.mp h1le).1 h1I, heq, comap_fibreOf hv G h2p (sup_le_iff.mp h2le).1 h2I]`. Introduce and unpack `Q ⟨⟨⟨hQp, hQle⟩, hQmin⟩, hQrel⟩`. Establish `hWp : (Q.comap (baseSubst κ G)).IsPrime` using `Ideal.IsPrime.comap _ (hK := hQp)`. Establish `hPW : P' ≤ Q.comap (baseSubst κ G)` using `hle (sup_le_iff.mp hQle).1`.

Establish `hsW : s ∈ Q.comap (baseSubst κ G)` using `Ideal.mem_comap.mpr ((Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQle).2)`. Establish `hWI : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P'` using `imageZ_comap hv G hQp.ne_top`. Establish `hmap : fibreOf κ G (Q.comap (baseSubst κ G)) = Q` using `fibreOf_comap hv G Q`. Use `⟨Q.comap (baseSubst κ G), ⟨⟨⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, ?_⟩, ?_⟩, ?_, hWI⟩, hmap⟩` and prove the remaining obligations. Introduce and unpack `W' ⟨hW'p, hW'le⟩ hW'W`.

Establish `hPW'` using `(sup_le_iff.mp hW'le).1`. Establish `hsW'` using `(Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hW'le).2`. Establish `hW'I : imageZ v W' = imageZ v P'` using `le_antisymm (by rw [← hWI]; exact Ideal.comap_mono hW'W) (Ideal.comap_mono hPW')`. Establish `hm` using `hQmin ⟨fibreOf_isPrime hv G hW'p hPW' hW'I, sup_le (hfib hPW') ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW'))⟩ (by rw [← hmap]; exact Ideal.map_mono hW'W)`. Combine the equalities or inequalities in the displayed calculation.

Introduce `k'`. Distinguish the cases in `hk : k' ∈ Set.range κ`. Take `⟨k, rfl⟩` from `hk`. Take `⟨i, hi⟩` from `hPrel k`. Establish `hx : (X (v ⟨k, i⟩) : MRing ι') ∉ Q.comap (baseSubst κ G)` using `fun h => hi (by`.

Rewrite using `[← hWI, imageZ, Ideal.mem_comap]`. Use `show rename v (X ⟨k, i⟩) ∈ Q.comap (baseSubst κ G)`. Rewrite using `[rename_X]`. Conclude with `h)`. Establish `hvk` using `hv.2.2.1 ⟨k, i⟩`.

Generalize the expression as in `v ⟨k, i⟩ = q at hx hvk`. Take `⟨k'', j⟩` from `q`. Simplify using `only at hvk`. Substitute `hvk` using the available equality. Conclude with `⟨j, hx⟩`.

Take `⟨i, hi⟩` from `hQrel ⟨k', hk⟩`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← baseSubst_X_fibre G ⟨⟨k', hk⟩, i⟩]`. Conclude with `h`. Rewrite using `[IsHorizontal, eq_bot_iff]`.

Introduce `n hn`. Establish `hn' : n ∈ (imageZ v P').comap (C : ℤ →+* MRing ι)`. Rewrite using `[Ideal.mem_comap, ← hWI, imageZ, Ideal.mem_comap]`. Use `show rename v (C n) ∈ Q.comap (baseSubst κ G)`. Rewrite using `[rename_C]`.

Conclude with `Ideal.mem_comap.mp hn`. Rewrite `hn'` using `[hPhor]`. Conclude with `hn'`.
-/
theorem PFFibreBij.proof : PFFibreBij.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s hv hP' hP
  classical
  have hPrel : IsRelevant (imageZ v P') := hP.2.1.2.2
  have hPhor : IsHorizontal (imageZ v P') := hP.2.2.1
  have hfib : ∀ {W : Ideal (MRing ι')}, P' ≤ W → fibreIdeal κ G ≤ fibreOf κ G W := by
    intro W hW c hc
    obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
    refine mem_fibreOf_of_mul_eq G hg e (hW ?_)
    rw [← baseSubst_mem_fibreIdeal hv G, ← e]
    exact Ideal.mul_mem_right _ _ hc
  have hle : ∀ {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}, fibreIdeal κ G ≤ Q → P' ≤ Q.comap (baseSubst κ G) :=
    fun hQ f hf => hQ ((baseSubst_mem_fibreIdeal hv G f).mpr hf)
  refine ⟨?_, ?_, ?_⟩
  · rintro W ⟨⟨⟨⟨hWp, hWle⟩, hWmin⟩, hWrel⟩, -, hWI⟩
    have hPW := (sup_le_iff.mp hWle).1
    have hsW := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hWle).2
    have hcW := comap_fibreOf hv G hWp hPW hWI
    refine ⟨⟨⟨fibreOf_isPrime hv G hWp hPW hWI, sup_le (hfib hPW)
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW))⟩, ?_⟩, ?_⟩
    · rintro Q' ⟨hQ'p, hQ'le⟩ hQ'Q
      have hsQ' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQ'le).2
      have hm := hWmin ⟨Ideal.IsPrime.comap _ (hK := hQ'p), sup_le (hle (sup_le_iff.mp hQ'le).1)
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_comap.mpr hsQ'))⟩
        (by rw [← hcW]; exact Ideal.comap_mono hQ'Q)
      calc fibreOf κ G W ≤ fibreOf κ G (Q'.comap (baseSubst κ G)) := Ideal.map_mono hm
        _ = Q' := fibreOf_comap hv G Q'
    · intro k
      obtain ⟨i, hi⟩ := hWrel k.1
      refine ⟨i, fun h => hi ?_⟩
      rw [← hcW, Ideal.mem_comap, baseSubst_X_fibre G ⟨k, i⟩]
      exact h
  · rintro W₁ ⟨⟨⟨⟨h1p, h1le⟩, -⟩, -⟩, -, h1I⟩ W₂ ⟨⟨⟨⟨h2p, h2le⟩, -⟩, -⟩, -, h2I⟩ heq
    rw [← comap_fibreOf hv G h1p (sup_le_iff.mp h1le).1 h1I, heq,
      comap_fibreOf hv G h2p (sup_le_iff.mp h2le).1 h2I]
  · rintro Q ⟨⟨⟨hQp, hQle⟩, hQmin⟩, hQrel⟩
    have hWp : (Q.comap (baseSubst κ G)).IsPrime := Ideal.IsPrime.comap _ (hK := hQp)
    have hPW : P' ≤ Q.comap (baseSubst κ G) := hle (sup_le_iff.mp hQle).1
    have hsW : s ∈ Q.comap (baseSubst κ G) :=
      Ideal.mem_comap.mpr ((Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQle).2)
    have hWI : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := imageZ_comap hv G hQp.ne_top
    have hmap : fibreOf κ G (Q.comap (baseSubst κ G)) = Q := fibreOf_comap hv G Q
    refine ⟨Q.comap (baseSubst κ G), ⟨⟨⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, ?_⟩, ?_⟩,
      ?_, hWI⟩, hmap⟩
    · rintro W' ⟨hW'p, hW'le⟩ hW'W
      have hPW' := (sup_le_iff.mp hW'le).1
      have hsW' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hW'le).2
      have hW'I : imageZ v W' = imageZ v P' :=
        le_antisymm (by rw [← hWI]; exact Ideal.comap_mono hW'W) (Ideal.comap_mono hPW')
      have hm := hQmin ⟨fibreOf_isPrime hv G hW'p hPW' hW'I, sup_le (hfib hPW')
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW'))⟩
        (by rw [← hmap]; exact Ideal.map_mono hW'W)
      calc Q.comap (baseSubst κ G) ≤ (fibreOf κ G W').comap (baseSubst κ G) := Ideal.comap_mono hm
        _ = W' := comap_fibreOf hv G hW'p hPW' hW'I
    · intro k'
      by_cases hk : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := hk
        obtain ⟨i, hi⟩ := hPrel k
        have hx : (X (v ⟨k, i⟩) : MRing ι') ∉ Q.comap (baseSubst κ G) := fun h => hi (by
          rw [← hWI, imageZ, Ideal.mem_comap]
          show rename v (X ⟨k, i⟩) ∈ Q.comap (baseSubst κ G)
          rw [rename_X]
          exact h)
        have hvk := hv.2.2.1 ⟨k, i⟩
        generalize v ⟨k, i⟩ = q at hx hvk
        obtain ⟨k'', j⟩ := q
        simp only at hvk
        subst hvk
        exact ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := hQrel ⟨k', hk⟩
        refine ⟨i, fun h => hi ?_⟩
        rw [← baseSubst_X_fibre G ⟨⟨k', hk⟩, i⟩]
        exact h
    · rw [IsHorizontal, eq_bot_iff]
      intro n hn
      have hn' : n ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, ← hWI, imageZ, Ideal.mem_comap]
        show rename v (C n) ∈ Q.comap (baseSubst κ G)
        rw [rename_C]
        exact Ideal.mem_comap.mp hn
      rw [hPhor] at hn'
      exact hn'

end

end GroundTheory.Heights₂.Heights.Inter
