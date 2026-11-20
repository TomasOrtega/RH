import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.TransportLoc

variable {G G' : Type} [Group G] [Group G']

/- English proof (translation)
Use `show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)`. Rewrite using `[← h, ← map_mul, ← map_mul, e.injective.eq_iff]`.
-/
theorem mem_twCent_iff (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d x : G) :
    x ∈ twCent θ d ↔ e x ∈ twCent θ' (e d) := by
  show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)
  rw [← h, ← map_mul, ← map_mul, e.injective.eq_iff]

/- English proof (translation)
Simplify using `only [map_mul, map_inv, h]`.
-/
theorem map_twConj (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d y : G) :
    e (y⁻¹ * d * θ y) = (e y)⁻¹ * e d * θ' (e y) := by
  simp only [map_mul, map_inv, h]

/- English proof (translation)
Establish `ht' : t * d = d * θ t` using `ht`. Rewrite using `[map_mul, _root_.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twConj_mul (θ : G →* G) (d t w : G) (ht : t ∈ twCent θ d) :
    (t * w)⁻¹ * d * θ (t * w) = w⁻¹ * d * θ w := by
  have ht' : t * d = d * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc w⁻¹ * t⁻¹ * d * (θ t * θ w) = w⁻¹ * t⁻¹ * (d * θ t) * θ w := by group
    _ = w⁻¹ * d * θ w := by rw [← ht']; group

/- English proof (translation)
Use `Set.Finite.of_injOn (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) => DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin` and prove the remaining obligations. Introduce and unpack `q ⟨k, hk, hne⟩`. Take `⟨t, k₁, ht₀, hk₁, hout⟩` from `DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))`. Use `⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩` and prove the remaining obligations. Establish `hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) * (k₁⁻¹ * e k) = t * e (Quotient.out q * k)`.

Rewrite using `[hout, map_mul]`. Use `group`. Simplify using `only []`. Rewrite using `[hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]`. Conclude with `hne`.

Introduce `q₁ _ q₂ _ heq`. Take `⟨t', ht', k', hk', hy⟩` from `(DoubleCoset.eq _ _ _ _).1 heq`. Establish `h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k'`. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [map_mul, e.apply_symm_apply]`.

Conclude with `hy`. Establish `ht : e.symm t' ∈ twCent θ d`. Rewrite using `[mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]`. Conclude with `ht'`. Establish `hk : e.symm k' ∈ K`.

Rewrite using `[hK, e.apply_symm_apply]`. Conclude with `hk'`. Rewrite using `[← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂]`. Conclude with `(DoubleCoset.eq _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩`.
-/
theorem finite_support (e : G ≃* G') (θ : G →* G) (θ' : G' →* G')
    (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ)
    (hθ : ∀ x, e (θ x) = θ' (e x)) (hK : ∀ x, x ∈ K ↔ e x ∈ K') (hf : ∀ x, f x = f' (e x))
    (hfin : {q : DoubleCoset.Quotient (twCent θ' (e d) : Set G') (K' : Set G') |
      ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * e d * θ' (Quotient.out q * k)) ≠ 0}.Finite) :
    {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
      ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) =>
      DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin
  · rintro q ⟨k, hk, hne⟩
    obtain ⟨t, k₁, ht₀, hk₁, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))
    refine ⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩
    have hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) *
        (k₁⁻¹ * e k) = t * e (Quotient.out q * k) := by
      rw [hout, map_mul]; group
    simp only []
    rw [hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]
    exact hne
  · intro q₁ _ q₂ _ heq
    obtain ⟨t', ht', k', hk', hy⟩ := (DoubleCoset.eq _ _ _ _).1 heq
    have h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k' := by
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact hy
    have ht : e.symm t' ∈ twCent θ d := by
      rw [mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]; exact ht'
    have hk : e.symm k' ∈ K := by
      rw [hK, e.apply_symm_apply]; exact hk'
    rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂]
    exact (DoubleCoset.eq _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩

/- English proof (translation)
Set `φ : K →* K'` to `{ toFun := fun k => ⟨e k, (hK k).1 k.2⟩ map_one' := by ext; simp map_mul' := fun a b => by ext; simp }`. Establish `hφ : Function.Surjective φ` using `fun k' => ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩`. Establish `hu' : ∀ k : K, u k = u' (φ k)` using `hu`. Establish `hstab : rStab u = (rStab u').comap φ`. Use extensionality with `k`.

Prove the components needed by the constructor for the conclusion. Introduce `hk x'`. Take `⟨x, rfl⟩` from `hφ x'`. Use `show u' (φ x * φ k) = u' (φ x)`. Rewrite using `[← map_mul, ← hu', ← hu']`.

Conclude with `hk x`. Introduce `hk x show u (x * k) = u x`. Rewrite using `[hu', hu', map_mul]`. Conclude with `hk (φ x)`. Rewrite using `[hstab, Subgroup.index_comap_of_surjective _ hφ]`.

Conclude with `h`.
-/
theorem index_ne_zero (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K')
    (u : K → ℂ) (u' : K' → ℂ) (hu : ∀ k : K, u k = u' ⟨e k, (hK k).1 k.2⟩)
    (h : (rStab u').index ≠ 0) : (rStab u).index ≠ 0 := by
  let φ : K →* K' :=
    { toFun := fun k => ⟨e k, (hK k).1 k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := fun k' =>
    ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩
  have hu' : ∀ k : K, u k = u' (φ k) := hu
  have hstab : rStab u = (rStab u').comap φ := by
    ext k
    constructor
    · intro hk x'
      obtain ⟨x, rfl⟩ := hφ x'
      show u' (φ x * φ k) = u' (φ x)
      rw [← map_mul, ← hu', ← hu']
      exact hk x
    · intro hk x
      show u (x * k) = u x
      rw [hu', hu', map_mul]
      exact hk (φ x)
  rw [hstab, Subgroup.index_comap_of_surjective _ hφ]
  exact h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩`. Introduce and unpack `⟨k', hk', h⟩`. Use `⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩` and prove the remaining obligations.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← h]`. Simplify using `[MulAut.conj_apply]`.
-/
theorem mem_conj_iff (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K') (y x : G) :
    x ∈ K.map (MulAut.conj y).toMonoidHom ↔ e x ∈ K'.map (MulAut.conj (e y)).toMonoidHom := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k', hk', h⟩
    refine ⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩
    apply e.injective
    rw [← h]
    simp [MulAut.conj_apply]

variable [TopologicalSpace G] [TopologicalSpace G']

/- English proof (translation)
Establish `h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G)`. Use `MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t` as an intermediate fact. Conclude with `(congrArg (fun S : Subgroup G' => (S : Set G')) this).symm`. Rewrite using `[h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]`.
-/
theorem isCompact_closure_zpowers_iff (e : G ≃ₜ* G') (t : G) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
  have h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t
    exact (congrArg (fun S : Subgroup G' => (S : Set G')) this).symm
  rw [h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]

/- English proof (translation)
Unfold `cptPart`. Rewrite using `[MonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `t'`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, ⟨ht, hc⟩, rfl⟩`. Conclude with `⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩`. Introduce and unpack `⟨ht', hc⟩`. Use `⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩` and prove the remaining obligations. Rewrite using `[hT]`.

Simplify using `using ht'`. Rewrite using `[isCompact_closure_zpowers_iff e]`. Simplify using `using hc`.
-/
theorem map_cptPart (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G') (hT : ∀ x, x ∈ T ↔ e x ∈ T') :
    (cptPart T).map e.toMulEquiv.toMonoidHom = cptPart T' := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext t'
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩
  · rintro ⟨ht', hc⟩
    refine ⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩
    · rw [hT]; simpa using ht'
    · rw [isCompact_closure_zpowers_iff e]; simpa using hc

/- English proof (translation)
Introduce `G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h`. Take `⟨h₁, h₂, h₃, h₄⟩` from `h`. Establish `hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x)` using `hθ`. Establish `hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K'` using `hK`. Establish `hfm : ∀ x, f x = f' (e.toMulEquiv x)` using `hf`.

Establish `hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d)` using `mem_twCent_iff e.toMulEquiv θ θ' hθm d`. Use `⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Apply `e.toMulEquiv.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`.

Conclude with `h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)`. Introduce `y`. Use `index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))` and prove the remaining obligations. Introduce `k`. Use `map_twConj e.toMulEquiv θ θ' hθm d (y * k)` as an intermediate fact.

Rewrite using `[hfm, this, map_mul]`. Both sides reduce to the same expression. Introduce `y`. Take `⟨ha, hb⟩` from `h₄ (e y)`. Establish `hB` using `map_cptPart e (twCent θ d) (twCent θ' (e d)) hT`.

Establish `hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom = (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom`. Use extensionality with `x`. Rewrite using `[Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]`. Conclude with `and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hA]`. Introduce `x hx`. Establish `hx'` using `ha hx`. Rewrite `hx'` using `[← hB]`. Take `⟨z, hz, hzx⟩` from `hx'`.

Rewrite using `[← e.toMulEquiv.injective hzx]` and apply the resulting hypothesis. Rewrite using `[hA, Subgroup.relIndex_comap, hB]`. Conclude with `hb`.
-/
theorem locConds_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x) := hθ
  have hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K' := hK
  have hfm : ∀ x, f x = f' (e.toMulEquiv x) := hf
  have hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d) :=
    mem_twCent_iff e.toMulEquiv θ θ' hθm d
  refine ⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩
  · intro x hx y hy
    apply e.toMulEquiv.injective
    rw [map_mul, map_mul]
    exact h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)
  · intro y
    refine index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))
    intro k
    have := map_twConj e.toMulEquiv θ θ' hθm d (y * k)
    rw [hfm, this, map_mul]
    rfl
  · intro y
    obtain ⟨ha, hb⟩ := h₄ (e y)
    have hB := map_cptPart e (twCent θ d) (twCent θ' (e d)) hT
    have hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom =
        (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)
    constructor
    · rw [hA]
      intro x hx
      have hx' := ha hx
      rw [← hB] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← e.toMulEquiv.injective hzx]
    · rw [hA, Subgroup.relIndex_comap, hB]
      exact hb

end GlobalTheory.CompanionTheory.TransportLoc

end
