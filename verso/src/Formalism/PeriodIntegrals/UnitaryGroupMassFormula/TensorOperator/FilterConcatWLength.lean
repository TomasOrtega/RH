import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

/- English proof (translation)
Simplify using `only [concatW, liftW, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, y, hy, rfl⟩`. Conclude with `hy`. Introduce `h`.

Conclude with `⟨z.1, z.2, h, rfl⟩`.
-/
theorem mem_concatW {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (z : Fin n' × (Fin k × Fin k)) :
    z ∈ concatW w ↔ z.2 ∈ w z.1 := by
  simp only [concatW, liftW, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨t, y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨z.1, z.2, h, rfl⟩

/- English proof (translation)
Rewrite using `[← List.countP_eq_length_filter]`. Simplify using `only [concatW, liftW, List.countP_flatMap]`. Rewrite using `[← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_eq_single t]`. Simplify using `[Function.comp_def]`. Introduce `b _ hb`.

Simplify using `[Function.comp_def, hb]`. Simplify using the standard rewrite rules.
-/
theorem filter_concatW_length {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (t : Fin n') :
    ((concatW w).filter fun z => z.1 = t).length = (w t).length := by
  rw [← List.countP_eq_length_filter]
  simp only [concatW, liftW, List.countP_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_eq_single t]
  · simp [Function.comp_def]
  · intro b _ hb
    simp [Function.comp_def, hb]
  · simp

/- English proof (translation)
Simplify using `only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]`.
-/
theorem prod_smul_eq {σ K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (c : ι → K) (x : ι → MvPolynomial σ K) :
    ∏ i, (c i • x i) = (∏ i, c i) • ∏ i, x i := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

/- English proof (translation)
Use `show monomial (partS μ t) (1 : K) ∈ restrictSupport K {ν : Fin (m + 1) →₀ ℕ | ∑ c, ν c = d t}`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `x hx`. Establish `hx'` using `support_monomial_subset hx`. Rewrite `hx'` using `[Finset.mem_singleton]`.

Substitute `hx'` using the available equality. Establish `h` using `hμ t`. Simplify `h` using `[partS, multideg]`.
-/
theorem partS_mem {K : Type} [CommRing K] {n' m : ℕ} {d : Fin n' → ℕ} (μ : Fin n' × Fin (m + 1) →₀ ℕ)
    (hμ : μ ∈ {μ : Fin n' × Fin (m + 1) →₀ ℕ | ∀ i, multideg μ i = d i}) (t : Fin n') :
    monomial (partS μ t) (1 : K) ∈ Hd K (m + 1) (d t) := by
  show monomial (partS μ t) (1 : K) ∈ restrictSupport K {ν : Fin (m + 1) →₀ ℕ | ∑ c, ν c = d t}
  rw [mem_restrictSupport_iff]
  intro x hx
  have hx' := support_monomial_subset hx
  rw [Finset.mem_singleton] at hx'
  subst hx'
  have h := hμ t
  simpa [partS, multideg] using h

/- English proof (translation)
Unfold `StepPure`. Introduce `hFB hOP K _ _ n' m hm vec TT d c ν hν hνc hν0 B S hB hS`. Establish `hex : ∀ t : Fin n', ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1)))) (a : List (Fin (m + 1) × Fin (m + 1)) → K), (∀ l ∈ L, l.length ≤ (if t ∈ TT then c else 0)) ∧ ∀ P ∈ Hd K (m + 1) (d t), ∀ Q ∈ Hd K (m + 1) (d t), fockR (theta K m (vec t) P * S t) (theta K m (vec t) Q * B t) = …`. Introduce `t`. Use `hOP K m hm (vec t) (d t) (if t ∈ TT then c else 0) (ν t) (hν t) ?_ (B t) (hB t) (S t) (hS t)` and prove the remaining obligations.

Use `split_ifs with ht`. Conclude with `hνc t ht`. Simplify using `[hν0 t ht]`. Use `choose L a hLlen hLfock using hex`. Set `f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K` to `∑ w ∈ Fintype.piFinset L, Finsupp.single (concatW w) (∏ t, a t (w t))`.

Unfold `Ok`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Establish `hl'` using `Finsupp.support_finsetSum hl`. Rewrite `hl'` using `[Finset.mem_biUnion]`.

Take `⟨w, hw, hlw⟩` from `hl'`. Establish `hlw'` using `Finsupp.support_single_subset hlw`. Rewrite `hlw'` using `[Finset.mem_singleton]`. Substitute `hlw'` using the available equality. Rewrite `hw` using `[Fintype.mem_piFinset]`.

Unfold `WordOK`. Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Rewrite `hz` using `[mem_concatW]`. Assume the negation of the conclusion as `hzT`.

Establish `hlen` using `hLlen z.1 (w z.1) (hw z.1)`. Rewrite `hlen` using `[if_neg hzT]`. Consider the cases of `hwz : w z.1 with`. Consider the case `nil => simp [hwz] at hz`. Consider the case `cons _ _ => simp [hwz] at hlen`.

Introduce `t`. Rewrite using `[filter_concatW_length]`. Establish `hlen` using `hLlen t (w t) (hw t)`. Apply the tactic sequence `split_ifs at hlen <;> omega`. Establish `hcombo : ∀ G, combo f G = ∑ w ∈ Fintype.piFinset L, (∏ t, a t (w t)) • opWord (concatW w) G`.

Introduce `G`. Simplify using `only [combo, f]`. Rewrite using `[← Finsupp.sum_finsetSum_index (fun l => zero_smul K (opWord l G)) (fun l b₁ b₂ => add_smul b₁ b₂ (opWord l G))]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (zero_smul K (opWord (concatW w) G))]`.

Establish `hTh : ∀ F : Fin n' → MvPolynomial (Fin (m + 1)) K, Th0 K m vec (∏ t, embS K t (F t)) = ∏ t, blockEmb K t (theta K m (vec t) (F t))`. Introduce `F`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun t _ => blockSubstitution_blockInclusion vec t (F t)`. Establish `main : ∀ P Q : Fin n' → MvPolynomial (Fin (m + 1)) K, (∀ t, P t ∈ Hd K (m + 1) (d t)) → (∀ t, Q t ∈ Hd K (m + 1) (d t)) → fockR (Th0 K m vec (∏ t, embS K t (P t)) * ∏ t, blockEmb K t (S t)) (Th0 K m vec (∏ t, embS K t (Q t)) * ∏ t, blockEmb K t (B t)) = fockR (Th0 K m vec (combo …`.

Introduce `P Q hP hQ`. Establish `hc : combo f (∏ t, embS K t (P t)) = ∏ t, embS K t (∑ l ∈ L t, a t l • word1 l (P t))`. Rewrite using `[hcombo]`. Simplify using `only [map_sum, map_smul]`. Rewrite using `[Finset.prod_univ_sum]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[prod_smul_eq, hL K n' (m + 1) w P]`. Rewrite using `[hc, hTh, hTh, hTh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Simplify using `only [← map_mul]`. Rewrite using `[hFB K (Fin n') (m + 1) (m + 1), hFB K (Fin n') (m + 1) (m + 1)]`.

Conclude with `Finset.prod_congr rfl fun t _ => hLfock t (P t) (hP t) (Q t) (hQ t)`. Set `Φ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K` to `(fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂ ((LinearMap.mulRight K (∏ t, blockEmb K t (S t))).comp (Th0 K m vec).toLinearMap) ((LinearMap.mulRight K (∏ t, blockEmb K t (B t))).comp (Th0 K m vec).toLinearMap)`. Set `Ψ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K` to `(fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂ ((Th0 K m vec).toLinearMap.comp (comboL f)) (Th0 K m vec).toLinearMap`. Establish `key` using `bilin_ext_restrict {μ | ∀ i, multideg μ i = d i} Φ Ψ (by`. Introduce `μ hμ μ' hμ'`.

Use `show fockB _ K (Th0 K m vec (monomial μ 1) * ∏ t, blockEmb K t (S t)) (Th0 K m vec (monomial μ' 1) * ∏ t, blockEmb K t (B t)) = fockB _ K (Th0 K m vec (combo f (monomial μ 1))) (Th0 K m vec (monomial μ' 1))`. Rewrite using `[fockB_apply, fockB_apply, hM K n' (m + 1) μ, hM K n' (m + 1) μ']`. Conclude with `main _ _ (fun t => partS_mem μ hμ t) (fun t => partS_mem μ' hμ' t))`. Introduce `G hG H hH`. Rewrite using `[← fockB_apply, ← fockB_apply]`.

Conclude with `key G hG H hH`.
-/
theorem stepPure_of (hL : StepLift) (hM : StepMonoFactor) : StepPure := by
  unfold StepPure
  intro hFB hOP K _ _ n' m hm vec TT d c ν hν hνc hν0 B S hB hS
  classical
  have hex : ∀ t : Fin n', ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1))))
      (a : List (Fin (m + 1) × Fin (m + 1)) → K),
      (∀ l ∈ L, l.length ≤ (if t ∈ TT then c else 0)) ∧
      ∀ P ∈ Hd K (m + 1) (d t), ∀ Q ∈ Hd K (m + 1) (d t),
        fockR (theta K m (vec t) P * S t) (theta K m (vec t) Q * B t) =
          fockR (theta K m (vec t) (∑ l ∈ L, a l • word1 l P)) (theta K m (vec t) Q) := by
    intro t
    refine hOP K m hm (vec t) (d t) (if t ∈ TT then c else 0) (ν t) (hν t) ?_ (B t) (hB t)
      (S t) (hS t)
    split_ifs with ht
    · exact hνc t ht
    · simp [hν0 t ht]
  choose L a hLlen hLfock using hex
  let f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K :=
    ∑ w ∈ Fintype.piFinset L, Finsupp.single (concatW w) (∏ t, a t (w t))
  unfold Ok
  refine ⟨f, ?_, ?_⟩
  · intro l hl
    have hl' := Finsupp.support_finsetSum hl
    rw [Finset.mem_biUnion] at hl'
    obtain ⟨w, hw, hlw⟩ := hl'
    have hlw' := Finsupp.support_single_subset hlw
    rw [Finset.mem_singleton] at hlw'
    subst hlw'
    rw [Fintype.mem_piFinset] at hw
    unfold WordOK
    constructor
    · intro z hz
      rw [mem_concatW] at hz
      by_contra hzT
      have hlen := hLlen z.1 (w z.1) (hw z.1)
      rw [if_neg hzT] at hlen
      cases hwz : w z.1 with
      | nil => simp [hwz] at hz
      | cons _ _ => simp [hwz] at hlen
    · intro t
      rw [filter_concatW_length]
      have hlen := hLlen t (w t) (hw t)
      split_ifs at hlen <;> omega
  · have hcombo : ∀ G, combo f G =
        ∑ w ∈ Fintype.piFinset L, (∏ t, a t (w t)) • opWord (concatW w) G := by
      intro G
      simp only [combo, f]
      rw [← Finsupp.sum_finsetSum_index (fun l => zero_smul K (opWord l G))
        (fun l b₁ b₂ => add_smul b₁ b₂ (opWord l G))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finsupp.sum_single_index (zero_smul K (opWord (concatW w) G))]
    have hTh : ∀ F : Fin n' → MvPolynomial (Fin (m + 1)) K,
        Th0 K m vec (∏ t, embS K t (F t)) = ∏ t, blockEmb K t (theta K m (vec t) (F t)) := by
      intro F
      rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => blockSubstitution_blockInclusion vec t (F t)
    have main : ∀ P Q : Fin n' → MvPolynomial (Fin (m + 1)) K,
        (∀ t, P t ∈ Hd K (m + 1) (d t)) → (∀ t, Q t ∈ Hd K (m + 1) (d t)) →
        fockR (Th0 K m vec (∏ t, embS K t (P t)) * ∏ t, blockEmb K t (S t))
            (Th0 K m vec (∏ t, embS K t (Q t)) * ∏ t, blockEmb K t (B t)) =
          fockR (Th0 K m vec (combo f (∏ t, embS K t (P t))))
            (Th0 K m vec (∏ t, embS K t (Q t))) := by
      intro P Q hP hQ
      have hc : combo f (∏ t, embS K t (P t)) =
          ∏ t, embS K t (∑ l ∈ L t, a t l • word1 l (P t)) := by
        rw [hcombo]
        simp only [map_sum, map_smul]
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [prod_smul_eq, hL K n' (m + 1) w P]
      rw [hc, hTh, hTh, hTh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp only [← map_mul]
      rw [hFB K (Fin n') (m + 1) (m + 1), hFB K (Fin n') (m + 1) (m + 1)]
      exact Finset.prod_congr rfl fun t _ => hLfock t (P t) (hP t) (Q t) (hQ t)
    let Φ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((LinearMap.mulRight K (∏ t, blockEmb K t (S t))).comp (Th0 K m vec).toLinearMap)
        ((LinearMap.mulRight K (∏ t, blockEmb K t (B t))).comp (Th0 K m vec).toLinearMap)
    let Ψ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((Th0 K m vec).toLinearMap.comp (comboL f)) (Th0 K m vec).toLinearMap
    have key := bilin_ext_restrict {μ | ∀ i, multideg μ i = d i} Φ Ψ (by
      intro μ hμ μ' hμ'
      show fockB _ K (Th0 K m vec (monomial μ 1) * ∏ t, blockEmb K t (S t))
          (Th0 K m vec (monomial μ' 1) * ∏ t, blockEmb K t (B t)) =
        fockB _ K (Th0 K m vec (combo f (monomial μ 1))) (Th0 K m vec (monomial μ' 1))
      rw [fockB_apply, fockB_apply, hM K n' (m + 1) μ, hM K n' (m + 1) μ']
      exact main _ _ (fun t => partS_mem μ hμ t) (fun t => partS_mem μ' hμ' t))
    intro G hG H hH
    rw [← fockB_apply, ← fockB_apply]
    exact key G hG H hH

end PI.TOW
