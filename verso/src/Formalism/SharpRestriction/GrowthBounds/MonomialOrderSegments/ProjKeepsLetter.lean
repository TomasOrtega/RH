import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.FockMonomialRight

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

section Generic

variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)

/- English proof (translation)
Establish `h` using `(hπ G hG).2.2.2 A hA hAW`. Rewrite `h` using `[fock_sub_left]`. Rewrite using `[fock_comm A (π G), fock_comm A G]`. Conclude with `(sub_eq_zero.mp h).symm`.
-/
theorem fock_proj_right {W : Set (MvPolynomial (L × Fin r) K)}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d W π) {A G : MvPolynomial (L × Fin r) K}
    (hA : A ∈ PolK K r d) (hAW : A ∈ W) (hG : G ∈ PolK K r d) : fock A (π G) = fock A G := by
  have h := (hπ G hG).2.2.2 A hA hAW
  rw [fock_sub_left] at h
  rw [fock_comm A (π G), fock_comm A G]
  exact (sub_eq_zero.mp h).symm

/- English proof (translation)
Take `⟨⟨π'', hπ''⟩, -⟩` from `hP hD L sg r d S'' th''`. Establish `hfix : π'' F = F` using `(hπ'' F hF).2.2.1 hFW`. Establish `hcomm : π (π'' F) = π'' (π F)`. Break down `hS with h | h | h` into its components or cases. Conclude with `((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF`.

Conclude with `(((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm`. Conclude with `((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF`. Establish `hE : π F = π'' (π F)` using `by rw [← hcomm, hfix]`. Rewrite using `[hE]`. Conclude with `(hπ'' (π F) (hπ F hF).1).2.1`.
-/
theorem proj_preserves (hP : PROJ K v p C0) (hD : DVRHyp v p) {S S'' : Finset L} {th th'' : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π)
    (hS : S ⊆ S'' ∨ S'' ⊆ S ∨ Disjoint S S'') {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) (hFW : F ∈ Aset sg S'' th'') : π F ∈ Aset sg S'' th'' := by
  obtain ⟨⟨π'', hπ''⟩, -⟩ := hP hD L sg r d S'' th''
  have hfix : π'' F = F := (hπ'' F hF).2.2.1 hFW
  have hcomm : π (π'' F) = π'' (π F) := by
    rcases hS with h | h | h
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF
    · exact (((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF
  have hE : π F = π'' (π F) := by rw [← hcomm, hfix]
  rw [hE]
  exact (hπ'' (π F) (hπ F hF).1).2.1

/- English proof (translation)
Rewrite `ha`, the goal using `[bge_iff]`. Establish `hb` using `((hP hD L sg r d S th).2 π hπ).2.2 F hF`. Establish `h2` using `ha.trans hb`. Generalize the expression as in `vBB v (π F) = x at h2 ⊢`. Proceed by induction on `x using WithTop.recTopCoe with`.

Consider the case `top => exact le_top`. Consider the case `coe x`. Rewrite `h2` using `[← WithTop.coe_add, WithTop.coe_le_coe]`. Rewrite using `[WithTop.coe_le_coe]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bge_proj (hP : PROJ K v p C0) (hD : DVRHyp v p) {S : Finset L} {th : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π) {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) {a : ℝ} (ha : bge v a F) :
    bge v (a - (r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i)) (π F) := by
  rw [bge_iff] at ha ⊢
  have hb := ((hP hD L sg r d S th).2 π hπ).2.2 F hF
  have h2 := ha.trans hb
  generalize vBB v (π F) = x at h2 ⊢
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_, fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩` and prove the remaining obligations. Introduce `F _ a ha`. Simplify using `using ha`.

Consider the case `@insert x s hx ih`. Establish `hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z)` using `fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)`. Take `⟨Pr, h1, h2, h3, h4, h5, h6⟩` from `ih hpair'`. Take `⟨⟨πx, hπx⟩, -⟩` from `hP hD L sg r d (S x) (th x)`. Establish `hPx` using `(hP hD L sg r d (S x) (th x)).2 πx hπx`.

Use `⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F hF`. Conclude with `(hπx _ (h1 F hF)).1`. Introduce `F hF y hy`. Break down `Finset.mem_insert.mp hy with rfl | hy` into its components or cases.

Conclude with `(hπx _ (h1 F hF)).2.1`. Conclude with `proj_preserves sg d hP hD hπx (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)`. Introduce `A hA hAW G hG`. Rewrite using `[LinearMap.comp_apply, fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]`. Conclude with `h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG`.

Introduce `F hF a ha`. Establish `hb` using `bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)`. Rewrite using `[LinearMap.comp_apply]`. Use `bge_mono v ?_ hb` and prove the remaining obligations. Rewrite using `[Finset.card_insert_eq_ite, if_neg hx]`.

Apply `le_of_eq` to reduce the goal to its premises. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `S'' th'' hS F hF hFW`. Establish `hPr` using `h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW`.

Rewrite using `[LinearMap.comp_apply]`. Break down `hS x (Finset.mem_insert_self x s) with h | h` into its components or cases. Conclude with `proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr`. Conclude with `proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr`. Introduce `i hi hout a F hF`.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]`. Conclude with `hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)`.
-/
theorem prodProj (hP : PROJ K v p C0) (hD : DVRHyp v p) {ι : Type} (s : Finset ι)
    (S : ι → Finset L) (th : ι → ℤ)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, S x ⊆ S y ∨ S y ⊆ S x ∨ Disjoint (S x) (S y)) :
    ∃ Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K,
      (∀ F ∈ PolK K r d, Pr F ∈ PolK K r d) ∧
      (∀ F ∈ PolK K r d, ∀ x ∈ s, Pr F ∈ Aset sg (S x) (th x)) ∧
      (∀ A ∈ PolK K r d, (∀ x ∈ s, A ∈ Aset sg (S x) (th x)) →
        ∀ G ∈ PolK K r d, fock A (Pr G) = fock A G) ∧
      (∀ F ∈ PolK K r d, ∀ a : ℝ, bge v a F →
        bge v (a - s.card * ((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i))) (Pr F)) ∧
      (∀ (S'' : Finset L) (th'' : ℤ), (∀ x ∈ s, S x ⊆ S'' ∨ Disjoint (S x) S'') →
        ∀ F ∈ PolK K r d, F ∈ Aset sg S'' th'' → Pr F ∈ Aset sg S'' th'') ∧
      (∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_,
      fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩
    intro F _ a ha
    simpa using ha
  | @insert x s hx ih =>
    have hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z) :=
      fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    obtain ⟨Pr, h1, h2, h3, h4, h5, h6⟩ := ih hpair'
    obtain ⟨⟨πx, hπx⟩, -⟩ := hP hD L sg r d (S x) (th x)
    have hPx := (hP hD L sg r d (S x) (th x)).2 πx hπx
    refine ⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F hF
      exact (hπx _ (h1 F hF)).1
    · intro F hF y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hπx _ (h1 F hF)).2.1
      · exact proj_preserves sg d hP hD hπx
          (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)
    · intro A hA hAW G hG
      rw [LinearMap.comp_apply,
        fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]
      exact h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG
    · intro F hF a ha
      have hb := bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)
      rw [LinearMap.comp_apply]
      refine bge_mono v ?_ hb
      rw [Finset.card_insert_eq_ite, if_neg hx]
      apply le_of_eq
      push_cast
      ring
    · intro S'' th'' hS F hF hFW
      have hPr := h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW
      rw [LinearMap.comp_apply]
      rcases hS x (Finset.mem_insert_self x s) with h | h
      · exact proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr
      · exact proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr
    · intro i hi hout a F hF
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]
      exact hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)

end Generic

section Torus

variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

/- English proof (translation)
Use `MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]`. Rewrite using `[map_add, mul_add, hP, hQ, map_add]`.
-/
theorem euler_eq_dg {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)
  · rw [MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]
  · rw [map_add, mul_add, hP, hQ, map_add]

/- English proof (translation)
Rewrite using `[dg_eq_sum_f, MvPolynomial.coeff_sum]`. Distinguish the cases in `h : α ∈ F.support`. Rewrite using `[Finset.sum_eq_single α (fun β _ hβ => by rw [MvPolynomial.coeff_monomial, if_neg hβ]) (fun h' => absurd h h'), MvPolynomial.coeff_monomial, if_pos rfl]`. Establish `h0 : F.coeff α = 0` using `by simpa using h`. Rewrite using `[h0, mul_zero]`.

Conclude with `Finset.sum_eq_zero (fun β hβ => by`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg (fun (e : β = α) => h (e ▸ hβ))])`.
-/
private theorem coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K)
    (α : σ →₀ ℕ) : (dg f F).coeff α = f α * F.coeff α := by
  classical
  rw [dg_eq_sum_f, MvPolynomial.coeff_sum]
  by_cases h : α ∈ F.support
  · rw [Finset.sum_eq_single α (fun β _ hβ => by rw [MvPolynomial.coeff_monomial, if_neg hβ])
      (fun h' => absurd h h'), MvPolynomial.coeff_monomial, if_pos rfl]
  · have h0 : F.coeff α = 0 := by simpa using h
    rw [h0, mul_zero]
    exact Finset.sum_eq_zero (fun β hβ => by
      rw [MvPolynomial.coeff_monomial, if_neg (fun (e : β = α) => h (e ▸ hβ))])

/- English proof (translation)
Establish `hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d`. Rewrite using `[mem_PolK_iff]`. Introduce `α hα k`. Establish `hαζ : α = ζ`. Assume the negation of the conclusion as `hne`.

Rewrite `hα` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)]`. Conclude with `hα rfl`. Rewrite using `[hαζ]`. Conclude with `hζ k`. Establish `h` using `hcomm a _ hmono`.

Rewrite `h` using `[euler_eq_dg, euler_eq_dg]`. Simplify using `only [dg_monomial, mul_one] at h`. Establish `h'` using `congrArg (fun G => MvPolynomial.coeff ζ' G) h`. Simplify using `only [coeff_dg_eq_mul_coeff] at h'`. Establish `hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) = ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K)`.

Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite `h'` using `[hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul]`. Establish `hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0` using `by simpa using hζ'`. Establish `hc` using `mul_right_cancel₀ hne h'`. Conclude with `hc.symm` after adjusting the coercions.
-/
theorem proj_keeps_letter (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  have h := hcomm a _ hmono
  rw [euler_eq_dg, euler_eq_dg] at h
  simp only [dg_monomial, mul_one] at h
  have h' := congrArg (fun G => MvPolynomial.coeff ζ' G) h
  simp only [coeff_dg_eq_mul_coeff] at h'
  have hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) =
      ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h'
  have hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0 := by simpa using hζ'
  have hc := mul_right_cancel₀ hne h'
  exact_mod_cast hc.symm

end Torus

/- English proof (translation)
Establish `hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d`. Rewrite using `[mem_PolK_iff]`. Introduce `α hα k`. Establish `hαζ : α = ζ`. Assume the negation of the conclusion as `hne`.

Rewrite `hα` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)]`. Conclude with `hα rfl`. Rewrite using `[hαζ]`. Conclude with `hζ k`. Conclude with `⟨fun k => (mem_PolK_iff d _).mp (h1 _ hmono) ζ' hζ' k, fun i hi hout a => proj_keeps_letter d Pr i (h6 i hi hout) ζ hζ ζ' hζ' a⟩`.
-/
theorem prodProj_entries {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r]
    (d : L → ℕ) {ι : Type} (s : Finset ι) (S : ι → Finset L)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (h1 : ∀ F ∈ PolK K r d, Pr F ∈ PolK K r d)
    (h6 : ∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) :
    (∀ k, ldeg ζ' k = d k) ∧
      ∀ i, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ a, ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  exact ⟨fun k => (mem_PolK_iff d _).mp (h1 _ hmono) ζ' hζ' k,
    fun i hi hout a => proj_keeps_letter d Pr i (h6 i hi hout) ζ hζ ζ' hζ' a⟩

end Formalism.MainNotions.PlaneGram
