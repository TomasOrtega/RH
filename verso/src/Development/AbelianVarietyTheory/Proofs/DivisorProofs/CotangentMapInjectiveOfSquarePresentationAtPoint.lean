import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CotangentSquare

open MvPolynomial

variable {O B σ : Type} [CommRing O] [CommRing B]

def firstOrderKer (η : MvPolynomial σ B →+* O) : Ideal (MvPolynomial σ B) where
  carrier := {F | η F = 0 ∧ ∀ l, η (pderiv l F) = 0}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨by simp [hF, hG], fun l => by simp [hF' l, hG' l]⟩
  zero_mem' := ⟨by simp, fun l => by simp⟩
  smul_mem' := by
    rintro G F ⟨hF, hF'⟩
    exact ⟨by simp [hF], fun l => by simp [pderiv_mul, hF, hF' l]⟩

/- English proof (translation)
Use `hk.2 l` as an intermediate fact. Simplify using `[map_sum, pderiv_mul, hf, this]`.
-/
theorem pderiv_comb [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by
  have := hk.2 l
  simp [map_sum, pderiv_mul, hf, this]

/- English proof (translation)
Introduce `hJ`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ hc this.symm`.
-/
theorem det_ne_zero_of_mul_eq [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by
  intro hJ
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

/- English proof (translation)
Introduce `O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb`. Use `set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ`. Set `η : MvPolynomial σ B →+* O` to `(ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)`. Establish `hη : ∀ F, η F = ε (Ψ F)` using `fun F => rfl`. Use `set q := (RingHom.ker ε).comap Ψ with hq`.

Establish `hqmem : ∀ F, F ∈ q ↔ η F = 0` using `fun F => by`. Rewrite using `[hq, Ideal.mem_comap, RingHom.mem_ker, hη]`. Establish `hkerq : RingHom.ker Ψ ≤ q` using `fun F hF => by`. Rewrite using `[hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]`. Establish `hηf : ∀ i, η (f i) = 0` using `fun i => by rw [hη, hf i, map_zero]`.

Use `set K := firstOrderKer η with hK`. Establish `hq2 : q ^ 2 ≤ K`. Rewrite using `[pow_two]`. Use `Ideal.mul_le.2 fun a ha b' hb' => ?_` and prove the remaining obligations. Rewrite `ha`, `hb'` using `[hqmem]`.

Conclude with `⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩`. Establish `hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2`. Use `hker.trans (sup_le_sup_left ?_ _)` and prove the remaining obligations. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mono_right hkerq`.

Establish `hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K` using `hkerL.trans (sup_le_sup_left hq2 _)`. Establish `hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ`. Rewrite using `[Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]`. Establish `lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L → ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L`. Introduce `L hL F hF`.

Take `⟨G, hG, hGF⟩` from `(Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF`. Establish `h1 : F - G ∈ RingHom.ker Ψ` using `by rw [RingHom.mem_ker, map_sub, hGF, sub_self]`. Establish `h2 : F = (F - G) + G` using `by ring`. Rewrite using `[h2]`. Conclude with `Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)`.

Establish `hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `i hi`. Rewrite `hi` using `[Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[Ideal.mem_comap]`.

Establish `: algebraMap B A i = Ψ (C i)` using `by simp [hΨ]`. Rewrite using `[this]`. Use `Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩` and prove the remaining obligations. Rewrite using `[hη]`. Simplify `hi` using `[hΨ]`.

Set `Jac : Matrix σ σ O` to `fun i l => η (pderiv l (f i))`. Establish `hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l, (if j = l then c else 0) = ∑ i, η (g i) * Jac i l`. Introduce `j`. Use `set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF`. Establish `ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε`.

Rewrite using `[RingHom.mem_ker]`. Simplify using the standard rewrite rules. Establish `hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j)))`. Simplify using `[hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]`. Establish `hmem : Ψ F ∈ K.map Ψ`.

Rewrite using `[hΨF]`. Use `(sup_le ?_ hIB) (hc2 _ ha)` and prove the remaining obligations. Rewrite using `[hsq]`. Conclude with `Ideal.map_mono hq2`. Establish `hF2` using `lift K hkerK F hmem`.

Rewrite `hF2` using `[Submodule.mem_sup]`. Take `⟨s, hs, k, hk, hsk⟩` from `hF2`. Take `⟨g, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hs`. Use `⟨g, fun l => ?_⟩` and prove the remaining obligations. Establish `e1` using `pderiv_comb η f g hηf k hk l`.

Rewrite `e1` using `[hsk]`. Rewrite using `[← e1, hF]`. Distinguish the cases in `hjl : j = l`. Substitute `hjl` using the available equality. Simplify using `[pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]`.

Simplify using `[hjl, pderiv_X_of_ne (Ne.symm hjl)]`. Use `choose g hg using hrow`. Set `N : Matrix σ σ O` to `fun j i => η (g j i)`. Establish `hNJ : N * Jac = c • (1 : Matrix σ σ O)`. Use extensionality with `j l`.

Rewrite using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hdet : Jac.det ≠ 0` using `det_ne_zero_of_mul_eq hc hNJ`. Establish `hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2`. Use `lift _ hkerL (C b) ?_` and prove the remaining obligations.

Rewrite using `[← hsq]`. Simplify `hb` using `[hΨ]`. Rewrite `hCb` using `[Submodule.mem_sup]`. Take `⟨s, hs, k, hk, hsk⟩` from `hCb`. Take `⟨g', rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hs`.

Establish `hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0`. Use function extensionality and compare the values at `l`. Establish `e1` using `pderiv_comb η f g' hηf k (hq2 hk) l`. Rewrite `e1` using `[hsk]`. Simplify using `only [pderiv_C, map_zero] at e1`.

Express the relevant statement in the definitionally equal form `∑ i, η (g' i) * Jac i l = 0`. Conclude with `e1.symm`. Establish `hv0` using `Matrix.eq_zero_of_vecMul_eq_zero hdet hv`. Establish `hCq : C b ∈ q ^ 2`. Rewrite using `[← hsk]`.

Use `Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk` and prove the remaining obligations. Rewrite using `[pow_two]`. Use `Ideal.mul_mem_mul ?_ (hkerq ?_)` and prove the remaining obligations. Rewrite using `[hqmem]`. Conclude with `congrFun hv0 i`.

Rewrite using `[RingHom.mem_ker]`. Conclude with `hf i`. Set `ev : MvPolynomial σ B →ₐ[B] B` to `aeval (fun j => algebraMap O B (ε (x j)))`. Establish `hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `[ev, η, hΨ]`. Introduce `i`. Simplify using `[ev, η, hΨ, ← IsScalarTower.algebraMap_apply]`. Establish `hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A)`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `F hF`. Rewrite `hF` using `[hqmem]`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]`. Both sides reduce to the same expression.

Establish `: b = ev (C b)` using `by simp [ev]`. Rewrite using `[this]`. Conclude with `Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)`.
-/
theorem cotangent_map_injective_of_square_presentation : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  intro O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb
  classical
  set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ
  let η : MvPolynomial σ B →+* O := (ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  set q := (RingHom.ker ε).comap Ψ with hq
  have hqmem : ∀ F, F ∈ q ↔ η F = 0 := fun F => by
    rw [hq, Ideal.mem_comap, RingHom.mem_ker, hη]
  have hkerq : RingHom.ker Ψ ≤ q := fun F hF => by
    rw [hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]
  have hηf : ∀ i, η (f i) = 0 := fun i => by rw [hη, hf i, map_zero]
  set K := firstOrderKer η with hK
  have hq2 : q ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b' hb' => ?_
    rw [hqmem] at ha hb'
    exact ⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩
  have hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine hker.trans (sup_le_sup_left ?_ _)
    rw [pow_two]; exact Ideal.mul_mono_right hkerq
  have hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K := hkerL.trans (sup_le_sup_left hq2 _)
  have hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ := by
    rw [Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]
  have lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L →
      ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L := by
    intro L hL F hF
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF
    have h1 : F - G ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, hGF, sub_self]
    have h2 : F = (F - G) + G := by ring
    rw [h2]; exact Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)
  have hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker] at hi
    rw [Ideal.mem_comap]
    have : algebraMap B A i = Ψ (C i) := by simp [hΨ]
    rw [this]
    refine Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩
    rw [hη]; simpa [hΨ] using hi
  let Jac : Matrix σ σ O := fun i l => η (pderiv l (f i))
  have hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l,
      (if j = l then c else 0) = ∑ i, η (g i) * Jac i l := by
    intro j
    set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF
    have ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker]; simp
    have hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j))) := by
      simp [hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hmem : Ψ F ∈ K.map Ψ := by
      rw [hΨF]
      refine (sup_le ?_ hIB) (hc2 _ ha)
      rw [hsq]; exact Ideal.map_mono hq2
    have hF2 := lift K hkerK F hmem
    rw [Submodule.mem_sup] at hF2
    obtain ⟨s, hs, k, hk, hsk⟩ := hF2
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine ⟨g, fun l => ?_⟩
    have e1 := pderiv_comb η f g hηf k hk l
    rw [hsk] at e1
    rw [← e1, hF]
    by_cases hjl : j = l
    · subst hjl
      simp [pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]
    · simp [hjl, pderiv_X_of_ne (Ne.symm hjl)]
  choose g hg using hrow
  let N : Matrix σ σ O := fun j i => η (g j i)
  have hNJ : N * Jac = c • (1 : Matrix σ σ O) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]
    split_ifs <;> simp
  have hdet : Jac.det ≠ 0 := det_ne_zero_of_mul_eq hc hNJ
  have hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine lift _ hkerL (C b) ?_
    rw [← hsq]; simpa [hΨ] using hb
  rw [Submodule.mem_sup] at hCb
  obtain ⟨s, hs, k, hk, hsk⟩ := hCb
  obtain ⟨g', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
  have hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0 := by
    funext l
    have e1 := pderiv_comb η f g' hηf k (hq2 hk) l
    rw [hsk] at e1
    simp only [pderiv_C, map_zero] at e1
    change ∑ i, η (g' i) * Jac i l = 0
    exact e1.symm
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hCq : C b ∈ q ^ 2 := by
    rw [← hsk]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hkerq ?_)
    · rw [hqmem]; exact congrFun hv0 i
    · rw [RingHom.mem_ker]; exact hf i
  let ev : MvPolynomial σ B →ₐ[B] B := aeval (fun j => algebraMap O B (ε (x j)))
  have hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ev, η, hΨ]
    · intro i; simp [ev, η, hΨ, ← IsScalarTower.algebraMap_apply]
  have hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [hqmem] at hF
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]
    rfl
  have : b = ev (C b) := by simp [ev]
  rw [this]
  exact Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)

end GlobalTheory.CotangentSquare
