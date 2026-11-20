import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory Matrix
open scoped ComplexConjugate NumberField.LiesOver

namespace UpperTheory.ConvolutionTheory.L1

section co
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/- English proof (translation)
The claim follows from `IsTotallyComplex.isComplex w`.
-/
private theorem cpx (w : InfinitePlace K) : IsComplex w := IsTotallyComplex.isComplex w

open Classical in

private def co (τ : K →+* ℂ) : mixedSpace K →+* ℂ :=
  if (mk τ).embedding = τ then complexComp ⟨mk τ, cpx _⟩
  else (starRingEnd ℂ).comp (complexComp ⟨mk τ, cpx _⟩)

/- English proof (translation)
Distinguish the cases in `h : (mk τ).embedding = τ`. Use `left`. Introduce `a`. Simplify using `[co, h]`. Use `right`.

Introduce `a`. Simplify using `[co, h]`.
-/
private theorem co_cases (τ : K →+* ℂ) :
    (∀ a, co τ a = a.2 ⟨mk τ, cpx _⟩) ∨ (∀ a, co τ a = conj (a.2 ⟨mk τ, cpx _⟩)) := by
  by_cases h : (mk τ).embedding = τ
  · left; intro a; simp [co, h]
  · right; intro a; simp [co, h]

/- English proof (translation)
Distinguish the cases in `h : (mk τ).embedding = τ`. Simplify using `[co, h, along]`. Simplify using `[co, h, along]`.
-/
private theorem co_along (τ : K →+* ℂ) (z : ℂ) : co τ (along τ z) = z := by
  by_cases h : (mk τ).embedding = τ
  · simp [co, h, along]
  · simp [co, h, along]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[along]`. Use function extensionality and compare the values at `⟨w, hw⟩`. Distinguish the cases in `h : w = mk τ`. Substitute `h` using the available equality.

Distinguish the cases in `h : (mk τ).embedding = τ`. Simplify using `[co, h, along]`. Simplify using `[co, h, along]`. Simplify using `[along, h]`.
-/
private theorem along_mul (τ : K →+* ℂ) (a : mixedSpace K) : along τ 1 * a = along τ (co τ a) := by
  refine Prod.ext ?_ ?_
  · simp [along]
  · funext ⟨w, hw⟩
    by_cases h : w = mk τ
    · subst h
      by_cases h : (mk τ).embedding = τ
      · simp [co, h, along]
      · simp [co, h, along]
    · simp [along, h]

/- English proof (translation)
Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `⟨w, hw⟩`. Simplify using `[along]`.
-/
private theorem along_zero (τ : K →+* ℂ) : along τ 0 = 0 := by
  refine Prod.ext rfl ?_
  funext ⟨w, hw⟩
  simp [along]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `ha` to reduce the goal to its premises. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `⟨w, hw⟩`.

Conclude with `absurd hw (not_isReal_iff_isComplex.2 (cpx w))`. Use function extensionality and compare the values at `⟨w, hw⟩`. Establish `h` using `hc w.embedding`. Establish `hm : mk w.embedding = w` using `mk_embedding w`. Break down `co_cases w.embedding with h1 | h1` into its components or cases.

Rewrite `h` using `[h1]`. Simplify `h` using `[hm]`. Rewrite `h` using `[h1]`. Simplify `h` using `[hm]`.
-/
private theorem ne_zero_co {a : mixedSpace K} (ha : a ≠ 0) : ∃ τ : K →+* ℂ, co τ a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply ha
  refine Prod.ext ?_ ?_
  · funext ⟨w, hw⟩
    exact absurd hw (not_isReal_iff_isComplex.2 (cpx w))
  · funext ⟨w, hw⟩
    have h := hc w.embedding
    have hm : mk w.embedding = w := mk_embedding w
    rcases co_cases w.embedding with h1 | h1
    · rw [h1] at h
      simpa [hm] using h
    · rw [h1] at h
      simpa [hm] using h

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Apply the tactic sequence `rcases co_cases τ with h1 | h1 <;> simp [h1, along, hc]`.
-/
private theorem mk_eq_of_co_along {τ τ₀ : K →+* ℂ} {z : ℂ} (h : co τ (along τ₀ z) ≠ 0) : mk τ = mk τ₀ := by
  by_contra hc
  apply h
  rcases co_cases τ with h1 | h1 <;> simp [h1, along, hc]

open Classical in

private def cc (w : InfinitePlace K) (τ : K →+* ℂ) : w.Completion →+* ℂ :=
  if w.embedding = τ then Completion.extensionEmbedding w
  else (starRingEnd ℂ).comp (Completion.extensionEmbedding w)

/- English proof (translation)
Establish `h0 : Continuous (Completion.extensionEmbedding w)` using `(Completion.isometry_extensionEmbedding w).continuous`. Distinguish the cases in `h : w.embedding = τ`. Simplify `h0` using `[cc, h]`. Simplify `Complex.continuous_conj.comp h0` using `[cc, h]`.
-/
private theorem continuous_cc (w : InfinitePlace K) (τ : K →+* ℂ) : Continuous (cc w τ) := by
  have h0 : Continuous (Completion.extensionEmbedding w) := (Completion.isometry_extensionEmbedding w).continuous
  by_cases h : w.embedding = τ
  · simpa [cc, h] using h0
  · simpa [cc, h] using Complex.continuous_conj.comp h0

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : Completion.extensionEmbedding (mk τ) (algebraMap K _ x) = (mk τ).embedding x`. Rewrite using `[Completion.algebraMap_apply]`. Conclude with `Completion.extensionEmbedding_coe _ _`. Distinguish the cases in `h1 : (mk τ).embedding = τ`.

Rewrite using `[cc, if_pos h1, e, h1]`. Establish `h` using `(embedding_mk_eq τ).resolve_left h1`. Rewrite using `[cc, if_neg h1, RingHom.comp_apply, e, h]`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
private theorem cc_alg (τ : K →+* ℂ) (w : InfinitePlace K) (h : mk τ = w) (x : K) :
    cc w τ (algebraMap K w.Completion x) = τ x := by
  subst h
  have e : Completion.extensionEmbedding (mk τ) (algebraMap K _ x) = (mk τ).embedding x := by
    rw [Completion.algebraMap_apply]
    exact Completion.extensionEmbedding_coe _ _
  by_cases h1 : (mk τ).embedding = τ
  · rw [cc, if_pos h1, e, h1]
  · have h := (embedding_mk_eq τ).resolve_left h1
    rw [cc, if_neg h1, RingHom.comp_apply, e, h]
    simp [ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Distinguish the cases in `h : (mk τ).embedding = τ`. Simplify using `[co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]`. Simplify using `[co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]`.
-/
private theorem co_psi (τ : K →+* ℂ) (y : InfiniteAdeleRing K) :
    co τ (InfiniteAdeleRing.ringEquiv_mixedSpace K y) = cc (mk τ) τ (y (mk τ)) := by
  by_cases h : (mk τ).embedding = τ
  · simp [co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]
  · simp [co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]

/- English proof (translation)
Establish `hd : DenseRange (algebraMap K w.Completion)`. Use `Dense.mono ?_ (Completion.denseRange_coe w)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨WithAbs.equiv _ x, Completion.algebraMap_apply _ _⟩`. Conclude with `DFunLike.coe_injective (hd.equalizer hf hg (funext h))`.
-/
private theorem cc_unique (w : InfinitePlace K) (f g : w.Completion →+* ℂ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K _ x) = g (algebraMap K _ x)) : f = g := by
  have hd : DenseRange (algebraMap K w.Completion) := by
    refine Dense.mono ?_ (Completion.denseRange_coe w)
    rintro _ ⟨x, rfl⟩
    exact ⟨WithAbs.equiv _ x, Completion.algebraMap_apply _ _⟩
  exact DFunLike.coe_injective (hd.equalizer hf hg (funext h))

/- English proof (translation)
Rewrite `h`, the goal using `[mem_unitaryGroup_iff]`. Establish `h2` using `congrArg (RingHom.mapMatrix (starRingEnd ℂ)) h`. Rewrite `h2` using `[map_mul, map_one]`. Establish `e : star (M.map (starRingEnd ℂ)) = RingHom.mapMatrix (starRingEnd ℂ) (star M)`. Use extensionality with `i j`.

Simplify using `[Matrix.star_apply]`. Rewrite using `[e]`. Conclude with `h2`.
-/
private theorem conj_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M ∈ unitaryGroup (Fin n) ℂ) :
    M.map (starRingEnd ℂ) ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at h ⊢
  have h2 := congrArg (RingHom.mapMatrix (starRingEnd ℂ)) h
  rw [map_mul, map_one] at h2
  have e : star (M.map (starRingEnd ℂ)) = RingHom.mapMatrix (starRingEnd ℂ) (star M) := by
    ext i j
    simp [Matrix.star_apply]
  rw [e]
  exact h2

/- English proof (translation)
Break down `co_cases τ with h1 | h1` into its components or cases. Establish `e : M.map (co τ) = M.map (complexComp ⟨mk τ, cpx _⟩)` using `by ext i j; simp [h1]`. Rewrite using `[e]`. Establish `e : M.map (co τ) = (M.map (complexComp ⟨mk τ, cpx _⟩)).map (starRingEnd ℂ)` using `by ext i j; simp [h1]`. Establish `e2 : M.map (complexComp ⟨mk τ, cpx _⟩) = (M.map (co τ)).map (starRingEnd ℂ)` using `by ext i j; simp [h1]`.

Conclude with `⟨fun h => e2 ▸ conj_unitary h, fun h => e ▸ conj_unitary h⟩`.
-/
private theorem co_unitary {n : ℕ} (τ : K →+* ℂ) (M : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    M.map (co τ) ∈ unitaryGroup (Fin n) ℂ ↔ M.map (complexComp ⟨mk τ, cpx _⟩) ∈ unitaryGroup (Fin n) ℂ := by
  rcases co_cases τ with h1 | h1
  · have e : M.map (co τ) = M.map (complexComp ⟨mk τ, cpx _⟩) := by ext i j; simp [h1]
    rw [e]
  · have e : M.map (co τ) = (M.map (complexComp ⟨mk τ, cpx _⟩)).map (starRingEnd ℂ) := by ext i j; simp [h1]
    have e2 : M.map (complexComp ⟨mk τ, cpx _⟩) = (M.map (co τ)).map (starRingEnd ℂ) := by ext i j; simp [h1]
    exact ⟨fun h => e2 ▸ conj_unitary h, fun h => e ▸ conj_unitary h⟩

/- English proof (translation)
Establish `e : (⟨mk τ, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = ⟨mk τ₀, cpx _⟩` using `Subtype.ext h`. Rewrite using `[co_unitary, co_unitary, e]`.
-/
private theorem co_unitary_of_mk {n : ℕ} {τ τ₀ : K →+* ℂ} (h : mk τ = mk τ₀) (M : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    M.map (co τ) ∈ unitaryGroup (Fin n) ℂ ↔ M.map (co τ₀) ∈ unitaryGroup (Fin n) ℂ := by
  have e : (⟨mk τ, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = ⟨mk τ₀, cpx _⟩ := Subtype.ext h
  rw [co_unitary, co_unitary, e]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx τ`. Rewrite using `[co_unitary]`. Conclude with `complexCompM_mem_unitaryGroup hx ⟨mk τ, cpx _⟩`. Introduce `h`.

Use `mem_archCompact_of_unitary x (fun v => absurd v.2 (not_isReal_iff_isComplex.2 (cpx _))) fun v => ?_` and prove the remaining obligations. Establish `h1` using `(co_unitary _ _).1 (h v.1.embedding)`. Establish `e : (⟨mk v.1.embedding, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = v` using `Subtype.ext (mk_embedding _)`. Rewrite `h1` using `[e]`. Conclude with `h1`.
-/
private theorem archC_iff {n : ℕ} (x : archGroup K n) :
    x ∈ archCompact K n ↔
      ∀ τ : K →+* ℂ, (mat ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n)).map (co τ) ∈ unitaryGroup (Fin n) ℂ := by
  constructor
  · intro hx τ
    rw [co_unitary]
    exact complexCompM_mem_unitaryGroup hx ⟨mk τ, cpx _⟩
  · intro h
    refine mem_archCompact_of_unitary x (fun v => absurd v.2 (not_isReal_iff_isComplex.2 (cpx _))) fun v => ?_
    have h1 := (co_unitary _ _).1 (h v.1.embedding)
    have e : (⟨mk v.1.embedding, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = v := Subtype.ext (mk_embedding _)
    rw [e] at h1
    exact h1

end co

section ext
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w => by rw [← not_isReal_iff_isComplex] intro h have h1 := isReal_iff.1 h have h2 := ComplexEmbedding.IsReal.comp (algebraMap F E) h1 exact not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (mk (w.embedding.comp (algebraMap F E)))) (isReal_mk_iff.2 h2)⟩`.
-/
private theorem totC (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] :
    IsTotallyComplex E := ⟨fun w => by
  rw [← not_isReal_iff_isComplex]
  intro h
  have h1 := isReal_iff.1 h
  have h2 := ComplexEmbedding.IsReal.comp (algebraMap F E) h1
  exact not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (mk (w.embedding.comp (algebraMap F E))))
    (isReal_mk_iff.2 h2)⟩

variable [IsTotallyComplex E]

/- English proof (translation)
Rewrite using `[co_psi, co_psi]`. Establish `key : ∀ (v : InfinitePlace F), mk (τ.comp (algebraMap F E)) = v → cc (mk (τ.comp (algebraMap F E))) (τ.comp (algebraMap F E)) (y (mk (τ.comp (algebraMap F E)))) = cc v (τ.comp (algebraMap F E)) (y v)`. Introduce and unpack `_ rfl`. Both sides reduce to the same expression. Establish `hv : mk (τ.comp (algebraMap F E)) = (mk τ).comap (algebraMap F E)` using `(comap_mk _ _).symm`.

Rewrite using `[key _ hv, GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply]`. Establish `hcont : Continuous (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion)` using `NumberField.LiesOver.continuous_completionMap (v := (mk τ).comap (algebraMap F E)) (w := mk τ)`. Establish `h : (cc (mk τ) τ).comp (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion) = cc ((mk τ).comap (algebraMap F E)) (τ.comp (algebraMap F E))`. Use `cc_unique _ _ _ ((continuous_cc _ _).comp hcont) (continuous_cc _ _) fun x => ?_` and prove the remaining obligations. Rewrite using `[cc_alg _ _ hv, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E, cc_alg _ _ rfl]`.

Both sides reduce to the same expression. Conclude with `congrArg (fun f => f (y ((mk τ).comap (algebraMap F E)))) h`.
-/
private theorem co_iota (τ : E →+* ℂ) (y : InfiniteAdeleRing F) :
    co τ (InfiniteAdeleRing.ringEquiv_mixedSpace E (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) y)) =
      co (τ.comp (algebraMap F E)) (InfiniteAdeleRing.ringEquiv_mixedSpace F y) := by
  rw [co_psi, co_psi]
  have key : ∀ (v : InfinitePlace F), mk (τ.comp (algebraMap F E)) = v →
      cc (mk (τ.comp (algebraMap F E))) (τ.comp (algebraMap F E)) (y (mk (τ.comp (algebraMap F E)))) =
        cc v (τ.comp (algebraMap F E)) (y v) := by
    rintro _ rfl
    rfl
  have hv : mk (τ.comp (algebraMap F E)) = (mk τ).comap (algebraMap F E) := (comap_mk _ _).symm
  rw [key _ hv, GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply]
  have hcont : Continuous (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion) :=
    NumberField.LiesOver.continuous_completionMap (v := (mk τ).comap (algebraMap F E)) (w := mk τ)
  have h : (cc (mk τ) τ).comp (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion) =
      cc ((mk τ).comap (algebraMap F E)) (τ.comp (algebraMap F E)) := by
    refine cc_unique _ _ _ ((continuous_cc _ _).comp hcont) (continuous_cc _ _) fun x => ?_
    rw [cc_alg _ _ hv, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply F E, cc_alg _ _ rfl]
    rfl
  exact congrArg (fun f => f (y ((mk τ).comap (algebraMap F E)))) h

end ext

section intersection_update_fsHerm_neg_one
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

private def P (τ : K →+* ℂ) (z : ℂ) : InfiniteAdeleRing K := (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (along τ z)

private def cq (τ : K →+* ℂ) : InfiniteAdeleRing K →+* ℂ :=
  (co τ).comp (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedSpace K)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cq_apply (τ : K →+* ℂ) (x : InfiniteAdeleRing K) :
    cq τ x = co τ (InfiniteAdeleRing.ringEquiv_mixedSpace K x) := rfl

/- English proof (translation)
Rewrite using `[cq_apply, P, RingEquiv.apply_symm_apply, co_along]`.
-/
private theorem cq_P (τ : K →+* ℂ) (z : ℂ) : cq τ (P τ z) = z := by
  rw [cq_apply, P, RingEquiv.apply_symm_apply, co_along]

/- English proof (translation)
Apply `(InfiniteAdeleRing.ringEquiv_mixedSpace K).injective` to reduce the goal to its premises. Rewrite using `[map_mul, P, P, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, along_mul, cq_apply]`.
-/
private theorem twoPow_mul_twoPow (τ : K →+* ℂ) (x : InfiniteAdeleRing K) : P τ 1 * x = P τ (cq τ x) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
  rw [map_mul, P, P, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, along_mul, cq_apply]

/- English proof (translation)
Rewrite using `[P, along_zero, map_zero]`.
-/
private theorem P_zero (τ : K →+* ℂ) : P τ 0 = 0 := by
  rw [P, along_zero, map_zero]

/- English proof (translation)
Introduce `h`. Use `cq_P τ 1` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`.
-/
private theorem P_one_ne (τ : K →+* ℂ) : P τ 1 ≠ 0 := by
  intro h
  have := cq_P τ 1
  rw [h, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Establish `hc : cq τ x * cq τ x = cq τ x` using `by rw [← map_mul, hi]`. Establish `e : x = P τ (cq τ x)` using `by rw [← twoPow_mul_twoPow, hx]`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 hc with h | h` into its components or cases. Rewrite `e` using `[h, P_zero]`. Conclude with `absurd e h0`.

Rewrite `e` using `[h]`. Then use the resulting hypothesis.
-/
private theorem idem_eq (τ : K →+* ℂ) {x : InfiniteAdeleRing K} (hx : P τ 1 * x = x) (hi : x * x = x) (h0 : x ≠ 0) :
    x = P τ 1 := by
  have hc : cq τ x * cq τ x = cq τ x := by rw [← map_mul, hi]
  have e : x = P τ (cq τ x) := by rw [← twoPow_mul_twoPow, hx]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hc with h | h
  · rw [h, P_zero] at e
    exact absurd e h0
  · rwa [h] at e

end intersection_update_fsHerm_neg_one

section main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
  [IsTotallyComplex E] {σ : E ≃ₐ[F] E} {m : ℕ}

/- English proof (translation)
The claim follows from `co_iota τ y`.
-/
private theorem cq_iota (τ : E →+* ℂ) (y : InfiniteAdeleRing F) :
    cq τ (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) y) = cq (τ.comp (algebraMap F E)) y :=
  co_iota τ y

/- English proof (translation)
Use `set τ' := τ.comp (algebraMap F E) with hτ'`. Use `set π : InfiniteAdeleRing E := P τ 1 with hπ`. Use `set πF : InfiniteAdeleRing F := P τ' 1 with hπF`. Establish `hidem : π * π = π` using `by rw [hπ, twoPow_mul_twoPow, cq_P]`. Establish `hidemF : πF * πF = πF` using `by rw [hπF, twoPow_mul_twoPow, cq_P]`.

Establish `h1 : π * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K` using `F) (L := E) πF = π := by`. Rewrite using `[hπ, twoPow_mul_twoPow, cq_iota, ← hτ', hπF, cq_P]`. Establish `h2 : ∀ i, πF * D.e π i = D.e π i`. Introduce `i`. Establish `h` using `congrFun (congrArg D.e h1) i`.

Rewrite `h` using `[map_mul, Pi.mul_apply, D.map_diag, mul_comm]`. Conclude with `h`. Establish `hne : D.e π ≠ 0` using `fun h => P_one_ne τ (D.e.injective (h.trans (map_zero _).symm))`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hne`. Establish `hidemk : D.e π k * D.e π k = D.e π k`.

Establish `h` using `congrFun (congrArg D.e hidem) k`. Rewrite `h` using `[map_mul, Pi.mul_apply]`. Then use the resulting hypothesis. Establish `hk1 : D.e π k = πF` using `idem_eq τ' (h2 k) hidemk hk`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hs : D.e.symm (Pi.single k πF) = π`.

Use `idem_eq τ ?_ ?_ ?_` and prove the remaining obligations. Apply `D.e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, RingEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`.

Substitute `hj` using the available equality. Establish `hk1' : D.e (P τ 1) j = πF` using `hk1`. Simplify using `[hk1', hidemF]`. Simplify using `[Pi.single_eq_of_ne hj]`. Apply `D.e.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, RingEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `[hidemF]`.

Simplify using `[Pi.single_eq_of_ne hj]`. Introduce `h`. Establish `h'` using `congrArg D.e h`. Rewrite `h'` using `[RingEquiv.apply_symm_apply, map_zero]`. Use `congrFun h' k` as an intermediate fact.

Simplify using `only [Pi.single_eq_same, Pi.zero_apply] at this`. Conclude with `P_one_ne τ' this`. Rewrite using `[← hs, RingEquiv.apply_symm_apply]`.
-/
private theorem exists_continuousLinearMap_tens_update (D : InfD σ m) (τ : E →+* ℂ) :
    ∃ k : Fin (m + 1), D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1) := by
  set τ' := τ.comp (algebraMap F E) with hτ'
  set π : InfiniteAdeleRing E := P τ 1 with hπ
  set πF : InfiniteAdeleRing F := P τ' 1 with hπF
  have hidem : π * π = π := by rw [hπ, twoPow_mul_twoPow, cq_P]
  have hidemF : πF * πF = πF := by rw [hπF, twoPow_mul_twoPow, cq_P]
  have h1 : π * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) πF = π := by
    rw [hπ, twoPow_mul_twoPow, cq_iota, ← hτ', hπF, cq_P]
  have h2 : ∀ i, πF * D.e π i = D.e π i := by
    intro i
    have h := congrFun (congrArg D.e h1) i
    rw [map_mul, Pi.mul_apply, D.map_diag, mul_comm] at h
    exact h
  have hne : D.e π ≠ 0 := fun h => P_one_ne τ (D.e.injective (h.trans (map_zero _).symm))
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  have hidemk : D.e π k * D.e π k = D.e π k := by
    have h := congrFun (congrArg D.e hidem) k
    rwa [map_mul, Pi.mul_apply] at h
  have hk1 : D.e π k = πF := idem_eq τ' (h2 k) hidemk hk
  refine ⟨k, ?_⟩
  have hs : D.e.symm (Pi.single k πF) = π := by
    refine idem_eq τ ?_ ?_ ?_
    · apply D.e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      funext j
      by_cases hj : j = k
      · subst hj
        have hk1' : D.e (P τ 1) j = πF := hk1
        simp [hk1', hidemF]
      · simp [Pi.single_eq_of_ne hj]
    · apply D.e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hidemF]
      · simp [Pi.single_eq_of_ne hj]
    · intro h
      have h' := congrArg D.e h
      rw [RingEquiv.apply_symm_apply, map_zero] at h'
      have := congrFun h' k
      simp only [Pi.single_eq_same, Pi.zero_apply] at this
      exact P_one_ne τ' this
  rw [← hs, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `h : P τ z = P τ 1 * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K` using `F) (L := E) (P (τ.comp (algebraMap F E)) z) := by`. Rewrite using `[twoPow_mul_twoPow, cq_iota, cq_P]`. Rewrite using `[h, map_mul, hk]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`.

Substitute `hj` using the available equality. Rewrite using `[Pi.mul_apply, D.map_diag, Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow, cq_P]`. Simplify using `[Pi.single_eq_of_ne hj]`.
-/
private theorem position_P (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1))
    (hk : D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1)) (z : ℂ) :
    D.e (P τ z) = Pi.single k (P (τ.comp (algebraMap F E)) z) := by
  have h : P τ z = P τ 1 * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (P (τ.comp (algebraMap F E)) z) := by
    rw [twoPow_mul_twoPow, cq_iota, cq_P]
  rw [h, map_mul, hk]
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Pi.mul_apply, D.map_diag, Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow, cq_P]
  · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Establish `h` using `congrFun (congrArg D.e (twoPow_mul_twoPow τ x)) k`. Rewrite `h` using `[map_mul, Pi.mul_apply, hk, position_P D τ k hk (cq τ x), Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow]`. Establish `h'` using `congrArg (cq (τ.comp (algebraMap F E))) h`. Rewrite `h'` using `[cq_P, cq_P]`. Then use the resulting hypothesis.
-/
private theorem position_cq (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1))
    (hk : D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1)) (x : InfiniteAdeleRing E) :
    cq (τ.comp (algebraMap F E)) (D.e x k) = cq τ x := by
  have h := congrFun (congrArg D.e (twoPow_mul_twoPow τ x)) k
  rw [map_mul, Pi.mul_apply, hk, position_P D τ k hk (cq τ x), Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow] at h
  have h' := congrArg (cq (τ.comp (algebraMap F E))) h
  rwa [cq_P, cq_P] at h'

/- English proof (translation)
Use `set e : InfiniteAdeleRing E := D.e.symm (Pi.single i (P τ₀ 1)) with he`. Establish `hDe : D.e e = Pi.single i (P τ₀ 1)` using `RingEquiv.apply_symm_apply _ _`. Establish `hne : InfiniteAdeleRing.ringEquiv_mixedSpace E e ≠ 0`. Introduce `h`. Establish `h0 : e = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace E).injective (h.trans (map_zero _).symm)`.

Rewrite `hDe` using `[h0, map_zero]`. Use `congrFun hDe i` as an intermediate fact. Simplify using `only [Pi.single_eq_same, Pi.zero_apply] at this`. Conclude with `P_one_ne τ₀ this.symm`. Take `⟨τ, hτ⟩` from `ne_zero_co hne`.

Take `⟨k, hk⟩` from `exists_continuousLinearMap_tens_update D τ`. Establish `h1` using `position_cq D τ k hk e`. Rewrite `h1` using `[hDe]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality.

Use `⟨τ, hk, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[Pi.single_eq_same]`. Use `mk_eq_of_co_along (z := 1) ?_` and prove the remaining obligations. Establish `h2 : co (τ.comp (algebraMap F E)) (along τ₀ 1) = cq (τ.comp (algebraMap F E)) (P τ₀ 1)`. Rewrite using `[cq_apply, P, RingEquiv.apply_symm_apply]`.

Rewrite using `[h2, h1]`. Conclude with `hτ`. Rewrite `h1` using `[Pi.single_eq_of_ne hki, map_zero]`. Conclude with `absurd h1.symm hτ`.
-/
private theorem exists_over (D : InfD σ m) (i : Fin (m + 1)) (τ₀ : F →+* ℂ) :
    ∃ τ : E →+* ℂ, D.e (P τ 1) = Pi.single i (P (τ.comp (algebraMap F E)) 1) ∧ mk (τ.comp (algebraMap F E)) = mk τ₀ := by
  set e : InfiniteAdeleRing E := D.e.symm (Pi.single i (P τ₀ 1)) with he
  have hDe : D.e e = Pi.single i (P τ₀ 1) := RingEquiv.apply_symm_apply _ _
  have hne : InfiniteAdeleRing.ringEquiv_mixedSpace E e ≠ 0 := by
    intro h
    have h0 : e = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective (h.trans (map_zero _).symm)
    rw [h0, map_zero] at hDe
    have := congrFun hDe i
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact P_one_ne τ₀ this.symm
  obtain ⟨τ, hτ⟩ := ne_zero_co hne
  obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
  have h1 := position_cq D τ k hk e
  rw [hDe] at h1
  by_cases hki : k = i
  · subst hki
    refine ⟨τ, hk, ?_⟩
    rw [Pi.single_eq_same] at h1
    refine mk_eq_of_co_along (z := 1) ?_
    have h2 : co (τ.comp (algebraMap F E)) (along τ₀ 1) = cq (τ.comp (algebraMap F E)) (P τ₀ 1) := by
      rw [cq_apply, P, RingEquiv.apply_symm_apply]
    rw [h2, h1]
    exact hτ
  · rw [Pi.single_eq_of_ne hki, map_zero] at h1
    exact absurd h1.symm hτ

end main

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ m D`. Use `haveI : IsTotallyComplex E := totC F E`. Apply the tactic sequence `have entry : ∀ (n : ℕ) (g : archGroup E n) (i : Fin (m + 1)) (τ : E →+* ℂ), D.e (P τ 1) = Pi.single i (P (τ.comp (algebraMap F E)) 1) → (mat (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n)).map (co (τ.comp (algebraMap F E))) = (mat ((g : (ArchMatrix E n)ˣ …`. Introduce `n g i τ hk`. Use extensionality with `a b`.

Establish `h` using `position_cq D τ i hk ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (mat ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) a b))`. Rewrite `h` using `[cq_apply, cq_apply, RingEquiv.apply_symm_apply]`. Conclude with `h`. Use `⟨fun τ => ?_, fun n g => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_continuousLinearMap_tens_update D τ`.

Use `⟨k, fun z => ?_⟩` and prove the remaining obligations. Establish `h` using `position_P D τ k hk z`. Conclude with `(D.e.symm_apply_apply (P τ z)).symm.trans (congrArg D.e.symm h)`. Rewrite using `[archC_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i`. Rewrite using `[archC_iff]`. Introduce `τ₀`. Take `⟨τ, hτ, hm⟩` from `exists_over D i τ₀`. Apply the tactic sequence `rw [← co_unitary_of_mk hm, entry n g i τ hτ]`.

Conclude with `h τ`. Introduce `h τ`. Take `⟨k, hk⟩` from `exists_continuousLinearMap_tens_update D τ`. Establish `h1` using `(archC_iff _).1 (h k) (τ.comp (algebraMap F E))`. Apply the tactic sequence `rwa [entry n g k τ hk] at h1`.
-/
theorem _root_.UpperTheory.ConvolutionTheory.L1.positionOf :
    UpperTheory.ConvolutionTheory.L1.PositionOf := by
  intro F E _ _ _ _ _ _ σ m D
  haveI : IsTotallyComplex E := totC F E
  have entry : ∀ (n : ℕ) (g : archGroup E n) (i : Fin (m + 1)) (τ : E →+* ℂ),
      D.e (P τ 1) = Pi.single i (P (τ.comp (algebraMap F E)) 1) →
      (mat (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n)).map (co (τ.comp (algebraMap F E))) =
        (mat ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)).map (co τ) := by
    intro n g i τ hk
    ext a b
    have h := position_cq D τ i hk ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (mat ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) a b))
    rw [cq_apply, cq_apply, RingEquiv.apply_symm_apply] at h
    exact h
  refine ⟨fun τ => ?_, fun n g => ?_⟩
  · obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
    refine ⟨k, fun z => ?_⟩
    have h := position_P D τ k hk z
    exact (D.e.symm_apply_apply (P τ z)).symm.trans (congrArg D.e.symm h)
  · rw [archC_iff]
    constructor
    · intro h i
      rw [archC_iff]
      intro τ₀
      obtain ⟨τ, hτ, hm⟩ := exists_over D i τ₀
      rw [← co_unitary_of_mk hm, entry n g i τ hτ]
      exact h τ
    · intro h τ
      obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
      have h1 := (archC_iff _).1 (h k) (τ.comp (algebraMap F E))
      rwa [entry n g k τ hk] at h1

end UpperTheory.ConvolutionTheory.L1
