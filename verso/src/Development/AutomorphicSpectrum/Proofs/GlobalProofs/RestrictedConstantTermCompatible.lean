import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n n' : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) {m m' : ℕ}

/- English proof (translation)
Use extensionality with `j`. Both sides reduce to the same expression.
-/
theorem mulVec_col {R : Type} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (i : Fin c) : A *ᵥ Bᵀ i = (A * B)ᵀ i := by
  ext j
  rfl

omit [NumberField E] in
variable {σ J} in

/- English proof (translation)
Use `⟨fun hy => by rwa [h y (hA hy)], fun hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `(inv_mem h) _ (hA hy)`. Rewrite `h1` using `[mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]`. Rewrite using `[h1]` and apply the resulting hypothesis.
-/
theorem mem_iff_of_ptStab {A A' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {g : GAd σ J}
    (h : g ∈ ptStab σ J A) (hA : A' ≤ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A' ↔ (matHom _ σ J g).1 *ᵥ y ∈ A' := by
  refine ⟨fun hy => by rwa [h y (hA hy)], fun hy => ?_⟩
  have h1 := (inv_mem h) _ (hA hy)
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at h1
  rwa [h1]

omit [NumberField E] in
variable {σ J J'} in

/- English proof (translation)
Establish `c0 : ∀ {a c d : ℕ} (U : Matrix (Fin a) (Fin c) E) (W : Matrix (Fin c) (Fin d) E), adMat F U * adMat F W = adMat F (U * W)` using `fun U W => (Matrix.map_mul ..).symm`. Establish `dM : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = adMat F I *ᵥ ((matHom _ σ J' b).1 *ᵥ (adMat F P *ᵥ y) - adMat F P *ᵥ y)` using `fun y => by`. Rewrite using `[hg, add_mulVec, one_mulVec, add_sub_cancel_left, ← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec]`. Establish `pe : ∀ i, adMat F P *ᵥ (adMat F X)ᵀ (e i) = (adMat F X')ᵀ i` using `fun i => by`. Rewrite using `[mulVec_col, c0]`.

Use `conv_rhs => rw [← hPX]`. Both sides reduce to the same expression. Establish `ie : ∀ i, adMat F I *ᵥ (adMat F X')ᵀ i = (adMat F X)ᵀ (e i)` using `fun i => by`. Rewrite using `[mulVec_col, c0, hIX]`. Both sides reduce to the same expression.

Establish `hz : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0` using `fun l hl => by`. Rewrite using `[mulVec_col, c0]`. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `inclR (F := F) (AF F) ((P * X) i l) = 0`. Rewrite using `[hPT l hl i, map_zero]`.

Establish `ip : ∀ (S : Set (Fin m')) y, y ∈ colSpan F X' S → adMat F I *ᵥ y ∈ colSpan F X (e '' S)` using `fun S y hy => by`. Use `(Submodule.span_le (p := (colSpan F X (e '' S)).comap (adMat F I).mulVecLin)).2 ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Express the relevant statement in the definitionally equal form `adMat F I *ᵥ _ ∈ colSpan F X (e '' S)`. Rewrite using `[ie]`.

Conclude with `Submodule.subset_span ⟨e i, ⟨i, hi, rfl⟩, rfl⟩`. Establish `e0 : {i | ∃ k' ∈ ({k} : Finset (Fin m')), i ≤ k'} = {i | i ≤ k}` using `by simp`. Establish `fixB : ∀ i ≤ k, (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ i = (adMat F X')ᵀ i` using `fun i hi => by`. Establish `h` using `(Subgroup.mem_iInf.1 hb.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)`. Establish `e3 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < i} = ∅`.

Use extensionality with `l`. Simplify using `using fun _ => hi`. Rewrite `h` using `[e3, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h`. Establish `spanB : ∀ j, k < j → (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ j - (adMat F X')ᵀ j ∈ colSpan F X' {i | i ≤ k}` using `fun j hj => by`.

Establish `h` using `(Subgroup.mem_iInf.1 hb.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)`. Establish `e2 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < j} = {i | i ≤ k}` using `by simp [hj]`. Rewrite `h` using `[e2]`. Then use the resulting hypothesis. Establish `perpB : ∀ w ∈ colPerp σ J' X' {i | i ≤ k}, (matHom _ σ J' b).1 *ᵥ w - w ∈ colSpan F X' {i | i ≤ k}` using `fun w hw => by`. Establish `h` using `hb.2.2 w (by rwa [e0])`.

Rewrite `h` using `[e0]`. Then use the resulting hypothesis. Set `A : Set (Fin m)` to `{i | ∃ k' ∈ insert (e k) T, i ≤ k'}`. Establish `hup : ∀ i, i ∈ upTo T → i ∈ A` using `fun i ⟨t, ht, hi⟩ => ⟨t, Finset.mem_insert_of_mem ht, hi⟩`. Establish `hA : ∀ i ∈ A, i ∈ upTo T ∨ ∃ i', i' ≤ k ∧ e i' = i` using `fun i ⟨t, ht, hi⟩ => by`. Break down `Finset.mem_insert.1 ht with rfl | ht` into its components or cases.

Distinguish the cases in `h : i ∈ upTo T`. Conclude with `Or.inl h`. Take `⟨i', rfl⟩` from `(hr i).1 h`. Conclude with `Or.inr ⟨i', he.le_iff_le.1 hi, rfl⟩`. Conclude with `Or.inl ⟨t, ht, hi⟩`.

Establish `fix : ∀ i ∈ A, (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i` using `fun i hi => by`. Rewrite using `[← sub_eq_zero, dM]`. Break down `hA i hi with h | ⟨i', h, rfl⟩` into its components or cases. Rewrite using `[hz i h, mulVec_zero, sub_zero, mulVec_zero]`. Rewrite using `[pe, fixB i' h, sub_self, mulVec_zero]`.

Establish `pt : g ∈ ptStab σ J (colSpan F X A)` using `fun y hy => by`. Use `(Submodule.span_le (p := LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id)).2 ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `fix i hi`. Establish `pp : ∀ y ∈ colPerp σ J X A, adMat F P *ᵥ y ∈ colPerp σ J' X' {i | i ≤ k}` using `fun y hy => by`.

Simplify using `only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢`. Introduce `i hi`. Establish `h1 : Formalism.UG.cT (σ : E →+* E) X' * J' * P = (Formalism.UG.cT (σ : E →+* E) X * J).submatrix e id`. Rewrite using `[Matrix.mul_assoc, ← hG, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hIX]`. Both sides reduce to the same expression.

Establish `h2` using `hy (e i) ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩`. Express the relevant statement in the definitionally equal form `(adMat F (Formalism.UG.cT (σ : E →+* E) X' * J') *ᵥ adMat F P *ᵥ y) i = 0`. Rewrite using `[mulVec_mulVec, c0, h1]`. Conclude with `h2`. Use `⟨Subgroup.mem_iInf.2 fun j => ⟨mem_iff_of_ptStab pt ?_, fun y hy => ?_⟩, mem_iff_of_ptStab pt le_rfl, fun y hy => ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.span_mono (Set.image_mono fun i ⟨k', h1, h2, _⟩ => ⟨k', h1, h2⟩)`. It suffices to establish `h : y ∈ (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap ((matHom _ σ J g).1 - 1).mulVecLin by`. Rewrite `h` using `[Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]`. Then use the resulting hypothesis. Use `(Submodule.span_le (p := (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap ((matHom _ σ J g).1 - 1).mulVecLin)).2 ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]`. Distinguish the cases in `hj : j ∈ A`. Rewrite using `[fix j hj, sub_self]`. Conclude with `zero_mem _`. Take `⟨j', rfl⟩` from `(hr j).1 fun h => hj (hup j h)`.

Establish `hk : k < j'` using `lt_of_not_ge fun h => hj ⟨e k, Finset.mem_insert_self _ _, he.monotone h⟩`. Rewrite using `[dM, pe]`. Use `Submodule.span_mono (Set.image_mono ?_) (ip _ _ (spanB j' hk))` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `⟨e k, Finset.mem_insert_self _ _, he.monotone hi, he hk⟩`.

Rewrite using `[dM]`. Use `Submodule.span_mono (Set.image_mono ?_) (ip _ _ (perpB _ (pp y hy)))` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩`.
-/
theorem mem_unip_of_mat {T : Finset (Fin m)} {X : Matrix (Fin n) (Fin m) E} {X' : Matrix (Fin n') (Fin m') E}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E} {e : Fin m' → Fin m}
    (he : StrictMono e) (hr : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPX : P * X.submatrix id e = X')
    (hPT : ∀ l ∈ upTo T, ∀ i, (P * X) i l = 0)
    (hG : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    {g : GAd σ J} {b : GAd σ J'}
    (hg : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    {k : Fin m'} (hb : b ∈ unip σ J' X' {k}) : g ∈ unip σ J X (insert (e k) T) := by
  classical
  have c0 : ∀ {a c d : ℕ} (U : Matrix (Fin a) (Fin c) E) (W : Matrix (Fin c) (Fin d) E),
      adMat F U * adMat F W = adMat F (U * W) := fun U W => (Matrix.map_mul ..).symm
  have dM : ∀ y, (matHom _ σ J g).1 *ᵥ y - y =
      adMat F I *ᵥ ((matHom _ σ J' b).1 *ᵥ (adMat F P *ᵥ y) - adMat F P *ᵥ y) := fun y => by
    rw [hg, add_mulVec, one_mulVec, add_sub_cancel_left, ← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  have pe : ∀ i, adMat F P *ᵥ (adMat F X)ᵀ (e i) = (adMat F X')ᵀ i := fun i => by
    rw [mulVec_col, c0]
    conv_rhs => rw [← hPX]
    rfl
  have ie : ∀ i, adMat F I *ᵥ (adMat F X')ᵀ i = (adMat F X)ᵀ (e i) := fun i => by
    rw [mulVec_col, c0, hIX]
    rfl
  have hz : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    rw [mulVec_col, c0]
    ext i
    change inclR (F := F) (AF F) ((P * X) i l) = 0
    rw [hPT l hl i, map_zero]
  have ip : ∀ (S : Set (Fin m')) y, y ∈ colSpan F X' S → adMat F I *ᵥ y ∈ colSpan F X (e '' S) := fun S y hy => by
    refine (Submodule.span_le (p := (colSpan F X (e '' S)).comap (adMat F I).mulVecLin)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    change adMat F I *ᵥ _ ∈ colSpan F X (e '' S)
    rw [ie]
    exact Submodule.subset_span ⟨e i, ⟨i, hi, rfl⟩, rfl⟩
  have e0 : {i | ∃ k' ∈ ({k} : Finset (Fin m')), i ≤ k'} = {i | i ≤ k} := by simp
  have fixB : ∀ i ≤ k, (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ i = (adMat F X')ᵀ i := fun i hi => by
    have h := (Subgroup.mem_iInf.1 hb.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have e3 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < i} = ∅ := by
      ext l
      simpa using fun _ => hi
    rw [e3, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have spanB : ∀ j, k < j → (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ j - (adMat F X')ᵀ j ∈ colSpan F X' {i | i ≤ k} :=
    fun j hj => by
      have h := (Subgroup.mem_iInf.1 hb.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
      have e2 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < j} = {i | i ≤ k} := by simp [hj]
      rwa [e2] at h
  have perpB : ∀ w ∈ colPerp σ J' X' {i | i ≤ k}, (matHom _ σ J' b).1 *ᵥ w - w ∈ colSpan F X' {i | i ≤ k} := fun w hw => by
    have h := hb.2.2 w (by rwa [e0])
    rwa [e0] at h
  let A : Set (Fin m) := {i | ∃ k' ∈ insert (e k) T, i ≤ k'}
  have hup : ∀ i, i ∈ upTo T → i ∈ A := fun i ⟨t, ht, hi⟩ => ⟨t, Finset.mem_insert_of_mem ht, hi⟩
  have hA : ∀ i ∈ A, i ∈ upTo T ∨ ∃ i', i' ≤ k ∧ e i' = i := fun i ⟨t, ht, hi⟩ => by
    rcases Finset.mem_insert.1 ht with rfl | ht
    · by_cases h : i ∈ upTo T
      · exact Or.inl h
      · obtain ⟨i', rfl⟩ := (hr i).1 h
        exact Or.inr ⟨i', he.le_iff_le.1 hi, rfl⟩
    · exact Or.inl ⟨t, ht, hi⟩
  have fix : ∀ i ∈ A, (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i := fun i hi => by
    rw [← sub_eq_zero, dM]
    rcases hA i hi with h | ⟨i', h, rfl⟩
    · rw [hz i h, mulVec_zero, sub_zero, mulVec_zero]
    · rw [pe, fixB i' h, sub_self, mulVec_zero]
  have pt : g ∈ ptStab σ J (colSpan F X A) := fun y hy => by
    refine (Submodule.span_le (p := LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact fix i hi
  have pp : ∀ y ∈ colPerp σ J X A, adMat F P *ᵥ y ∈ colPerp σ J' X' {i | i ≤ k} := fun y hy => by
    simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
    intro i hi
    have h1 : Formalism.UG.cT (σ : E →+* E) X' * J' * P = (Formalism.UG.cT (σ : E →+* E) X * J).submatrix e id := by
      rw [Matrix.mul_assoc, ← hG, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hIX]
      rfl
    have h2 := hy (e i) ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩
    change (adMat F (Formalism.UG.cT (σ : E →+* E) X' * J') *ᵥ adMat F P *ᵥ y) i = 0
    rw [mulVec_mulVec, c0, h1]
    exact h2
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨mem_iff_of_ptStab pt ?_, fun y hy => ?_⟩,
    mem_iff_of_ptStab pt le_rfl, fun y hy => ?_⟩
  · exact Submodule.span_mono (Set.image_mono fun i ⟨k', h1, h2, _⟩ => ⟨k', h1, h2⟩)
  · suffices h : y ∈ (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin by
      rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec] at h
    refine (Submodule.span_le (p := (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
      ((matHom _ σ J g).1 - 1).mulVecLin)).2 ?_ hy
    rintro _ ⟨j, rfl, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]
    by_cases hj : j ∈ A
    · rw [fix j hj, sub_self]
      exact zero_mem _
    · obtain ⟨j', rfl⟩ := (hr j).1 fun h => hj (hup j h)
      have hk : k < j' := lt_of_not_ge fun h => hj ⟨e k, Finset.mem_insert_self _ _, he.monotone h⟩
      rw [dM, pe]
      refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (spanB j' hk))
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi, he hk⟩
  · rw [dM]
    refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (perpB _ (pp y hy)))
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩

end Core

/- English proof (translation)
Introduce `D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb`. Take `⟨he, hr, hX, -⟩` from `hS`. Use `mem_unip_of_mat he hr hX ?_ ?_ cT_frameMat_mul_gram (mat_eq hι hs b) hb` and prove the remaining obligations. Rewrite using `[← hX, ← Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.one_mul]`. Introduce `l hl i`.

Establish `h` using `prM_mulVec_eq_zero (V' := V') (ι := ι) (x := fun j => X j l) fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1`. Conclude with `congrFun h i`.
-/
theorem unip_embed : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b ∈ unip D.sp.cm.sig V'.gram X' {k}, s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨he, hr, hX, -⟩ := hS
  refine mem_unip_of_mat he hr hX ?_ ?_ cT_frameMat_mul_gram (mat_eq hι hs b) hb
  · rw [← hX, ← Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.one_mul]
  · intro l hl i
    have h := prM_mulVec_eq_zero (V' := V') (ι := ι) (x := fun j => X j l) fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
    exact congrFun h i

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
