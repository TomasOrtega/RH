import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

/- English proof (translation)
Unfold `kMinor`. Establish `e : A.submatrix (I ∘ σ) (Fin.castLE hk) = (A.submatrix I (Fin.castLE hk)).submatrix σ id`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.det_permute]`.
-/
theorem kMinor_comp_perm {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ)
    (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    kMinor A k hk (I ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : F) * kMinor A k hk I := by
  unfold kMinor
  have e : A.submatrix (I ∘ σ) (Fin.castLE hk) = (A.submatrix I (Fin.castLE hk)).submatrix σ id := by
    ext a b
    simp
  rw [e, Matrix.det_permute]

/- English proof (translation)
Take `⟨h0, h1⟩` from `h`. Use `⟨?_, fun J => ?_⟩` and prove the remaining obligations. Rewrite using `[kMinor_comp_perm]`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Simplify `h0` using `[hs]`.

Simplify `h0` using `[hs]`. Rewrite using `[kMinor_comp_perm]`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Simplify `h1 J` using `[hs]`. Simplify `O.neg_mem (h1 J)` using `[hs, div_neg]`.
-/
theorem normAt_comp_perm {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) (h : NormAt O Y k hk I) :
    NormAt O Y k hk (I ∘ σ) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, fun J => ?_⟩
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h0
    · simpa [hs] using h0
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h1 J
    · simpa [hs, div_neg] using O.neg_mem (h1 J)

/- English proof (translation)
Set `e : {x // x ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1))} ≃ {x // x ∈ Set.range f}` to `(Equiv.ofInjective _ (Fin.castSucc_injective k)).symm.trans (Equiv.ofInjective f hf)`. Use `⟨e.extendSubtype, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `e.extendSubtype_apply_of_mem a.castSucc ⟨a, rfl⟩`. Rewrite using `[h]`. Establish `h2 : (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm ⟨a.castSucc, ⟨a, rfl⟩⟩ = a` using `Equiv.ofInjective_symm_apply _ a`.

Simplify using `only [e, Equiv.trans_apply]`. Use `erw [h2]`. Both sides reduce to the same expression.
-/
theorem exists_perm_castSucc {k : ℕ} (f : Fin k → Fin (k + 1)) (hf : Function.Injective f) :
    ∃ g : Equiv.Perm (Fin (k + 1)), ∀ a : Fin k, g a.castSucc = f a := by
  classical
  let e : {x // x ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1))} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  have h := e.extendSubtype_apply_of_mem a.castSucc ⟨a, rfl⟩
  rw [h]
  have h2 : (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm
      ⟨a.castSucc, ⟨a, rfl⟩⟩ = a := Equiv.ofInjective_symm_apply _ a
  simp only [e, Equiv.trans_apply]
  erw [h2]
  rfl

def castEmb {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩

/- English proof (translation)
Use `⟨g.viaFintypeEmbedding (castEmb hm), fun a => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) < m`. Establish `e1 : Fin.castLE hj a = castEmb hmr ⟨a, ha⟩` using `by ext; simp [castEmb]`. Establish `e2 : a = castEmb hm ⟨a, ha⟩` using `by ext; simp [castEmb]`. Rewrite using `[e1, Equiv.Perm.viaFintypeEmbedding_apply_image]`.

Use `conv_rhs => rw [e2, Equiv.Perm.viaFintypeEmbedding_apply_image]`. Use `ext`. Simplify using `[castEmb]`. Establish `n1 : Fin.castLE hj a ∉ Set.range (castEmb hmr)`. Introduce and unpack `⟨b, hb⟩`.

Use `congrArg Fin.val hb` as an intermediate fact. Establish `hb2` using `b.2`. Simplify using `[castEmb] at this`. Use linear arithmetic over natural numbers and integers. Establish `n2 : a ∉ Set.range (castEmb hm)`.

Introduce and unpack `⟨b, hb⟩`. Use `congrArg Fin.val hb` as an intermediate fact. Establish `hb2` using `b.2`. Simplify using `[castEmb] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n1, Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n2]`.
-/
theorem exists_perm_restrict {m j r : ℕ} (hm : m ≤ j) (hj : j ≤ r) (hmr : m ≤ r)
    (g : Equiv.Perm (Fin m)) :
    ∃ σ : Equiv.Perm (Fin j), ∀ a : Fin j,
      g.viaFintypeEmbedding (castEmb hmr) (Fin.castLE hj a) = Fin.castLE hj (σ a) := by
  classical
  refine ⟨g.viaFintypeEmbedding (castEmb hm), fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have e1 : Fin.castLE hj a = castEmb hmr ⟨a, ha⟩ := by ext; simp [castEmb]
    have e2 : a = castEmb hm ⟨a, ha⟩ := by ext; simp [castEmb]
    rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image]
    conv_rhs => rw [e2, Equiv.Perm.viaFintypeEmbedding_apply_image]
    ext; simp [castEmb]
  · have n1 : Fin.castLE hj a ∉ Set.range (castEmb hmr) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    have n2 : a ∉ Set.range (castEmb hm) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n1,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n2]

/- English proof (translation)
Establish `hinj : Function.Injective I`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Use `h.1 ?_` and prove the remaining obligations. Unfold `kMinor`.

Use `Matrix.det_zero_of_row_eq hne ?_` and prove the remaining obligations. Use extensionality with `c`. Simplify using `[hab]`. Conclude with `⟨Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj), rfl⟩`.
-/
theorem exists_perm_top {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (I : Fin r → Fin r) (h : NormAt O Y r le_rfl I) : ∃ w : Equiv.Perm (Fin r), ⇑w = I := by
  have hinj : Function.Injective I := by
    intro a b hab
    by_contra hne
    refine h.1 ?_
    unfold kMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    ext c
    simp [hab]
  exact ⟨Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj), rfl⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_perm_castSucc f hf`. Use `⟨w * g.viaFintypeEmbedding (castEmb hk), fun j hj hkj => ?_⟩` and prove the remaining obligations. Break down `Nat.eq_or_lt_of_le hkj with rfl | hlt` into its components or cases. Establish `e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) = (w ∘ Fin.castLE hk) ∘ f`. Use function extensionality and compare the values at `a`.

Establish `e1 : Fin.castLE hj a = castEmb hk a.castSucc` using `by ext; simp [castEmb]`. Simplify using `only [Function.comp_apply, Equiv.Perm.mul_apply]`. Rewrite using `[e1, Equiv.Perm.viaFintypeEmbedding_apply_image, hg]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hn`. Take `⟨σ, hσ⟩` from `exists_perm_restrict (m := k + 1) (j := j) hlt hj hk g`. Establish `e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) = (w ∘ Fin.castLE hj) ∘ σ`. Use function extensionality and compare the values at `a`. Simplify using `only [Function.comp_apply, Equiv.Perm.mul_apply]`.

Rewrite using `[hσ]`. Rewrite using `[e]`. Conclude with `normAt_comp_perm O Y j hj _ σ (hw j hj hlt)`.
-/
theorem perm_step {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F) (k : ℕ)
    (hk : k + 1 ≤ r) (w : Equiv.Perm (Fin r)) (f : Fin k → Fin (k + 1)) (hf : Function.Injective f)
    (hw : ∀ (j : ℕ) (hj : j ≤ r), k + 1 ≤ j → NormAt O Y j hj (w ∘ Fin.castLE hj))
    (hn : NormAt O Y k (Nat.le_of_succ_le hk) ((w ∘ Fin.castLE hk) ∘ f)) :
    ∃ w' : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), k ≤ j → NormAt O Y j hj (w' ∘ Fin.castLE hj) := by
  classical
  obtain ⟨g, hg⟩ := exists_perm_castSucc f hf
  refine ⟨w * g.viaFintypeEmbedding (castEmb hk), fun j hj hkj => ?_⟩
  rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
  · have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hk) ∘ f := by
      funext a
      have e1 : Fin.castLE hj a = castEmb hk a.castSucc := by ext; simp [castEmb]
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image, hg]
      rfl
    rw [e]
    exact hn
  · obtain ⟨σ, hσ⟩ := exists_perm_restrict (m := k + 1) (j := j) hlt hj hk g
    have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hj) ∘ σ := by
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [hσ]
    rw [e]
    exact normAt_comp_perm O Y j hj _ σ (hw j hj hlt)

/- English proof (translation)
Establish `key : ∀ d : ℕ, d ≤ r → ∃ w : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), r - d ≤ j → NormAt O Y j hj (w ∘ Fin.castLE hj)`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `_`.

Take `⟨I, hI⟩` from `hall r le_rfl`. Take `⟨w, hw⟩` from `exists_perm_top O Y I hI`. Use `⟨w, fun j hj hrj => ?_⟩` and prove the remaining obligations. Establish `hjr : j = r` using `le_antisymm hj (by simpa using hrj)`. Substitute `hjr` using the available equality.

Establish `e : (⇑w ∘ Fin.castLE hj) = I`. Use function extensionality and compare the values at `a`. Simplify using `[hw]`. Rewrite using `[e]`. Conclude with `hI`.

Consider the case `succ d ih`. Introduce `hd`. Take `⟨w, hw⟩` from `ih (by omega)`. Take `⟨k, hkd⟩ : ∃ k, k + 1 = r - d` from `⟨r - d - 1, by omega⟩`. Establish `hk : k + 1 ≤ r` using `by omega`.

Take `⟨I, hI⟩` from `hall k (Nat.le_of_succ_le hk)`. Take `⟨f, hf, hn⟩` from `hex k hk (w ∘ Fin.castLE hk) I (hw _ hk (by omega)) hI`. Take `⟨w', hw'⟩` from `perm_step O Y k hk w f hf (fun j hj h => hw j hj (by omega)) hn`. Conclude with `⟨w', fun j hj h => hw' j hj (by omega)⟩`. Take `⟨w, hw⟩` from `key r le_rfl`.

Conclude with `⟨w, fun k hk => hw k hk (by omega)⟩`.
-/
theorem exists_perm_normAt {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (hex : ∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r),
      NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I →
        ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧
          NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f))
    (hall : ∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  have key : ∀ d : ℕ, d ≤ r → ∃ w : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), r - d ≤ j →
      NormAt O Y j hj (w ∘ Fin.castLE hj) := by
    intro d
    induction d with
    | zero =>
      intro _
      obtain ⟨I, hI⟩ := hall r le_rfl
      obtain ⟨w, hw⟩ := exists_perm_top O Y I hI
      refine ⟨w, fun j hj hrj => ?_⟩
      have hjr : j = r := le_antisymm hj (by simpa using hrj)
      subst hjr
      have e : (⇑w ∘ Fin.castLE hj) = I := by
        funext a
        simp [hw]
      rw [e]
      exact hI
    | succ d ih =>
      intro hd
      obtain ⟨w, hw⟩ := ih (by omega)
      obtain ⟨k, hkd⟩ : ∃ k, k + 1 = r - d := ⟨r - d - 1, by omega⟩
      have hk : k + 1 ≤ r := by omega
      obtain ⟨I, hI⟩ := hall k (Nat.le_of_succ_le hk)
      obtain ⟨f, hf, hn⟩ := hex k hk (w ∘ Fin.castLE hk) I (hw _ hk (by omega)) hI
      obtain ⟨w', hw'⟩ := perm_step O Y k hk w f hf (fun j hj h => hw j hj (by omega)) hn
      exact ⟨w', fun j hj h => hw' j hj (by omega)⟩
  obtain ⟨w, hw⟩ := key r le_rfl
  exact ⟨w, fun k hk => hw k hk (by omega)⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
