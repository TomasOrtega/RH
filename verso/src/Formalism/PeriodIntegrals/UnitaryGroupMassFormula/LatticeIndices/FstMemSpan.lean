import Mathlib

noncomputable section

namespace MassDataIdxSpl

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}

def pr1 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).1
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

def pr2 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).2
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

def inj1 : (n → K) →ₗ[K] (n → T) where
  toFun w i := θ.symm (w i, 0)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    rw [← map_add]
    simp
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← map_smul]
    simp

def inj2 : (n → K) →ₗ[K] (n → T) where
  toFun w i := θ.symm (0, w i)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    rw [← map_add]
    simp
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← map_smul]
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_apply_alt (v : n → T) (i : n) : pr1 θ v i = (θ (v i)).1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_apply_alt (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show θ.symm ((θ (v i)).1, 0) + θ.symm (0, (θ (v i)).2) = v i`. Rewrite using `[← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AlgEquiv.symm_apply_apply]`.
-/
theorem inj_add (v : n → T) : inj1 θ (pr1 θ v) + inj2 θ (pr2 θ v) = v := by
  funext i
  show θ.symm ((θ (v i)).1, 0) + θ.symm (0, (θ (v i)).2) = v i
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AlgEquiv.symm_apply_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show θ.symm ((θ (v i)).1, 0) = θ.symm (1, 0) * v i`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Apply the tactic sequence `ext <;> simp`.
-/
theorem inl_fst_alt (v : n → T) : inj1 θ (pr1 θ v) = θ.symm (1, 0) • v := by
  funext i
  show θ.symm ((θ (v i)).1, 0) = θ.symm (1, 0) * v i
  apply θ.injective
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  ext <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show θ.symm (0, (θ (v i)).2) = θ.symm (0, 1) * v i`. Apply `θ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Apply the tactic sequence `ext <;> simp`.
-/
theorem inr_snd_alt (v : n → T) : inj2 θ (pr2 θ v) = θ.symm (0, 1) • v := by
  funext i
  show θ.symm (0, (θ (v i)).2) = θ.symm (0, 1) * v i
  apply θ.injective
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  ext <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1`. Rewrite using `[map_mul, Prod.fst_mul]`.
-/
theorem fst_smul_alt (c : T) (v : n → T) : pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
  funext i
  show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
  rw [map_mul, Prod.fst_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2`. Rewrite using `[map_mul, Prod.snd_mul]`.
-/
theorem snd_smul_alt (c : T) (v : n → T) : pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
  funext i
  show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
  rw [map_mul, Prod.snd_mul]

variable {ι : Type} (Y : ι → n → T) (s : Set ι)

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨a, ha, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [fst_smul_alt]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem fst_mem_span_alt {v : n → T} (hv : v ∈ Submodule.span T (Y '' s)) :
    pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [fst_smul_alt]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨a, ha, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [snd_smul_alt]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem snd_mem_span {v : n → T} (hv : v ∈ Submodule.span T (Y '' s)) :
    pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [snd_smul_alt]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Rewrite using `[inl_fst_alt]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_of_tower_mem _ c hx`.
-/
private theorem inl_mem_span_lemma {w : n → K} (hw : w ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s)) :
    inj1 θ w ∈ Submodule.span T (Y '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [inl_fst_alt]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hx

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Rewrite using `[inr_snd_alt]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_of_tower_mem _ c hx`.
-/
private theorem inr_mem_span_lemma_2 {w : n → K} (hw : w ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s)) :
    inj2 θ w ∈ Submodule.span T (Y '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [inr_snd_alt]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hx

/- English proof (translation)
Use `⟨fun hv => ⟨fst_mem_span_alt θ Y s hv, snd_mem_span θ Y s hv⟩, fun ⟨h1, h2⟩ => ?_⟩` and prove the remaining obligations. Rewrite using `[← inj_add θ v]`. Conclude with `Submodule.add_mem _ (inl_mem_span_lemma θ Y s h1) (inr_mem_span_lemma_2 θ Y s h2)`.
-/
theorem mem_span_iff (v : n → T) :
    v ∈ Submodule.span T (Y '' s) ↔ pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) ∧
      pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by
  refine ⟨fun hv => ⟨fst_mem_span_alt θ Y s hv, snd_mem_span θ Y s hv⟩, fun ⟨h1, h2⟩ => ?_⟩
  rw [← inj_add θ v]
  exact Submodule.add_mem _ (inl_mem_span_lemma θ Y s h1) (inr_mem_span_lemma_2 θ Y s h2)

end MassDataIdxSpl
