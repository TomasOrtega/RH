import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrameMemSG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondProjSplitMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedCore

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

section Reindex

variable {K : Type} [Field K] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {m : ℕ}

/- English proof (translation)
Establish `h : Submodule.span 𝕜 T ≤ (Submodule.span 𝕜 (f '' T)).comap (f : A →ₗ[𝕜] B)`. Rewrite using `[Submodule.span_le]`. Introduce `t ht`. Use `show f t ∈ Submodule.span 𝕜 (f '' T)`. Conclude with `Submodule.subset_span ⟨t, ht, rfl⟩`.

Conclude with `h hx`.
-/
private theorem linearEquiv_mem_span_image_of_mem_span {𝕜 A B : Type} [Field 𝕜] [AddCommGroup A] [Module 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B] (f : A ≃ₗ[𝕜] B) (T : Set A) (x : A)
    (hx : x ∈ Submodule.span 𝕜 T) : f x ∈ Submodule.span 𝕜 (f '' T) := by
  have h : Submodule.span 𝕜 T ≤ (Submodule.span 𝕜 (f '' T)).comap (f : A →ₗ[𝕜] B) := by
    rw [Submodule.span_le]
    intro t ht
    show f t ∈ Submodule.span 𝕜 (f '' T)
    exact Submodule.subset_span ⟨t, ht, rfl⟩
  exact h hx

/- English proof (translation)
Establish `hmv : ∀ w : n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm`. Introduce `w`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]`. Conclude with `Fintype.sum_equiv e.symm _ _ (fun _ => rfl)`.

Set `L : (n → K) ≃ₗ[K] (ι → K)` to `LinearEquiv.funCongrLeft K K e.symm`. Establish `hL : ∀ w : n → K, L w = w ∘ e.symm` using `fun _ => rfl`. Unfold `FlagC`. Apply `forall_congr'` to reduce the goal to its premises. Introduce `b`.

Use `show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈ Submodule.span K ((fun c => v c ∘ e.symm) '' {a | a < b}) ↔ M *ᵥ v b - v b ∈ Submodule.span K (v '' {a | a < b})`. Establish `himg : (fun c => v c ∘ e.symm) '' {a | a < b} = L '' (v '' {a | a < b})`. Rewrite using `[Set.image_image]`. Apply the tactic sequence `try rfl`. Establish `hw : Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm = L (M *ᵥ v b - v b)`.

Rewrite using `[hmv, map_sub, hL, hL]`. Rewrite using `[himg, hw]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `linearEquiv_mem_span_image_of_mem_span L.symm _ _ h`.

Use `first`. Consider the case `rwa [LinearEquiv.symm_apply_apply, LinearEquiv.symm_image_image] at h2`. Consider the case `simpa [Set.image_image] using h2`. Conclude with `linearEquiv_mem_span_image_of_mem_span L _ _`.
-/
theorem flagC_reindex (e : n ≃ ι) (M : Matrix n n K) (v : Fin m → n → K) :
    FlagC (Matrix.reindex e e M) (fun b => v b ∘ e.symm) ↔ FlagC M v := by
  have hmv : ∀ w : n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm := by
    intro w
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  let L : (n → K) ≃ₗ[K] (ι → K) := LinearEquiv.funCongrLeft K K e.symm
  have hL : ∀ w : n → K, L w = w ∘ e.symm := fun _ => rfl
  unfold FlagC
  apply forall_congr'
  intro b
  show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈
      Submodule.span K ((fun c => v c ∘ e.symm) '' {a | a < b}) ↔
      M *ᵥ v b - v b ∈ Submodule.span K (v '' {a | a < b})
  have himg : (fun c => v c ∘ e.symm) '' {a | a < b} = L '' (v '' {a | a < b}) := by
    rw [Set.image_image]
    try rfl
  have hw : Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm = L (M *ᵥ v b - v b) := by
    rw [hmv, map_sub, hL, hL]
  rw [himg, hw]
  constructor
  · intro h
    have h2 := linearEquiv_mem_span_image_of_mem_span L.symm _ _ h
    first
      | rwa [LinearEquiv.symm_apply_apply, LinearEquiv.symm_image_image] at h2
      | simpa [Set.image_image] using h2
  · exact linearEquiv_mem_span_image_of_mem_span L _ _

end Reindex

section Split

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

def cmp1 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).1)

def cmp2 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).2)

def jm1 : Matrix (Fin n) (Fin n) R := (JR R J).map (fun t => (θ t).1)

/- English proof (translation)
Establish `hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J` using `g.2`. Set `f1 : R ⊗[F] E →+* R` to `(RingHom.fst R R).comp θ.toRingEquiv.toRingHom`. Establish `h1` using `congrArg (fun M => Matrix.map M f1) hg`. Simplify using `only [Matrix.map_mul] at h1`. Establish `e1 : (Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map f1 = (cmp2 σ J θ g)ᵀ`.

Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]`. Use `show (θ (sigR R σ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i))).1 = (θ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i)).2`. Rewrite using `[hθ]`. Both sides reduce to the same expression.

Rewrite `h1` using `[e1]`. Conclude with `h1`.
-/
theorem cmp_unit (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) (g : HA R σ J) :
    (cmp2 σ J θ g)ᵀ * jm1 J θ * cmp1 σ J θ g = jm1 J θ := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J := g.2
  let f1 : R ⊗[F] E →+* R := (RingHom.fst R R).comp θ.toRingEquiv.toRingHom
  have h1 := congrArg (fun M => Matrix.map M f1) hg
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map f1 = (cmp2 σ J θ g)ᵀ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    show (θ (sigR R σ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i))).1 = (θ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i)).2
    rw [hθ]
    rfl
  rw [e1] at h1
  exact h1

/- English proof (translation)
Establish `h1 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr1 θ (c • v) = (θ c).1 • pr1 θ v`. Introduce `c v`. Use function extensionality and compare the values at `i`. Use `show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1`. Rewrite using `[map_mul]`.

Both sides reduce to the same expression. Establish `h2 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr2 θ (c • v) = (θ c).2 • pr2 θ v`. Introduce `c v`. Use function extensionality and compare the values at `i`. Use `show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2`.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hinj : ∀ x y : Fin n → R ⊗[F] E, pr1 θ x = pr1 θ y → pr2 θ x = pr2 θ y → x = y`. Introduce `x y hx hy`. Use function extensionality and compare the values at `i`.

Apply `θ.injective` to reduce the goal to its premises. Conclude with `Prod.ext (congrFun hx i) (congrFun hy i)`. Simplify using `only [Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`.

Use `⟨⟨fun i => (θ (c i)).1, ?_⟩, ⟨fun i => (θ (c i)).2, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [h1]`. Rewrite using `[map_sum]`. Simplify using `only [h2]`.

Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`. Use `⟨fun i => θ.symm (a i, b i), ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_sum]`. Simplify using `only [h1, AlgEquiv.apply_symm_apply]`.

Conclude with `ha`. Rewrite using `[map_sum]`. Simplify using `only [h2, AlgEquiv.apply_symm_apply]`. Conclude with `hb`.
-/
private theorem mem_span_image_iff_pr1_pr2_mem_span {ι : Type} [Fintype ι] (s : Set ι) (u : ι → Fin n → R ⊗[F] E)
    (w : Fin n → R ⊗[F] E) :
    w ∈ Submodule.span (R ⊗[F] E) (u '' s) ↔
      pr1 θ w ∈ Submodule.span R ((fun i => pr1 θ (u i)) '' s) ∧
      pr2 θ w ∈ Submodule.span R ((fun i => pr2 θ (u i)) '' s) := by
  classical
  have h1 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  have h2 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
    rw [map_mul]
    rfl
  have hinj : ∀ x y : Fin n → R ⊗[F] E, pr1 θ x = pr1 θ y → pr2 θ x = pr2 θ y → x = y := by
    intro x y hx hy
    funext i
    apply θ.injective
    exact Prod.ext (congrFun hx i) (congrFun hy i)
  simp only [Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun i => (θ (c i)).1, ?_⟩, ⟨fun i => (θ (c i)).2, ?_⟩⟩
    · rw [map_sum]
      simp only [h1]
    · rw [map_sum]
      simp only [h2]
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨fun i => θ.symm (a i, b i), ?_⟩
    apply hinj
    · rw [map_sum]
      simp only [h1, AlgEquiv.apply_symm_apply]
      exact ha
    · rw [map_sum]
      simp only [h2, AlgEquiv.apply_symm_apply]
      exact hb

/- English proof (translation)
Establish `hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr1 θ w k = (θ (w k)).1` using `fun _ _ => rfl`. Use function extensionality and compare the values at `i`. Simplify using `only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp1, Matrix.map_apply, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]`.
-/
private theorem pr1_lin_eq_cmp1_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr1 θ (lin R σ J g v) = cmp1 σ J θ g *ᵥ pr1 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr1 θ w k = (θ (w k)).1 := fun _ _ => rfl
  funext i
  simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp1, Matrix.map_apply,
    map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]

/- English proof (translation)
Establish `hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr2 θ w k = (θ (w k)).2` using `fun _ _ => rfl`. Use function extensionality and compare the values at `i`. Simplify using `only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp2, Matrix.map_apply, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]`.
-/
private theorem pr2_lin_eq_cmp2_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr2 θ (lin R σ J g v) = cmp2 σ J θ g *ᵥ pr2 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr2 θ w k = (θ (w k)).2 := fun _ _ => rfl
  funext i
  simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp2, Matrix.map_apply,
    map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]

/- English proof (translation)
Establish `hm : g ∈ Ssub R σ J P ↔ UniC R σ J (F0 P) g` using `Iff.rfl`. Rewrite using `[hm]`. Unfold `UniC FlagC`. Rewrite using `[← forall_and]`. Apply `forall_congr'` to reduce the goal to its premises.

Introduce `b`. Use `show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ spanR (F := F) R (F0 P) {a | a < b} ↔ (cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (F0 P b)) - pr1 θ (ratV (F := F) R (F0 P b)) ∈ Submodule.span R ((fun c => pr1 θ (ratV (F := F) R (F0 P c))) '' {a | a < b})) ∧ ( …`. Unfold `spanR`. Rewrite using `[mem_span_image_iff_pr1_pr2_mem_span, map_sub, map_sub, pr1_lin_eq_cmp1_mulVec, pr2_lin_eq_cmp2_mulVec]`.
-/
theorem mem_Ssub_iff_flagC {r : ℕ} (P : Frame E n r) (g : HA R σ J) :
    g ∈ Ssub R σ J P ↔ FlagC (cmp1 σ J θ g) (fun b => pr1 θ (ratV (F := F) R (F0 P b))) ∧
      FlagC (cmp2 σ J θ g) (fun b => pr2 θ (ratV (F := F) R (F0 P b))) := by
  have hm : g ∈ Ssub R σ J P ↔ UniC R σ J (F0 P) g := Iff.rfl
  rw [hm]
  unfold UniC FlagC
  rw [← forall_and]
  apply forall_congr'
  intro b
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ spanR (F := F) R (F0 P) {a | a < b} ↔
    (cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (F0 P b)) - pr1 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr1 θ (ratV (F := F) R (F0 P c))) '' {a | a < b})) ∧
    (cmp2 σ J θ g *ᵥ pr2 θ (ratV (F := F) R (F0 P b)) - pr2 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr2 θ (ratV (F := F) R (F0 P c))) '' {a | a < b}))
  unfold spanR
  rw [mem_span_image_iff_pr1_pr2_mem_span, map_sub, map_sub, pr1_lin_eq_cmp1_mulVec, pr2_lin_eq_cmp2_mulVec]

end Split

end MassDataIdxStIm
