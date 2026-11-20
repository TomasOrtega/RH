import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.InvFormUnique

/- English proof (translation)
Set `f : W →ₗ[ℂ] H₂` to `j₂ ∘ₗ W.subtype`. Establish `hfi : Function.Injective f` using `hinj.comp Subtype.val_injective`. Set `e : W ≃ₗ[ℂ] LinearMap.range f` to `LinearEquiv.ofInjective f hfi`. Set `ψ : V →ₗ[ℂ] ℂ` to `(innerₛₗ ℂ (j₁ v)) ∘ₗ j₁ - (innerₛₗ ℂ (j₂ v)) ∘ₗ j₂`. Establish `hψ : ∀ x, ψ x = inner ℂ (j₁ v) (j₁ x) - inner ℂ (j₂ v) (j₂ x)` using `fun x => by`.

Simplify using `[ψ]`. Set `g : LinearMap.range f →ₗ[ℂ] ℂ` to `ψ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap`. Choose the witnesses or unpack the hypotheses as in `⟨u, huW, hrep⟩ : ∃ u ∈ W, ∀ z ∈ W, inner ℂ (j₂ u) (j₂ z) = ψ z := by`. Set `u'` to `(InnerProductSpace.toDual ℂ (LinearMap.range f)).symm (LinearMap.toContinuousLinearMap g)`. Establish `key : ∀ s : LinearMap.range f, inner ℂ (u' : H₂) (s : H₂) = g s`.

Introduce `s`. Rewrite using `[← Submodule.coe_inner]`. Conclude with `InnerProductSpace.toDual_symm_apply`. Use `⟨(e.symm u' : V), (e.symm u').2, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `key (e ⟨z, hz⟩)`.

Establish `h2 : ((e ⟨z, hz⟩ : LinearMap.range f) : H₂) = j₂ z` using `LinearEquiv.ofInjective_apply _ _`. Establish `h3 : ((u' : LinearMap.range f) : H₂) = j₂ (e.symm u' : V)` using `by conv_lhs => rw [← e.apply_symm_apply u']`. Conclude with `LinearEquiv.ofInjective_apply _ _`. Rewrite `h1` using `[h2, h3]`. Rewrite using `[h1]`.

Simplify using `[g]`. Establish `hker : ∀ i, A i u = 0`. Introduce `i`. Establish `horth : ∀ z ∈ W, inner ℂ (j₂ (A i u)) (j₂ z) = 0`. Introduce `z hz`.

Rewrite using `[h₂, hrep _ (hA' i z hz), hψ, ← h₁, ← h₂, hv]`. Simplify using the standard rewrite rules. Establish `h0` using `horth _ (hA i u huW)`. Rewrite `h0` using `[inner_self_eq_zero]`. Conclude with `hinj (by rw [h0, map_zero])`.

Take `⟨c, hc⟩` from `hline u hker`. Establish `hψv : ψ v = 0` using `by rw [hψ, hn, sub_self]`. Establish `hψu : ψ u = 0` using `by rw [← hc, map_smul, hψv, smul_zero]`. Establish `hj : j₂ u = 0`. Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), hrep u huW, hψu]`.

Establish `hy'` using `hrep y hy`. Rewrite `hy'` using `[hj, inner_zero_left, hψ]`. Conclude with `sub_eq_zero.mp hy'.symm`.
-/
theorem inner_eq_of_common_kernel_line {V H₁ H₂ ι : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : V →ₗ[ℂ] H₁) (j₂ : V →ₗ[ℂ] H₂) (A A' : ι → Module.End ℂ V) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hA : ∀ i, ∀ w ∈ W, A i w ∈ W) (hA' : ∀ i, ∀ w ∈ W, A' i w ∈ W)
    (h₁ : ∀ i x y, inner ℂ (j₁ (A i x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (A' i y)))
    (h₂ : ∀ i x y, inner ℂ (j₂ (A i x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (A' i y)))
    (hinj : Function.Injective j₂) (v : V) (hv : ∀ i, A i v = 0)
    (hline : ∀ h, (∀ i, A i h = 0) → ∃ c : ℂ, c • v = h)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (y : V) (hy : y ∈ W) :
    inner ℂ (j₁ v) (j₁ y) = inner ℂ (j₂ v) (j₂ y) := by
  classical

  let f : W →ₗ[ℂ] H₂ := j₂ ∘ₗ W.subtype
  have hfi : Function.Injective f := hinj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hfi
  let ψ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ (j₁ v)) ∘ₗ j₁ - (innerₛₗ ℂ (j₂ v)) ∘ₗ j₂
  have hψ : ∀ x, ψ x = inner ℂ (j₁ v) (j₁ x) - inner ℂ (j₂ v) (j₂ x) := fun x => by
    simp [ψ]
  let g : LinearMap.range f →ₗ[ℂ] ℂ := ψ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap

  obtain ⟨u, huW, hrep⟩ : ∃ u ∈ W, ∀ z ∈ W, inner ℂ (j₂ u) (j₂ z) = ψ z := by
    let u' := (InnerProductSpace.toDual ℂ (LinearMap.range f)).symm (LinearMap.toContinuousLinearMap g)
    have key : ∀ s : LinearMap.range f, inner ℂ (u' : H₂) (s : H₂) = g s := by
      intro s
      rw [← Submodule.coe_inner]
      exact InnerProductSpace.toDual_symm_apply
    refine ⟨(e.symm u' : V), (e.symm u').2, fun z hz => ?_⟩
    have h1 := key (e ⟨z, hz⟩)
    have h2 : ((e ⟨z, hz⟩ : LinearMap.range f) : H₂) = j₂ z := LinearEquiv.ofInjective_apply _ _
    have h3 : ((u' : LinearMap.range f) : H₂) = j₂ (e.symm u' : V) := by
      conv_lhs => rw [← e.apply_symm_apply u']
      exact LinearEquiv.ofInjective_apply _ _
    rw [h2, h3] at h1
    rw [h1]
    simp [g]

  have hker : ∀ i, A i u = 0 := by
    intro i
    have horth : ∀ z ∈ W, inner ℂ (j₂ (A i u)) (j₂ z) = 0 := by
      intro z hz
      rw [h₂, hrep _ (hA' i z hz), hψ, ← h₁, ← h₂, hv]
      simp
    have h0 := horth _ (hA i u huW)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])

  obtain ⟨c, hc⟩ := hline u hker
  have hψv : ψ v = 0 := by rw [hψ, hn, sub_self]
  have hψu : ψ u = 0 := by rw [← hc, map_smul, hψv, smul_zero]
  have hj : j₂ u = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hrep u huW, hψu]
  have hy' := hrep y hy
  rw [hj, inner_zero_left, hψ] at hy'
  exact sub_eq_zero.mp hy'.symm

/- English proof (translation)
Unfold `adjZ Eab Jm Formalism.UG.Jpq`. Establish `hJ : (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) : Mat p q) = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1))`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, apply_ite]`.

Rewrite using `[hJ]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Apply the tactic sequence `all_goals try exact (h : False).elim`. Use `all_goals`. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> simp_all`.
-/
theorem adjZ_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : adjZ (Eab a b) = Eab b a := by
  unfold adjZ Eab Jm Formalism.UG.Jpq

  have hJ : (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) : Mat p q) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, apply_ite]
  rw [hJ]
  rcases a with a | a <;> rcases b with b | b
  all_goals try exact (h : False).elim
  all_goals
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> simp_all

/- English proof (translation)
Unfold `IsKC Eab`. Introduce `c d hcd`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hcd h`.
-/
theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  unfold IsKC Eab
  intro c d hcd
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j`. Apply the tactic sequence `all_goals first`. Consider the case `exact ⟨True.intro, True.intro⟩`. Consider the case `exact (h : False).elim`.
-/
theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b ∧ sameBlock b a := by
  rcases a with i | i <;> rcases b with j | j
  all_goals first
    | exact ⟨True.intro, True.intro⟩
    | exact (h : False).elim

/- English proof (translation)
Apply the tactic sequence `cases a <;> exact True.intro`.
-/
theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> exact True.intro

/- English proof (translation)
Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
private theorem mem_hwSub_iff' {p q : ℕ} {V0 : Type} [AddCommGroup V0] [Module ℂ V0]
    (f : Mat p q →ₗ[ℂ] Module.End ℂ V0) (μ : Ix p q → ℚ) (z : V0) :
    z ∈ hwSub f μ ↔ (∀ a, f (Eab a a) z = (μ a : ℂ) • z) ∧ ∀ a b, posC a b → f (Eab a b) z = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/- English proof (translation)
Set `N : Submodule ℂ M.V` to `{ carrier := {z | ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_ofPred_eq] at ha hb ⊢`. Introduce `w`. Rewrite using `[map_add, map_add, inner_add_left, inner_add_left, ha, hb]`.

Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_ofPred_eq, map_zero, inner_zero_left, implies_true]`. Use the proof step `smul_mem' := by`. Introduce `c a ha`. Simplify using `only [Set.mem_ofPred_eq] at ha ⊢`.

Introduce `w`. Rewrite using `[map_smul, map_smul, inner_smul_left, inner_smul_left, ha] }`. Establish `hmemN : ∀ z, z ∈ N ↔ ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)` using `fun z => Iff.rfl`. Establish `hNinv : ∀ Z, ∀ z ∈ N, M.act Z z ∈ N`. Introduce `Z z hz`.

Rewrite `hz`, the goal using `[hmemN]`. Introduce `w`. Rewrite using `[h₁, h₂, hz]`. Take `⟨hv0, hvmem⟩ : v ≠ 0 ∧ v ∈ hwSub M.act μ` from `hv`. Establish `hmem` using `(mem_hwSub_iff' M.act μ v).mp hvmem`.

Set `A : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V` to `Sum.elim (fun ab => M.act (Eab ab.1.1 ab.1.2)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)`. Set `A' : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V` to `Sum.elim (fun ab => M.act (Eab ab.1.2 ab.1.1)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)`. Establish `hh : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M.V →ₗ[ℂ] H), (∀ Z z w, inner ℂ (j (M.act Z z)) (j w) = inner ℂ (j z) (j (M.act (adjZ Z) w))) → ∀ i z w, inner ℂ (j (A i z)) (j w) = inner ℂ (j z) (j (A' i w))`. Introduce `H _ _ j hj`. Introduce and unpack `(⟨⟨a, b⟩, hab⟩ | c) z w`.

Simplify using `only [A, A', Sum.elim_inl]`. Rewrite using `[hj, adjZ_Eab (sameBlock_of_posC hab).1]`. Simplify using `only [A, A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]`. Rewrite using `[hj, adjZ_Eab (sameBlock_refl c)]`. Apply the tactic sequence `all_goals simp`.

Establish `hAv : ∀ i, A i v = 0`. Introduce and unpack `(⟨⟨a, b⟩, hab⟩ | c)`. Conclude with `hmem.2 a b hab`. Simplify using `only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[hmem.1 c, sub_self]`.

Establish `hline : ∀ z, (∀ i, A i z = 0) → ∃ c : ℂ, c • v = z`. Introduce `z hz0`. Establish `hzmem : z ∈ hwSub M.act μ`. Rewrite using `[mem_hwSub_iff']`. Use `⟨fun c => ?_, fun a b hab => hz0 (Sum.inl ⟨(a, b), hab⟩)⟩` and prove the remaining obligations.

Establish `hc0` using `hz0 (Sum.inr c)`. Simplify using `only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hc0`. Conclude with `hc0`. Establish `hne : (⟨v, hvmem⟩ : hwSub M.act μ) ≠ 0`. Rewrite using `[Ne, Submodule.mk_eq_zero]` and apply the resulting hypothesis.

Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hzmem⟩`. Conclude with `⟨c, by simpa using congrArg Subtype.val hc⟩`. Establish `hvN : v ∈ N`. Rewrite using `[hmemN]`. Introduce `w`.

Take `⟨W, hWfin, hwW, hWst⟩` from `M.kfin w`. Use `hWfin` as an intermediate fact. Establish `hWst' : ∀ Z, IsKC Z → ∀ u ∈ W, M.act Z u ∈ W` using `hWst`. Establish `hAW : ∀ i, ∀ u ∈ W, A i u ∈ W`. Introduce and unpack `(⟨⟨a, b⟩, hab⟩ | c) u hu`.

Conclude with `hWst' _ (isKC_Eab (sameBlock_of_posC hab).1) u hu`. Simplify using `only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)`. Establish `hA'W : ∀ i, ∀ u ∈ W, A' i u ∈ W`. Introduce and unpack `(⟨⟨a, b⟩, hab⟩ | c) u hu`.

Conclude with `hWst' _ (isKC_Eab (sameBlock_of_posC hab).2) u hu`. Simplify using `only [A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)`. Conclude with `inner_eq_of_common_kernel_line j₁ j₂ A A' W hAW hA'W (hh H₁ j₁ h₁) (hh H₂ j₂ h₂) hinj v hAv hline hn w hwW`. Take `⟨-, hirr2⟩` from `hirr`.

Break down `hirr2 N hNinv with hN | hN` into its components or cases. Conclude with `absurd ((Submodule.mem_bot ℂ).mp (hN ▸ hvN)) hv0`. Establish `hx : x ∈ N` using `by rw [hN]; exact Submodule.mem_top`. Conclude with `(hmemN x).mp hx y`.
-/
theorem inner_eq_of_irreducible (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂)
    (h₁ : ∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y)))
    (hinj : Function.Injective j₂) (hirr : IrrGK M) (μ : Ix p q → ℚ) (v : M.V) (hv : IsHW M.act μ v)
    (hdim : Module.finrank ℂ ↥(hwSub M.act μ) = 1)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (x y : M.V) :
    inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  classical

  let N : Submodule ℂ M.V :=
    { carrier := {z | ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        intro w
        rw [map_add, map_add, inner_add_left, inner_add_left, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, inner_zero_left, implies_true]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro w
        rw [map_smul, map_smul, inner_smul_left, inner_smul_left, ha] }
  have hmemN : ∀ z, z ∈ N ↔ ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w) := fun z => Iff.rfl

  have hNinv : ∀ Z, ∀ z ∈ N, M.act Z z ∈ N := by
    intro Z z hz
    rw [hmemN] at hz ⊢
    intro w
    rw [h₁, h₂, hz]
  obtain ⟨hv0, hvmem⟩ : v ≠ 0 ∧ v ∈ hwSub M.act μ := hv
  have hmem := (mem_hwSub_iff' M.act μ v).mp hvmem

  let A : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.1 ab.1.2)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  let A' : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.2 ab.1.1)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  have hh : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M.V →ₗ[ℂ] H),
      (∀ Z z w, inner ℂ (j (M.act Z z)) (j w) = inner ℂ (j z) (j (M.act (adjZ Z) w))) →
      ∀ i z w, inner ℂ (j (A i z)) (j w) = inner ℂ (j z) (j (A' i w)) := by
    intro H _ _ j hj
    rintro (⟨⟨a, b⟩, hab⟩ | c) z w
    · simp only [A, A', Sum.elim_inl]
      rw [hj, adjZ_Eab (sameBlock_of_posC hab).1]
    · simp only [A, A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
      rw [hj, adjZ_Eab (sameBlock_refl c)]
      all_goals simp
  have hAv : ∀ i, A i v = 0 := by
    rintro (⟨⟨a, b⟩, hab⟩ | c)
    · exact hmem.2 a b hab
    · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hmem.1 c, sub_self]
  have hline : ∀ z, (∀ i, A i z = 0) → ∃ c : ℂ, c • v = z := by
    intro z hz0
    have hzmem : z ∈ hwSub M.act μ := by
      rw [mem_hwSub_iff']
      refine ⟨fun c => ?_, fun a b hab => hz0 (Sum.inl ⟨(a, b), hab⟩)⟩
      have hc0 := hz0 (Sum.inr c)
      simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hc0
      exact hc0
    have hne : (⟨v, hvmem⟩ : hwSub M.act μ) ≠ 0 := by
      rwa [Ne, Submodule.mk_eq_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hzmem⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

  have hvN : v ∈ N := by
    rw [hmemN]
    intro w
    obtain ⟨W, hWfin, hwW, hWst⟩ := M.kfin w
    have := hWfin
    have hWst' : ∀ Z, IsKC Z → ∀ u ∈ W, M.act Z u ∈ W := hWst
    have hAW : ∀ i, ∀ u ∈ W, A i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).1) u hu
      · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    have hA'W : ∀ i, ∀ u ∈ W, A' i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).2) u hu
      · simp only [A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    exact inner_eq_of_common_kernel_line j₁ j₂ A A' W hAW hA'W (hh H₁ j₁ h₁) (hh H₂ j₂ h₂) hinj v hAv
      hline hn w hwW

  obtain ⟨-, hirr2⟩ := hirr
  rcases hirr2 N hNinv with hN | hN
  · exact absurd ((Submodule.mem_bot ℂ).mp (hN ▸ hvN)) hv0
  · have hx : x ∈ N := by rw [hN]; exact Submodule.mem_top
    exact (hmemN x).mp hx y

end GlobalTheory.InvFormUnique
