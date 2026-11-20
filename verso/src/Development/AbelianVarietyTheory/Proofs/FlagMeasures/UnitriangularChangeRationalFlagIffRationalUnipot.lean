import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagChange

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth_X {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => lt_of_lt_of_le ha h)`.
-/
theorem Xa_mono (F : FlagG S r T) {i j : ℕ} (h : i ≤ j) : F.Xa i ≤ F.Xa j :=
  Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => lt_of_lt_of_le ha h)

/- English proof (translation)
Simplify using `[FlagG.fvec]`.
-/
theorem fvec_castSucc (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc = F.e a := by
  simp [FlagG.fvec]

/- English proof (translation)
Simplify using `[FlagG.fvec]`.
-/
theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, h, rfl⟩`.
-/
theorem e_mem_Xa (F : FlagG S r T) (a : Fin r) {j : ℕ} (h : a.1 < j) : F.e a ∈ F.Xa j :=
  Submodule.subset_span ⟨a, h, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem e_mem_X (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.X :=
  Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, rfl⟩` from `h`. Use `Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F b a.castSucc` as an intermediate fact. Simplify using `only [brS, fvec_castSucc] at this`.

Rewrite using `[this]`. Simplify using `[Fin.castSucc_ne_last]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [map_add, hx, hy]`. Consider the case `smul c x _ hx => simp [LinearMap.map_smulₛₗ₂, hx]`.
-/
theorem X_orth_fvec (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) (b : Fin (r + 1)) :
    S.hT x (F.fvec b) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    have := Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F b a.castSucc
    simp only [brS, fvec_castSucc] at this
    rw [this]
    simp [Fin.castSucc_ne_last]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [LinearMap.map_smulₛₗ₂, hx]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y h`. Take `⟨a, rfl⟩` from `h`. Rewrite using `[← fvec_castSucc]`. Conclude with `X_orth_fvec F hx _`.

Consider the case `zero => simp`. Consider the case `add y y' _ _ h h' => simp [map_add, h, h']`. Consider the case `smul c y _ h => simp [h]`.
-/
theorem X_iso (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨a, rfl⟩ := h
    rw [← fvec_castSucc]
    exact X_orth_fvec F hx _
  | zero => simp
  | add y y' _ _ h h' => simp [map_add, h, h']
  | smul c y _ h => simp [h]

/- English proof (translation)
Rewrite using `[← fvec_last]`. Conclude with `X_orth_fvec F hx _`.
-/
theorem isotropicSpan_orthogonal_anisotropicVector (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  rw [← fvec_last]; exact X_orth_fvec F hx _

/- English proof (translation)
Rewrite using `[Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap x F.z, isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]`.
-/
theorem z_orth_X (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT F.z x = 0 := by
  rw [Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap x F.z, isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]

/- English proof (translation)
Unfold `FlagG.fvec`. Use `linearIndependent_fin_snoc.2 ⟨F.e_indep, fun hz => ?_⟩` and prove the remaining obligations. Establish `h` using `isotropicSpan_orthogonal_anisotropicVector F (x := F.z) hz`. Rewrite `h` using `[F.z_norm]`. Conclude with `hT (neg_eq_zero.1 h)`.
-/
theorem fvec_indep (F : FlagG S r T) (hT : T ≠ 0) : LinearIndependent E F.fvec := by
  unfold FlagG.fvec
  refine linearIndependent_fin_snoc.2 ⟨F.e_indep, fun hz => ?_⟩
  have h := isotropicSpan_orthogonal_anisotropicVector F (x := F.z) hz
  rw [F.z_norm] at h
  exact hT (neg_eq_zero.1 h)

/- English proof (translation)
Establish `e : g b - F.fvec b = ∑ a ∈ Finset.univ.erase b, A a b • F.fvec a`. Rewrite using `[hg b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hA.2 b, one_smul, add_sub_cancel_left]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Establish `hab : a ≠ b` using `Finset.ne_of_mem_erase ha`.

Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Establish `hlt : a.1 < b.1` using `h`. Establish `hr : a.1 < r` using `by have := b.2; omega`. Establish `ea : a = (⟨a.1, hr⟩ : Fin r).castSucc` using `by ext; rfl`. Rewrite using `[ea, fvec_castSucc]`.

Conclude with `Submodule.smul_mem _ _ (e_mem_Xa F _ hlt)`. Rewrite using `[hA.1 a b h, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem chg_sub_mem (F : FlagG S r T) {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hA : Uni A)
    {g : Fin (r + 1) → S.V} (hg : Chg F.fvec A g) (b : Fin (r + 1)) : g b - F.fvec b ∈ F.Xa b.1 := by
  have e : g b - F.fvec b = ∑ a ∈ Finset.univ.erase b, A a b • F.fvec a := by
    rw [hg b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hA.2 b, one_smul, add_sub_cancel_left]
  rw [e]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hab : a ≠ b := Finset.ne_of_mem_erase ha
  rcases lt_or_gt_of_ne hab with h | h
  · have hlt : a.1 < b.1 := h
    have hr : a.1 < r := by have := b.2; omega
    have ea : a = (⟨a.1, hr⟩ : Fin r).castSucc := by ext; rfl
    rw [ea, fvec_castSucc]
    exact Submodule.smul_mem _ _ (e_mem_Xa F _ hlt)
  · rw [hA.1 a b h, zero_smul]
    exact Submodule.zero_mem _

/- English proof (translation)
Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun a b h => hA.1 a b h)]`. Simplify using `[hA.2]`. Rewrite `hf`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `c hc`.

Establish `hs : ∑ a, (A.mulVec c) a • f a = 0`. Rewrite using `[← hc]`. Simplify using `only [hg _, Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Establish `h0` using `hf _ hs`. Establish `hc0 : c = 0` using `Matrix.eq_zero_of_mulVec_eq_zero (by rw [hdet]; exact one_ne_zero) (funext h0)`. Conclude with `fun i => congrFun hc0 i`.
-/
theorem chg_indep {n : ℕ} {f g : Fin n → S.V} (hf : LinearIndependent E f)
    {A : Matrix (Fin n) (Fin n) E} (hA : Uni A) (hg : Chg f A g) : LinearIndependent E g := by
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun a b h => hA.1 a b h)]
    simp [hA.2]
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc
  have hs : ∑ a, (A.mulVec c) a • f a = 0 := by
    rw [← hc]
    simp only [hg _, Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have h0 := hf _ hs
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hdet]; exact one_ne_zero) (funext h0)
  exact fun i => congrFun hc0 i

/- English proof (translation)
Set `g : Fin (r + 1) → S.V` to `fun b => ∑ a, A a b • F.fvec a`. Establish `hg : Chg F.fvec A g` using `fun b => rfl`. Establish `hli` using `chg_indep (fvec_indep F hT) hA hg`. Establish `hsub` using `chg_sub_mem F hA hg`. Establish `heX : ∀ a : Fin r, g a.castSucc ∈ F.X` using `fun a => by`.

Establish `h1` using `Xa_le_X F _ (hsub a.castSucc)`. Rewrite `h1` using `[fvec_castSucc]`. Simplify using `using F.X.add_mem h1 (e_mem_X F a)`. Establish `hzX : g (Fin.last r) - F.z ∈ F.X`. Establish `h1` using `Xa_le_X F _ (hsub (Fin.last r))`.

Rewrite `h1` using `[fvec_last]`. Then use the resulting hypothesis. Establish `hz : g (Fin.last r) = F.z + (g (Fin.last r) - F.z)` using `by abel`. Set `F₁ : FlagG S r T` to `{ e := fun a => g a.castSucc z := g (Fin.last r) e_indep := hli.comp _ (Fin.castSucc_injective r) e_iso := fun a b => X_iso F (heX a) (heX b) z_orth := fun a => by show S.hT (g a.castSucc) (g (Fin.last r)) = 0`. Rewrite using `[hz, map_add, isotropicSpan_orthogonal_anisotropicVector F (heX a), X_iso F (heX a) hzX, add_zero]`. Use `z_norm := by show S.hT (g (Fin.last r)) (g (Fin.last r)) = -T`.

Rewrite using `[hz]`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[isotropicSpan_orthogonal_anisotropicVector F hzX, z_orth_X F hzX, X_iso F hzX hzX, F.z_norm]`. Simplify using `}`. Establish `hF : F₁.fvec = g`.

Use function extensionality and compare the values at `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => exact fvec_last F₁`. Consider the case `cast b => exact fvec_castSucc F₁ b`. Conclude with `⟨F₁, by rw [hF]; exact hg⟩`.
-/
theorem exists_chg (F : FlagG S r T) (hT : T ≠ 0) {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hA : Uni A) :
    ∃ F₁ : FlagG S r T, Chg F.fvec A F₁.fvec := by
  let g : Fin (r + 1) → S.V := fun b => ∑ a, A a b • F.fvec a
  have hg : Chg F.fvec A g := fun b => rfl
  have hli := chg_indep (fvec_indep F hT) hA hg
  have hsub := chg_sub_mem F hA hg
  have heX : ∀ a : Fin r, g a.castSucc ∈ F.X := fun a => by
    have h1 := Xa_le_X F _ (hsub a.castSucc)
    rw [fvec_castSucc] at h1
    simpa using F.X.add_mem h1 (e_mem_X F a)
  have hzX : g (Fin.last r) - F.z ∈ F.X := by
    have h1 := Xa_le_X F _ (hsub (Fin.last r))
    rwa [fvec_last] at h1
  have hz : g (Fin.last r) = F.z + (g (Fin.last r) - F.z) := by abel
  let F₁ : FlagG S r T :=
    { e := fun a => g a.castSucc
      z := g (Fin.last r)
      e_indep := hli.comp _ (Fin.castSucc_injective r)
      e_iso := fun a b => X_iso F (heX a) (heX b)
      z_orth := fun a => by
        show S.hT (g a.castSucc) (g (Fin.last r)) = 0
        rw [hz, map_add, isotropicSpan_orthogonal_anisotropicVector F (heX a), X_iso F (heX a) hzX, add_zero]
      z_norm := by
        show S.hT (g (Fin.last r)) (g (Fin.last r)) = -T
        rw [hz]
        simp only [map_add, LinearMap.add_apply]
        rw [isotropicSpan_orthogonal_anisotropicVector F hzX, z_orth_X F hzX, X_iso F hzX hzX, F.z_norm]
        simp }
  have hF : F₁.fvec = g := by
    funext b
    induction b using Fin.lastCases with
    | last => exact fvec_last F₁
    | cast b => exact fvec_castSucc F₁ b
  exact ⟨F₁, by rw [hF]; exact hg⟩

/- English proof (translation)
Establish `hsub` using `chg_sub_mem F hA hc`. Establish `hsubX : ∀ b, F₁.fvec b - F.fvec b ∈ F.X` using `fun b => Xa_le_X F _ (hsub b)`. Use `set P : Submodule E S.V := Submodule.span E (Set.range F.fvec) with hP`. Use `set U : Submodule E S.V := orth S F.X with hU`. Establish `hfU : ∀ b, F.fvec b ∈ U` using `fun b => mem_orth_X.2 fun x hx => X_orth_fvec F hx b`.

Establish `hPU : P ≤ U` using `Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hfU b)`. Take `⟨C', hC'⟩` from `Submodule.exists_isCompl P`. Use `set C : Submodule E S.V := C' ⊓ U with hC`. Establish `hPC : Disjoint P C` using `hC'.disjoint.mono_right inf_le_left`. Establish `hsup : P ⊔ C = U`.

Establish `h` using `sup_inf_assoc_of_le C' hPU`. Rewrite `h` using `[hC'.sup_eq_top, top_inf_eq]`. Conclude with `h.symm`. Establish `hCU : C ≤ U` using `inf_le_right`. Set `bC` to `Module.finBasis E C`.

Set `c : Fin (Module.finrank E C) → S.V` to `fun i => (bC i : S.V)`. Establish `hcI : LinearIndependent E c` using `bC.linearIndependent.map' C.subtype (Submodule.ker_subtype C)`. Establish `hcC : Submodule.span E (Set.range c) ≤ C` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (bC i).2)`. Establish `hf₁P : ∀ b, F₁.fvec b ∈ P` using `fun b => by`. Establish `h1 : F₁.fvec b = F.fvec b + ∑ a ∈ Finset.univ.erase b, A a b • F.fvec a`.

Rewrite using `[hc b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hA.2 b, one_smul]`. Rewrite using `[h1]`. Conclude with `P.add_mem (Submodule.subset_span ⟨b, rfl⟩) (Submodule.sum_mem _ fun a _ => P.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩))`. Establish `hxI : LinearIndependent E (Sum.elim F.fvec c)` using `(fvec_indep F hT).sum_type hcI (hPC.mono le_rfl hcC)`. Establish `hyI : LinearIndependent E (Sum.elim F₁.fvec c)` using `(fvec_indep F₁ hT).sum_type hcI (hPC.mono (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hf₁P b)) hcC)`.

Establish `hcross : ∀ a i, S.hT (F.fvec a) (c i) = S.hT (F₁.fvec a) (c i)`. Introduce `a i`. Establish `h1 : S.hT (F₁.fvec a - F.fvec a) (c i) = 0` using `mem_orth_X.1 (hCU (bC i).2) _ (hsubX a)`. Rewrite `h1` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `h1.symm`.

Establish `hG : ∀ i j, S.hT (Sum.elim F.fvec c i) (Sum.elim F.fvec c j) = S.hT (Sum.elim F₁.fvec c i) (Sum.elim F₁.fvec c j)`. Introduce and unpack `(a | i) (b | j)`. Establish `h` using `Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F b a`. Establish `h₁` using `Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F₁ b a`. Simplify using `only [brS] at h h₁`.

Simplify using `only [Sum.elim_inl]`. Rewrite using `[h, h₁]`. Conclude with `hcross a j`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap (F.fvec b) (c i), Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap (F₁.fvec b) (c i), hcross b i]`.

Both sides reduce to the same expression. Take `⟨n, hn, hnf⟩` from `Formalism.L2.SG.NGCut.NormalVectorPairings.witt_tuple _ _ hxI hyI hG`. Establish `hnF : ∀ a, n (F.fvec a) = F₁.fvec a` using `fun a => hnf (Sum.inl a)`. Establish `hnc : ∀ i, n (c i) = c i` using `fun i => hnf (Sum.inr i)`. Set `m : S.V →ₗ[E] S.V` to `(n : S.V →ₗ[E] S.V) - LinearMap.id`.

Establish `hm : ∀ x, m x = n x - x` using `fun x => rfl`. Establish `hmC : C ≤ LinearMap.ker m`. Establish `hext : m ∘ₗ C.subtype = 0` using `bC.ext fun i => by show m (c i) = 0`. Rewrite using `[hm, hnc, sub_self]`. Introduce `x hx`.

Conclude with `LinearMap.congr_fun hext ⟨x, hx⟩`. Establish `hmP : P ≤ F.X.comap m` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `show m (F.fvec b) ∈ F.X`. Rewrite using `[hm, hnF]`.

Conclude with `hsubX b)`. Use `⟨n, hn, fun j x hx => ?_, fun x hx => ?_, fun a => (hnF a).symm⟩` and prove the remaining obligations. Establish `hle : F.Xa (j + 1) ≤ (F.Xa j).comap m` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `ha' : a.1 < j + 1` using `ha`.

Use `show m (F.e a) ∈ F.Xa j`. Rewrite using `[hm, ← fvec_castSucc, hnF]`. Conclude with `Xa_mono F (by simpa using Nat.lt_succ_iff.1 ha') (hsub a.castSucc))`. Conclude with `hle hx`. Establish `hx' : x ∈ P ⊔ C` using `by rw [hsup]; exact hx`.

Take `⟨p, hp, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx'`. Establish `h1 : m p ∈ F.X` using `hmP hp`. Establish `h2 : m w = 0` using `hmC hw`. Establish `h3 : m (p + w) ∈ F.X` using `by rw [map_add, h2, add_zero]; exact h1`. Conclude with `h3`.
-/
theorem exists_unip (F F₁ : FlagG S r T) (hT : T ≠ 0) {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hA : Uni A)
    (hc : Chg F.fvec A F₁.fvec) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) ∧
      (∀ x ∈ orth S F.X, n x - x ∈ F.X) ∧ ∀ a, F₁.fvec a = n (F.fvec a) := by
  have hsub := chg_sub_mem F hA hc
  have hsubX : ∀ b, F₁.fvec b - F.fvec b ∈ F.X := fun b => Xa_le_X F _ (hsub b)

  set P : Submodule E S.V := Submodule.span E (Set.range F.fvec) with hP
  set U : Submodule E S.V := orth S F.X with hU
  have hfU : ∀ b, F.fvec b ∈ U := fun b => mem_orth_X.2 fun x hx => X_orth_fvec F hx b
  have hPU : P ≤ U := Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hfU b)
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl P
  set C : Submodule E S.V := C' ⊓ U with hC
  have hPC : Disjoint P C := hC'.disjoint.mono_right inf_le_left
  have hsup : P ⊔ C = U := by
    have h := sup_inf_assoc_of_le C' hPU
    rw [hC'.sup_eq_top, top_inf_eq] at h
    exact h.symm
  have hCU : C ≤ U := inf_le_right
  let bC := Module.finBasis E C
  let c : Fin (Module.finrank E C) → S.V := fun i => (bC i : S.V)
  have hcI : LinearIndependent E c :=
    bC.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hcC : Submodule.span E (Set.range c) ≤ C :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (bC i).2)
  have hf₁P : ∀ b, F₁.fvec b ∈ P := fun b => by
    have h1 : F₁.fvec b = F.fvec b + ∑ a ∈ Finset.univ.erase b, A a b • F.fvec a := by
      rw [hc b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hA.2 b, one_smul]
    rw [h1]
    exact P.add_mem (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.sum_mem _ fun a _ => P.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩))
  have hxI : LinearIndependent E (Sum.elim F.fvec c) :=
    (fvec_indep F hT).sum_type hcI (hPC.mono le_rfl hcC)
  have hyI : LinearIndependent E (Sum.elim F₁.fvec c) :=
    (fvec_indep F₁ hT).sum_type hcI
      (hPC.mono (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hf₁P b)) hcC)
  have hcross : ∀ a i, S.hT (F.fvec a) (c i) = S.hT (F₁.fvec a) (c i) := by
    intro a i
    have h1 : S.hT (F₁.fvec a - F.fvec a) (c i) = 0 := mem_orth_X.1 (hCU (bC i).2) _ (hsubX a)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
    exact h1.symm
  have hG : ∀ i j, S.hT (Sum.elim F.fvec c i) (Sum.elim F.fvec c j) =
      S.hT (Sum.elim F₁.fvec c i) (Sum.elim F₁.fvec c j) := by
    rintro (a | i) (b | j)
    · have h := Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F b a
      have h₁ := Formalism.L2.SG.NGCut.NormalVectorPairings.brS_fvec F₁ b a
      simp only [brS] at h h₁
      simp only [Sum.elim_inl]
      rw [h, h₁]
    · exact hcross a j
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap (F.fvec b) (c i),
        Formalism.L2.SG.NGCut.NormalVectorPairings.hT_swap (F₁.fvec b) (c i), hcross b i]
    · rfl
  obtain ⟨n, hn, hnf⟩ := Formalism.L2.SG.NGCut.NormalVectorPairings.witt_tuple _ _ hxI hyI hG
  have hnF : ∀ a, n (F.fvec a) = F₁.fvec a := fun a => hnf (Sum.inl a)
  have hnc : ∀ i, n (c i) = c i := fun i => hnf (Sum.inr i)
  let m : S.V →ₗ[E] S.V := (n : S.V →ₗ[E] S.V) - LinearMap.id
  have hm : ∀ x, m x = n x - x := fun x => rfl
  have hmC : C ≤ LinearMap.ker m := by
    have hext : m ∘ₗ C.subtype = 0 := bC.ext fun i => by
      show m (c i) = 0
      rw [hm, hnc, sub_self]
    intro x hx
    exact LinearMap.congr_fun hext ⟨x, hx⟩
  have hmP : P ≤ F.X.comap m := Submodule.span_le.2 (by
    rintro _ ⟨b, rfl⟩
    show m (F.fvec b) ∈ F.X
    rw [hm, hnF]
    exact hsubX b)
  refine ⟨n, hn, fun j x hx => ?_, fun x hx => ?_, fun a => (hnF a).symm⟩
  · have hle : F.Xa (j + 1) ≤ (F.Xa j).comap m := Submodule.span_le.2 (by
      rintro _ ⟨a, ha, rfl⟩
      have ha' : a.1 < j + 1 := ha
      show m (F.e a) ∈ F.Xa j
      rw [hm, ← fvec_castSucc, hnF]
      exact Xa_mono F (by simpa using Nat.lt_succ_iff.1 ha') (hsub a.castSucc))
    exact hle hx
  · have hx' : x ∈ P ⊔ C := by rw [hsup]; exact hx
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have h1 : m p ∈ F.X := hmP hp
    have h2 : m w = 0 := hmC hw
    have h3 : m (p + w) ∈ F.X := by rw [map_add, h2, add_zero]; exact h1
    exact h3

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, ha, rfl⟩` from `h`. Establish `ha' : a.1 < j` using `ha`. Use `⟨Pi.single a 1, fun i hi => ?_, ?_⟩` and prove the remaining obligations.

Establish `: i ≠ a` using `fun e => by subst e; omega`. Simplify using `[this]`. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, hc, rfl⟩` from `hx`. Take `⟨d, hd, rfl⟩` from `hy`. Use `⟨c + d, fun i hi => by simp [hc i hi, hd i hi], ?_⟩` and prove the remaining obligations. Simplify using `[add_smul, Finset.sum_add_distrib]`. Consider the case `smul t x _ hx`.

Take `⟨c, hc, rfl⟩` from `hx`. Use `⟨t • c, fun i hi => by simp [hc i hi], ?_⟩` and prove the remaining obligations. Simplify using `[Finset.smul_sum, smul_smul]`.
-/
theorem Xa_coords (F : FlagG S r T) {j : ℕ} {x : S.V} (hx : x ∈ F.Xa j) :
    ∃ c : Fin r → E, (∀ i : Fin r, j ≤ i.1 → c i = 0) ∧ x = ∑ i, c i • F.e i := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, rfl⟩ := h
    have ha' : a.1 < j := ha
    refine ⟨Pi.single a 1, fun i hi => ?_, ?_⟩
    · have : i ≠ a := fun e => by subst e; omega
      simp [this]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    refine ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨t • c, fun i hi => by simp [hc i hi], ?_⟩
    simp [Finset.smul_sum, smul_smul]

/- English proof (translation)
Establish `hX : F.X = F.Xa r`. Unfold `FlagG.X FlagG.Xa`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]`.

Conclude with `⟨fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩`. Establish `hb : ∀ b : Fin (r + 1), n (F.fvec b) - F.fvec b ∈ F.Xa b.1`. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[fvec_last, Fin.val_last, ← hX]`. Conclude with `hp _ (mem_orth_X.2 fun x hx => isotropicSpan_orthogonal_anisotropicVector F hx)`. Consider the case `cast b`. Rewrite using `[fvec_castSucc, Fin.val_castSucc]`. Conclude with `hf _ _ (e_mem_Xa F b (Nat.lt_succ_self _))`.

Use `choose c hc0 hc using fun b => Xa_coords F (hb b)`. Set `B : Matrix (Fin (r + 1)) (Fin (r + 1)) E` to `fun a b => Fin.lastCases 0 (fun i => c b i) a`. Establish `hBc : ∀ (i : Fin r) b, B i.castSucc b = c b i` using `fun i b => by simp [B]`. Establish `hBl : ∀ b, B (Fin.last r) b = 0` using `fun b => by simp [B]`. Establish `hBz : ∀ a b : Fin (r + 1), b.1 ≤ a.1 → B a b = 0`.

Introduce `a b h`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hBl b`. Consider the case `cast i => rw [hBc]; exact hc0 b i (by simpa using h)`. Use `⟨1 + B, ⟨fun a b h => ?_, fun a => ?_⟩, fun b => ?_⟩` and prove the remaining obligations.

Establish `hne : a ≠ b` using `ne_of_gt h`. Establish `hle : b.1 ≤ a.1` using `le_of_lt h`. Simplify using `[Matrix.one_apply_ne hne, hBz a b hle]`. Simplify using `[hBz a a le_rfl]`. Establish `h1 : ∑ a, B a b • F.fvec a = ∑ i, c b i • F.e i`.

Rewrite using `[Fin.sum_univ_castSucc, hBl, zero_smul, add_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hBc, fvec_castSucc]`. Establish `h2 : ∑ a, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) a b • F.fvec a = F.fvec b`. Simplify using `[Matrix.one_apply]`.

Simplify using `only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]`. Rewrite using `[h1, h2, ← hc b, hn b]`. Normalize the expressions using the abelian group laws.
-/
theorem tri_of_unip (F F₁ : FlagG S r T) (n : S.V ≃ₗ[E] S.V)
    (hf : ∀ j, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) (hp : ∀ x ∈ orth S F.X, n x - x ∈ F.X)
    (hn : ∀ a, F₁.fvec a = n (F.fvec a)) : Tri E F.fvec F₁.fvec := by
  have hX : F.X = F.Xa r := by
    unfold FlagG.X FlagG.Xa
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  have hb : ∀ b : Fin (r + 1), n (F.fvec b) - F.fvec b ∈ F.Xa b.1 := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [fvec_last, Fin.val_last, ← hX]
      exact hp _ (mem_orth_X.2 fun x hx => isotropicSpan_orthogonal_anisotropicVector F hx)
    | cast b =>
      rw [fvec_castSucc, Fin.val_castSucc]
      exact hf _ _ (e_mem_Xa F b (Nat.lt_succ_self _))
  choose c hc0 hc using fun b => Xa_coords F (hb b)
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => Fin.lastCases 0 (fun i => c b i) a
  have hBc : ∀ (i : Fin r) b, B i.castSucc b = c b i := fun i b => by simp [B]
  have hBl : ∀ b, B (Fin.last r) b = 0 := fun b => by simp [B]
  have hBz : ∀ a b : Fin (r + 1), b.1 ≤ a.1 → B a b = 0 := by
    intro a b h
    induction a using Fin.lastCases with
    | last => exact hBl b
    | cast i => rw [hBc]; exact hc0 b i (by simpa using h)
  refine ⟨1 + B, ⟨fun a b h => ?_, fun a => ?_⟩, fun b => ?_⟩
  · have hne : a ≠ b := ne_of_gt h
    have hle : b.1 ≤ a.1 := le_of_lt h
    simp [Matrix.one_apply_ne hne, hBz a b hle]
  · simp [hBz a a le_rfl]
  · have h1 : ∑ a, B a b • F.fvec a = ∑ i, c b i • F.e i := by
      rw [Fin.sum_univ_castSucc, hBl, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBc, fvec_castSucc]
    have h2 : ∑ a, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) a b • F.fvec a = F.fvec b := by
      simp [Matrix.one_apply]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    rw [h1, h2, ← hc b, hn b]
    abel

end Gen

/- English proof (translation)
Introduce `D T F hT`. Use `⟨fun A hA => ?_, fun F₁ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨G, hG⟩` from `exists_chg F.fl hT hA`. Conclude with `⟨⟨G, G.z⟩, hG⟩`. Introduce and unpack `⟨A, hA, hc⟩`.

Take `⟨n, hi, hf, hp, hn⟩` from `exists_unip F.fl F₁.fl hT hA hc`. Conclude with `⟨n, ⟨hi, hf, hp⟩, hn⟩`. Introduce and unpack `⟨n, ⟨-, hf, hp⟩, hn⟩`. Conclude with `tri_of_unip F.fl F₁.fl n hf hp hn`.
-/
theorem flag_change : ∀ (D : D7) {T : D.host.E} (F : LFlag (VS D) D.R.rS T), T ≠ 0 →
    (∀ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Uni A →
      ∃ F₁ : LFlag (VS D) D.R.rS T, Chg (frame F) A (frame F₁)) ∧
    (∀ F₁ : LFlag (VS D) D.R.rS T, Tri D.host.E (frame F) (frame F₁) ↔
      ∃ n ∈ Formalism.L2.SG.NGData.NRat F, ∀ a, frame F₁ a = n (frame F a)) := by
  intro D T F hT
  refine ⟨fun A hA => ?_, fun F₁ => ⟨?_, ?_⟩⟩
  · obtain ⟨G, hG⟩ := exists_chg F.fl hT hA
    exact ⟨⟨G, G.z⟩, hG⟩
  · rintro ⟨A, hA, hc⟩
    obtain ⟨n, hi, hf, hp, hn⟩ := exists_unip F.fl F₁.fl hT hA hc
    exact ⟨n, ⟨hi, hf, hp⟩, hn⟩
  · rintro ⟨n, ⟨-, hf, hp⟩, hn⟩
    exact tri_of_unip F.fl F₁.fl n hf hp hn

end GlobalTheory.FlagChange
