import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.NFrameTri

section Gen

variable {K : Type} [CommRing K] {W : Type} [AddCommGroup W] [Module K W] {m : ℕ}

def flag (K : Type) [CommRing K] [Module K W] (f : Fin m → W) (j : ℕ) : Submodule K W :=
  Submodule.span K (f '' {a | a.val < j})

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)`.
-/
lemma flag_mono (f : Fin m → W) {i j : ℕ} (h : i ≤ j) : flag K f i ≤ flag K f j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

/- English proof (translation)
Simplify using `[flag]`.
-/
lemma flag_zero (f : Fin m → W) : flag K f 0 = ⊥ := by
  simp [flag]

def Lowers (f : Fin m → W) (n : W ≃ₗ[K] W) : Prop :=
  ∀ j, ∀ v ∈ flag K f (j + 1), n v - v ∈ flag K f j

/- English proof (translation)
Introduce `j v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `flag_mono f (Nat.lt_succ_iff.mp hb) (h b)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Establish `: n (x + y) - (x + y) = (n x - x) + (n y - y)` using `by rw [map_add]; abel`. Rewrite using `[this]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx`. Establish `: n (c • x) - c • x = c • (n x - x)` using `by rw [map_smul, smul_sub]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
lemma lowers_of_gen (f : Fin m → W) (n : W ≃ₗ[K] W)
    (h : ∀ b : Fin m, n (f b) - f b ∈ flag K f b.val) : Lowers f n := by
  intro j v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact flag_mono f (Nat.lt_succ_iff.mp hb) (h b)
  | zero => simp
  | add x y _ _ hx hy =>
    have : n (x + y) - (x + y) = (n x - x) + (n y - y) := by rw [map_add]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : n (c • x) - c • x = c • (n x - x) := by rw [map_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Introduce `j v hv`. Establish `h1` using `h' j v hv`. Establish `h2 : n' v ∈ flag K f (j + 1)`. Establish `: n' v = (n' v - v) + v` using `by abel`. Rewrite using `[this]`.

Conclude with `add_mem (flag_mono f (Nat.le_succ j) h1) hv`. Establish `: (n * n') v - v = (n (n' v) - n' v) + (n' v - v)`. Rewrite using `[LinearEquiv.mul_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `add_mem (h j _ h2) h1`.
-/
lemma Lowers.mul {f : Fin m → W} {n n' : W ≃ₗ[K] W} (h : Lowers f n) (h' : Lowers f n') :
    Lowers f (n * n') := by
  intro j v hv
  have h1 := h' j v hv
  have h2 : n' v ∈ flag K f (j + 1) := by
    have : n' v = (n' v - v) + v := by abel
    rw [this]; exact add_mem (flag_mono f (Nat.le_succ j) h1) hv
  have : (n * n') v - v = (n (n' v) - n' v) + (n' v - v) := by
    rw [LinearEquiv.mul_apply]; abel
  rw [this]; exact add_mem (h j _ h2) h1

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `v hv`. Rewrite `hv` using `[flag_zero, Submodule.mem_bot]`.

Conclude with `⟨0, zero_mem _, by simp [hv]⟩`. Consider the case `succ j ih`. Introduce `v hv`. Take `⟨w, hw, e⟩` from `ih _ (h j v hv)`. Use `⟨v - w, sub_mem hv (flag_mono f (Nat.le_succ j) hw), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, e]`. Normalize the expressions using the abelian group laws.
-/
lemma Lowers.surj {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) :
    ∀ j, ∀ v ∈ flag K f j, ∃ w ∈ flag K f j, n w = v := by
  intro j
  induction j with
  | zero =>
    intro v hv
    rw [flag_zero, Submodule.mem_bot] at hv
    exact ⟨0, zero_mem _, by simp [hv]⟩
  | succ j ih =>
    intro v hv
    obtain ⟨w, hw, e⟩ := ih _ (h j v hv)
    refine ⟨v - w, sub_mem hv (flag_mono f (Nat.le_succ j) hw), ?_⟩
    rw [map_sub, e]; abel

/- English proof (translation)
Introduce `j v hv`. Take `⟨w, hw, rfl⟩` from `h.surj _ v hv`. Establish `e : n⁻¹ (n w) = w` using `n.symm_apply_apply w`. Establish `: n⁻¹ (n w) - n w = -(n w - w)` using `by rw [e]; abel`. Rewrite using `[this]`.

Conclude with `neg_mem (h j w hw)`.
-/
lemma Lowers.inv {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Lowers f n⁻¹ := by
  intro j v hv
  obtain ⟨w, hw, rfl⟩ := h.surj _ v hv
  have e : n⁻¹ (n w) = w := n.symm_apply_apply w
  have : n⁻¹ (n w) - n w = -(n w - w) := by rw [e]; abel
  rw [this]; exact neg_mem (h j w hw)

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Use `⟨Pi.single b 1, fun a ha => Pi.single_eq_of_ne ?_ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `absurd hb (not_lt.mpr ha)`. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, rfl⟩` from `hx`.

Take `⟨d, hd, rfl⟩` from `hy`. Conclude with `⟨c + d, fun a ha => by simp [hc a ha, hd a ha], by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul s x _ hx`. Take `⟨c, hc, rfl⟩` from `hx`. Conclude with `⟨s • c, fun a ha => by simp [hc a ha], by simp [Finset.smul_sum, smul_smul]⟩`.
-/
lemma exists_coef (f : Fin m → W) (j : ℕ) (v : W) (hv : v ∈ flag K f j) :
    ∃ c : Fin m → K, (∀ a, j ≤ a.val → c a = 0) ∧ v = ∑ a, c a • f a := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨Pi.single b 1, fun a ha => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hb (not_lt.mpr ha)
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun a ha => by simp [hc a ha, hd a ha], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨s • c, fun a ha => by simp [hc a ha], by simp [Finset.smul_sum, smul_smul]⟩

/- English proof (translation)
Establish `: ∀ b : Fin m, ∃ c : Fin m → K, (∀ a, b.val ≤ a.val → c a = 0) ∧ n (f b) - f b = ∑ a, c a • f a` using `fun b => exists_coef f _ _ (h b.val (f b) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩))`. Use `choose c hc e using this`. Use `⟨Matrix.of fun a b => c b a + if a = b then 1 else 0, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩` and prove the remaining obligations. Simplify using `[hc b a hab.le, hab.ne']`. Simplify using `[hc a a le_rfl]`.

Simplify using `only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← e]`. Simplify using the standard rewrite rules.
-/
lemma Lowers.tri {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Tri K f (fun b => n (f b)) := by
  have : ∀ b : Fin m, ∃ c : Fin m → K, (∀ a, b.val ≤ a.val → c a = 0) ∧ n (f b) - f b = ∑ a, c a • f a :=
    fun b => exists_coef f _ _ (h b.val (f b) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩))
  choose c hc e using this
  refine ⟨Matrix.of fun a b => c b a + if a = b then 1 else 0, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
  · simp [hc b a hab.le, hab.ne']
  · simp [hc a a le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← e]
    simp

end Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨a.castSucc, ha, rfl⟩`.
-/
lemma Fj_le_flag {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) (j : ℕ) : Fr.Fj j ≤ flag E Fr.f j := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.castSucc, ha, rfl⟩

/- English proof (translation)
Introduce `x hx`. Establish `: H.h x (Fr.f (Fin.last r)) = 0`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Conclude with `Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)`. Consider the case `zero => exact H.h_zero_left _`. Consider the case `add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]`. Rewrite using `[H.h_herm, this, map_zero]`.
-/
lemma last_mem_perp {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) :
    Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
  intro x hx
  have : H.h x (Fr.f (Fin.last r)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  rw [H.h_herm, this, map_zero]

/- English proof (translation)
Take `⟨-, h1, h2⟩` from `hn`. Apply `lowers_of_gen` to reduce the goal to its premises. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Use `Submodule.span_mono ?_ (h2 _ (last_mem_perp Fr))` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨a.castSucc, a.isLt, rfl⟩`. Consider the case `cast a`. Conclude with `Fj_le_flag Fr _ (h1 (a.val + 1) a.isLt (Fr.e a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩))`.
-/
lemma lowers_of_mem_NSet {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.NSet) :
    Lowers Fr.f n := by
  obtain ⟨-, h1, h2⟩ := hn
  apply lowers_of_gen
  intro b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.span_mono ?_ (h2 _ (last_mem_perp Fr))
    rintro _ ⟨a, rfl⟩
    exact ⟨a.castSucc, a.isLt, rfl⟩
  | cast a =>
    exact Fj_le_flag Fr _ (h1 (a.val + 1) a.isLt (Fr.e a)
      (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩))

/- English proof (translation)
Introduce `n hn`. Apply `Lowers.tri` to reduce the goal to its premises. Proceed by induction on `hn using Subgroup.closure_induction with`. Consider the case `mem x hx => exact lowers_of_mem_NSet Fr hx`. Consider the case `one => intro j v _`.

Simplify using the standard rewrite rules. Consider the case `mul x y _ _ hx hy => exact hx.mul hy`. Consider the case `inv x _ hx => exact hx.inv`.
-/
theorem tri_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) :
    ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  intro n hn
  apply Lowers.tri
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact lowers_of_mem_NSet Fr hx
  | one => intro j v _; simp
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

end GlobalTheory.NFrameTri
