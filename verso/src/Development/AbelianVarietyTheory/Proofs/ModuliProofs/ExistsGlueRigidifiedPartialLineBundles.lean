import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPartialBundleIsoNormalisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PartialBundleGlue

/- English proof (translation)
Establish `key : ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') → gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')) = gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹`. Introduce `x a a' b b' hm`. Use `show gm (𝟙 X) x _ (res _ (M.g a a') * (res _ (L.g b b'))⁻¹) = _`. Rewrite using `[map_mul, map_inv, gm_res (𝟙 X) x _ hm, gm_res (𝟙 X) x _ hm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x a a' b b' ha ha' hb hb'`. Establish `hm : x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')` using `⟨⟨ha, hb⟩, ha', hb'⟩`. Use `congrArg (gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) (h (a, b) (a', b'))` as an intermediate fact. Rewrite using `[← key x a a' b b' hm]`. Conclude with `(gm_res (𝟙 X) x _ hm _).symm.trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hm _))))`.

Introduce and unpack `h ⟨a, b⟩ ⟨a', b'⟩`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Use `h x a a' b b' hx.1.1 hx.2.1 hx.1.2 hx.2.2` as an intermediate fact. Rewrite `this` using `[← key x a a' b b' hx]`.

Conclude with `(gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)`.
-/
theorem iso_isGen_iff {X : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) :
    w.IsGen ↔ ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a → x ∈ M.U a' → x ∈ L.U b → x ∈ L.U b' →
      gm (𝟙 X) x (M.U a ⊓ L.U b) (w.s (a, b)) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
          gm (𝟙 X) x (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have key : ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') →
      gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ := by
    intro x a a' b b' hm
    show gm (𝟙 X) x _ (res _ (M.g a a') * (res _ (L.g b b'))⁻¹) = _
    rw [map_mul, map_inv, gm_res (𝟙 X) x _ hm, gm_res (𝟙 X) x _ hm]
  constructor
  · intro h x a a' b b' ha ha' hb hb'
    have hm : x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ha', hb'⟩
    have := congrArg (gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) (h (a, b) (a', b'))
    rw [← key x a a' b b' hm]
    exact (gm_res (𝟙 X) x _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hm _))))
  · rintro h ⟨a, b⟩ ⟨a', b'⟩
    apply unit_ext
    intro x hx
    have := h x a a' b b' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    rw [← key x a a' b b' hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

/- English proof (translation)
Introduce `J J'`. Take `⟨a, rfl⟩ : ∃ a, J = fun _ => a` from `⟨J PUnit.unit, rfl⟩`. Take `⟨b, rfl⟩ : ∃ b, J' = fun _ => b` from `⟨J' PUnit.unit, rfl⟩`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`.

Establish `ha : e x ∈ L.U a` using `mem_pull.1 hx.1`. Establish `hb : e x ∈ L.U b` using `mem_pull.1 hx.2`. Establish `eg : gm (𝟙 S) x ((L.pull e).U (fun _ => a) ⊓ (L.pull e).U (fun _ => b)) ((L.pull e).g (fun _ => a) (fun _ => b)) = gm e x (L.U a ⊓ L.U b) (L.g a b)` using `by show gm (𝟙 S) x _ (∏ _k : PUnit, (res _ (pullU e _ (L.g a b))) ^ (1 : ℤ)) = _`. Rewrite using `[Fintype.prod_unique, zpow_one]`. Conclude with `(gm_res (𝟙 S) x _ hx _).trans (gm_pull (𝟙 S) e x (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)`.

Rewrite using `[map_mul, gm_res _ x _ hx, gm_res _ x _ hx, eg]`. Conclude with `h x a b ha hb`.
-/
theorem pull_isGen_of {X S : Scheme.{0}} {L : LB X} {e : S ⟶ X} (r : (L.pull e).Gen)
    (h : ∀ (x : S) (a b : L.ι), e x ∈ L.U a → e x ∈ L.U b →
      gm (𝟙 S) x ((L.pull e).U fun _ => a) (r.s fun _ => a) =
        gm e x (L.U a ⊓ L.U b) (L.g a b) * gm (𝟙 S) x ((L.pull e).U fun _ => b) (r.s fun _ => b)) :
    r.IsGen := by
  intro J J'
  obtain ⟨a, rfl⟩ : ∃ a, J = fun _ => a := ⟨J PUnit.unit, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, J' = fun _ => b := ⟨J' PUnit.unit, rfl⟩
  apply unit_ext
  intro x hx
  have ha : e x ∈ L.U a := mem_pull.1 hx.1
  have hb : e x ∈ L.U b := mem_pull.1 hx.2
  have eg : gm (𝟙 S) x ((L.pull e).U (fun _ => a) ⊓ (L.pull e).U (fun _ => b))
      ((L.pull e).g (fun _ => a) (fun _ => b)) = gm e x (L.U a ⊓ L.U b) (L.g a b) := by
    show gm (𝟙 S) x _ (∏ _k : PUnit, (res _ (pullU e _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 S) x _ hx _).trans (gm_pull (𝟙 S) e x (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, eg]
  exact h x a b ha hb

/- English proof (translation)
Introduce `X S p e I U M hep hrig hU hM hself hr hiso`. Use `choose r hr using hr`. Use `choose w hw hn using fun i j => GlobalTheory.T.exists_partialBundle_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j) (hr i) (hr j) (hiso j i)`. Establish `hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c → gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) * gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) = gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c))`. Introduce `i j k`.

Use `GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_` and prove the remaining obligations. Introduce `x a b c ha hb hc`. Establish `h₁` using `hn i j x a b ha hb`. Establish `h₂` using `hn j k x b c hb hc`. Establish `h₃` using `hn i k x a c ha hc`.

Rewrite `h₃` using `[h₁, h₂, ← _root_.mul_assoc]`. Conclude with `mul_right_cancel h₃`. Set `L : LB X` to `⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩`. Use `⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩`. Introduce and unpack `⟨i, a⟩`.

Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[map_one]`. Conclude with `(gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))`. Introduce and unpack `⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩`.

Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]`. Conclude with `hc i j k x a b c hx.1.1 hx.1.2 hx.2`. Apply `pull_isGen_of` to reduce the goal to its premises.

Introduce and unpack `x ⟨i, a⟩ ⟨j, b⟩ ha hb`. Conclude with `hn i j x a b ha hb`. Introduce `i`. Use `⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'`.

Establish `h₁` using `hc j j' i x b b' a hb hb' ha`. Establish `h₂` using `(iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'`. Rewrite `h₂` using `[hself j' b' x hb', _root_.one_mul]`. Rewrite `h₁` using `[h₂, ← _root_.mul_assoc]`. Conclude with `h₁.symm`.
-/
theorem exists_glue : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  intro X S p e I U M hep hrig hU hM hself hr hiso
  choose r hr using hr
  choose w hw hn using fun i j => GlobalTheory.T.exists_partialBundle_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j)
    (hr i) (hr j) (hiso j i)
  have hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c →
      gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) *
        gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) =
        gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c)) := by
    intro i j k
    refine GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig
      (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_
    intro x a b c ha hb hc
    have h₁ := hn i j x a b ha hb
    have h₂ := hn j k x b c hb hc
    have h₃ := hn i k x a c ha hc
    rw [h₁, h₂, ← _root_.mul_assoc] at h₃
    exact mul_right_cancel h₃
  let L : LB X := ⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩
  · rintro ⟨i, a⟩
    apply unit_ext
    intro x hx
    rw [map_one]
    exact (gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact hc i j k x a b c hx.1.1 hx.1.2 hx.2
  · apply pull_isGen_of
    rintro x ⟨i, a⟩ ⟨j, b⟩ ha hb
    exact hn i j x a b ha hb
  · intro i
    refine ⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩
    rintro x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'
    have h₁ := hc j j' i x b b' a hb hb' ha
    have h₂ := (iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'
    rw [hself j' b' x hb', _root_.one_mul] at h₂
    rw [h₂, ← _root_.mul_assoc] at h₁
    exact h₁.symm

end GlobalTheory.PartialBundleGlue
