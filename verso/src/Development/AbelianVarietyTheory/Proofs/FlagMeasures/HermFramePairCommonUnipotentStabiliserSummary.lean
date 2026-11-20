import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnipStab

section One

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa`. Use `Submodule.span_mono (Set.image_mono fun c hc => ?_)` and prove the remaining obligations. Establish `hc' : (c : ℕ) < a` using `hc`. Conclude with `lt_of_lt_of_le hc' h`.
-/
theorem _root_.GlobalTheory.UnipStab.Xa_mono {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  refine Submodule.span_mono (Set.image_mono fun c hc => ?_)
  have hc' : (c : ℕ) < a := hc
  exact lt_of_lt_of_le hc' h

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa`. Conclude with `Submodule.subset_span ⟨a, h, rfl⟩`.
-/
private theorem hermFlag_basis_vector_mem_graded_lemma (a : Fin r) {n : ℕ} (h : (a : ℕ) < n) :
    F.e a.castSucc ∈ F.Xa n := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  exact Submodule.subset_span ⟨a, h, rfl⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
The claim follows from `hermFlag_basis_vector_mem_graded_lemma F a a.isLt`.
-/
theorem _root_.GlobalTheory.UnipStab.e_mem_X (a : Fin r) : F.e a.castSucc ∈ F.X :=
  hermFlag_basis_vector_mem_graded_lemma F a a.isLt

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `hy a ha`.

Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => simp [hx, hz]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
private theorem hermFlag_orthogonal_graded_of_basis_lemma_2 {n : ℕ} {y : V}
    (hy : ∀ a : Fin r, (a : ℕ) < n → H.B (F.e a.castSucc) y = 0) {x : V} (hx : x ∈ F.Xa n) :
    H.B x y = 0 := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact hy a ha
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
The claim follows from `hermFlag_orthogonal_graded_of_basis_lemma_2 F (fun a _ => hy a) hx`.
-/
theorem _root_.GlobalTheory.UnipStab.orth_X {y : V}
    (hy : ∀ a : Fin r, H.B (F.e a.castSucc) y = 0) {x : V} (hx : x ∈ F.X) :
    H.B x y = 0 :=
  hermFlag_orthogonal_graded_of_basis_lemma_2 F (fun a _ => hy a) hx

variable {F}

/- English proof (translation)
Establish `: F.Xa (a + 1) ≤ (F.Xa a).comap (g - LinearMap.id)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `Xa_mono F (Nat.lt_succ_iff.1 hb) (hg.2.2.1 b)`. Conclude with `this hx`.
-/
theorem step {g : V →ₗ[K] V} (hg : F.InN g) (a : ℕ) {x : V} (hx : x ∈ F.Xa (a + 1)) :
    g x - x ∈ F.Xa a := by
  have : F.Xa (a + 1) ≤ (F.Xa a).comap (g - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Xa_mono F (Nat.lt_succ_iff.1 hb) (hg.2.2.1 b)
  exact this hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg`. Take `⟨-, -, he, -⟩` from `hg`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, rfl⟩` from `hx`. Establish `hb' : (b : ℕ) < a` using `hb`. Establish `h1 : g (F.e b.castSucc) - F.e b.castSucc ∈ F.Xa a` using `_root_.GlobalTheory.UnipStab.Xa_mono F hb'.le (he b)`. Establish `h2` using `hermFlag_basis_vector_mem_graded_lemma F b hb'`. Simplify using `using add_mem h1 h2`.

Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => simpa using add_mem hx hz`. Consider the case `smul c x _ hx => simpa using Submodule.smul_mem _ c hx`.
-/
theorem _root_.GlobalTheory.UnipStab.map_Xa {g : V →ₗ[K] V} (hg : F.InN g) (a : ℕ) {x : V}
    (hx : x ∈ F.Xa a) : g x ∈ F.Xa a := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg
  obtain ⟨-, -, he, -⟩ := hg
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : (b : ℕ) < a := hb
    have h1 : g (F.e b.castSucc) - F.e b.castSucc ∈ F.Xa a :=
      _root_.GlobalTheory.UnipStab.Xa_mono F hb'.le (he b)
    have h2 := hermFlag_basis_vector_mem_graded_lemma F b hb'
    simpa using add_mem h1 h2
  | zero => simp
  | add x z _ _ hx hz => simpa using add_mem hx hz
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.z`. Conclude with `hg.2.2.2 _ F.zperp`.
-/
theorem _root_.GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem {g : V →ₗ[K] V} (hg : F.InN g) :
    g F.z - F.z ∈ F.X := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.z
  exact hg.2.2.2 _ F.zperp

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN`. Apply the tactic sequence `refine ⟨fun x y => rfl, (1 : V ≃ₗ[K] V).bijective, fun a => ?_, fun y _ => ?_⟩ <;>`. Simplify using `[LinearEquiv.coe_coe]`.
-/
theorem _root_.GlobalTheory.UnipStab.inN_one : F.InN ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN
  refine ⟨fun x y => rfl, (1 : V ≃ₗ[K] V).bijective, fun a => ?_, fun y _ => ?_⟩ <;>
    simp [LinearEquiv.coe_coe]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem hermFlag_isotropic_eq_graded_lemma_4 : F.X = F.Xa r := rfl

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Rewrite `hx`, the goal using `[hermFlag_isotropic_eq_graded_lemma_4 F]`. Conclude with `_root_.GlobalTheory.UnipStab.map_Xa hg r hx`.
-/
private theorem hermFlagUnipotent_maps_isotropic_lemma_3 {g : V →ₗ[K] V} (hg : F.InN g) {x : V}
    (hx : x ∈ F.X) : g x ∈ F.X := by
  rw [hermFlag_isotropic_eq_graded_lemma_4 F] at hx ⊢
  exact _root_.GlobalTheory.UnipStab.map_Xa hg r hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Establish `hs'` using `hs`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ht ⊢`. Take `⟨hsi, -, hse, hsy⟩` from `hs`. Take `⟨hti, -, hte, hty⟩` from `ht`. Use `⟨fun x y => ?_, (s * t).bijective, fun a => ?_, fun y hy => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `H.B (s (t x)) (s (t y)) = H.B x y`. Conclude with `(hsi _ _).trans (hti _ _)`. Express the relevant statement in the definitionally equal form `s (t (F.e a.castSucc)) - F.e a.castSucc ∈ F.Xa a`. Establish `h1 : s (t (F.e a.castSucc) - F.e a.castSucc) ∈ F.Xa a` using `_root_.GlobalTheory.UnipStab.map_Xa hs' a (hte a)`. Establish `h2 : s (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a` using `hse a`.

Use `add_mem h1 h2` as an intermediate fact. Rewrite `this` using `[map_sub, sub_add_sub_cancel]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `s (t y) - y ∈ F.X`. Establish `h1 : s (t y - y) ∈ F.X` using `hermFlagUnipotent_maps_isotropic_lemma_3 hs' (hty y hy)`. Establish `h2 : s y - y ∈ F.X` using `hsy y hy`.

Use `add_mem h1 h2` as an intermediate fact. Rewrite `this` using `[map_sub, sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.UnipStab.inN_mul {s t : V ≃ₗ[K] V} (hs : F.InN (s : V →ₗ[K] V))
    (ht : F.InN (t : V →ₗ[K] V)) : F.InN ((s * t : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hs' := hs
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ht ⊢
  obtain ⟨hsi, -, hse, hsy⟩ := hs
  obtain ⟨hti, -, hte, hty⟩ := ht
  refine ⟨fun x y => ?_, (s * t).bijective, fun a => ?_, fun y hy => ?_⟩
  · change H.B (s (t x)) (s (t y)) = H.B x y
    exact (hsi _ _).trans (hti _ _)
  · change s (t (F.e a.castSucc)) - F.e a.castSucc ∈ F.Xa a
    have h1 : s (t (F.e a.castSucc) - F.e a.castSucc) ∈ F.Xa a :=
      _root_.GlobalTheory.UnipStab.map_Xa hs' a (hte a)
    have h2 : s (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a := hse a
    have := add_mem h1 h2
    rwa [map_sub, sub_add_sub_cancel] at this
  · change s (t y) - y ∈ F.X
    have h1 : s (t y - y) ∈ F.X := hermFlagUnipotent_maps_isotropic_lemma_3 hs' (hty y hy)
    have h2 : s y - y ∈ F.X := hsy y hy
    have := add_mem h1 h2
    rwa [map_sub, sub_add_sub_cancel] at this

/- English proof (translation)
Establish `h1 : S.map (s : V →ₗ[K] V) = S`. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h y hy`. Conclude with `LinearEquiv.finrank_map_eq s S`.

Rewrite `hx` using `[← h1]`. Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`.
-/
theorem symm_mem [FiniteDimensional K V] (s : V ≃ₗ[K] V) (S : Submodule K V)
    (h : ∀ x ∈ S, s x ∈ S) {x : V} (hx : x ∈ S) : s.symm x ∈ S := by
  have h1 : S.map (s : V →ₗ[K] V) = S := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    · exact LinearEquiv.finrank_map_eq s S
  rw [← h1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Establish `hle : (F.Xa a).map (s : V →ₗ[K] V) ≤ F.Xa a`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `_root_.GlobalTheory.UnipStab.map_Xa hs a hw`. Establish `heq` using `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s (F.Xa a))`. Rewrite `hx` using `[← heq]`.

Take `⟨w, hw, rfl⟩` from `hx`. Simplify using `using hw`.
-/
private theorem hermFlagUnipotent_symm_maps_graded_lemma_5 [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : F.InN (s : V →ₗ[K] V)) (a : ℕ) {x : V} (hx : x ∈ F.Xa a) : s.symm x ∈ F.Xa a := by
  have hle : (F.Xa a).map (s : V →ₗ[K] V) ≤ F.Xa a := by
    rintro _ ⟨w, hw, rfl⟩
    exact _root_.GlobalTheory.UnipStab.map_Xa hs a hw
  have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s (F.Xa a))
  rw [← heq] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  simpa using hw

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Establish `hs'` using `hs`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ⊢`. Take `⟨hsi, -, hse, hsy⟩` from `hs`. Use `⟨fun x y => ?_, (s⁻¹).bijective, fun a => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `H.B (s.symm x) (s.symm y) = H.B x y`.

Use `hsi (s.symm x) (s.symm y)` as an intermediate fact. Simplify using `using this.symm`. Express the relevant statement in the definitionally equal form `s.symm (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a`. Establish `h` using `Submodule.neg_mem _ (hermFlagUnipotent_symm_maps_graded_lemma_5 hs' a (hse a))`. Establish `heq : -(s.symm ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc)) = s.symm (F.e a.castSucc) - F.e a.castSucc`.

Simplify using the standard rewrite rules. Rewrite `h` using `[heq]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `s.symm y - y ∈ F.X`. Establish `hperp : ∀ a : Fin r, H.B (F.e a.castSucc) (s.symm y) = 0`. Introduce `a`.

Establish `h1` using `hsi (F.e a.castSucc) (s.symm y)`. Establish `h2 : H.B ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc) y = 0`. Use `_root_.GlobalTheory.UnipStab.orth_X F hy ?_` and prove the remaining obligations. Rewrite using `[hermFlag_isotropic_eq_graded_lemma_4 F]`. Conclude with `_root_.GlobalTheory.UnipStab.Xa_mono F a.isLt.le (hse a)`.

Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1`. Rewrite using `[← h1]`. Simplify `h2` using `[hy a]`. Establish `h3` using `Submodule.neg_mem _ (hsy (s.symm y) hperp)`. Simplify using `using h3`.
-/
theorem _root_.GlobalTheory.UnipStab.inN_inv [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : F.InN (s : V →ₗ[K] V)) : F.InN ((s⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hs' := hs
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ⊢
  obtain ⟨hsi, -, hse, hsy⟩ := hs
  refine ⟨fun x y => ?_, (s⁻¹).bijective, fun a => ?_, fun y hy => ?_⟩
  · change H.B (s.symm x) (s.symm y) = H.B x y
    have := hsi (s.symm x) (s.symm y)
    simpa using this.symm
  · change s.symm (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a
    have h := Submodule.neg_mem _ (hermFlagUnipotent_symm_maps_graded_lemma_5 hs' a (hse a))
    have heq : -(s.symm ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc)) =
        s.symm (F.e a.castSucc) - F.e a.castSucc := by
      simp
    rwa [heq] at h
  · change s.symm y - y ∈ F.X
    have hperp : ∀ a : Fin r, H.B (F.e a.castSucc) (s.symm y) = 0 := by
      intro a
      have h1 := hsi (F.e a.castSucc) (s.symm y)
      have h2 : H.B ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc) y = 0 := by
        refine _root_.GlobalTheory.UnipStab.orth_X F hy ?_
        rw [hermFlag_isotropic_eq_graded_lemma_4 F]
        exact _root_.GlobalTheory.UnipStab.Xa_mono F a.isLt.le (hse a)
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      simpa [hy a] using h2
    have h3 := Submodule.neg_mem _ (hsy (s.symm y) hperp)
    simpa using h3

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg`. Take `⟨-, -, he, -⟩` from `hg`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, rfl⟩` from `hx`. Establish `hb' : (b : ℕ) < k + 1` using `hb`. Conclude with `_root_.GlobalTheory.UnipStab.Xa_mono F (by omega) (he b)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz`.

Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `add_mem hx hz`. Consider the case `smul c x _ hx`. Rewrite using `[map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
private theorem hermFlagUnipotent_sub_lowers_graded_lemma_6 {g : V →ₗ[K] V} (hg : F.InN g) (k : ℕ)
    {x : V} (hx : x ∈ F.Xa (k + 1)) : g x - x ∈ F.Xa k := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg
  obtain ⟨-, -, he, -⟩ := hg
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : (b : ℕ) < k + 1 := hb
    exact _root_.GlobalTheory.UnipStab.Xa_mono F (by omega) (he b)
  | zero => simp
  | add x z _ _ hx hz =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hx hz
  | smul c x _ hx =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx`. Simplify using `using hx`.
-/
private theorem hermFlag_graded_zero_lemma_7 {x : V} (hx : x ∈ F.Xa 0) : x = 0 := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  simpa using hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in

/- English proof (translation)
Establish `hs'` using `hs`. Establish `hinv` using `_root_.GlobalTheory.UnipStab.inN_inv hs`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs hinv`. Take `⟨hsi, -, -, hsy⟩` from `hs`. Take `⟨-, -, hie, -⟩` from `hinv`.

Use `set u : V →ₗ[K] V := (s : V →ₗ[K] V) - 1 with hu`. Establish `hu_apply : ∀ v, u v = s v - v` using `fun v => by simp [hu]`. Establish `hdown : ∀ n ≤ r, ∀ v : V, ∀ b : Fin r, (b : ℕ) < n → H.B (F.e b.castSucc) ((u ^ n) v) = 0`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro _ v b hb`. Conclude with `absurd hb (Nat.not_lt_zero _)`. Consider the case `succ n ih`. Introduce `hn v b hb`. Establish `hwperp` using `ih (by omega) v`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Generalize the expression as in `(u ^ n) v = w at hwperp ⊢`. Rewrite using `[hu_apply, map_sub]`. Establish `h1` using `hsi (s.symm (F.e b.castSucc)) w`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1`.

Rewrite using `[h1]`. Establish `hx : s.symm (F.e b.castSucc) - F.e b.castSucc ∈ F.Xa n` using `_root_.GlobalTheory.UnipStab.Xa_mono F (by omega) (hie b)`. Establish `h2` using `hermFlag_orthogonal_graded_of_basis_lemma_2 F hwperp hx`. Rewrite `h2` using `[map_sub, LinearMap.sub_apply]`. Conclude with `h2`.

Establish `hX : ∀ v, u ((u ^ r) v) ∈ F.Xa r` using `fun v => by`. Rewrite using `[hu_apply]`. Conclude with `hsy _ (fun b => hdown r le_rfl v b b.isLt)`. Establish `hup : ∀ n m : ℕ, ∀ x ∈ F.Xa (m + n), (u ^ n) x ∈ F.Xa m`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro m x hx`. Simplify using `using hx`. Consider the case `succ n ih`. Introduce `m x hx`.

Rewrite using `[pow_succ, Module.End.mul_apply]`. Use `ih m _ ?_` and prove the remaining obligations. Rewrite using `[hu_apply]`. Rewrite `hx` using `[← add_assoc]`. Conclude with `hermFlagUnipotent_sub_lowers_graded_lemma_6 hs' _ hx`.

Establish `h21 : 2 * r + 1 = r + (1 + r)` using `by omega`. Rewrite using `[h21, pow_add, pow_add, pow_one]`. Use extensionality with `v`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]`. Apply `hermFlag_graded_zero_lemma_7 F` to reduce the goal to its premises.

Apply `hup r 0` to reduce the goal to its premises. Rewrite using `[zero_add]`. Conclude with `hX v`.
-/
theorem _root_.GlobalTheory.UnipStab.pow_eq_zero [FiniteDimensional K V]
    {s : V ≃ₗ[K] V} (hs : F.InN (s : V →ₗ[K] V)) :
    ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := by
  have hs' := hs
  have hinv := _root_.GlobalTheory.UnipStab.inN_inv hs
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs hinv
  obtain ⟨hsi, -, -, hsy⟩ := hs
  obtain ⟨-, -, hie, -⟩ := hinv
  set u : V →ₗ[K] V := (s : V →ₗ[K] V) - 1 with hu
  have hu_apply : ∀ v, u v = s v - v := fun v => by simp [hu]
  have hdown : ∀ n ≤ r, ∀ v : V, ∀ b : Fin r, (b : ℕ) < n →
      H.B (F.e b.castSucc) ((u ^ n) v) = 0 := by
    intro n
    induction n with
    | zero => intro _ v b hb; exact absurd hb (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn v b hb
      have hwperp := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply]
      generalize (u ^ n) v = w at hwperp ⊢
      rw [hu_apply, map_sub]
      have h1 := hsi (s.symm (F.e b.castSucc)) w
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
      rw [h1]
      have hx : s.symm (F.e b.castSucc) - F.e b.castSucc ∈ F.Xa n :=
        _root_.GlobalTheory.UnipStab.Xa_mono F (by omega) (hie b)
      have h2 := hermFlag_orthogonal_graded_of_basis_lemma_2 F hwperp hx
      rw [map_sub, LinearMap.sub_apply] at h2
      exact h2
  have hX : ∀ v, u ((u ^ r) v) ∈ F.Xa r := fun v => by
    rw [hu_apply]
    exact hsy _ (fun b => hdown r le_rfl v b b.isLt)
  have hup : ∀ n m : ℕ, ∀ x ∈ F.Xa (m + n), (u ^ n) x ∈ F.Xa m := by
    intro n
    induction n with
    | zero => intro m x hx; simpa using hx
    | succ n ih =>
      intro m x hx
      rw [pow_succ, Module.End.mul_apply]
      refine ih m _ ?_
      rw [hu_apply]
      rw [← add_assoc] at hx
      exact hermFlagUnipotent_sub_lowers_graded_lemma_6 hs' _ hx
  have h21 : 2 * r + 1 = r + (1 + r) := by omega
  rw [h21, pow_add, pow_add, pow_one]
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]
  apply hermFlag_graded_zero_lemma_7 F
  apply hup r 0
  rw [zero_add]
  exact hX v

/- English proof (translation)
Use `hg.2.2.2 y fun a => ?_` and prove the remaining obligations. Rewrite using `[← H.herm, (mem_perp_iff H S y).1 hy _ (hS (e_mem_X F a)), star_zero]`.
-/
theorem sub_mem_X {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hS : F.X ≤ S) {y : V}
    (hy : y ∈ perp H S) : g y - y ∈ F.X := by
  refine hg.2.2.2 y fun a => ?_
  rw [← H.herm, (mem_perp_iff H S y).1 hy _ (hS (e_mem_X F a)), star_zero]

end One

section Two

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Unfold `_root_.GlobalTheory.DegCnt.NF.R at h`. Proceed by induction on `h using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`.

Consider the case `one => exact ⟨_root_.GlobalTheory.UnipStab.inN_one, _root_.GlobalTheory.UnipStab.inN_one⟩`. Consider the case `mul x y _ _ hx hy`. Conclude with `⟨_root_.GlobalTheory.UnipStab.inN_mul hx.1 hy.1, _root_.GlobalTheory.UnipStab.inN_mul hx.2 hy.2⟩`. Consider the case `inv x _ hx => exact ⟨_root_.GlobalTheory.UnipStab.inN_inv hx.1, _root_.GlobalTheory.UnipStab.inN_inv hx.2⟩`. Introduce `h`.

Unfold `_root_.GlobalTheory.DegCnt.NF.R`. Conclude with `Subgroup.subset_closure h`.
-/
theorem _root_.GlobalTheory.UnipStab.mem_R (s : V ≃ₗ[K] V) :
    s ∈ N.R ↔
      N.F.InN (s : V →ₗ[K] V) ∧
        N.F'.InN (s : V →ₗ[K] V) := by
  constructor
  · intro h
    unfold _root_.GlobalTheory.DegCnt.NF.R at h
    induction h using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨_root_.GlobalTheory.UnipStab.inN_one, _root_.GlobalTheory.UnipStab.inN_one⟩
    | mul x y _ _ hx hy =>
      exact ⟨_root_.GlobalTheory.UnipStab.inN_mul hx.1 hy.1, _root_.GlobalTheory.UnipStab.inN_mul hx.2 hy.2⟩
    | inv x _ hx => exact ⟨_root_.GlobalTheory.UnipStab.inN_inv hx.1, _root_.GlobalTheory.UnipStab.inN_inv hx.2⟩
  · intro h
    unfold _root_.GlobalTheory.DegCnt.NF.R
    exact Subgroup.subset_closure h

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.DegCnt.NF.fixing`. Rewrite using `[mem_fixingSubgroup_iff]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.UnipStab.mem_fixing (S : Submodule K V) (t : V ≃ₗ[K] V) :
    t ∈ N.fixing S ↔ ∀ v ∈ S, t v = v := by
  unfold _root_.GlobalTheory.DegCnt.NF.fixing
  rw [mem_fixingSubgroup_iff]
  rfl

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Take `⟨h1, h2⟩` from `(_root_.GlobalTheory.UnipStab.mem_R N s).1 hs`. Unfold `_root_.GlobalTheory.HermLat.uPerp at hy`. Rewrite `hy` using `[_root_.GlobalTheory.HermLat.mem_perp_iff]`. Establish `hF : ∀ a : Fin r, H.B (N.F.e a.castSucc) y = 0` using `fun a => by`. Rewrite using `[← H.herm, hy _ (Submodule.mem_sup_left (_root_.GlobalTheory.UnipStab.e_mem_X _ a)), star_zero]`.

Establish `hF' : ∀ a : Fin r, H.B (N.F'.e a.castSucc) y = 0` using `fun a => by`. Rewrite using `[← H.herm, hy _ (Submodule.mem_sup_right (_root_.GlobalTheory.UnipStab.e_mem_X _ a)), star_zero]`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.II`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at h1 h2`. Conclude with `Submodule.mem_inf.mpr ⟨h1.2.2.2 y hF, h2.2.2.2 y hF'⟩`.
-/
theorem _root_.GlobalTheory.UnipStab.sub_mem_II {s : V ≃ₗ[K] V}
    (hs : s ∈ N.R) {y : V}
    (hy : y ∈ _root_.GlobalTheory.HermLat.uPerp N.F N.F') :
    s y - y ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.UnipStab.mem_R N s).1 hs
  unfold _root_.GlobalTheory.HermLat.uPerp at hy
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hy
  have hF : ∀ a : Fin r, H.B (N.F.e a.castSucc) y = 0 := fun a => by
    rw [← H.herm, hy _ (Submodule.mem_sup_left (_root_.GlobalTheory.UnipStab.e_mem_X _ a)),
      star_zero]
  have hF' : ∀ a : Fin r, H.B (N.F'.e a.castSucc) y = 0 := fun a => by
    rw [← H.herm, hy _ (Submodule.mem_sup_right (_root_.GlobalTheory.UnipStab.e_mem_X _ a)),
      star_zero]
  unfold _root_.Formalism.HermitianLatticeCounting.S6.II
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at h1 h2
  exact Submodule.mem_inf.mpr ⟨h1.2.2.2 y hF, h2.2.2.2 y hF'⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `hle : _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' ≤ (_root_.Formalism.HermitianLatticeCounting.S6.V0 F F').comap g`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.V0`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[Submodule.mem_comap]`.

Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (hermFlagUnipotent_maps_isotropic_lemma_3 hg hy))`. Introduce `y hy`. Rewrite using `[Submodule.mem_comap]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (hermFlagUnipotent_maps_isotropic_lemma_3 hg' hy))`. Simplify using `only [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : g F.z - F.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}` using `Submodule.mem_sup_left (Submodule.mem_sup_left (_root_.GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem hg))`. Establish `h2 : F.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}` using `Submodule.mem_sup_right (Submodule.subset_span (by simp))`. Simplify using `using add_mem h1 h2`. Establish `h1 : g F'.z - F'.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}` using `Submodule.mem_sup_left (Submodule.mem_sup_right (_root_.GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem hg'))`.

Establish `h2 : F'.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}` using `Submodule.mem_sup_right (Submodule.subset_span (by simp))`. Simplify using `using add_mem h1 h2`. Conclude with `hle hx`.
-/
private theorem hermFramePairCommonUnipotent_maps_span_lemma_9 {F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} {g : V →ₗ[K] V}
    (hg : F.InN g) (hg' : F'.InN g) {x : V} (hx : x ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 F F') : g x ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' := by
  have hle : _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' ≤ (_root_.Formalism.HermitianLatticeCounting.S6.V0 F F').comap g := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      rw [Submodule.mem_comap]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (hermFlagUnipotent_maps_isotropic_lemma_3 hg hy))
    · intro y hy
      rw [Submodule.mem_comap]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (hermFlagUnipotent_maps_isotropic_lemma_3 hg' hy))
    · simp only [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff,
        SetLike.mem_coe, Submodule.mem_comap]
      refine ⟨?_, ?_⟩
      · have h1 : g F.z - F.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z} :=
          Submodule.mem_sup_left (Submodule.mem_sup_left
            (_root_.GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem hg))
        have h2 : F.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z} :=
          Submodule.mem_sup_right (Submodule.subset_span (by simp))
        simpa using add_mem h1 h2
      · have h1 : g F'.z - F'.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z} :=
          Submodule.mem_sup_left (Submodule.mem_sup_right
            (_root_.GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem hg'))
        have h2 : F'.z ∈ F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z} :=
          Submodule.mem_sup_right (Submodule.subset_span (by simp))
        simpa using add_mem h1 h2
  exact hle hx

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.DegCnt.NF.R1 at ht ⊢`. Rewrite `ht`, the goal using `[Subgroup.mem_inf]`. Use `⟨mul_mem (mul_mem hs ht.1) (inv_mem hs), ?_⟩` and prove the remaining obligations. Establish `ht2` using `(_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht.2`. Rewrite using `[_root_.GlobalTheory.UnipStab.mem_fixing]`.

Introduce `v hv`. Establish `hinv` using `(_root_.GlobalTheory.UnipStab.mem_R N s⁻¹).1 (inv_mem hs)`. Establish `hmem : s.symm v ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F'` using `hermFramePairCommonUnipotent_maps_span_lemma_9 hinv.1 hinv.2 hv`. Express the relevant statement in the definitionally equal form `s (t (s.symm v)) = v`. Rewrite using `[ht2 _ hmem, LinearEquiv.apply_symm_apply]`.
-/
private theorem hermFramePairCommonUnipotent_conj_mem_fixingBoth_lemma_8 {s t : V ≃ₗ[K] V}
    (hs : s ∈ N.R) (ht : t ∈ N.R1) :
    s * t * s⁻¹ ∈ N.R1 := by
  unfold _root_.GlobalTheory.DegCnt.NF.R1 at ht ⊢
  rw [Subgroup.mem_inf] at ht ⊢
  refine ⟨mul_mem (mul_mem hs ht.1) (inv_mem hs), ?_⟩
  have ht2 := (_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht.2
  rw [_root_.GlobalTheory.UnipStab.mem_fixing]
  intro v hv
  have hinv := (_root_.GlobalTheory.UnipStab.mem_R N s⁻¹).1 (inv_mem hs)
  have hmem : s.symm v ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' :=
    hermFramePairCommonUnipotent_maps_span_lemma_9 hinv.1 hinv.2 hv
  change s (t (s.symm v)) = v
  rw [ht2 _ hmem, LinearEquiv.apply_symm_apply]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.DegCnt.NF.ZI at ht ⊢`. Rewrite `ht`, the goal using `[Subgroup.mem_inf]`. Use `⟨hermFramePairCommonUnipotent_conj_mem_fixingBoth_lemma_8 N hs ht.1, ?_⟩` and prove the remaining obligations. Establish `ht1` using `ht.1`. Unfold `_root_.GlobalTheory.DegCnt.NF.R1 at ht1`.

Rewrite `ht1` using `[Subgroup.mem_inf]`. Establish `hfix1` using `(_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht1.2`. Establish `hfix2` using `(_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht.2`. Rewrite using `[_root_.GlobalTheory.UnipStab.mem_fixing]`. Introduce `v hv`.

Establish `hvperp : v ∈ _root_.GlobalTheory.HermLat.uPerp N.F N.F'`. Establish `hv'` using `hv`. Unfold `_root_.GlobalTheory.DegCnt.NF.Wt at hv'`. Unfold `_root_.GlobalTheory.HermLat.uPerp`. Rewrite `hv'`, the goal using `[_root_.GlobalTheory.HermLat.mem_perp_iff]`.

Introduce `x hx`. Apply `hv'` to reduce the goal to its premises. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.V0`. Conclude with `Submodule.mem_sup_left hx`.

Establish `hw` using `_root_.GlobalTheory.UnipStab.sub_mem_II N (inv_mem hs) hvperp`. Establish `hw0 : s.symm v - v ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F'`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.II at hw`. Unfold `_root_.Formalism.HermitianLatticeCounting.S6.V0`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_inf.mp hw).1)`.

Establish `htv : t v = v` using `hfix2 v hv`. Establish `htw : t (s.symm v - v) = s.symm v - v` using `hfix1 _ hw0`. Rewrite `htw` using `[map_sub, htv, sub_left_inj]`. Express the relevant statement in the definitionally equal form `s (t (s.symm v)) = v`. Rewrite using `[htw, LinearEquiv.apply_symm_apply]`.
-/
theorem _root_.GlobalTheory.UnipStab.conj_ZI {s t : V ≃ₗ[K] V}
    (hs : s ∈ N.R)
    (ht : t ∈ N.ZI) :
    s * t * s⁻¹ ∈ N.ZI := by
  unfold _root_.GlobalTheory.DegCnt.NF.ZI at ht ⊢
  rw [Subgroup.mem_inf] at ht ⊢
  refine ⟨hermFramePairCommonUnipotent_conj_mem_fixingBoth_lemma_8 N hs ht.1, ?_⟩
  have ht1 := ht.1
  unfold _root_.GlobalTheory.DegCnt.NF.R1 at ht1
  rw [Subgroup.mem_inf] at ht1
  have hfix1 := (_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht1.2
  have hfix2 := (_root_.GlobalTheory.UnipStab.mem_fixing N _ t).1 ht.2
  rw [_root_.GlobalTheory.UnipStab.mem_fixing]
  intro v hv
  have hvperp : v ∈ _root_.GlobalTheory.HermLat.uPerp N.F N.F' := by
    have hv' := hv
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hv'
    unfold _root_.GlobalTheory.HermLat.uPerp
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hv' ⊢
    intro x hx
    apply hv'
    apply Submodule.mem_sup_left
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0
    exact Submodule.mem_sup_left hx
  have hw := _root_.GlobalTheory.UnipStab.sub_mem_II N (inv_mem hs) hvperp
  have hw0 : s.symm v - v ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hw
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_inf.mp hw).1)
  have htv : t v = v := hfix2 v hv
  have htw : t (s.symm v - v) = s.symm v - v := hfix1 _ hw0
  rw [map_sub, htv, sub_left_inj] at htw
  change s (t (s.symm v)) = v
  rw [htw, LinearEquiv.apply_symm_apply]

end Two

open NumberField in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H _ r N`. Use `⟨_root_.GlobalTheory.UnipStab.mem_R N, fun s hs y hy => _root_.GlobalTheory.UnipStab.sub_mem_II N hs hy, fun s hs t ht => hermFramePairCommonUnipotent_conj_mem_fixingBoth_lemma_8 N hs ht, fun s hs t ht => _root_.GlobalTheory.UnipStab.conj_ZI N hs ht, fun s hs => _root_.GlobalTheo …` and prove the remaining obligations.
-/
theorem _root_.GlobalTheory.UnipStab.common_unipotent_stabiliser : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r), (∀ s : V ≃ₗ[K] V, s ∈ N.R ↔ N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)) ∧ (∀ s ∈ N.R, ∀ y ∈ _root_.GlobalTheory.HermLat.uPerp N.F N.F', s y - y ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F') ∧ (∀ s ∈ N.R, ∀ t ∈ N.R1, s * t * s⁻¹ ∈ N.R1) ∧ (∀ s ∈ N.R, ∀ t ∈ N.ZI, s * t * s⁻¹ ∈ N.ZI) ∧ ∀ s ∈ N.R, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := by
  intro K V _ _ _ _ _ _ _ _ H _ r N
  refine ⟨_root_.GlobalTheory.UnipStab.mem_R N,
    fun s hs y hy => _root_.GlobalTheory.UnipStab.sub_mem_II N hs hy,
    fun s hs t ht => hermFramePairCommonUnipotent_conj_mem_fixingBoth_lemma_8 N hs ht,
    fun s hs t ht => _root_.GlobalTheory.UnipStab.conj_ZI N hs ht,
    fun s hs => _root_.GlobalTheory.UnipStab.pow_eq_zero
      ((_root_.GlobalTheory.UnipStab.mem_R N s).1 hs).1⟩

end GlobalTheory.UnipStab
