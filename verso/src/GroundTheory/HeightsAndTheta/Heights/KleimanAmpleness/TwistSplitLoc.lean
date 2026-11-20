import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise AddMonoidAlgebra

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[map_X]`. Conclude with `X_mem_monos hi`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem map_C_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s ∈ monos (S := MvPolynomial (Fin (r + 1)) S) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]; exact X_mem_monos hi
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[aeval_X]`. Conclude with `(mem_support x).mp (hI hi)`.

Consider the case `one => simp`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_ne_zero ha hb`.
-/
theorem eval_ne_zero_of_subset {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {s : Poly S N}
    (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Conclude with `⟨X i, X_mem_monos hi, 1, isHomogeneous_X S i, (map_X _ _).symm, by rw [xyHom_X, aeval_X, Nat.cast_one]⟩`. Consider the case `one`.

Conclude with `⟨1, one_mem _, 0, isHomogeneous_one _ _, (map_one _).symm, by rw [map_one, map_one, AddMonoidAlgebra.one_def]; rfl⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨a₀, ha₀, ea, hae, rfl, hxa⟩` from `ha`. Take `⟨b₀, hb₀, eb, hbe, rfl, hxb⟩` from `hb`. Use `⟨a₀ * b₀, mul_mem ha₀ hb₀, ea + eb, hae.mul hbe, (map_mul _ _ _).symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hxa, hxb, single_mul_single, map_mul]`. Use `congr 1`.
-/
theorem xyHom_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly (MvPolynomial (Fin (r + 1)) S) N}
    (hs : s ∈ monos I) : ∃ s₀ ∈ monos (S := S) I, ∃ e : ℕ, s₀.IsHomogeneous e ∧
      s = MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀ ∧
      xyHom S x η s = single ((0 : ℤ), (e : ℤ)) (aeval x s₀) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, X_mem_monos hi, 1, isHomogeneous_X S i, (map_X _ _).symm,
      by rw [xyHom_X, aeval_X, Nat.cast_one]⟩
  | one =>
    exact ⟨1, one_mem _, 0, isHomogeneous_one _ _, (map_one _).symm,
      by rw [map_one, map_one, AddMonoidAlgebra.one_def]; rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, ea, hae, rfl, hxa⟩ := ha
    obtain ⟨b₀, hb₀, eb, hbe, rfl, hxb⟩ := hb
    refine ⟨a₀ * b₀, mul_mem ha₀ hb₀, ea + eb, hae.mul hbe, (map_mul _ _ _).symm, ?_⟩
    rw [map_mul, hxa, hxb, single_mul_single, map_mul]
    congr 1

/- English proof (translation)
Take `⟨s₀, hs₀, e, -, -, h⟩` from `xyHom_of_mem_monos η hs`. Rewrite using `[h]`. Establish `hv` using `eval_ne_zero_of_subset hI hs₀`. Use `isUnit_iff_exists_inv.mpr ⟨single ((0 : ℤ), -(e : ℤ)) (aeval x s₀)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[single_mul_single, mul_inv_cancel₀ hv, AddMonoidAlgebra.one_def]`.

Use `congr 1`. Apply the tactic sequence `ext <;> simp`.
-/
theorem isUnit_xyHom {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly (MvPolynomial (Fin (r + 1)) S) N} (hs : s ∈ monos I) : IsUnit (xyHom S x η s) := by
  obtain ⟨s₀, hs₀, e, -, -, h⟩ := xyHom_of_mem_monos η hs
  rw [h]
  have hv := eval_ne_zero_of_subset hI hs₀
  refine isUnit_iff_exists_inv.mpr ⟨single ((0 : ℤ), -(e : ℤ)) (aeval x s₀)⁻¹, ?_⟩
  rw [single_mul_single, mul_inv_cancel₀ hv, AddMonoidAlgebra.one_def]
  congr 1
  ext <;> simp

variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

/- English proof (translation)
Rewrite using `[Module.End.isUnit_iff]`. Establish `hu : IsUnit (UT.ofL (x` using `x) (η := η) (xyHom S x η s)) := isUnit_xyHom η hI s.2`. Establish `: ⇑(algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N) (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) = fun v => UT.ofL (x` using `x) (η := η) (xyHom S x η s) * v := by`. Use function extensionality and compare the values at `v`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hu.unit.mulLeft_bijective`.
-/
theorem locEmb_isUnit {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) :
    IsUnit (algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) := by
  rw [Module.End.isUnit_iff]
  have hu : IsUnit (UT.ofL (x := x) (η := η) (xyHom S x η s)) := isUnit_xyHom η hI s.2
  have : ⇑(algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) =
      fun v => UT.ofL (x := x) (η := η) (xyHom S x η s) * v := by
    funext v; rfl
  rw [this]
  exact hu.unit.mulLeft_bijective

def locEmb (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I →ₗ[Poly (MvPolynomial (Fin (r + 1)) S) N] UT x η :=
  LocalizedModule.lift (monos I) (twSub η M₀).subtype (locEmb_isUnit η hI)

/- English proof (translation)
Establish `h0 : locEmb η M₀ I hI (LocalizedModule.mk m s) = (locEmb_isUnit η hI s).unit⁻¹.1 ((twSub η M₀).subtype m)` using `LocalizedModule.lift_mk _ _ _ _ _`. Rewrite using `[h0]`. Establish `key` using `congrArg (fun f : Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η) => f ((twSub η M₀).subtype m)) (IsUnit.mul_val_inv (locEmb_isUnit η hI s))`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply] at key`. Conclude with `key`.
-/
theorem xyHom_mul_locEmb_mk {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (m : TwM η M₀)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) :
    xyHom S x η s * UT.toL (locEmb η M₀ I hI (LocalizedModule.mk m s)) = m.val := by
  have h0 : locEmb η M₀ I hI (LocalizedModule.mk m s) =
      (locEmb_isUnit η hI s).unit⁻¹.1 ((twSub η M₀).subtype m) :=
    LocalizedModule.lift_mk _ _ _ _ _
  rw [h0]
  have key := congrArg (fun f : Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η) =>
    f ((twSub η M₀).subtype m)) (IsUnit.mul_val_inv (locEmb_isUnit η hI s))
  simp only [Module.End.mul_apply, Module.End.one_apply] at key
  exact key

/- English proof (translation)
Establish `key` using `xyHom_mul_locEmb_mk η M₀ hI m s`. Rewrite `key` using `[h]`. Rewrite using `[← key, ← mul_assoc, single_mul_single, inv_mul_cancel₀ hv]`. Establish `: single (((0 : ℤ), -(e : ℤ)) + ((0 : ℤ), (e : ℤ))) (1 : Ω) = 1`. Apply the tactic sequence `rw [AddMonoidAlgebra.one_def]; congr 1; ext <;> simp`.

Rewrite using `[this, one_mul]`.
-/
theorem locEmb_mk {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (m : TwM η M₀)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) {e : ℕ} {v : Ω}
    (h : xyHom S x η s = single ((0 : ℤ), (e : ℤ)) v) (hv : v ≠ 0) :
    UT.toL (locEmb η M₀ I hI (LocalizedModule.mk m s)) = single ((0 : ℤ), -(e : ℤ)) v⁻¹ * m.val := by
  have key := xyHom_mul_locEmb_mk η M₀ hI m s
  rw [h] at key
  rw [← key, ← mul_assoc, single_mul_single, inv_mul_cancel₀ hv]
  have : single (((0 : ℤ), -(e : ℤ)) + ((0 : ℤ), (e : ℤ))) (1 : Ω) = 1 := by
    rw [AddMonoidAlgebra.one_def]; congr 1; ext <;> simp
  rw [this, one_mul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `UT.toL (locEmb η M₀ I hI ((algebraMap _ (Poly (MvPolynomial (Fin (r + 1)) S) N) c) • w)) = _`. Rewrite using `[LinearMap.map_smul, UT.smul_def, MvPolynomial.algebraMap_eq, xyHom_C]`.
-/
theorem locEmb_smul' {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (c : MvPolynomial (Fin (r + 1)) S)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    UT.toL (locEmb η M₀ I hI (c • w)) = yHom S η c * UT.toL (locEmb η M₀ I hI w) := by
  change UT.toL (locEmb η M₀ I hI ((algebraMap _ (Poly (MvPolynomial (Fin (r + 1)) S) N) c) • w)) = _
  rw [LinearMap.map_smul, UT.smul_def, MvPolynomial.algebraMap_eq, xyHom_C]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Proceed by induction on `w using LocalizedModule.induction_on with`. Consider the case `h m s`. Establish `key` using `xyHom_mul_locEmb_mk η M₀ hI m s`.

Rewrite `key` using `[hw]`. Establish `hm : m = 0` using `TwM.val_injective (by rw [← key, TwM.val_zero]; exact mul_zero _)`. Rewrite using `[hm, LocalizedModule.zero_mk]`. Both sides reduce to the same expression.
-/
theorem locEmb_injective {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) :
    Function.Injective (locEmb η M₀ I hI) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have key := xyHom_mul_locEmb_mk η M₀ hI m s
    rw [hw] at key
    have hm : m = 0 := TwM.val_injective (by rw [← key, TwM.val_zero]; exact mul_zero _)
    rw [hm, LocalizedModule.zero_mk]
    rfl

/- English proof (translation)
Proceed by induction on `w using LocalizedModule.induction_on with`. Consider the case `h m s`. Rewrite using `[locRes_mk]`. Establish `hu` using `isUnit_xyHom η hJ (monos_mono h s.2)`. Establish `k1` using `xyHom_mul_locEmb_mk η M₀ hJ m ⟨(s : Poly _ N), monos_mono h s.2⟩`.

Establish `k2` using `xyHom_mul_locEmb_mk η M₀ hI m s`. Conclude with `hu.mul_left_cancel (k1.trans k2.symm)`.
-/
theorem locEmb_locRes {I J : Finset (Fin (N + 1))} (hI : I ⊆ support x) (hJ : J ⊆ support x) (h : I ⊆ J)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    locEmb η M₀ J hJ (locRes h w) = locEmb η M₀ I hI w := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    have hu := isUnit_xyHom η hJ (monos_mono h s.2)
    have k1 := xyHom_mul_locEmb_mk η M₀ hJ m ⟨(s : Poly _ N), monos_mono h s.2⟩
    have k2 := xyHom_mul_locEmb_mk η M₀ hI m s
    exact hu.mul_left_cancel (k1.trans k2.symm)

/- English proof (translation)
Take `⟨i, hiJ, hi⟩` from `Finset.not_subset.mp hJ`. Establish `hxi : x i = 0`. Assume the negation of the conclusion as `h`. Conclude with `hi ((mem_support x).mpr h)`. Establish `hX : ∀ m : TwM η M₀, (X i : Poly (MvPolynomial (Fin (r + 1)) S) N) • m = 0` using `fun m => TwM.val_injective (by rw [TwM.val_smul, xyHom_X, hxi, single_zero, zero_mul, TwM.val_zero])`.

Establish `hz : ∀ w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J, w = 0`. Introduce `w`. Proceed by induction on `w using LocalizedModule.induction_on with`. Consider the case `h m s`. Express the relevant statement in the definitionally equal form `(LocalizedModule.mk m s : LocalizedModule (monos J) (TwM η M₀)) = (0 : LocalizedModule (monos J) (TwM η M₀))`.

Rewrite using `[← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]`. Use `⟨⟨X i, X_mem_monos hiJ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_zero, smul_zero]`. Conclude with `hX _`. Conclude with `⟨fun w w' => by rw [hz w, hz w']⟩`.
-/
theorem twLocMod_subsingleton {J : Finset (Fin (N + 1))} (hJ : ¬ J ⊆ support x) :
    Subsingleton (LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J) := by
  obtain ⟨i, hiJ, hi⟩ := Finset.not_subset.mp hJ
  have hxi : x i = 0 := by
    by_contra h; exact hi ((mem_support x).mpr h)
  have hX : ∀ m : TwM η M₀, (X i : Poly (MvPolynomial (Fin (r + 1)) S) N) • m = 0 := fun m =>
    TwM.val_injective (by rw [TwM.val_smul, xyHom_X, hxi, single_zero, zero_mul, TwM.val_zero])
  have hz : ∀ w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J, w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h m s =>
      change (LocalizedModule.mk m s : LocalizedModule (monos J) (TwM η M₀)) =
        (0 : LocalizedModule (monos J) (TwM η M₀))
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hiJ⟩, ?_⟩
      rw [smul_zero, smul_zero]
      exact hX _
  exact ⟨fun w w' => by rw [hz w, hz w']⟩

def LocGood (c : ℤ) (I : Finset (Fin (N + 1))) (W : LaurUT Ω) : Prop :=
  ∀ b : ℤ, W.coeff (b, c) ∈ twLocPart η M₀ b c I

/- English proof (translation)
Proceed by induction on `c' using MvPolynomial.induction_on generalizing W with`. Consider the case `C a`. Introduce `b`. Rewrite using `[yHom_C, coeff_single_mul_sub, sub_zero]`. Use `Submodule.smul_mem _ a (hW b)` as an intermediate fact.

Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis. Consider the case `add p q hp hq`. Introduce `b`. Rewrite using `[map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]`. Conclude with `add_mem (hp hW b) (hq hW b)`.

Consider the case `mul_X p j hp`. Rewrite using `[map_mul, mul_assoc]`. Apply `hp` to reduce the goal to its premises. Introduce `b`. Rewrite using `[yHom_X, coeff_single_mul_sub]`.

Use `twLocPart_eta_mul η M₀ j (hW (b - 1))` as an intermediate fact. Simplify using `using this`.
-/
theorem locGood_yHom_mul {c : ℤ} {I : Finset (Fin (N + 1))} (c' : MvPolynomial (Fin (r + 1)) S)
    {W : LaurUT Ω} (hW : LocGood η M₀ c I W) : LocGood η M₀ c I (yHom S η c' * W) := by
  induction c' using MvPolynomial.induction_on generalizing W with
  | C a =>
    intro b
    rw [yHom_C, coeff_single_mul_sub, sub_zero]
    have := Submodule.smul_mem _ a (hW b)
    rwa [Algebra.smul_def] at this
  | add p q hp hq =>
    intro b
    rw [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem (hp hW b) (hq hW b)
  | mul_X p j hp =>
    rw [map_mul, mul_assoc]
    apply hp
    intro b
    rw [yHom_X, coeff_single_mul_sub]
    have := twLocPart_eta_mul η M₀ j (hW (b - 1))
    simpa using this

/- English proof (translation)
Use `Submodule.span_induction (p := fun w _ => LocGood η M₀ c I.1 (UT.toL (locEmb η M₀ I.1 hI w))) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, -, hse, -, rfl⟩`. Take `⟨s₀, hs₀, e', hs₀e, hss, hxs⟩` from `xyHom_of_mem_monos η s.2`. Establish `hv` using `eval_ne_zero_of_subset hI hs₀`. Establish `hne : (s : Poly (MvPolynomial (Fin (r + 1)) S) N) ≠ 0` using `fun h0 => hv (by`.

Rewrite `hxs` using `[h0, map_zero]`. Use `congrArg (fun W : LaurUT Ω => W.coeff ((0 : ℤ), (e' : ℤ))) hxs` as an intermediate fact. Simplify using `using this.symm)`. Establish `h1 : (s : Poly (MvPolynomial (Fin (r + 1)) S) N).IsHomogeneous e'` using `hss ▸ hs₀e.map C`. Take `rfl : e' = e` from `h1.inj_right hse hne`.

Introduce `b`. Rewrite using `[locEmb_mk η M₀ hI m s hxs hv, coeff_single_mul_sub]`. Apply the tactic sequence `have hidx : ((b, c) : ℤ × ℤ) - ((0 : ℤ), -(e' : ℤ)) = (b, c + e') := by ext <;> simp`. Rewrite using `[hidx]`. Conclude with `Submodule.subset_span ⟨m.val.coeff (b, c + e'), s₀, c + e', e', hs₀, hs₀e, m.isTw (b, c + e'), by ring, rfl⟩`.

Introduce `b`. Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `u v _ _ hu hv b`. Rewrite using `[map_add]`.

Express the relevant statement in the definitionally equal form `(UT.toL _ + UT.toL _).coeff _ ∈ _`. Rewrite using `[AddMonoidAlgebra.coeff_add, Finsupp.add_apply]`. Conclude with `add_mem (hu b) (hv b)`. Introduce `c' u _ hu`. Rewrite using `[locEmb_smul']`.

Conclude with `locGood_yHom_mul η M₀ c' hu`.
-/
theorem locGood_locEmb (I : StdCell N) (hI : I.1 ⊆ support x) {c : ℤ}
    {w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I.1} (hw : w ∈ degLoc (twGraded η M₀) c I) :
    LocGood η M₀ c I.1 (UT.toL (locEmb η M₀ I.1 hI w)) := by
  refine Submodule.span_induction (p := fun w _ => LocGood η M₀ c I.1 (UT.toL (locEmb η M₀ I.1 hI w)))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, s, a, e, -, hse, -, rfl⟩
    obtain ⟨s₀, hs₀, e', hs₀e, hss, hxs⟩ := xyHom_of_mem_monos η s.2
    have hv := eval_ne_zero_of_subset hI hs₀
    have hne : (s : Poly (MvPolynomial (Fin (r + 1)) S) N) ≠ 0 := fun h0 => hv (by
      rw [h0, map_zero] at hxs
      have := congrArg (fun W : LaurUT Ω => W.coeff ((0 : ℤ), (e' : ℤ))) hxs
      simpa using this.symm)
    have h1 : (s : Poly (MvPolynomial (Fin (r + 1)) S) N).IsHomogeneous e' := hss ▸ hs₀e.map C
    obtain rfl : e' = e := h1.inj_right hse hne
    intro b
    rw [locEmb_mk η M₀ hI m s hxs hv, coeff_single_mul_sub]
    have hidx : ((b, c) : ℤ × ℤ) - ((0 : ℤ), -(e' : ℤ)) = (b, c + e') := by ext <;> simp
    rw [hidx]
    exact Submodule.subset_span ⟨m.val.coeff (b, c + e'), s₀, c + e', e', hs₀, hs₀e, m.isTw (b, c + e'),
      by ring, rfl⟩
  · intro b; rw [map_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv b
    rw [map_add]
    change (UT.toL _ + UT.toL _).coeff _ ∈ _
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem (hu b) (hv b)
  · intro c' u _ hu
    rw [locEmb_smul']
    exact locGood_yHom_mul η M₀ c' hu

/- English proof (translation)
Use `Submodule.span_induction (p := fun y _ => ∃ w ∈ degLoc (twGraded η M₀) c I, UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨z, s₀, a, e, hs₀, hse, hz, hae, rfl⟩`. Set `m : TwM η M₀` to `TwM.mk (single (b, a) z) (isTw_single η M₀ hz)`. Set `s : monos (S` to `MvPolynomial (Fin (r + 1)) S) I.1 := ⟨MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀, map_C_mem_monos hs₀⟩`. Use `⟨LocalizedModule.mk m s, Submodule.subset_span ⟨m, s, a, e, ?_, hse.map C, hae, rfl⟩, ?_⟩` and prove the remaining obligations.

Conclude with `single_mem_tDeg (b, a) z`. Establish `hv` using `eval_ne_zero_of_subset hI hs₀`. Rewrite using `[locEmb_mk η M₀ hI m s (xyHom_map_C x η hse) hv, TwM.val_mk, single_mul_single]`. Use `congr 1`. Use `ext`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Conclude with `⟨0, Submodule.zero_mem _, by rw [map_zero, single_zero]; rfl⟩`. Introduce and unpack `u v _ _ ⟨w, hw, hwu⟩ ⟨w', hw', hwv⟩`.

Use `⟨w + w', Submodule.add_mem _ hw hw', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Express the relevant statement in the definitionally equal form `UT.toL _ + UT.toL _ = _`. Rewrite using `[hwu, hwv, single_add]`. Both sides reduce to the same expression.

Introduce and unpack `r' u _ ⟨w, hw, hwu⟩`. Use `⟨(C r' : MvPolynomial (Fin (r + 1)) S) • w, Submodule.smul_mem _ _ hw, ?_⟩` and prove the remaining obligations. Rewrite using `[locEmb_smul', hwu, yHom_C, single_mul_single, zero_add, Algebra.smul_def]`.
-/
theorem exists_locEmb_eq (I : StdCell N) (hI : I.1 ⊆ support x) {b c : ℤ} {y : Ω}
    (hy : y ∈ twLocPart η M₀ b c I.1) :
    ∃ w ∈ degLoc (twGraded η M₀) c I, UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y := by
  refine Submodule.span_induction (p := fun y _ => ∃ w ∈ degLoc (twGraded η M₀) c I,
    UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₀, a, e, hs₀, hse, hz, hae, rfl⟩
    let m : TwM η M₀ := TwM.mk (single (b, a) z) (isTw_single η M₀ hz)
    let s : monos (S := MvPolynomial (Fin (r + 1)) S) I.1 :=
      ⟨MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀, map_C_mem_monos hs₀⟩
    refine ⟨LocalizedModule.mk m s, Submodule.subset_span ⟨m, s, a, e, ?_, hse.map C, hae, rfl⟩, ?_⟩
    · exact single_mem_tDeg (b, a) z
    · have hv := eval_ne_zero_of_subset hI hs₀
      rw [locEmb_mk η M₀ hI m s (xyHom_map_C x η hse) hv, TwM.val_mk, single_mul_single]
      congr 1
      ext
      · simp
      · simp; omega
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, single_zero]; rfl⟩
  · rintro u v _ _ ⟨w, hw, hwu⟩ ⟨w', hw', hwv⟩
    refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
    rw [map_add]
    change UT.toL _ + UT.toL _ = _
    rw [hwu, hwv, single_add]
    rfl
  · rintro r' u _ ⟨w, hw, hwu⟩
    refine ⟨(C r' : MvPolynomial (Fin (r + 1)) S) • w, Submodule.smul_mem _ _ hw, ?_⟩
    rw [locEmb_smul', hwu, yHom_C, single_mul_single, zero_add, Algebra.smul_def]

end Loc

end

end GroundTheory.Heights₂.Heights.Kleiman
