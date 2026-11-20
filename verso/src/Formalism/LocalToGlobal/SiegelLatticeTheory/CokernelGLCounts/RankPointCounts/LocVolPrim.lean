import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocFramePrimJoint

noncomputable section

namespace Formalism.L2.SG.Pf.LocVolPrim

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets
  Formalism.L2.SG.HidaSetting
open scoped nonZeroDivisors

section Iso

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using h.map (ι.symm.toRingHom.toIntAlgHom)`. Introduce `h`. Simplify using `using h.map (ι.toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_iff_of_ringEquiv (ι : K ≃+* L) (x : K) : IsIntegral ℤ (ι x) ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    simpa using h.map (ι.symm.toRingHom.toIntAlgHom)
  · intro h
    simpa using h.map (ι.toRingHom.toIntAlgHom)

/- English proof (translation)
Conclude with `(IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 L)).symm.trans ((isIntegral_iff_of_ringEquiv ι x).trans (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)))`.
-/
theorem int_iff (ι : K ≃+* L) (x : K) :
    (∃ o : 𝓞 L, algebraMap (𝓞 L) L o = ι x) ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x := by
  exact (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 L)).symm.trans
    ((isIntegral_iff_of_ringEquiv ι x).trans (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)))

def CorrFI (ι : K ≃+* L) (A : FractionalIdeal (𝓞 K)⁰ K) (B : FractionalIdeal (𝓞 L)⁰ L) : Prop :=
  ∀ y : K, y ∈ A ↔ ι y ∈ B

variable (ι : K ≃+* L)

/- English proof (translation)
Introduce `y` and use `by rw [FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff] exact (int_iff ι y).symm`.
-/
theorem corr_one : CorrFI ι 1 1 := fun y => by
  rw [FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff]
  exact (int_iff ι y).symm

/- English proof (translation)
Use `h (ι.symm y)` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem corr_symm {A B} (h : CorrFI ι A B) (y : L) : ι.symm y ∈ A ↔ y ∈ B := by
  have := h (ι.symm y)
  rwa [RingEquiv.apply_symm_apply] at this

/- English proof (translation)
Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `FractionalIdeal.mul_induction_on (C := fun t => ι t ∈ B * B') hy ?_ ?_` and prove the remaining obligations. Introduce `a ha a' ha' show ι (a * a') ∈ B * B'`.

Rewrite using `[map_mul]`. Conclude with `FractionalIdeal.mul_mem_mul ((h a).1 ha) ((h' a').1 ha')`. Introduce `x x' hx hx' show ι (x + x') ∈ B * B'`. Rewrite using `[map_add]`. Conclude with `FractionalIdeal.mem_coe.1 (add_mem (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hx'))`.

Introduce `hy`. Establish `key : ι.symm (ι y) ∈ A * A'`. Use `FractionalIdeal.mul_induction_on (C := fun t => ι.symm t ∈ A * A') hy ?_ ?_` and prove the remaining obligations. Introduce `b hb b' hb' show ι.symm (b * b') ∈ A * A'`. Rewrite using `[map_mul]`.

Conclude with `FractionalIdeal.mul_mem_mul ((corr_symm ι h b).2 hb) ((corr_symm ι h' b').2 hb')`. Introduce `x x' hx hx' show ι.symm (x + x') ∈ A * A'`. Rewrite using `[map_add]`. Conclude with `FractionalIdeal.mem_coe.1 (add_mem (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hx'))`. Rewrite `key` using `[RingEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem corr_mul {A B A' B'} (h : CorrFI ι A B) (h' : CorrFI ι A' B') : CorrFI ι (A * A') (B * B') := by
  intro y
  constructor
  · intro hy
    refine FractionalIdeal.mul_induction_on (C := fun t => ι t ∈ B * B') hy ?_ ?_
    · intro a ha a' ha'
      show ι (a * a') ∈ B * B'
      rw [map_mul]
      exact FractionalIdeal.mul_mem_mul ((h a).1 ha) ((h' a').1 ha')
    · intro x x' hx hx'
      show ι (x + x') ∈ B * B'
      rw [map_add]
      exact FractionalIdeal.mem_coe.1 (add_mem (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hx'))
  · intro hy
    have key : ι.symm (ι y) ∈ A * A' := by
      refine FractionalIdeal.mul_induction_on (C := fun t => ι.symm t ∈ A * A') hy ?_ ?_
      · intro b hb b' hb'
        show ι.symm (b * b') ∈ A * A'
        rw [map_mul]
        exact FractionalIdeal.mul_mem_mul ((corr_symm ι h b).2 hb) ((corr_symm ι h' b').2 hb')
      · intro x x' hx hx'
        show ι.symm (x + x') ∈ A * A'
        rw [map_add]
        exact FractionalIdeal.mem_coe.1 (add_mem (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hx'))
    rwa [RingEquiv.symm_apply_apply] at key

/- English proof (translation)
The claim follows from `| 0 => by simp only [pow_zero]; exact corr_one ι | k + 1 => by rw [pow_succ, pow_succ]; exact corr_mul ι (corr_pow h k) h`.
-/
theorem corr_pow {A B} (h : CorrFI ι A B) : ∀ k : ℕ, CorrFI ι (A ^ k) (B ^ k)
  | 0 => by simp only [pow_zero]; exact corr_one ι
  | k + 1 => by rw [pow_succ, pow_succ]; exact corr_mul ι (corr_pow h k) h

/- English proof (translation)
Introduce `y`. Rewrite using `[FractionalIdeal.mem_inv_iff hA, FractionalIdeal.mem_inv_iff hB]`. Prove the components needed by the constructor for the conclusion. Introduce `H b hb`. Establish `h1` using `(corr_one ι (y * ι.symm b)).1 (H (ι.symm b) ((corr_symm ι h b).2 hb))`.

Rewrite `h1` using `[map_mul, RingEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `H a ha`. Establish `h1` using `H (ι a) ((h a).1 ha)`. Rewrite `h1` using `[← map_mul]`. Conclude with `(corr_one ι _).2 h1`.
-/
theorem corr_inv {A B} (h : CorrFI ι A B) (hA : A ≠ 0) (hB : B ≠ 0) : CorrFI ι A⁻¹ B⁻¹ := by
  intro y
  rw [FractionalIdeal.mem_inv_iff hA, FractionalIdeal.mem_inv_iff hB]
  constructor
  · intro H b hb
    have h1 := (corr_one ι (y * ι.symm b)).1 (H (ι.symm b) ((corr_symm ι h b).2 hb))
    rwa [map_mul, RingEquiv.apply_symm_apply] at h1
  · intro H a ha
    have h1 := H (ι a) ((h a).1 ha)
    rw [← map_mul] at h1
    exact (corr_one ι _).2 h1

/- English proof (translation)
Rewrite using `[zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]`. Conclude with `corr_inv ι (corr_pow ι h k) (pow_ne_zero _ hA) (pow_ne_zero _ hB)`.
-/
theorem corr_zpow_neg {A B} (h : CorrFI ι A B) (hA : A ≠ 0) (hB : B ≠ 0) (k : ℕ) :
    CorrFI ι (A ^ (-(k : ℤ))) (B ^ (-(k : ℤ))) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact corr_inv ι (corr_pow ι h k) (pow_ne_zero _ hA) (pow_ne_zero _ hB)

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `H s`. Take `⟨z, hz⟩` from `H (s : K) (by rw [FractionalIdeal.mem_one_iff]; exact ⟨s, rfl⟩)`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite `hz` using `[Algebra.traceForm_apply]`. Rewrite using `[← hz]`. Simplify using the standard rewrite rules. Introduce `H a ha`. Rewrite `ha` using `[FractionalIdeal.mem_one_iff]`.

Take `⟨s, rfl⟩` from `ha`. Take `⟨z, hz⟩` from `H s`. Rewrite using `[RingHom.mem_range]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply]`.

Simplify using `using hz.symm`.
-/
theorem mem_dual_one_iff (t : K) :
    t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (t * (s : K)) = z := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)]
  constructor
  · intro H s
    obtain ⟨z, hz⟩ := H (s : K) (by rw [FractionalIdeal.mem_one_iff]; exact ⟨s, rfl⟩)
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply] at hz
    rw [← hz]
    simp
  · intro H a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨z, hz⟩ := H s
    rw [RingHom.mem_range]
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hz.symm

/- English proof (translation)
Establish `h1 : (x : K) ∈ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ↔ x ∈ differentIdeal ℤ (𝓞 K)`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', hx', hxx⟩`. Establish `: x' = x` using `RingOfIntegers.ext hxx`.

Rewrite using `[← this]` and apply the resulting hypothesis. Introduce `hx`. Conclude with `⟨x, hx, rfl⟩`. Apply the tactic sequence `rw [← h1, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), FractionalIdeal.mem_inv_iff (by first | exact FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero | exact FractionalIdeal.dual_ne_zero one_ne_zero)]`. Prove the components needed by the constructor for the conclusion.

Introduce `H b hb`. Use `H b ((mem_dual_one_iff b).2 hb)` as an intermediate fact. Rewrite `this` using `[FractionalIdeal.mem_one_iff]`. Conclude with `this`. Introduce `H b hb`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `H b ((mem_dual_one_iff b).1 hb)`.
-/
theorem mem_diff_iff (x : 𝓞 K) : x ∈ differentIdeal ℤ (𝓞 K) ↔
    ∀ b : K, (∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (b * (s : K)) = z) →
      ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = (x : K) * b := by
  have h1 : (x : K) ∈ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ↔
      x ∈ differentIdeal ℤ (𝓞 K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨x', hx', hxx⟩
      have : x' = x := RingOfIntegers.ext hxx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← h1, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K),
    FractionalIdeal.mem_inv_iff (by first | exact FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero | exact FractionalIdeal.dual_ne_zero one_ne_zero)]
  constructor
  · intro H b hb
    have := H b ((mem_dual_one_iff b).2 hb)
    rw [FractionalIdeal.mem_one_iff] at this
    exact this
  · intro H b hb
    rw [FractionalIdeal.mem_one_iff]
    exact H b ((mem_dual_one_iff b).1 hb)

/- English proof (translation)
Conclude with `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofRingEquiv (f := ι) (fun q => by simp)) t`.
-/
theorem trace_map (t : K) : Algebra.trace ℚ L (ι t) = Algebra.trace ℚ K t := by
  exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofRingEquiv (f := ι) (fun q => by simp)) t

def intEquiv : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv ι

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intEquiv_coe (x : 𝓞 K) : ((intEquiv ι x : 𝓞 L) : L) = ι (x : K) := rfl

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_diff_iff]`. Introduce `b hb`. Establish `hb' : ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (ι.symm b * (s : K)) = z`. Introduce `s`. Take `⟨z, hz⟩` from `hb (intEquiv ι s)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← trace_map ι, map_mul, RingEquiv.apply_symm_apply, ← intEquiv_coe]`. Conclude with `hz`. Take `⟨o, ho⟩` from `hx _ hb'`. Establish `key` using `(int_iff ι (ι.symm (((intEquiv ι x : 𝓞 L) : L) * b))).2 ⟨o, by rw [ho, map_mul, intEquiv_coe, RingEquiv.symm_apply_apply]⟩`.

Simplify using `using key`.
-/
theorem diff_mem_map (x : 𝓞 K) (hx : x ∈ differentIdeal ℤ (𝓞 K)) :
    intEquiv ι x ∈ differentIdeal ℤ (𝓞 L) := by
  rw [mem_diff_iff] at hx ⊢
  intro b hb
  have hb' : ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (ι.symm b * (s : K)) = z := by
    intro s
    obtain ⟨z, hz⟩ := hb (intEquiv ι s)
    refine ⟨z, ?_⟩
    rw [← trace_map ι, map_mul, RingEquiv.apply_symm_apply, ← intEquiv_coe]
    exact hz
  obtain ⟨o, ho⟩ := hx _ hb'
  have key := (int_iff ι (ι.symm (((intEquiv ι x : 𝓞 L) : L) * b))).2
    ⟨o, by rw [ho, map_mul, intEquiv_coe, RingEquiv.symm_apply_apply]⟩
  simpa using key

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Ideal.map_le_iff_le_comap.2 (fun x hx => diff_mem_map ι x hx)`. Introduce `y hy`. Establish `h1` using `diff_mem_map ι.symm y hy`. Establish `h2 : intEquiv ι (intEquiv ι.symm y) = y`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[intEquiv_coe, intEquiv_coe, RingEquiv.apply_symm_apply]`. Rewrite using `[← h2]`. Conclude with `Ideal.mem_map_of_mem _ h1`.
-/
theorem diff_map_eq :
    Ideal.map (intEquiv ι : 𝓞 K →+* 𝓞 L) (differentIdeal ℤ (𝓞 K)) = differentIdeal ℤ (𝓞 L) := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 (fun x hx => diff_mem_map ι x hx)
  · intro y hy
    have h1 := diff_mem_map ι.symm y hy
    have h2 : intEquiv ι (intEquiv ι.symm y) = y := by
      apply RingOfIntegers.ext
      rw [intEquiv_coe, intEquiv_coe, RingEquiv.apply_symm_apply]
    rw [← h2]
    exact Ideal.mem_map_of_mem _ h1

end Iso

section Data

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def iotaF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    { toFun := fun a => ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).mpr ⟨a, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
    ⟨RingHom.injective _, fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y).mp y.2
      exact ⟨a, Subtype.ext ha⟩⟩

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))`. Introduce `x y hxy`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Use `congrArg (fun t : 𝓞 E => (t : E)) hxy` as an intermediate fact.

Conclude with `this`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]`. Conclude with `differentIdeal_ne_bot`.
-/
private theorem dd_ne_lemma (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := by
    intro x y hxy
    apply RingOfIntegers.ext
    apply (algebraMap F E).injective
    have := congrArg (fun t : 𝓞 E => (t : E)) hxy
    exact this
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot

/- English proof (translation)
The claim follows from `dd_ne_lemma _ _`.
-/
theorem ddS_ne (D : D7) : ddS D ≠ 0 := dd_ne_lemma _ _

/- English proof (translation)
The claim follows from `dd_ne_lemma _ _`.
-/
theorem ddE_ne : PI.LocFramePrim.ddE (E := X.B.I.E) X.B.I.F ≠ 0 := dd_ne_lemma _ _

/- English proof (translation)
Establish `hle : I.map (intEquiv ι : 𝓞 K →+* 𝓞 L) ≤ I.comap ((intEquiv ι).symm : 𝓞 L →+* 𝓞 K)` using `Ideal.map_le_iff_le_comap.2 (fun x hx => by`. Rewrite using `[Ideal.mem_comap]`. Simplify using `using hx)`. Introduce `y`. Rewrite using `[FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨intEquiv ι x, Ideal.mem_map_of_mem _ hx, intEquiv_coe ι x⟩`. Introduce and unpack `⟨x', hx', hy⟩`. Use `⟨(intEquiv ι).symm x', ?_, ?_⟩` and prove the remaining obligations.

Use `hle hx'` as an intermediate fact. Rewrite `this` using `[Ideal.mem_comap]`. Simplify using `using this`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[← hy]`.

Use `show ι (((intEquiv ι).symm x' : 𝓞 K) : K) = ((x' : 𝓞 L) : L)`. Rewrite using `[← intEquiv_coe, RingEquiv.apply_symm_apply]`.
-/
private theorem corr_map_lemma_2 {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (ι : K ≃+* L) (I : Ideal (𝓞 K)) :
    CorrFI ι (I : FractionalIdeal (𝓞 K)⁰ K)
      ((I.map (intEquiv ι : 𝓞 K →+* 𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
  have hle : I.map (intEquiv ι : 𝓞 K →+* 𝓞 L) ≤ I.comap ((intEquiv ι).symm : 𝓞 L →+* 𝓞 K) :=
    Ideal.map_le_iff_le_comap.2 (fun x hx => by
      rw [Ideal.mem_comap]
      simpa using hx)
  intro y
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨intEquiv ι x, Ideal.mem_map_of_mem _ hx, intEquiv_coe ι x⟩
  · rintro ⟨x', hx', hy⟩
    refine ⟨(intEquiv ι).symm x', ?_, ?_⟩
    · have := hle hx'
      rw [Ideal.mem_comap] at this
      simpa using this
    · apply ι.injective
      rw [← hy]
      show ι (((intEquiv ι).symm x' : 𝓞 K) : K) = ((x' : 𝓞 L) : L)
      rw [← intEquiv_coe, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hmap : Ideal.map (intEquiv X.ιE : 𝓞 X.B.I.E →+* 𝓞 D.host.E) (Ideal.map (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (differentIdeal ℤ (𝓞 X.B.I.F))) = Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))`. Rewrite using `[Ideal.map_map, ← diff_map_eq (iotaF X), Ideal.map_map]`. Use `congr 1`. Use `corr_map_lemma_2 X.ιE (Ideal.map (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (differentIdeal ℤ (𝓞 X.B.I.F)))` as an intermediate fact. Rewrite `this` using `[hmap]`.

Conclude with `this`.
-/
theorem dd_corr : CorrFI X.ιE (PI.LocFramePrim.ddE X.B.I.F) (ddS D) := by
  have hmap : Ideal.map (intEquiv X.ιE : 𝓞 X.B.I.E →+* 𝓞 D.host.E)
      (Ideal.map (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (differentIdeal ℤ (𝓞 X.B.I.F))) =
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) := by
    rw [Ideal.map_map, ← diff_map_eq (iotaF X), Ideal.map_map]
    congr 1
  have := corr_map_lemma_2 X.ιE (Ideal.map (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (differentIdeal ℤ (𝓞 X.B.I.F)))
  rw [hmap] at this
  exact this

/- English proof (translation)
Establish `hk : -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = -(((D.R.rS - (a : ℕ) : ℕ)) : ℤ)`. Rewrite using `[Nat.cast_sub a.2.le]`. Unfold `aaD`. Rewrite using `[hk]`. Conclude with `corr_zpow_neg _ (dd_corr X) (ddE_ne X) (ddS_ne D) _`.
-/
theorem aa_corr (a : Fin D.R.rS) :
    CorrFI X.ιE (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ)))) (aaD D a) := by
  have hk : -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = -(((D.R.rS - (a : ℕ) : ℕ)) : ℤ) := by
    rw [Nat.cast_sub a.2.le]
  unfold aaD
  rw [hk]
  exact corr_zpow_neg _ (dd_corr X) (ddE_ne X) (ddS_ne D) _

/- English proof (translation)
The claim follows from `corr_inv _ (aa_corr X a) (zpow_ne_zero _ (ddE_ne X)) (zpow_ne_zero _ (ddS_ne D))`.
-/
theorem aainv_corr (a : Fin D.R.rS) :
    CorrFI X.ιE (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))⁻¹ (aaD D a)⁻¹ := corr_inv _ (aa_corr X a) (zpow_ne_zero _ (ddE_ne X)) (zpow_ne_zero _ (ddS_ne D))

end Data

section Crd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[← intEquiv_coe]`. Simplify using `only [RingEquiv.apply_symm_apply]`.
-/
theorem intEquiv_symm_coe {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (ι : K ≃+* L)
    (t : 𝓞 L) : (((intEquiv ι).symm t : 𝓞 K) : K) = ι.symm (t : L) := by
  apply ι.injective
  rw [← intEquiv_coe]
  simp only [RingEquiv.apply_symm_apply]

def cinv (x : Fin X.B.I.n → X.B.I.E) : (VS D).V := ∑ i, X.ιE (x i) • X.bas i

abbrev crd (y : (VS D).V) : Fin X.B.I.n → X.B.I.E := crdOf X.B.I X.ιE X.bas y

/- English proof (translation)
Simplify using `only [cinv, crd, crdOf, RingEquiv.apply_symm_apply]`. Conclude with `X.bas.sum_repr y`.
-/
theorem cinv_crd (y : (VS D).V) : cinv X (crd X y) = y := by
  simp only [cinv, crd, crdOf, RingEquiv.apply_symm_apply]
  exact X.bas.sum_repr y

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [crd, crdOf, cinv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, RingEquiv.symm_apply_ap …`.
-/
theorem crd_cinv (x : Fin X.B.I.n → X.B.I.E) : crd X (cinv X x) = x := by
  funext i
  simp only [crd, crdOf, cinv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, RingEquiv.symm_apply_apply]

/- English proof (translation)
Simplify using `only [cinv, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]`.
-/
theorem cinv_add (x y : Fin X.B.I.n → X.B.I.E) : cinv X (x + y) = cinv X x + cinv X y := by
  simp only [cinv, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[cinv]`.
-/
theorem cinv_zero : cinv X 0 = 0 := by
  simp [cinv]

/- English proof (translation)
Simplify using `only [cinv, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]`.
-/
theorem cinv_smul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) : cinv X (c • x) = X.ιE c • cinv X x := by
  simp only [cinv, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Establish `h1 : o • x = (o : X.B.I.E) • x`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply]`. Both sides reduce to the same expression. Rewrite using `[h1, cinv_smul, ← intEquiv_coe]`.

Conclude with `(algebra_compatible_smul D.host.E (intEquiv X.ιE o) (cinv X x)).symm`.
-/
theorem cinv_osmul (o : 𝓞 X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    cinv X (o • x) = intEquiv X.ιE o • cinv X x := by
  have h1 : o • x = (o : X.B.I.E) • x := by
    funext i
    simp only [Pi.smul_apply]
    rfl
  rw [h1, cinv_smul, ← intEquiv_coe]
  exact (algebra_compatible_smul D.host.E (intEquiv X.ιE o) (cinv X x)).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[crdOf, map_add]`.
-/
theorem crd_add (x y : (VS D).V) : crd X (x + y) = crd X x + crd X y := by
  funext i
  simp [crdOf, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[crdOf]`.
-/
theorem crd_zero : crd X 0 = 0 := by
  funext i
  simp [crdOf]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[crdOf, map_smul, smul_eq_mul, map_mul]`.
-/
theorem crd_smul (c : D.host.E) (y : (VS D).V) : crd X (c • y) = X.ιE.symm c • crd X y := by
  funext i
  simp [crdOf, map_smul, smul_eq_mul, map_mul]

/- English proof (translation)
Rewrite using `[algebra_compatible_smul D.host.E o y, crd_smul]`. Use function extensionality and compare the values at `i`. Use `show X.ιE.symm (o : D.host.E) * crd X y i = (((intEquiv X.ιE).symm o : 𝓞 X.B.I.E) : X.B.I.E) * crd X y i`. Rewrite using `[intEquiv_symm_coe]`.
-/
theorem crd_osmul (o : 𝓞 D.host.E) (y : (VS D).V) :
    crd X (o • y) = (intEquiv X.ιE).symm o • crd X y := by
  rw [algebra_compatible_smul D.host.E o y, crd_smul]
  funext i
  show X.ιE.symm (o : D.host.E) * crd X y i = (((intEquiv X.ιE).symm o : 𝓞 X.B.I.E) : X.B.I.E) * crd X y i
  rw [intEquiv_symm_coe]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Set `M : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E)` to `{ carrier := {y | cinv X y ∈ Submodule.span (𝓞 D.host.E) S2} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, cinv_add] at *`. Conclude with `add_mem ha hb`.

Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_ofPred_eq, cinv_zero]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun o a ha => by`. Simplify using `only [Set.mem_ofPred_eq, cinv_osmul] at *`.

Conclude with `Submodule.smul_mem _ _ ha }`. Establish `hle : Submodule.span (𝓞 X.B.I.E) S ≤ M` using `Submodule.span_le.2 (fun a ha => Submodule.subset_span (h1 a ha))`. Conclude with `hle hy`. Introduce `hy`. Set `M : Submodule (𝓞 D.host.E) (VS D).V` to `{ carrier := {x | crd X x ∈ Submodule.span (𝓞 X.B.I.E) S} add_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_ofPred_eq, crd_add] at *`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_ofPred_eq, crd_zero]`. Conclude with `zero_mem _`.

Use the proof step `smul_mem' := fun o a ha => by`. Simplify using `only [Set.mem_ofPred_eq, crd_osmul] at *`. Conclude with `Submodule.smul_mem _ _ ha }`. Establish `hle : Submodule.span (𝓞 D.host.E) S2 ≤ M` using `Submodule.span_le.2 (fun a ha => Submodule.subset_span (h2 a ha))`. Establish `h3 : crd X (cinv X y) ∈ Submodule.span (𝓞 X.B.I.E) S` using `hle hy`.

Rewrite `h3` using `[crd_cinv]`. Then use the resulting hypothesis.
-/
theorem span_corr (S : Set (Fin X.B.I.n → X.B.I.E)) (S2 : Set (VS D).V) (h1 : ∀ y ∈ S, cinv X y ∈ S2)
    (h2 : ∀ x ∈ S2, crd X x ∈ S) (y : Fin X.B.I.n → X.B.I.E) :
    y ∈ Submodule.span (𝓞 X.B.I.E) S ↔ cinv X y ∈ Submodule.span (𝓞 D.host.E) S2 := by
  constructor
  · intro hy
    let M : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E) :=
      { carrier := {y | cinv X y ∈ Submodule.span (𝓞 D.host.E) S2}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, cinv_add] at *
          exact add_mem ha hb
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, cinv_zero]
          exact zero_mem _
        smul_mem' := fun o a ha => by
          simp only [Set.mem_ofPred_eq, cinv_osmul] at *
          exact Submodule.smul_mem _ _ ha }
    have hle : Submodule.span (𝓞 X.B.I.E) S ≤ M :=
      Submodule.span_le.2 (fun a ha => Submodule.subset_span (h1 a ha))
    exact hle hy
  · intro hy
    let M : Submodule (𝓞 D.host.E) (VS D).V :=
      { carrier := {x | crd X x ∈ Submodule.span (𝓞 X.B.I.E) S}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, crd_add] at *
          exact add_mem ha hb
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, crd_zero]
          exact zero_mem _
        smul_mem' := fun o a ha => by
          simp only [Set.mem_ofPred_eq, crd_osmul] at *
          exact Submodule.smul_mem _ _ ha }
    have hle : Submodule.span (𝓞 D.host.E) S2 ≤ M :=
      Submodule.span_le.2 (fun a ha => Submodule.subset_span (h2 a ha))
    have h3 : crd X (cinv X y) ∈ Submodule.span (𝓞 X.B.I.E) S := hle hy
    rwa [crd_cinv] at h3

/- English proof (translation)
Rewrite using `[Submodule.mem_sup, Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨cinv X a, (hA a).1 ha, cinv X b, (hB b).1 hb, (cinv_add X a b).symm⟩`. Introduce and unpack `⟨a, ha, b, hb, hab⟩`.

Use `⟨crd X a, (hA _).2 (by rwa [cinv_crd]), crd X b, (hB _).2 (by rwa [cinv_crd]), ?_⟩` and prove the remaining obligations. Rewrite using `[← crd_add, hab, crd_cinv]`.
-/
theorem sup_corr {A B : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E)} {A2 B2 : Submodule (𝓞 D.host.E) (VS D).V}
    (hA : ∀ y, y ∈ A ↔ cinv X y ∈ A2) (hB : ∀ y, y ∈ B ↔ cinv X y ∈ B2) (y : Fin X.B.I.n → X.B.I.E) :
    y ∈ A ⊔ B ↔ cinv X y ∈ A2 ⊔ B2 := by
  rw [Submodule.mem_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨cinv X a, (hA a).1 ha, cinv X b, (hB b).1 hb, (cinv_add X a b).symm⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨crd X a, (hA _).2 (by rwa [cinv_crd]), crd X b, (hB _).2 (by rwa [cinv_crd]), ?_⟩
    rw [← crd_add, hab, crd_cinv]

/- English proof (translation)
Unfold `PI.LocFramePrim.latSpan latSpanS`. Use `span_corr X _ _ ?_ ?_ y` and prove the remaining obligations. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Conclude with `⟨a, X.ιE x, (h a x).1 hx, by rw [cinv_smul, cinv_crd]⟩`. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`.

Conclude with `⟨a, X.ιE.symm x, (corr_symm X.ιE (h a) x).2 hx, crd_smul X x (w a)⟩`.
-/
theorem latSpan_corr {r : ℕ} (aa : Fin r → FractionalIdeal (𝓞 X.B.I.E)⁰ X.B.I.E)
    (aa2 : Fin r → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : ∀ a, CorrFI X.ιE (aa a) (aa2 a))
    (w : Fin r → (VS D).V) (y : Fin X.B.I.n → X.B.I.E) :
    y ∈ PI.LocFramePrim.latSpan aa (fun a => crd X (w a)) ↔ cinv X y ∈ latSpanS aa2 w := by
  unfold PI.LocFramePrim.latSpan latSpanS
  refine span_corr X _ _ ?_ ?_ y
  · rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨a, X.ιE x, (h a x).1 hx, by rw [cinv_smul, cinv_crd]⟩
  · rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨a, X.ιE.symm x, (corr_symm X.ιE (h a) x).2 hx, crd_smul X x (w a)⟩

def LbC : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E) where
  carrier := {y | cinv X y ∈ X.Lb}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, cinv_add] at *
    exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, cinv_zero]; exact zero_mem _
  smul_mem' := fun o y hy => by
    simp only [Set.mem_ofPred_eq, cinv_osmul] at *
    exact X.Lb.smul_mem _ hy

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_LbC (y : Fin X.B.I.n → X.B.I.E) : y ∈ LbC X ↔ cinv X y ∈ X.Lb := Iff.rfl

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[X.L_eq y]`. Express the relevant statement in the definitionally equal form `cinv X y ∈ (VS D).L0 ↔ _`. Rewrite using `[X.Lam_split]`. Use `symm`.

Conclude with `sup_corr X (fun y => sup_corr X (fun y => latSpan_corr X _ _ (aa_corr X) X.eX y) (fun y => mem_LbC X y) y) (fun y => latSpan_corr X _ _ (aainv_corr X) X.fY y) y`.
-/
theorem split_crd (w : D.what₂.Word) :
    X.B.I.L = PI.LocFramePrim.latSpan
        (fun a : Fin D.R.rS => PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ)))) (frameOf X w).e ⊔
      LbC X ⊔ PI.LocFramePrim.latSpan
        (fun a : Fin D.R.rS => (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))⁻¹) (frameOf X w).f := by
  ext y
  rw [X.L_eq y]
  change cinv X y ∈ (VS D).L0 ↔ _
  rw [X.Lam_split]
  symm
  exact sup_corr X (fun y => sup_corr X (fun y => latSpan_corr X _ _ (aa_corr X) X.eX y)
    (fun y => mem_LbC X y) y) (fun y => latSpan_corr X _ _ (aainv_corr X) X.fY y) y

end Crd

section Hyp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Simplify using `only [cinv, Finset.sum_apply, map_sum, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem cinv_sum {ι : Type} (s : Finset ι) (x : ι → Fin X.B.I.n → X.B.I.E) :
    cinv X (∑ j ∈ s, x j) = ∑ j ∈ s, cinv X (x j) := by
  simp only [cinv, Finset.sum_apply, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Establish `h : starRingEnd D.host.E ((VS D).hT (X.eX a) (X.fY b)) = (VS D).hT (X.fY b) (X.eX a)` using `by first`. Consider the case `exact (VS D).herm (X.eX a) (X.fY b)`. Consider the case `exact (VS D).herm.eq (X.eX a) (X.fY b)`. Consider the case `exact LinearMap.IsSymm.eq (VS D).herm (X.eX a) (X.fY b)`. Rewrite using `[← h, X.ef]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem fe (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  have h : starRingEnd D.host.E ((VS D).hT (X.eX a) (X.fY b)) = (VS D).hT (X.fY b) (X.eX a) := by
    first
      | exact (VS D).herm (X.eX a) (X.fY b)
      | exact (VS D).herm.eq (X.eX a) (X.fY b)
      | exact LinearMap.IsSymm.eq (VS D).herm (X.eX a) (X.fY b)
  rw [← h, X.ef]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[fe, X.ff, Finset.sum_ite_eq']`.
-/
theorem pair_f (α β : Fin D.R.rS → D.host.E) (b : Fin D.R.rS) :
    (VS D).hT (X.fY b) ((∑ a, α a • X.eX a) + ∑ a, β a • X.fY a) = α b := by
  simp [fe, X.ff, Finset.sum_ite_eq']

/- English proof (translation)
Simplify using `[X.ee, X.ef, Finset.sum_ite_eq]`.
-/
theorem pair_e (α β : Fin D.R.rS → D.host.E) (b : Fin D.R.rS) :
    (VS D).hT (X.eX b) ((∑ a, α a • X.eX a) + ∑ a, β a • X.fY a) = β b := by
  simp [X.ee, X.ef, Finset.sum_ite_eq]

/- English proof (translation)
Rewrite `hG` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right] at hG`. Establish `hα : ∀ b, G (Fin.castAdd D.R.rS b) = 0` using `fun b => by`. Use `pair_f X (fun a => G (Fin.castAdd D.R.rS a)) (fun a => G (Fin.natAdd D.R.rS a)) b` as an intermediate fact. Rewrite `this` using `[hG, map_zero]`.

Conclude with `this.symm`. Establish `hβ : ∀ b, G (Fin.natAdd D.R.rS b) = 0` using `fun b => by`. Use `pair_e X (fun a => G (Fin.castAdd D.R.rS a)) (fun a => G (Fin.natAdd D.R.rS a)) b` as an intermediate fact. Rewrite `this` using `[hG, map_zero]`. Conclude with `this.symm`.

Introduce `i`. Conclude with `Fin.addCases hα hβ i`.
-/
theorem indep_V (G : Fin (D.R.rS + D.R.rS) → D.host.E) (hG : ∑ i, G i • Fin.append X.eX X.fY i = 0) :
    ∀ i, G i = 0 := by
  rw [Fin.sum_univ_add] at hG
  simp only [Fin.append_left, Fin.append_right] at hG
  have hα : ∀ b, G (Fin.castAdd D.R.rS b) = 0 := fun b => by
    have := pair_f X (fun a => G (Fin.castAdd D.R.rS a)) (fun a => G (Fin.natAdd D.R.rS a)) b
    rw [hG, map_zero] at this
    exact this.symm
  have hβ : ∀ b, G (Fin.natAdd D.R.rS b) = 0 := fun b => by
    have := pair_e X (fun a => G (Fin.castAdd D.R.rS a)) (fun a => G (Fin.natAdd D.R.rS a)) b
    rw [hG, map_zero] at this
    exact this.symm
  intro i
  exact Fin.addCases hα hβ i

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1 : ∑ j, X.ιE (g j) • Fin.append X.eX X.fY j = 0`. Establish `h2` using `congrArg (cinv X) hg`. Rewrite `h2` using `[cinv_sum, cinv_zero]`.

Rewrite using `[← h2]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[cinv_smul]`. Use `congr 1`. Use `Fin.addCases (fun b => ?_) (fun b => ?_) j` and prove the remaining obligations.

Simplify using `only [Fin.append_left]`. Conclude with `(cinv_crd X _).symm`. Simplify using `only [Fin.append_right]`. Conclude with `(cinv_crd X _).symm`. Use `indep_V X (fun j => X.ιE (g j)) h1 i` as an intermediate fact.

Simplify using `using this`.
-/
theorem hind_crd (w : D.what₂.Word) :
    LinearIndependent X.B.I.E (Fin.append (frameOf X w).e (frameOf X w).f) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : ∑ j, X.ιE (g j) • Fin.append X.eX X.fY j = 0 := by
    have h2 := congrArg (cinv X) hg
    rw [cinv_sum, cinv_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [cinv_smul]
    congr 1
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · simp only [Fin.append_left]
      exact (cinv_crd X _).symm
    · simp only [Fin.append_right]
      exact (cinv_crd X _).symm
  have := indep_V X (fun j => X.ιE (g j)) h1 i
  simpa using this

/- English proof (translation)
Rewrite `hs` using `[Submodule.span_union, Submodule.mem_sup]`. Take `⟨u, hu, v, hv, rfl⟩` from `hs`. Rewrite `hu`, `hv` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨α, rfl⟩` from `hu`. Take `⟨β, rfl⟩` from `hv`.

Establish `hα : ∀ b, α b = 0` using `fun b => by`. Rewrite using `[← pair_f X α β b]`. Conclude with `(X.Lb_perp _ hx b).2`. Establish `hβ : ∀ b, β b = 0` using `fun b => by`. Rewrite using `[← pair_e X α β b]`.

Conclude with `(X.Lb_perp _ hx b).1`. Simplify using `[hα, hβ]`.
-/
theorem dir_V (x : (VS D).V) (hx : x ∈ X.Lb)
    (hs : x ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)) : x = 0 := by
  rw [Submodule.span_union, Submodule.mem_sup] at hs
  obtain ⟨u, hu, v, hv, rfl⟩ := hs
  rw [Submodule.mem_span_range_iff_exists_fun] at hu hv
  obtain ⟨α, rfl⟩ := hu
  obtain ⟨β, rfl⟩ := hv
  have hα : ∀ b, α b = 0 := fun b => by
    rw [← pair_f X α β b]
    exact (X.Lb_perp _ hx b).2
  have hβ : ∀ b, β b = 0 := fun b => by
    rw [← pair_e X α β b]
    exact (X.Lb_perp _ hx b).1
  simp [hα, hβ]

/- English proof (translation)
Introduce `y hy hs`. Set `M : Submodule X.B.I.E (Fin X.B.I.n → X.B.I.E)` to `{ carrier := {y | cinv X y ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, cinv_add] at *`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_ofPred_eq, cinv_zero]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_ofPred_eq, cinv_smul] at *`. Conclude with `Submodule.smul_mem _ _ ha }`.

Establish `hle : Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) ≤ M`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Use `show cinv X (crd X (X.eX a)) ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)`. Rewrite using `[cinv_crd]`.

Conclude with `Submodule.subset_span (Or.inl ⟨a, rfl⟩)`. Use `show cinv X (crd X (X.fY a)) ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)`. Rewrite using `[cinv_crd]`. Conclude with `Submodule.subset_span (Or.inr ⟨a, rfl⟩)`. Establish `h0 : cinv X y = 0` using `dir_V X (cinv X y) ((mem_LbC X y).1 hy) (hle hs)`.

Rewrite using `[← crd_cinv X y, h0, crd_zero]`.
-/
theorem dir_crd (w : D.what₂.Word) : ∀ y ∈ LbC X,
    y ∈ Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) → y = 0 := by
  intro y hy hs
  let M : Submodule X.B.I.E (Fin X.B.I.n → X.B.I.E) :=
    { carrier := {y | cinv X y ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, cinv_add] at *
        exact add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, cinv_zero]
        exact zero_mem _
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, cinv_smul] at *
        exact Submodule.smul_mem _ _ ha }
  have hle : Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) ≤ M := by
    rw [Submodule.span_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · show cinv X (crd X (X.eX a)) ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)
      rw [cinv_crd]
      exact Submodule.subset_span (Or.inl ⟨a, rfl⟩)
    · show cinv X (crd X (X.fY a)) ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY)
      rw [cinv_crd]
      exact Submodule.subset_span (Or.inr ⟨a, rfl⟩)
  have h0 : cinv X y = 0 := dir_V X (cinv X y) ((mem_LbC X y).1 hy) (hle hs)
  rw [← crd_cinv X y, h0, crd_zero]

/- English proof (translation)
Use `show cinv X (crd X (X.zu w)) ∈ X.Lb`. Rewrite using `[cinv_crd]`. Conclude with `X.zu_Lb w`.
-/
theorem hz_crd (w : D.what₂.Word) : (frameOf X w).z ∈ LbC X := by
  show cinv X (crd X (X.zu w)) ∈ X.Lb
  rw [cinv_crd]
  exact X.zu_Lb w

/- English proof (translation)
Introduce `c hc`. Establish `h1 : cinv X ((frameOf X w).z) = X.zu w` using `cinv_crd X (X.zu w)`. Establish `hv : X.ιE c • X.zu w ∈ X.Lb`. Use `(mem_LbC X _).1 hc` as an intermediate fact. Rewrite `this` using `[cinv_smul, h1]`. Then use the resulting hypothesis.

Establish `hLb : X.Lb ≤ (VS D).L0`. Rewrite using `[X.Lam_split]`. Conclude with `le_sup_right.trans le_sup_left`. Establish `hker : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT.flip (X.zu w))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]`. Conclude with `(X.zu_orth w a).1`. Establish `hmem : X.ιE c • X.zu w ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu w).X`. Simplify using `only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]`.

Introduce `x hx`. Establish `hx' : x ∈ Submodule.span D.host.E (Set.range X.eX)`. Rewrite using `[← X.Fu_e w]`. Conclude with `hx`. Establish `h0 : (VS D).hT x (X.zu w) = 0`.

Use `LinearMap.mem_ker.1 (hker hx')` as an intermediate fact. Rewrite `this` using `[LinearMap.flip_apply]`. Then use the resulting hypothesis. Rewrite using `[map_smul, smul_eq_mul, h0, mul_zero]`. Take `⟨-, -, -, -, hprim⟩` from `X.Fu_fixed w`. Simplify using `only [X.flagZVector] at hprim`.

Take `⟨o, ho⟩` from `hprim (X.ιE c) (Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hLb hv, hmem⟩), hmem⟩)`. Use `⟨(intEquiv X.ιE).symm o, ?_⟩` and prove the remaining obligations. Rewrite using `[intEquiv_symm_coe, ho, RingEquiv.symm_apply_apply]`.
-/
theorem hzp_crd (w : D.what₂.Word) :
    ∀ c : X.B.I.E, c • (frameOf X w).z ∈ LbC X → ∃ o : 𝓞 X.B.I.E, (o : X.B.I.E) = c := by
  intro c hc
  have h1 : cinv X ((frameOf X w).z) = X.zu w := cinv_crd X (X.zu w)
  have hv : X.ιE c • X.zu w ∈ X.Lb := by
    have := (mem_LbC X _).1 hc
    rwa [cinv_smul, h1] at this
  have hLb : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]
    exact le_sup_right.trans le_sup_left
  have hker : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT.flip (X.zu w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact (X.zu_orth w a).1
  have hmem : X.ιE c • X.zu w ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu w).X := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← X.Fu_e w]
      exact hx
    have h0 : (VS D).hT x (X.zu w) = 0 := by
      have := LinearMap.mem_ker.1 (hker hx')
      rwa [LinearMap.flip_apply] at this
    rw [map_smul, smul_eq_mul, h0, mul_zero]
  obtain ⟨-, -, -, -, hprim⟩ := X.Fu_fixed w
  simp only [X.flagZVector] at hprim
  obtain ⟨o, ho⟩ := hprim (X.ιE c)
    (Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hLb hv, hmem⟩), hmem⟩)
  refine ⟨(intEquiv X.ιE).symm o, ?_⟩
  rw [intEquiv_symm_coe, ho, RingEquiv.symm_apply_apply]

end Hyp

/- English proof (translation)
The claim follows from `ChkLocFramePrim.primX_of hS X w (LbC X) X.B.I.L_fg (split_crd X w) (hind_crd X w) (dir_crd X w) (hz_crd X w) (hzp_crd X w)`.
-/
theorem primX {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (hS : PI.LocFramePrim.Statement) : PrimX X w := ChkLocFramePrim.primX_of hS X w (LbC X) X.B.I.L_fg (split_crd X w) (hind_crd X w) (dir_crd X w)
    (hz_crd X w) (hzp_crd X w)

end Formalism.L2.SG.Pf.LocVolPrim
