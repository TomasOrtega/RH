import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.StandardOpenEquiv

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

namespace RationalIdeles

open IdeleGroup

/- English proof (translation)
Rewrite using `[Subsingleton.elim w Rat.infinitePlace]`. Conclude with `Rat.isReal_infinitePlace`.
-/
theorem isReal_infinitePlace (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_infinitePlace default))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) :
    realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (isReal_infinitePlace default) (x default) :=
  rfl

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp (continuous_apply _)`.
-/
theorem continuous_realEquiv : Continuous realEquiv :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
    (continuous_apply _)

/- English proof (translation)
Conclude with `continuous_equiv_symm_of_eq realEquiv.toEquiv ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_infinitePlace default)).toHomeomorph) fun _ ↦ rfl`.
-/
theorem continuous_realEquiv_symm : Continuous realEquiv.symm := by
  exact continuous_equiv_symm_of_eq realEquiv.toEquiv
    ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
      (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (isReal_infinitePlace default)).toHomeomorph)
    fun _ ↦ rfl

def realUnitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃ₜ* ℝˣ :=
  unitsContinuousMulEquiv realEquiv.toMulEquiv continuous_realEquiv continuous_realEquiv_symm

def realPart : IdeleGroup ℚ →* ℝˣ :=
  realUnitsEquiv.toMulEquiv.toMonoidHom.comp (toInfinite ℚ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_realPart (x : IdeleGroup ℚ) : (realPart x : ℝ) = realEquiv (x : 𝔸[ℚ]).1 :=
  rfl

/- English proof (translation)
The claim follows from `realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ) @[simp]`.
-/
theorem continuous_realPart : Continuous realPart :=
  realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ)

@[simp]
/- English proof (translation)
Rewrite using `[coe_realPart, coe_diagonal]`. Conclude with `eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a`.
-/
theorem realPart_diagonal (a : ℚˣ) : (realPart (diagonal ℚ a) : ℝ) = a := by
  rw [coe_realPart, coe_diagonal]
  exact eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realPart_ofIntegerUnits (a : (InfiniteAdeleRing ℚ)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (ofIntegerUnits a u) = realUnitsEquiv a :=
  rfl

def positiveSubgroup : Subgroup (IdeleGroup ℚ) :=
  standardOpenSubgroup ℚ ⊓ (Units.posSubgroup ℝ).comap realPart

/- English proof (translation)
Rewrite using `[positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]`.
-/
theorem mem_positiveSubgroup {x : IdeleGroup ℚ} :
    x ∈ positiveSubgroup ↔ x ∈ standardOpenSubgroup ℚ ∧ 0 < (realPart x : ℝ) := by
  rw [positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]

/- English proof (translation)
Establish `h : (positiveSubgroup : Set (IdeleGroup ℚ)) = (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)}`. Use extensionality with `x`. Conclude with `mem_positiveSubgroup`. Rewrite using `[h]`. Conclude with `(isOpen_standardOpenSubgroup ℚ).inter (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))`.
-/
theorem isOpen_positiveSubgroup : IsOpen (positiveSubgroup : Set (IdeleGroup ℚ)) := by
  have h : (positiveSubgroup : Set (IdeleGroup ℚ)) =
      (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)} := by
    ext x
    exact mem_positiveSubgroup
  rw [h]
  exact (isOpen_standardOpenSubgroup ℚ).inter
    (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))

/- English proof (translation)
Rewrite using `[← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal, toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1`. Rewrite `hz` using `[Units.smul_def, Algebra.smul_def]`.

Conclude with `hz`. Break down `Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h` into its components or cases. Use `left`. Rewrite `hz'` using `[h, one_mul]`. Then use the resulting hypothesis. Use `right`.

Rewrite `hz'` using `[h, neg_one_mul, neg_eq_iff_eq_neg]`. Then use the resulting hypothesis. Introduce and unpack `(h | h)`. Conclude with `⟨1, by rw [one_smul, h]⟩`. Conclude with `⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩`.
-/
theorem diagonal_mem_standardOpenSubgroup_iff (a : ℚˣ) :
    diagonal ℚ a ∈ standardOpenSubgroup ℚ ↔ (a : ℚ) = 1 ∨ (a : ℚ) = -1 := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal,
    toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1 := by
      rw [Units.smul_def, Algebra.smul_def] at hz
      exact hz
    rcases Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h
    · left
      rwa [h, one_mul] at hz'
    · right
      rwa [h, neg_one_mul, neg_eq_iff_eq_neg] at hz'
  · rintro (h | h)
    · exact ⟨1, by rw [one_smul, h]⟩
    · exact ⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨hx, a, rfl⟩`. Take `⟨h1, h2⟩` from `mem_positiveSubgroup.1 hx`. Rewrite `h2` using `[realPart_diagonal]`. Rewrite using `[Subgroup.mem_bot]`.

Break down `(diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h` into its components or cases. Rewrite using `[show a = 1 from Units.ext h, map_one]`. Rewrite `h2` using `[h]`. Evaluate the numerical expressions using `at h2`.
-/
theorem positiveSubgroup_inf_diagonal_range : positiveSubgroup ⊓ (diagonal ℚ).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, a, rfl⟩
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hx
  rw [realPart_diagonal] at h2
  rw [Subgroup.mem_bot]
  rcases (diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h
  · rw [show a = 1 from Units.ext h, map_one]
  · rw [h] at h2
    norm_num at h2

/- English proof (translation)
Establish `h` using `Rat.classNumber_eq`. Rewrite `h` using `[NumberField.classNumber]`. Conclude with `Fintype.card_le_one_iff_subsingleton.1 h.le`.
-/
theorem subsingleton_classGroup : Subsingleton (ClassGroup (𝓞 ℚ)) := by
  have h := Rat.classNumber_eq
  rw [NumberField.classNumber] at h
  exact Fintype.card_le_one_iff_subsingleton.1 h.le

/- English proof (translation)
Establish `htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤`. Rewrite using `[← IdeleGroup.ker_toClassGroup, eq_top_iff]`. Introduce `x _`. Use `subsingleton_classGroup` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ` using `htop ▸ Subgroup.mem_top x`. Take `⟨_, ⟨a, rfl⟩, u, hu, rfl⟩` from `Subgroup.mem_sup.1 hx`. Break down `lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos` into its components or cases.

Establish `hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ` using `(diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))`. Establish `hp : diagonal ℚ (-1) * u ∈ positiveSubgroup`. Use `mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, realPart_diagonal]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_right_comm, ← map_mul, neg_one_mul, neg_neg]`. Conclude with `Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩, mul_comm _ _⟩`.
-/
theorem positiveSubgroup_sup_diagonal_range : positiveSubgroup ⊔ (diagonal ℚ).range = ⊤ := by
  have htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤ := by
    rw [← IdeleGroup.ker_toClassGroup, eq_top_iff]
    intro x _
    have := subsingleton_classGroup
    exact Subsingleton.elim _ _
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ := htop ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rcases lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos
  · have hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ :=
      (diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))
    have hp : diagonal ℚ (-1) * u ∈ positiveSubgroup := by
      refine mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩
      rw [map_mul, Units.val_mul, realPart_diagonal]
      push_cast
      linarith
    refine Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩
    rw [mul_right_comm, ← map_mul, neg_one_mul, neg_neg]
  · exact Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩,
      mul_comm _ _⟩

def positiveSubgroupEquivIdeleClassGroup : positiveSubgroup ≃ₜ* IdeleClassGroup ℚ :=
  openSubgroupEquivQuotient _ _ isOpen_positiveSubgroup positiveSubgroup_inf_diagonal_range
    positiveSubgroup_sup_diagonal_range

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem positiveSubgroupEquivIdeleClassGroup_apply (x : positiveSubgroup) :
    positiveSubgroupEquivIdeleClassGroup x = IdeleClassGroup.mk ℚ x :=
  rfl

def positiveSubgroupEquiv : positiveSubgroup ≃ₜ* Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ where
  toFun x := (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
    (standardOpenSubgroupEquiv ℚ ⟨x, (mem_positiveSubgroup.1 x.2).1⟩).2)
  invFun p := ⟨ofIntegerUnits (realUnitsEquiv.symm p.1) p.2, mem_positiveSubgroup.2
    ⟨ofIntegerUnits_mem _ _, by
      rw [realPart_ofIntegerUnits, ContinuousMulEquiv.apply_symm_apply]
      exact (Units.mem_posSubgroup _).1 p.1.2⟩⟩
  left_inv x := by
    have h : realUnitsEquiv.symm (realPart x) = toInfinite ℚ x :=
      realUnitsEquiv.symm_apply_apply _
    apply Subtype.ext
    change ofIntegerUnits (realUnitsEquiv.symm (realPart x)) _ = (x : IdeleGroup ℚ)
    rw [h]
    exact Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl)))
  right_inv p := Prod.ext (Subtype.ext (realUnitsEquiv.apply_symm_apply _))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (Subtype.ext (map_mul realPart (x : IdeleGroup ℚ) y))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := by
    exact ((continuous_realPart.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp ((standardOpenSubgroupEquiv ℚ).continuous.comp
        (continuous_subtype_val.subtype_mk _)))
  continuous_invFun := by
    exact (continuous_subtype_val.comp ((standardOpenSubgroupEquiv ℚ).symm.continuous.comp
      ((realUnitsEquiv.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))).subtype_mk _

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_positiveSubgroupEquiv_apply_fst (x : positiveSubgroup) :
    ((positiveSubgroupEquiv x).1 : ℝˣ) = realPart x :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_positiveSubgroupEquiv_apply_snd (x : positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((positiveSubgroupEquiv x).2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((x : IdeleGroup ℚ) : 𝔸[ℚ]).2 v :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `congrArg (fun q ↦ (q.1 : ℝˣ)) (positiveSubgroupEquiv.apply_symm_apply p) @[simp]`.
-/
theorem realPart_positiveSubgroupEquiv_symm_apply (p : Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (positiveSubgroupEquiv.symm p : IdeleGroup ℚ) = p.1 :=
  congrArg (fun q ↦ (q.1 : ℝˣ)) (positiveSubgroupEquiv.apply_symm_apply p)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_positiveSubgroupEquiv_symm_apply_snd (p : Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((positiveSubgroupEquiv.symm p : IdeleGroup ℚ) : 𝔸[ℚ]).2 v =
      ((p.2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) :=
  rfl

def integersRingEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃+* Π p : Nat.Primes, ℤ_[p] :=
  (RingEquiv.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

def integersHomeomorph :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃ₜ Π p : Nat.Primes, ℤ_[p] :=
  (Homeomorph.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph).trans
    (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem integersRingEquiv_eq_integersHomeomorph (x : Π v : HeightOneSpectrum (𝓞 ℚ),
    v.adicCompletionIntegers ℚ) : integersRingEquiv x = integersHomeomorph x :=
  rfl

/- English proof (translation)
The claim follows from `integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm`.
-/
theorem continuous_integersRingEquiv : Continuous integersRingEquiv :=
  integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm

/- English proof (translation)
Conclude with `continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph integersRingEquiv_eq_integersHomeomorph`.
-/
theorem continuous_integersRingEquiv_symm : Continuous integersRingEquiv.symm := by
  exact continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph
    integersRingEquiv_eq_integersHomeomorph

def integerUnitsEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      (Π p : Nat.Primes, ℤ_[p])ˣ :=
  ContinuousMulEquiv.piUnits.symm.trans
    (unitsContinuousMulEquiv integersRingEquiv.toMulEquiv continuous_integersRingEquiv
      continuous_integersRingEquiv_symm)

def integerUnitsEquivPi :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      Π p : Nat.Primes, ℤ_[p]ˣ :=
  integerUnitsEquiv.trans ContinuousMulEquiv.piUnits

def mulMap : ℚˣ × positiveSubgroup →* IdeleGroup ℚ :=
  (diagonal ℚ).coprod positiveSubgroup.subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulMap_apply (p : ℚˣ × positiveSubgroup) :
    mulMap p = diagonal ℚ p.1 * (p.2 : IdeleGroup ℚ) :=
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_one]`. Introduce and unpack `⟨a, u⟩ h`. Establish `h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1` using `h`. Establish `hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range` using `⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩`.

Rewrite `hu` using `[positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one]`. Establish `ha : diagonal ℚ a = 1` using `by rwa [hu, mul_one] at h'`. Conclude with `Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)`. Introduce `x`. Establish `hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range` using `positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x`.

Take `⟨u, hu, _, ⟨a, rfl⟩, rfl⟩` from `Subgroup.mem_sup.1 hx`. Conclude with `⟨(a, ⟨u, hu⟩), mul_comm _ _⟩`.
-/
theorem mulMap_bijective : Function.Bijective mulMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, u⟩ h
    have h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1 := h
    have hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range :=
      ⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩
    rw [positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one] at hu
    have ha : diagonal ℚ a = 1 := by rwa [hu, mul_one] at h'
    exact Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)
  · intro x
    have hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range :=
      positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x
    obtain ⟨u, hu, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(a, ⟨u, hu⟩), mul_comm _ _⟩

def ideleEquiv : IdeleGroup ℚ ≃* ℚˣ × Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  (MulEquiv.ofBijective mulMap mulMap_bijective).symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (positiveSubgroupEquiv.toMulEquiv.trans
      (MulEquiv.prodCongr (MulEquiv.refl _) integerUnitsEquivPi.toMulEquiv)))

def ideleClassGroupEquiv : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × (Π p : Nat.Primes, ℤ_[p])ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquiv))

def ideleClassGroupEquivPi : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquivPi))

/- English proof (translation)
Simplify using `only [ideleClassGroupEquiv, ContinuousMulEquiv.trans_apply]`. Rewrite using `[← positiveSubgroupEquivIdeleClassGroup_apply, ContinuousMulEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem ideleClassGroupEquiv_mk (x : positiveSubgroup) :
    ideleClassGroupEquiv (IdeleClassGroup.mk ℚ x) =
      (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
        integerUnitsEquiv (positiveSubgroupEquiv x).2) := by
  simp only [ideleClassGroupEquiv, ContinuousMulEquiv.trans_apply]
  rw [← positiveSubgroupEquivIdeleClassGroup_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

end RationalIdeles

end

end GroundTheory.Global
