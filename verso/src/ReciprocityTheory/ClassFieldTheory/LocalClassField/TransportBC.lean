import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

open scoped commutatorElement

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

noncomputable def Model.mapField (L : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (L.toSubfield.map (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x =>
    ⟨algebraMap K _ (m.e.symm (algebraMap ℚ_[p] m.K' x)), L.algebraMap_mem _, by
      show m.E _ = _
      rw [m.comm, RingEquiv.apply_symm_apply]
      rfl⟩

/- English proof (translation)
Introduce `x` and use `⟨by rintro ⟨y, hy, hyx⟩; rwa [← m.E.injective hyx], fun hx => ⟨x, hx, rfl⟩⟩`.
-/
theorem Model.corr_mapField (L : IntermediateField K (AlgebraicClosure K)) : m.Corr L (m.mapField L) := fun x =>
  ⟨by rintro ⟨y, hy, hyx⟩; rwa [← m.E.injective hyx], fun hx => ⟨x, hx, rfl⟩⟩

noncomputable def Model.comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    IntermediateField K (AlgebraicClosure K) :=
  (L'.toSubfield.comap (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x => by
    show m.E (algebraMap K _ x) ∈ L'
    rw [m.comm]
    exact h (m.e x).2

/- English proof (translation)
Introduce `_` and use `Iff.rfl`.
-/
theorem Model.corr_comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    m.Corr (m.comapField L' h) L' := fun _ => Iff.rfl

variable {m} {L : IntermediateField K (AlgebraicClosure K)} {L' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Introduce `x hx` and use `by have := (h (algebraMap K _ (m.e.symm ⟨x, hx⟩))).2 (L.algebraMap_mem _) rwa [m.comm, RingEquiv.apply_symm_apply] at this`.
-/
theorem Model.Corr.le (h : m.Corr L L') : m.K' ≤ L' := fun x hx => by
  have := (h (algebraMap K _ (m.e.symm ⟨x, hx⟩))).2 (L.algebraMap_mem _)
  rwa [m.comm, RingEquiv.apply_symm_apply] at this

noncomputable def Model.Corr.equiv (h : m.Corr L L') : L ≃+* IntermediateField.extendScalars h.le where
  toFun x := ⟨m.E x, (h x).2 x.2⟩
  invFun y := ⟨m.E.symm y, (h _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (m.E.symm_apply_apply _)
  right_inv y := Subtype.ext (m.E.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul m.E _ _)
  map_add' x y := Subtype.ext (map_add m.E _ _)

/- English proof (translation)
The claim follows from `RingHom.ext fun x => Subtype.ext (m.comm x).symm`.
-/
theorem Model.Corr.equiv_comp (h : m.Corr L L') :
    (algebraMap m.K' (IntermediateField.extendScalars h.le)).comp (m.e : K →+* m.K') =
      (h.equiv : L →+* IntermediateField.extendScalars h.le).comp (algebraMap K L) :=
  RingHom.ext fun x => Subtype.ext (m.comm x).symm

/- English proof (translation)
The claim follows from `RingHom.ext fun x => Subtype.ext (m.E_symm_coe x).symm`.
-/
theorem Model.Corr.equiv_symm_comp (h : m.Corr L L') :
    (algebraMap K L).comp (m.e.symm : m.K' →+* K) =
      (h.equiv.symm : IntermediateField.extendScalars h.le →+* L).comp
        (algebraMap m.K' (IntermediateField.extendScalars h.le)) :=
  RingHom.ext fun x => Subtype.ext (m.E_symm_coe x).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hL`. Establish `h1 : Module.Finite m.K' (IntermediateField.extendScalars h.le)` using `Module.Finite.of_equiv_equiv m.e h.equiv h.equiv_comp`. Use `m.fin` as an intermediate fact. Establish `h2 : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h.le)` using `FiniteDimensional.trans ℚ_[p] m.K' _`.

Conclude with `h2`. Introduce `hL'`. Use `finDim_extendScalars_of_le p hL' h.le` as an intermediate fact. Conclude with `Module.Finite.of_equiv_equiv m.e.symm h.equiv.symm h.equiv_symm_comp`.
-/
theorem Model.Corr.finite_iff (h : m.Corr L L') : FiniteDimensional K L ↔ FiniteDimensional ℚ_[p] L' := by
  constructor
  · intro hL
    have h1 : Module.Finite m.K' (IntermediateField.extendScalars h.le) :=
      Module.Finite.of_equiv_equiv m.e h.equiv h.equiv_comp
    have := m.fin
    have h2 : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h.le) :=
      FiniteDimensional.trans ℚ_[p] m.K' _
    exact h2
  · intro hL'
    have := finDim_extendScalars_of_le p hL' h.le
    exact Module.Finite.of_equiv_equiv m.e.symm h.equiv.symm h.equiv_symm_comp

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_of_equiv_equiv m.e h.equiv h.equiv_comp, RingEquiv.apply_symm_apply]`.
-/
theorem Model.Corr.norm_eq (h : m.Corr L L') (z : L) :
    m.e (Algebra.norm K z) = Algebra.norm m.K' (h.equiv z) := by
  rw [Algebra.norm_eq_of_equiv_equiv m.e h.equiv h.equiv_comp, RingEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[IntermediateField.mem_fixingSubgroup_iff, mem_subG_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hg y hy`. Establish `hx : m.E.symm y ∈ L` using `(h _).1 (by rwa [RingEquiv.apply_symm_apply])`. Use `hφ g (m.E.symm y)` as an intermediate fact.

Rewrite `this` using `[hg _ hx, RingEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `hg x hx`. Apply `m.E.injective` to reduce the goal to its premises. Rewrite using `[← hφ]`. Conclude with `hg _ ((h x).2 hx)`.
-/
theorem Model.mem_fixingSubgroup_iff_model {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L')
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : g ∈ L.fixingSubgroup ↔ φ g ∈ subG p m.K' L' := by
  rw [IntermediateField.mem_fixingSubgroup_iff, mem_subG_iff]
  constructor
  · intro hg y hy
    have hx : m.E.symm y ∈ L := (h _).1 (by rwa [RingEquiv.apply_symm_apply])
    have := hφ g (m.E.symm y)
    rwa [hg _ hx, RingEquiv.apply_symm_apply] at this
  · intro hg x hx
    apply m.E.injective
    rw [← hφ]
    exact hg _ ((h x).2 hx)

/- English proof (translation)
Use `hL.isGalois` as an intermediate fact. Rewrite using `[abRestrict_mk, ← Model.mem_fixingSubgroup_iff_model hφ h g, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]`.
-/
theorem Model.abelian_restriction_eq_one_iff {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L') (hL : IsFiniteAbelian K L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    abRestrict K L hL (toAb K g) = 1 ↔ φ g ∈ subG p m.K' L' := by
  have := hL.isGalois
  rw [abRestrict_mk, ← Model.mem_fixingSubgroup_iff_model hφ h g, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker]

/- English proof (translation)
Rewrite using `[commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]`.
-/
theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (commutator G).map (φ : G →* H) = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]

/- English proof (translation)
Establish `hφ` using `m.isGalIso_galIso`. Prove the components needed by the constructor for the conclusion. Introduce `hL`. Use `⟨h.le, h.finite_iff.1 hL.finiteDimensional, ?_⟩` and prove the remaining obligations. Introduce `τ hτ`.

Rewrite `hτ` using `[← map_commutator_mulEquiv m.galIso]`. Take `⟨g, hg, rfl⟩` from `hτ`. Use `show m.galIso g ∈ _`. Rewrite using `[← Model.abelian_restriction_eq_one_iff hφ h hL]`. Establish `h1 : toAb K g = 1` using `(QuotientGroup.eq_one_iff (N := Subgroup.topologicalClosure (commutator (Field.absoluteGaloisGroup K))) g).2 (Subgroup.le_topologicalClosure (G := Field.absoluteGaloisGroup K) _ hg)`.

Rewrite using `[h1, map_one]`. Introduce `hL'`. Use `m.charZero` as an intermediate fact. Establish `hfd` using `h.finite_iff.2 hL'.fin`. Establish `hn : L.fixingSubgroup.Normal`.

Establish `h1 : L.fixingSubgroup = (subG p m.K' L').comap m.galIso.toMonoidHom`. Use extensionality with `g`. Conclude with `Model.mem_fixingSubgroup_iff_model hφ h g`. Rewrite using `[h1]`. Use `hL'.normal` as an intermediate fact.

Use `infer_instance`. Establish `hG : IsGalois K L` using `(InfiniteGalois.normal_iff_isGalois L).1 hn`. Use `⟨hfd, hG, fun a b => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) a`. Take `⟨g', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) b`.

Rewrite using `[← map_mul, ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, Model.mem_fixingSubgroup_iff_model hφ h]`. Apply `hL'.comm` to reduce the goal to its premises. Establish `h2 : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆`. Rewrite using `[commutatorElement_def]`. Use `group`.

Rewrite using `[h2, map_commutatorElement]`. Conclude with `Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)`.
-/
theorem Model.isFiniteAbelian_iff_model (h : m.Corr L L') : IsFiniteAbelian K L ↔ IsAbLK p m.K' L' := by
  have hφ := m.isGalIso_galIso
  constructor
  · intro hL
    refine ⟨h.le, h.finite_iff.1 hL.finiteDimensional, ?_⟩
    intro τ hτ
    rw [← map_commutator_mulEquiv m.galIso] at hτ
    obtain ⟨g, hg, rfl⟩ := hτ
    show m.galIso g ∈ _
    rw [← Model.abelian_restriction_eq_one_iff hφ h hL]
    have h1 : toAb K g = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.topologicalClosure (commutator (Field.absoluteGaloisGroup K))) g).2
        (Subgroup.le_topologicalClosure (G := Field.absoluteGaloisGroup K) _ hg)
    rw [h1, map_one]
  · intro hL'
    have := m.charZero
    have hfd := h.finite_iff.2 hL'.fin
    have hn : L.fixingSubgroup.Normal := by
      have h1 : L.fixingSubgroup = (subG p m.K' L').comap m.galIso.toMonoidHom := by
        ext g
        exact Model.mem_fixingSubgroup_iff_model hφ h g
      rw [h1]
      have := hL'.normal
      infer_instance
    have hG : IsGalois K L := (InfiniteGalois.normal_iff_isGalois L).1 hn
    refine ⟨hfd, hG, fun a b => ?_⟩
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) a
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) b
    rw [← map_mul, ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, Model.mem_fixingSubgroup_iff_model hφ h]
    apply hL'.comm
    have h2 : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [h2, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/- English proof (translation)
Establish `hL'` using `h.finite_iff.1 hL`. Rewrite using `[mem_normGrp_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Set `y' : (PadicAlgCl p)ˣ` to `Units.map (m.E : AlgebraicClosure K →* PadicAlgCl p) (Units.map (algebraMap L (AlgebraicClosure K) : L →* AlgebraicClosure K) y)`.

Establish `hy' : (Additive.ofMul y' : KbarMult p) ∈ multOf p L'` using `(h _).2 y.1.2`. Use `⟨Additive.ofMul y', hy', ?_⟩` and prove the remaining obligations. Use `Additive.toMul.injective (Units.ext ?_)` and prove the remaining obligations. Use `(normHom_eq_algebraNorm hL' h.le _ hy').trans ?_` and prove the remaining obligations. Conclude with `congrArg Subtype.val (h.norm_eq (y : L)).symm`.

Introduce and unpack `⟨y, hy, hyx⟩`. Set `w : IntermediateField.extendScalars h.le` to `⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩`. Establish `hw : w ≠ 0` using `fun h0 => (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)`. Establish `hz : h.equiv.symm w ≠ 0` using `by simpa using hw`. Use `⟨Units.mk0 _ hz, Units.ext (m.e.injective (Subtype.ext ?_))⟩` and prove the remaining obligations.

Use `show ((m.e (Algebra.norm K (h.equiv.symm w)) : m.K') : PadicAlgCl p) = _`. Rewrite using `[h.norm_eq, RingEquiv.apply_symm_apply, ← normHom_eq_algebraNorm hL' h.le y hy, hyx]`. Both sides reduce to the same expression.
-/
theorem Model.mem_normGroup_iff_model (h : m.Corr L L') (hL : FiniteDimensional K L) (x : Kˣ) :
    x ∈ normGroup K L ↔ m.eU x ∈ normGrp p m.K' L' := by
  have hL' := h.finite_iff.1 hL
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, rfl⟩
    let y' : (PadicAlgCl p)ˣ := Units.map (m.E : AlgebraicClosure K →* PadicAlgCl p)
      (Units.map (algebraMap L (AlgebraicClosure K) : L →* AlgebraicClosure K) y)
    have hy' : (Additive.ofMul y' : KbarMult p) ∈ multOf p L' := (h _).2 y.1.2
    refine ⟨Additive.ofMul y', hy', ?_⟩
    refine Additive.toMul.injective (Units.ext ?_)
    refine (normHom_eq_algebraNorm hL' h.le _ hy').trans ?_
    exact congrArg Subtype.val (h.norm_eq (y : L)).symm
  · rintro ⟨y, hy, hyx⟩
    let w : IntermediateField.extendScalars h.le := ⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩
    have hw : w ≠ 0 := fun h0 => (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)
    have hz : h.equiv.symm w ≠ 0 := by simpa using hw
    refine ⟨Units.mk0 _ hz, Units.ext (m.e.injective (Subtype.ext ?_))⟩
    show ((m.e (Algebra.norm K (h.equiv.symm w)) : m.K') : PadicAlgCl p) = _
    rw [h.norm_eq, RingEquiv.apply_symm_apply, ← normHom_eq_algebraNorm hL' h.le y hy, hyx]
    rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
