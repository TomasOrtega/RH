import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumPointDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumPointDeg

variable {k : Type u} [Field k] {N : ℕ}

abbrev OneRing (k : Type u) [Field k] (N : ℕ) : Type u := NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k

abbrev coneField (P : Ideal (OneRing k N)) [P.IsPrime] : Type u := FractionRing (OneRing k N ⧸ P)

instance small_coneField [Small.{w} k] (P : Ideal (OneRing k N)) [P.IsPrime] : Small.{w} (coneField P) := by
  have : Small.{w} (OneRing k N ⧸ P) := small_of_surjective Ideal.Quotient.mk_surjective
  refine small_of_surjective (α := (OneRing k N ⧸ P) × nonZeroDivisors (OneRing k N ⧸ P))
    (f := fun z => IsLocalization.mk' (coneField P) z.1 z.2) fun z => ?_
  obtain ⟨q, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OneRing k N ⧸ P)) z
  exact ⟨q, rfl⟩

variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

def coneHom : OneRing k N →ₐ[k] Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  (Shrink.algEquiv k _).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k (OneRing k N ⧸ pp.comap (oneBlock (S := k) (N := N)).toRingHom) _).comp
      (Ideal.Quotient.mkₐ k (pp.comap (oneBlock (S := k) (N := N)).toRingHom)))

def pt : Fin (N + 1) → Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  fun i => coneHom pp (X ⟨(), i⟩)

/- English proof (translation)
Use `show (Shrink.algEquiv k (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom))).symm (algebraMap _ (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) (Ideal.Quotient.mk (pp.comap (oneBlock (S := k) (N := N)).toRingHom) f)) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ (AlgEquiv.injective _), IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Both sides reduce to the same expression.
-/
theorem coneHom_eq_zero_iff (f : OneRing k N) :
    coneHom.{u, w} pp f = 0 ↔ oneBlock (S := k) (N := N) f ∈ pp := by
  show (Shrink.algEquiv k (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom))).symm
    (algebraMap _ (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) (Ideal.Quotient.mk (pp.comap (oneBlock (S := k) (N := N)).toRingHom) f)) = 0 ↔ _
  rw [map_eq_zero_iff _ (AlgEquiv.injective _), IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply]`. Use `congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext fun v => ?_)) f` and prove the remaining obligations. Break down `v with ⟨⟨⟩, i⟩` into its components or cases. Rewrite using `[AlgHom.comp_apply]`. Use `show aeval (pt.{u, w} pp) (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) (X ⟨(), i⟩)) = _`.

Rewrite using `[rename_X, aeval_X]`. Both sides reduce to the same expression.
-/
theorem aeval_pt_oneBlock (f : OneRing k N) :
    aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) = coneHom pp f := by
  rw [← AlgHom.comp_apply]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext fun v => ?_)) f
  rcases v with ⟨⟨⟩, i⟩
  rw [AlgHom.comp_apply]
  show aeval (pt.{u, w} pp) (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) (X ⟨(), i⟩)) = _
  rw [rename_X, aeval_X]
  rfl

/- English proof (translation)
Rewrite using `[oneBlock, rename_rename]`. Conclude with `(congrArg (fun g => rename g f) (HilbertPositive.blockEquiv N).self_comp_symm).trans (rename_id_apply f)`.
-/
theorem oneBlock_surjective (f : Poly k N) :
    oneBlock (S := k) (N := N) (rename (HilbertPositive.blockEquiv N).symm f) = f := by
  rw [oneBlock, rename_rename]
  exact (congrArg (fun g => rename g f) (HilbertPositive.blockEquiv N).self_comp_symm).trans (rename_id_apply f)

/- English proof (translation)
Rewrite using `[← oneBlock_surjective f, aeval_pt_oneBlock, coneHom_eq_zero_iff]`.
-/
theorem aeval_pt_eq_zero_iff (f : Poly k N) : aeval (pt.{u, w} pp) f = 0 ↔ f ∈ pp := by
  rw [← oneBlock_surjective f, aeval_pt_oneBlock, coneHom_eq_zero_iff]

/- English proof (translation)
Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Rewrite using `[← sum_homogeneousComponent f]`. Use `Ideal.sum_mem _ fun d _ => ?_` and prove the remaining obligations.

Conclude with `(aeval_pt_eq_zero_iff pp _).1 ((mem_primeOf_of_isHomogeneous _ (homogeneousComponent_isHomogeneous d f)).1 (homogeneousComponent_mem_primeOf _ hf d))`. Introduce `hf`. Rewrite using `[← sum_homogeneousComponent f]`. Conclude with `Ideal.sum_mem _ fun d _ => (mem_primeOf_of_isHomogeneous _ (homogeneousComponent_isHomogeneous d f)).2 ((aeval_pt_eq_zero_iff pp _).2 (hh f hf d))`.
-/
theorem primeOf_pt (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) :
    primeOf (S := k) (pt.{u, w} pp) = pp := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    refine Ideal.sum_mem _ fun d _ => ?_
    exact (aeval_pt_eq_zero_iff pp _).1 ((mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).1 (homogeneousComponent_mem_primeOf _ hf d))
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun d _ => (mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).2 ((aeval_pt_eq_zero_iff pp _).2 (hh f hf d))

/- English proof (translation)
Establish `h1 : f.IsHomogeneous (b ())`. Introduce `d hd`. Use `congrFun (hf hd) ()` as an intermediate fact. Rewrite `this` using `[HilbertPositive.weight_blockWeight_one]`. Use `show Finsupp.weight (fun _ => 1) d = b ()`.

Rewrite using `[← Finsupp.degree_eq_weight_one]`. Conclude with `this`. Conclude with `h1.rename_isHomogeneous`.
-/
theorem isHomogeneous_oneBlock {f : OneRing k N} {b : Unit → ℕ} (hf : NumbersDVR.IsMultiHomog f b) :
    (oneBlock (S := k) (N := N) f).IsHomogeneous (b ()) := by
  have h1 : f.IsHomogeneous (b ()) := by
    intro d hd
    have := congrFun (hf hd) ()
    rw [HilbertPositive.weight_blockWeight_one] at this
    show Finsupp.weight (fun _ => 1) d = b ()
    rw [← Finsupp.degree_eq_weight_one]
    exact this
  exact h1.rename_isHomogeneous

/- English proof (translation)
Use `set P := pp.comap (oneBlock (S := k) (N := N)).toRingHom`. Establish `hΦ : ∀ f : OneRing k N, (Shrink.algEquiv k (coneField P)).symm (algebraMap (OneRing k N ⧸ P) (coneField P) (Ideal.Quotient.mk P f)) = aeval (pt.{u, w} pp) (oneBlock (S` using `k) (N := N) f) := fun f => by`. Rewrite using `[aeval_pt_oneBlock]`. Both sides reduce to the same expression. Take `⟨i, hi⟩` from `hrel`.

Establish `hyi : pt.{u, w} pp i ≠ 0`. Rewrite using `[← aeval_X (R := k) (pt.{u, w} pp) i, Ne, aeval_pt_eq_zero_iff]`. Conclude with `hi`. Establish `hmap : (FieldNumbers.homFracDegZero P).map (Shrink.algEquiv k (coneField P)).symm.toAlgHom = funField (k` using `k) (pt.{u, w} pp) := by`. Rewrite using `[FieldNumbers.homFracDegZero, IntermediateField.adjoin_map]`.

Use `le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩`. Establish `hF` using `isHomogeneous_oneBlock hf`. Establish `hG` using `isHomogeneous_oneBlock hg`. Establish `hchart : ∀ (F : Poly k N), F.IsHomogeneous (b ()) → aeval (pt.{u, w} pp) F / pt.{u, w} pp i ^ b () ∈ funField (k` using `k) (pt.{u, w} pp) := fun F hF' => VeryAmpleDim.mem_funField_of_mem_chartRing hyi ⟨F, X i ^ b (), b (), pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _, hF', isHomogeneous_X_pow _ _, by rw [map_pow, aeval_X]⟩`.

Use `IntermediateField.div_mem _ (hchart _ hF) (hchart _ hG) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[div_div_div_cancel_right₀ (pow_ne_zero (b ()) hyi), ← hΦ, ← hΦ, map_div₀]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨j, l, hj, rfl⟩`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises.

Establish `hjP : (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1)) : OneRing k N) ∉ P`. Express the relevant statement in the definitionally equal form `oneBlock (S := k) (N := N) (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1))) ∉ pp`. Rewrite using `[← aeval_pt_eq_zero_iff, aeval_pt_oneBlock]`. Conclude with `hj`. Use `⟨_, ⟨NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)) ⟨(), l⟩, X ⟨(), l⟩, X ⟨(), j⟩, isWeightedHomogeneous_X k _ _, isWeightedHomogeneous_X k _ _, hjP, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, map_div₀, hΦ, aeval_pt_oneBlock]`. Both sides reduce to the same expression. Unfold `FieldNumbers.resDeg`. Rewrite using `[dif_pos (inferInstance : P.IsPrime), ← hmap]`. Conclude with `((FieldNumbers.homFracDegZero P).equivMap _).toLinearEquiv.finrank_eq.symm`.
-/
theorem finrank_funField_pt (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    Module.finrank k (funField (k := k) (pt.{u, w} pp)) =
      FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) := by
  set P := pp.comap (oneBlock (S := k) (N := N)).toRingHom
  have hΦ : ∀ f : OneRing k N, (Shrink.algEquiv k (coneField P)).symm
      (algebraMap (OneRing k N ⧸ P) (coneField P) (Ideal.Quotient.mk P f)) =
        aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) := fun f => by
    rw [aeval_pt_oneBlock]; rfl
  obtain ⟨i, hi⟩ := hrel
  have hyi : pt.{u, w} pp i ≠ 0 := by
    rw [← aeval_X (R := k) (pt.{u, w} pp) i, Ne, aeval_pt_eq_zero_iff]; exact hi
  have hmap : (FieldNumbers.homFracDegZero P).map (Shrink.algEquiv k (coneField P)).symm.toAlgHom =
      funField (k := k) (pt.{u, w} pp) := by
    rw [FieldNumbers.homFracDegZero, IntermediateField.adjoin_map]
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
      have hF := isHomogeneous_oneBlock hf
      have hG := isHomogeneous_oneBlock hg
      have hchart : ∀ (F : Poly k N), F.IsHomogeneous (b ()) →
          aeval (pt.{u, w} pp) F / pt.{u, w} pp i ^ b () ∈ funField (k := k) (pt.{u, w} pp) := fun F hF' =>
        VeryAmpleDim.mem_funField_of_mem_chartRing hyi ⟨F, X i ^ b (), b (), pow_mem (X_mem_monos
          (Finset.mem_singleton_self i)) _, hF', isHomogeneous_X_pow _ _, by rw [map_pow, aeval_X]⟩
      convert IntermediateField.div_mem _ (hchart _ hF) (hchart _ hG) using 1
      rw [div_div_div_cancel_right₀ (pow_ne_zero (b ()) hyi), ← hΦ, ← hΦ, map_div₀]
      rfl
    · rintro _ ⟨j, l, hj, rfl⟩
      apply IntermediateField.subset_adjoin
      have hjP : (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1)) : OneRing k N) ∉ P := by
        change oneBlock (S := k) (N := N) (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1))) ∉ pp
        rw [← aeval_pt_eq_zero_iff, aeval_pt_oneBlock]; exact hj
      refine ⟨_, ⟨NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)) ⟨(), l⟩, X ⟨(), l⟩, X ⟨(), j⟩,
        isWeightedHomogeneous_X k _ _,
        isWeightedHomogeneous_X k _ _, hjP, rfl⟩, ?_⟩
      simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, map_div₀, hΦ, aeval_pt_oneBlock]
      rfl
  unfold FieldNumbers.resDeg
  rw [dif_pos (inferInstance : P.IsPrime), ← hmap]
  exact ((FieldNumbers.homFracDegZero P).equivMap _).toLinearEquiv.finrank_eq.symm

end InterNumPointDeg

/- English proof (translation)
Introduce `k _ Ω _ _ N x pp h`. Use `haveI : Small.{w} k := small_of_injective (algebraMap k Ω).injective`. Use `haveI := h.isPrime`. Establish `hpt` using `InterNumPointDeg.primeOf_pt.{u, w} pp h.homog`. Establish `hsub : IsSubvar (InterNumPointDeg.pt.{u, w} pp) pp 0` using `⟨h.isPrime, h.homog, hpt.le, h.relevant, h.dim⟩`.

Establish `hxy : ∀ i, InterNumPointDeg.pt.{u, w} pp i ≠ 0 → x i ≠ 0`. Introduce `i hi hx`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← aeval_X (R := k) (InterNumPointDeg.pt.{u, w} pp) i, InterNumPointDeg.aeval_pt_eq_zero_iff]`. Conclude with `h.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).2 (by rw [aeval_X, hx]))`.

Establish `h1` using `hIR k Ω N x _ (InterNumPointDeg.pt.{u, w} pp) hxy (hpt.symm ▸ h.le) pp 0 hsub Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0)`. Establish `h2` using `InterNumPoint.proof HilbertPoint.proof k _ N (InterNumPointDeg.pt.{u, w} pp) (hpt.symm ▸ hsub) ![]`. Rewrite `h2` using `[hpt]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem InterNumPointDeg.proof (hIR : InterNumRestrict.Statement.{u, w}) : InterNumPointDeg.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  haveI : Small.{w} k := small_of_injective (algebraMap k Ω).injective
  haveI := h.isPrime
  have hpt := InterNumPointDeg.primeOf_pt.{u, w} pp h.homog
  have hsub : IsSubvar (InterNumPointDeg.pt.{u, w} pp) pp 0 := ⟨h.isPrime, h.homog, hpt.le, h.relevant, h.dim⟩
  have hxy : ∀ i, InterNumPointDeg.pt.{u, w} pp i ≠ 0 → x i ≠ 0 := by
    intro i hi hx
    apply hi
    rw [← aeval_X (R := k) (InterNumPointDeg.pt.{u, w} pp) i, InterNumPointDeg.aeval_pt_eq_zero_iff]
    exact h.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).2 (by rw [aeval_X, hx]))
  have h1 := hIR k Ω N x _ (InterNumPointDeg.pt.{u, w} pp) hxy (hpt.symm ▸ h.le) pp 0 hsub
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0)
  have h2 := InterNumPoint.proof HilbertPoint.proof k _ N (InterNumPointDeg.pt.{u, w} pp)
    (hpt.symm ▸ hsub) ![]
  rw [hpt] at h2
  calc interNum pp (![] : Fin 0 → SubSystem k x Ω)
      = interNum pp (fun i : Fin 0 => (Fin.elim0 i : LineBundle k x).toSubSystem) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h1.symm
    _ = interNum pp (![] : Fin 0 → SubSystem k (InterNumPointDeg.pt.{u, w} pp) _) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h2
    _ = _ := by rw [InterNumPointDeg.finrank_funField_pt pp h.relevant]

end

end GroundTheory.Heights₂.Heights.Kleiman
