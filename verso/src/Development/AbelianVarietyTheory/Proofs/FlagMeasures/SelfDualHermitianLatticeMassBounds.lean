import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassEqConstMulContent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteClasses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThickOrbitSelfDualUnramifiedLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodular

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unfold

open GlobalTheory.HL.TracePart

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `hi` using `((fixG L Hm Y).inv_mem hh).2.2`. Use extensionality with `v`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]`. Use `and_congr_left fun hv => ?_` and prove the remaining obligations. Use `hi v hv` as an intermediate fact.

Rewrite `this` using `[Submodule.mem_bot, sub_eq_zero]`. Rewrite using `[this]`.
-/
theorem smul_inf_eq {Y : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hh : h ∈ fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (h • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by
  have hi := ((fixG L Hm Y).inv_mem hh).2.2
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  refine and_congr_left fun hv => ?_
  have := hi v hv
  rw [Submodule.mem_bot, sub_eq_zero] at this
  rw [this]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩`. Use `⟨_, ⟨g * k * g⁻¹, ⟨?_, ?_⟩, rfl⟩, A, hA, ?_⟩` and prove the remaining obligations. Conclude with `(isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg hk.1) ((isomG L Hm).inv_mem hg)`.

Establish `h2 : k • Λ = Λ` using `hk.2 show (g * k * g⁻¹) • g • Λ = g • Λ`. Rewrite using `[mul_smul, mul_smul, inv_smul_smul, h2]`. Conclude with `map_rmul g _ A`. Introduce and unpack `⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩`. Use `⟨_, ⟨_, ⟨g⁻¹ * k * g, ⟨?_, ?_⟩, rfl⟩, A, hA, rfl⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg) hk.1) hg`. Establish `h2 : k • g • Λ = g • Λ` using `hk.2 show (g⁻¹ * k * g) • Λ = Λ`. Rewrite using `[mul_smul, mul_smul, h2, inv_smul_smul]`. Use `(map_rmul g _ A).trans ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `a`. Establish `e1 : ∀ v, g (g⁻¹ v) = v` using `fun v => g.apply_symm_apply v`. Use `show g (g⁻¹ (k (g (g⁻¹ (x a))))) = k (x a)`. Rewrite using `[e1, e1]`.
-/
theorem image_thick (ϖ : 𝒪[F]) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm)
    (Λ : Submodule L.O (Fin n → E)) (x : Fin m → Fin n → E) (i : ℕ) :
    (fun x a => g (x a)) '' thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) fun a => g⁻¹ (x a)) i =
      thick L ϖ (torb (isomG L Hm ⊓ stabL L (g • Λ)) x) i := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨g * k * g⁻¹, ⟨?_, ?_⟩, rfl⟩, A, hA, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg hk.1) ((isomG L Hm).inv_mem hg)
    · have h2 : k • Λ = Λ := hk.2
      show (g * k * g⁻¹) • g • Λ = g • Λ
      rw [mul_smul, mul_smul, inv_smul_smul, h2]
    · exact map_rmul g _ A
  · rintro ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩
    refine ⟨_, ⟨_, ⟨g⁻¹ * k * g, ⟨?_, ?_⟩, rfl⟩, A, hA, rfl⟩, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg) hk.1) hg
    · have h2 : k • g • Λ = g • Λ := hk.2
      show (g⁻¹ * k * g) • Λ = Λ
      rw [mul_smul, mul_smul, h2, inv_smul_smul]
    · refine (map_rmul g _ A).trans ?_
      congr 1
      funext a
      have e1 : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
      show g (g⁻¹ (k (g (g⁻¹ (x a))))) = k (x a)
      rw [e1, e1]

variable [IsNonarchimedeanLocalField F] [CharZero F]

/- English proof (translation)
Use `set Y := Submodule.span E (Set.range x) with hY`. Set `φ : ((Fin n → E) ≃ₗ[E] (Fin n → E)) → MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E))` to `fun g => Quotient.mk _ (g • Λs)`. Establish `hout : ∀ g, ∃ h ∈ fixG L Hm Y, (φ g).out = h • g • Λs`. Introduce `g`. Establish `: (MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (φ g).out (g • Λs)` using `Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (g • Λs)`.

Take `⟨h, hh⟩` from `MulAction.orbitRel_apply.1 this`. Conclude with `⟨h.1, h.2, hh.symm⟩`. Establish `hinj : ∀ g ∈ s, ∀ g' ∈ s, φ g = φ g' → g = g'`. Introduce `g hg g' hg' e`. Take `⟨h, hh, e1⟩` from `hout g`.

Take `⟨h', hh', e2⟩` from `hout g'`. Establish `hsd : IsSD L Hm (φ g).out`. Rewrite using `[e1]`. Conclude with `isSD_smul hh.1 (isSD_smul (h1 g hg).1 hs)`. Establish `htr : (φ g).out ⊓ Y.restrictScalars L.O = Mh`.

Rewrite using `[e1, smul_inf_eq hh, (h1 g hg).2]`. Conclude with `(h2 _ hsd htr).unique ⟨hg, h, hh, e1⟩ ⟨hg', h', hh', e ▸ e2⟩`. Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun g _ => by unfold invVol; positivity)]`. Unfold `sigMass`. Rewrite using `[tsum_eq_sum (s := s.image φ), Finset.sum_image hinj]`.

Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations. Take `⟨h, hh, e1⟩` from `hout g`. Establish `hsd` using `isSD_smul (h1 g hg).1 hs`. Rewrite using `[e1, if_pos ⟨isSD_smul hh.1 hsd, by rw [smul_inf_eq hh, (h1 g hg).2]⟩, GlobalTheory.HL.Unimod.unimodular L Hm hH m x hx Λ0 _ h0 hsd.1 h hh]`. Introduce `o ho`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨hsd, htr⟩`. Take `⟨g, ⟨hg, h, hh, e⟩, -⟩` from `h2 _ hsd htr`. Use `ho (Finset.mem_image.2 ⟨g, hg, ?_⟩)` and prove the remaining obligations. Rewrite using `[← Quotient.out_eq o]`.

Use `(Quotient.sound ?_).symm` and prove the remaining obligations. Conclude with `MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩`.
-/
theorem sigMass_eq_sum (hH : IsHermND L Hm) {Λs : Submodule L.O (Fin n → E)} (hs : IsSD L Hm Λs)
    (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) {Λ0 : Submodule L.O (Fin n → E)}
    (h0 : IsLat L Λ0) (Mh : Submodule L.O (Fin n → E))
    (s : Finset ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    (h1 : ∀ g ∈ s, g ∈ isomG L Hm ∧
      (g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh)
    (h2 : ∀ Λ, IsSD L Hm Λ → Λ ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh →
      ∃! g, g ∈ s ∧ ∃ h ∈ fixG L Hm (Submodule.span E (Set.range x)), Λ = h • g • Λs) :
    sigMass L Hm (Submodule.span E (Set.range x)) Λ0 Mh =
      ENNReal.ofReal (∑ g ∈ s, invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs))) := by
  set Y := Submodule.span E (Set.range x) with hY
  let φ : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →
      MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)) :=
    fun g => Quotient.mk _ (g • Λs)
  have hout : ∀ g, ∃ h ∈ fixG L Hm Y, (φ g).out = h • g • Λs := by
    intro g
    have : (MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (φ g).out (g • Λs) :=
      Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (g • Λs)
    obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.1 this
    exact ⟨h.1, h.2, hh.symm⟩
  have hinj : ∀ g ∈ s, ∀ g' ∈ s, φ g = φ g' → g = g' := by
    intro g hg g' hg' e
    obtain ⟨h, hh, e1⟩ := hout g
    obtain ⟨h', hh', e2⟩ := hout g'
    have hsd : IsSD L Hm (φ g).out := by
      rw [e1]; exact isSD_smul hh.1 (isSD_smul (h1 g hg).1 hs)
    have htr : (φ g).out ⊓ Y.restrictScalars L.O = Mh := by
      rw [e1, smul_inf_eq hh, (h1 g hg).2]
    exact (h2 _ hsd htr).unique ⟨hg, h, hh, e1⟩ ⟨hg', h', hh', e ▸ e2⟩
  rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => by unfold invVol; positivity)]
  unfold sigMass
  rw [tsum_eq_sum (s := s.image φ), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨h, hh, e1⟩ := hout g
    have hsd := isSD_smul (h1 g hg).1 hs
    rw [e1, if_pos ⟨isSD_smul hh.1 hsd, by rw [smul_inf_eq hh, (h1 g hg).2]⟩,
      GlobalTheory.HL.Unimod.unimodular L Hm hH m x hx Λ0 _ h0 hsd.1 h hh]
  · intro o ho
    rw [if_neg]
    rintro ⟨hsd, htr⟩
    obtain ⟨g, ⟨hg, h, hh, e⟩, -⟩ := h2 _ hsd htr
    refine ho (Finset.mem_image.2 ⟨g, hg, ?_⟩)
    rw [← Quotient.out_eq o]
    refine (Quotient.sound ?_).symm
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx hmn Λ0 h0`. Take `⟨κ, hκ, hk⟩` from `GlobalTheory.HL.QuotMass.mass_eq_const_mul_content L ϖ hϖ Hm hH Λs hs m x hx Λ0 h0`. Use `⟨κ, hκ, fun A hA hint => ?_⟩` and prove the remaining obligations. Take `⟨s, h1, h2, i1, h3⟩` from `trace_partition L ϖ hϖ Hm hH Λs hs m x hx A hA`. Take `⟨i2, h4⟩` from `GlobalTheory.PrimScale.cont_prim_scale L ϖ hϖ Hm hH Λs hs m x hx hmn A hA hint`.

Rewrite using `[sigMass_eq_sum hH hs x hx h0 _ s h1 h2]`. Establish `hg : ∀ g, ∃ j : ℕ, g ∈ s → ∀ i ≥ j, IsCO (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) ∧ invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs)) * cont (hermLat L m) (horb …`. Introduce `g`. Distinguish the cases in `hgs : g ∈ s`. Use `swap`.

Conclude with `⟨0, fun h => absurd h hgs⟩`. Establish `hgi` using `(h1 g hgs).1`. Take `⟨j1, hj1⟩` from `hk _ (isSD_smul hgi hs)`. Take `⟨e, he⟩` from `GlobalTheory.HL.QuotMass.exists_pow_smul L ϖ hϖ hs.1 (fun a => g⁻¹ (x a))`. Take `⟨j2, -, hj2⟩` from `GlobalTheory.ThickOrbit.main L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e`.

Use `⟨max j1 j2, fun _ i hi => ?_⟩` and prove the remaining obligations. Establish `hco` using `(hj2 i (le_of_max_le_right hi) (isomG L Hm ⊓ stabL L Λs) le_rfl (fun k hk hk' => ⟨hk, (GlobalTheory.HL.congruence_subgroup_facts L ϖ hϖ Λs hs.1 1).2.1 le_rfl k hk'⟩) (fun a => g⁻¹ (x a)) he (gramT_isom ((isomG L Hm).inv_mem hgi) x)).1`. Use `⟨hco, ?_⟩` and prove the remaining obligations. Rewrite using `[hj1 i (le_of_max_le_left hi), ← image_thick ϖ hgi, ((GlobalTheory.HL.TupleJac.tuple_jacobian L ϖ hϖ Hm hH Λs hs m).2 g hgi _ hco).2]`. Use `choose j hj using hg`.

Use `set i := max (max (max i1 i2) 1) (s.sup j) with hi`. Establish `hij : ∀ g ∈ s, j g ≤ i` using `fun g hg => (Finset.le_sup hg).trans (le_max_right _ _)`. Take `⟨hU, hD⟩` from `h3 i (by omega)`. Take `⟨hl, hu⟩` from `h4 i (by omega)`. Establish `hherm : IsHerm L (gramT L Hm x)`.

Use function extensionality and compare the values at `a b`. Conclude with `(GlobalTheory.HL.Unimod.hf_swap L hH.1 _ _).symm`. Establish `hpos` using `((GlobalTheory.CongGrp.congK_group L ϖ hϖ m i (by omega)).2.2 _ hherm hx).2`. Establish `hsum` using `(GlobalTheory.HL.cont_biUnion (tupLat L Λs m) s _ (fun g hg => (hj g hg i (hij g hg)).1)).2 hD`. Rewrite `hl`, `hu` using `[hU, hsum]`.

Establish `key` using `Finset.sum_congr rfl fun g (hg : g ∈ s) => (hj g hg i (hij g hg)).2`. Rewrite `key` using `[← Finset.sum_mul, ← Finset.mul_sum]`. Prove the components needed by the constructor for the conclusion. Use `ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)` and prove the remaining obligations. Rewrite using `[key]`.

Use `mul_le_mul_of_nonneg_left hl hκ.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)` and prove the remaining obligations. Rewrite using `[key]`. Use `mul_le_mul_of_nonneg_left hu hκ.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx hmn Λ0 h0
  obtain ⟨κ, hκ, hk⟩ := GlobalTheory.HL.QuotMass.mass_eq_const_mul_content L ϖ hϖ Hm hH Λs hs m x hx Λ0 h0
  refine ⟨κ, hκ, fun A hA hint => ?_⟩
  obtain ⟨s, h1, h2, i1, h3⟩ := trace_partition L ϖ hϖ Hm hH Λs hs m x hx A hA
  obtain ⟨i2, h4⟩ := GlobalTheory.PrimScale.cont_prim_scale L ϖ hϖ Hm hH Λs hs m x hx hmn A hA hint
  rw [sigMass_eq_sum hH hs x hx h0 _ s h1 h2]
  have hg : ∀ g, ∃ j : ℕ, g ∈ s → ∀ i ≥ j,
      IsCO (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) ∧
      invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs)) *
        cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) = κ * cont (tupLat L Λs m)
          (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) := by
    intro g
    by_cases hgs : g ∈ s
    swap
    · exact ⟨0, fun h => absurd h hgs⟩
    have hgi := (h1 g hgs).1
    obtain ⟨j1, hj1⟩ := hk _ (isSD_smul hgi hs)
    obtain ⟨e, he⟩ := GlobalTheory.HL.QuotMass.exists_pow_smul L ϖ hϖ hs.1 (fun a => g⁻¹ (x a))
    obtain ⟨j2, -, hj2⟩ := GlobalTheory.ThickOrbit.main L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e
    refine ⟨max j1 j2, fun _ i hi => ?_⟩
    have hco := (hj2 i (le_of_max_le_right hi) (isomG L Hm ⊓ stabL L Λs) le_rfl
      (fun k hk hk' => ⟨hk, (GlobalTheory.HL.congruence_subgroup_facts L ϖ hϖ Λs hs.1 1).2.1 le_rfl k hk'⟩)
      (fun a => g⁻¹ (x a)) he (gramT_isom ((isomG L Hm).inv_mem hgi) x)).1
    refine ⟨hco, ?_⟩
    rw [hj1 i (le_of_max_le_left hi), ← image_thick ϖ hgi,
      ((GlobalTheory.HL.TupleJac.tuple_jacobian L ϖ hϖ Hm hH Λs hs m).2 g hgi _ hco).2]
  choose j hj using hg
  set i := max (max (max i1 i2) 1) (s.sup j) with hi
  have hij : ∀ g ∈ s, j g ≤ i := fun g hg => (Finset.le_sup hg).trans (le_max_right _ _)
  obtain ⟨hU, hD⟩ := h3 i (by omega)
  obtain ⟨hl, hu⟩ := h4 i (by omega)
  have hherm : IsHerm L (gramT L Hm x) := by
    funext a b
    exact (GlobalTheory.HL.Unimod.hf_swap L hH.1 _ _).symm
  have hpos := ((GlobalTheory.CongGrp.congK_group L ϖ hϖ m i (by omega)).2.2 _ hherm hx).2
  have hsum := (GlobalTheory.HL.cont_biUnion (tupLat L Λs m) s _
    (fun g hg => (hj g hg i (hij g hg)).1)).2 hD
  rw [hU, hsum] at hl hu
  have key := Finset.sum_congr rfl fun g (hg : g ∈ s) => (hj g hg i (hij g hg)).2
  rw [← Finset.sum_mul, ← Finset.mul_sum] at key
  constructor
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hl hκ.le
    linarith
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hu hκ.le
    linarith

end GlobalTheory.HL.Unfold
