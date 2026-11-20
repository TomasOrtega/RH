import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftM
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.HaarIdx

noncomputable section

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel PI.IntegralDiscriminantMembership

/- English proof (translation)
Use `haveI := hfin`. Use `haveI : Finite (Ideal (R ⧸ Ideal.span {c})) := Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {c}) => (I : Set (R ⧸ Ideal.span {c}))) SetLike.coe_injective`. Use `(Set.finite_univ.image (fun J : Ideal (R ⧸ Ideal.span {c}) => Ideal.comap (Ideal.Quotient.mk _) J)).subset ?_` and prove the remaining obligations. Introduce `m hm`. Use `⟨Ideal.map (Ideal.Quotient.mk _) m, Set.mem_univ _, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Conclude with `sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem m).mpr (hc m hm))`.
-/
theorem finite_max_of {R : Type*} [CommRing R] (c : R) (hc : ∀ m : Ideal R, m.IsMaximal → c ∈ m)
    (hfin : Finite (R ⧸ Ideal.span {c})) : {m : Ideal R | m.IsMaximal}.Finite := by
  haveI := hfin
  haveI : Finite (Ideal (R ⧸ Ideal.span {c})) :=
    Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {c}) => (I : Set (R ⧸ Ideal.span {c}))) SetLike.coe_injective
  refine (Set.finite_univ.image (fun J : Ideal (R ⧸ Ideal.span {c}) => Ideal.comap (Ideal.Quotient.mk _) J)).subset ?_
  intro m hm
  refine ⟨Ideal.map (Ideal.Quotient.mk _) m, Set.mem_univ _, ?_⟩
  dsimp only
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem m).mpr (hc m hm))

/- English proof (translation)
Use `(h.image (fun n : Ideal S => Ideal.comap e n)).subset ?_` and prove the remaining obligations. Introduce `m hm`. Use `haveI : m.IsMaximal := hm`. Use `⟨Ideal.map e m, Ideal.map_isMaximal_of_equiv e, ?_⟩` and prove the remaining obligations. Use `first`.

Consider the case `exact Ideal.comap_map_of_bijective _ e.bijective`. Consider the case `exact Ideal.comap_map_of_bijective e e.bijective`. Consider the case `simp`.
-/
theorem finite_max_of_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : {m : Ideal S | m.IsMaximal}.Finite) : {m : Ideal R | m.IsMaximal}.Finite := by
  refine (h.image (fun n : Ideal S => Ideal.comap e n)).subset ?_
  intro m hm
  haveI : m.IsMaximal := hm
  refine ⟨Ideal.map e m, Ideal.map_isMaximal_of_equiv e, ?_⟩
  first
  | exact Ideal.comap_map_of_bijective _ e.bijective
  | exact Ideal.comap_map_of_bijective e e.bijective
  | simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Use `hOK.loc` as an intermediate fact. Use `haveI : IsLocalRing 𝒪[F] := inferInstance`. Take `⟨⟨tr, htr⟩, ⟨nr, hnr⟩⟩` from `(mem_O_iff M r).mp r.2`. Use `set x : E := 1 - algebraMap F E (π : F) * r with hx`. Establish `hcj : M.L.cj x = 1 - algebraMap F E (π : F) * M.L.cj r`.

Rewrite using `[hx, map_sub, map_one, map_mul, cj_alg]`. Establish `hN : x * M.L.cj x = algebraMap F E ((1 : F) - (π : F) * ((tr : F) - (π : F) * (nr : F)))`. Rewrite using `[hcj, hx]`. Simplify using `only [map_sub, map_one, map_mul]`. Rewrite using `[htr, hnr]`.

Expand and normalize the polynomial expressions, which then agree. Use `set n : 𝒪[F] := 1 - π * (tr - π * nr) with hn`. Establish `hnu : IsUnit n`. Apply `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` to reduce the goal to its premises. Conclude with `mul_mem_nonunits_left hπ`.

Take `⟨nu, hnu'⟩` from `hnu`. Establish `hNn : x * M.L.cj x = algebraMap F E (n : F)` using `by rw [hN, hn]; push_cast; ring_nf`. Establish `hyO : M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) ∈ M.L.O` using `M.L.O.mul_mem (Formalism.L2.SG.Pf.Cnt.DualityBasisChange.cj_mem_O (M := M) x (by`. Rewrite using `[hx]`. Conclude with `M.L.O.sub_mem M.L.O.one_mem (M.L.O.mul_mem ((alg_mem_O M).mpr π.2) r.2)))`.

Use the proof step `((alg_mem_O M).mpr (nu⁻¹ : 𝒪[F]ˣ).1.2)`. Use `isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show x * (M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) = 1`. Rewrite using `[← mul_assoc, hNn, ← map_mul, ← hnu']`. Rewrite using `[show ((nu : 𝒪[F]) : F) * (((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1 by`.

Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Use the proof step `rfl, map_one]`.
-/
theorem unit_one_sub (M : Model F E) (hOK : M.OK) (π : 𝒪[F]) (hπ : π ∈ nonunits 𝒪[F]) (r : M.L.O) :
    IsUnit (1 - (⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ : M.L.O) * r) := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨⟨tr, htr⟩, ⟨nr, hnr⟩⟩ := (mem_O_iff M r).mp r.2
  set x : E := 1 - algebraMap F E (π : F) * r with hx
  have hcj : M.L.cj x = 1 - algebraMap F E (π : F) * M.L.cj r := by
    rw [hx, map_sub, map_one, map_mul, cj_alg]
  have hN : x * M.L.cj x = algebraMap F E ((1 : F) - (π : F) * ((tr : F) - (π : F) * (nr : F))) := by
    rw [hcj, hx]
    simp only [map_sub, map_one, map_mul]
    rw [htr, hnr]; ring
  set n : 𝒪[F] := 1 - π * (tr - π * nr) with hn
  have hnu : IsUnit n := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact mul_mem_nonunits_left hπ
  obtain ⟨nu, hnu'⟩ := hnu
  have hNn : x * M.L.cj x = algebraMap F E (n : F) := by rw [hN, hn]; push_cast; ring_nf
  have hyO : M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) ∈ M.L.O :=
    M.L.O.mul_mem (Formalism.L2.SG.Pf.Cnt.DualityBasisChange.cj_mem_O (M := M) x (by
      rw [hx]; exact M.L.O.sub_mem M.L.O.one_mem (M.L.O.mul_mem ((alg_mem_O M).mpr π.2) r.2)))
      ((alg_mem_O M).mpr (nu⁻¹ : 𝒪[F]ˣ).1.2)
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
  show x * (M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) = 1
  rw [← mul_assoc, hNn, ← map_mul, ← hnu']
  rw [show ((nu : 𝒪[F]) : F) * (((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1 by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl, map_one]

/- English proof (translation)
Use `hOK.loc` as an intermediate fact. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Use `set c : M.L.O := ⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ with hc`. Use `finite_max_of c (fun m hm => ?_) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hcm`.

Establish `htop : m ⊔ Ideal.span {c} = ⊤` using `hm.1.2 _ (lt_of_le_of_ne le_sup_left (fun h => hcm (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))))`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : M.L.O) ∈ m ⊔ Ideal.span {c})`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Establish `hu` using `unit_one_sub M hOK π hπ.not_isUnit r`. Establish `: a = 1 - c * r` using `by rw [← hab]; ring`.

Rewrite `ha` using `[this]`. Conclude with `hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)`. Establish `h` using `card_quot_pi M hOK π hπ`. Establish `hq : 0 < qF F` using `Nat.card_pos (α := 𝓀[F])`. Conclude with `Nat.finite_of_card_ne_zero (by rw [h]; positivity)`.
-/
theorem finite_max_O (M : Model F E) (hOK : M.OK) : {m : Ideal M.L.O | m.IsMaximal}.Finite := by
  have := hOK.loc
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  set c : M.L.O := ⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ with hc
  refine finite_max_of c (fun m hm => ?_) ?_
  · by_contra hcm
    have htop : m ⊔ Ideal.span {c} = ⊤ := hm.1.2 _ (lt_of_le_of_ne le_sup_left (fun h => hcm (h ▸
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))))
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : M.L.O) ∈ m ⊔ Ideal.span {c})
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have hu := unit_one_sub M hOK π hπ.not_isUnit r
    have : a = 1 - c * r := by rw [← hab]; ring
    rw [this] at ha
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  · have h := card_quot_pi M hOK π hπ
    have hq : 0 < qF F := Nat.card_pos (α := 𝓀[F])
    exact Nat.finite_of_card_ne_zero (by rw [h]; positivity)

section ModeG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Unfold `Formalism.MainNotions.S.Loc.Model.R`. Rewrite using `[hs]`. Simplify using `only [Subring.mem_comap, Subring.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, b⟩, hab, he⟩`.

Conclude with `⟨a, b, he.symm, hab⟩`. Introduce and unpack `⟨a, b, he, hab⟩`. Conclude with `⟨(a, b), hab, he.symm⟩`.
-/
theorem mem_R_some (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.e x = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), hab, he.symm⟩

/- English proof (translation)
Use `hOK.loc` as an intermediate fact. Use `haveI : IsLocalRing 𝒪[F] := inferInstance`. Take `⟨s, hsq⟩` from `Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq).1 hab.symm)`. Establish `hqn : g.q ∈ nonunits 𝒪[F]` using `g.q_irr.not_isUnit`. Establish `hqm : g.q ∈ IsLocalRing.maximalIdeal 𝒪[F]` using `(IsLocalRing.mem_maximalIdeal _).2 hqn`.

Establish `hb : IsUnit b`. Assume the negation of the conclusion as `hb`. Establish `hbm : b ∈ IsLocalRing.maximalIdeal 𝒪[F]` using `(IsLocalRing.mem_maximalIdeal _).2 hb`. Establish `ham : a ∈ IsLocalRing.maximalIdeal 𝒪[F]`. Establish `: a = b - s * g.q` using `by rw [hsq]; ring`.

Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ hbm (Ideal.mul_mem_left _ _ hqm)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 ham ha`. Take `⟨ua, rfl⟩` from `ha`. Take `⟨ub, rfl⟩` from `hb`.

Use `set y : E := g.e.symm (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) with hy`. Establish `hyR : y ∈ M.R`. Rewrite using `[mem_R_some M hs]`. Use `⟨_, _, by rw [hy, AlgEquiv.apply_symm_apply], ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq]`.

Use `Ideal.mem_span_singleton'.2 ⟨((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * s, ?_⟩` and prove the remaining obligations. Establish `h1 : ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ub : 𝒪[F]) = 1` using `Units.inv_mul ub`. Establish `h2 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ua : 𝒪[F]) = 1` using `Units.inv_mul ua`. Establish `e1 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) - ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) = ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub : 𝒪[F]) - (ua : 𝒪[F]))`. Take the linear combination `(-((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) * h1 + ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * h2`.

Rewrite using `[e1, ← hsq]`. Expand and normalize the polynomial expressions, which then agree. Use `isUnit_iff_exists_inv.2 ⟨⟨y, hyR⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (x : E) * y = 1`. Apply `g.e.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, he, hy, AlgEquiv.apply_symm_apply, map_one]`. Use `ext`. Use `show ((ua : 𝒪[F]) : F) * (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Use `show ((ub : 𝒪[F]) : F) * (((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.
-/
theorem isUnit_of_fst (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) (x : M.R)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F)))
    (hab : Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b) (ha : IsUnit a) :
    IsUnit x := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨s, hsq⟩ := Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq).1 hab.symm)
  have hqn : g.q ∈ nonunits 𝒪[F] := g.q_irr.not_isUnit
  have hqm : g.q ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hqn
  have hb : IsUnit b := by
    by_contra hb
    have hbm : b ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hb
    have ham : a ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have : a = b - s * g.q := by rw [hsq]; ring
      rw [this]
      exact Ideal.sub_mem _ hbm (Ideal.mul_mem_left _ _ hqm)
    exact (IsLocalRing.mem_maximalIdeal _).1 ham ha
  obtain ⟨ua, rfl⟩ := ha
  obtain ⟨ub, rfl⟩ := hb
  set y : E := g.e.symm (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) with hy
  have hyR : y ∈ M.R := by
    rw [mem_R_some M hs]
    refine ⟨_, _, by rw [hy, AlgEquiv.apply_symm_apply], ?_⟩
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.2 ⟨((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * s, ?_⟩
    have h1 : ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ub : 𝒪[F]) = 1 := Units.inv_mul ub
    have h2 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ua : 𝒪[F]) = 1 := Units.inv_mul ua
    have e1 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) - ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) =
        ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub : 𝒪[F]) - (ua : 𝒪[F])) := by
      linear_combination (-((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) * h1 + ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * h2
    rw [e1, ← hsq]; ring
  refine isUnit_iff_exists_inv.2 ⟨⟨y, hyR⟩, Subtype.ext ?_⟩
  show (x : E) * y = 1
  apply g.e.injective
  rw [map_mul, he, hy, AlgEquiv.apply_symm_apply, map_one]
  ext
  · show ((ua : 𝒪[F]) : F) * (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  · show ((ub : 𝒪[F]) : F) * (((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Take `⟨a', b', he', -⟩` from `(mem_R_some M hs (((u⁻¹ : (M.R)ˣ) : M.R) : E)).mp ((u⁻¹ : (M.R)ˣ) : M.R).2`. Establish `h1 : g.e ((((u : (M.R)ˣ) : M.R) : E) * (((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1`. Rewrite using `[← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one, map_one]`. Rewrite `h1` using `[map_mul, he, he']`.

Establish `h2 : (a : F) * a' = 1` using `congrArg Prod.fst h1`. Conclude with `⟨⟨a, a', Subtype.ext (by push_cast; exact h2), Subtype.ext (by push_cast; rw [mul_comm]; exact h2)⟩, rfl⟩`.
-/
theorem fst_isUnit (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : M.R) (hx : IsUnit x)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F))) : IsUnit a := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a', b', he', -⟩ := (mem_R_some M hs (((u⁻¹ : (M.R)ˣ) : M.R) : E)).mp ((u⁻¹ : (M.R)ˣ) : M.R).2
  have h1 : g.e ((((u : (M.R)ˣ) : M.R) : E) * (((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one, map_one]
  rw [map_mul, he, he'] at h1
  have h2 : (a : F) * a' = 1 := congrArg Prod.fst h1
  exact ⟨⟨a, a', Subtype.ext (by push_cast; exact h2), Subtype.ext (by push_cast; rw [mul_comm]; exact h2)⟩, rfl⟩

/- English proof (translation)
Use `hOK.loc` as an intermediate fact. Use `haveI : IsLocalRing 𝒪[F] := inferInstance`. Use `haveI : Nontrivial M.R := by`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun x : M.R => (g.e (x : E)).1) h`.

Simplify using `at h1`. Use `IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_` and prove the remaining obligations. Take `⟨a, b, he, hab⟩` from `(mem_R_some M hs x).1 x.2`. Take `⟨a', b', he', hab'⟩` from `(mem_R_some M hs y).1 y.2`. Establish `hsum : g.e ((x + y : M.R) : E) = (((a + a' : 𝒪[F]) : F), ((b + b' : 𝒪[F]) : F))`.

Rewrite using `[Subring.coe_add, map_add, he, he']`. Simplify using the standard rewrite rules. Establish `hu` using `fst_isUnit M hs (x + y) hxy (a + a') (b + b') hsum`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h` into its components or cases. Conclude with `hx (isUnit_of_fst M hOK hs x a b he hab h)`.

Conclude with `hy (isUnit_of_fst M hOK hs y a' b' he' hab' h)`.
-/
theorem isLocal_R (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) : IsLocalRing M.R := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  haveI : Nontrivial M.R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : M.R => (g.e (x : E)).1) h
    simp at h1
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_
  obtain ⟨a, b, he, hab⟩ := (mem_R_some M hs x).1 x.2
  obtain ⟨a', b', he', hab'⟩ := (mem_R_some M hs y).1 y.2
  have hsum : g.e ((x + y : M.R) : E) = (((a + a' : 𝒪[F]) : F), ((b + b' : 𝒪[F]) : F)) := by
    rw [Subring.coe_add, map_add, he, he']; simp
  have hu := fst_isUnit M hs (x + y) hxy (a + a') (b + b') hsum
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact hx (isUnit_of_fst M hOK hs x a b he hab h)
  · exact hy (isUnit_of_fst M hOK hs y a' b' he' hab' h)

end ModeG

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK`. Consider the cases of `hs : M.split with`. Consider the case `none`. Conclude with `finite_max_of_equiv (RingEquiv.subringCongr (PI.NGStepBBW.R_eq_O_of_none hs)) (finite_max_O M hOK)`. Consider the case `some g => haveI := isLocal_R M hOK hs`.

Use `(Set.finite_singleton (IsLocalRing.maximalIdeal M.R)).subset ?_` and prove the remaining obligations. Introduce `m hm`. Conclude with `IsLocalRing.eq_maximalIdeal hm`.
-/
theorem rFinMax_holds : RFinMax := by
  intro F _ _ _ E _ _ _ _ M hOK
  cases hs : M.split with
  | none =>
    exact finite_max_of_equiv (RingEquiv.subringCongr (PI.NGStepBBW.R_eq_O_of_none hs)) (finite_max_O M hOK)
  | some g =>
    haveI := isLocal_R M hOK hs
    refine (Set.finite_singleton (IsLocalRing.maximalIdeal M.R)).subset ?_
    intro m hm
    exact IsLocalRing.eq_maximalIdeal hm

/- English proof (translation)
The claim follows from `srLift_of_finMax rFinMax_holds`.
-/
theorem srLift_holds : SRLift := srLift_of_finMax rFinMax_holds

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF
