import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A` using `fun x => by`. Establish `h : IsIntegral A (algebraMap L Ω (x : L))` using `(x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (f x)).symm`. Establish `hu : v.asIdeal = P.under (𝓞 K)`. Use extensionality with `x`.

Rewrite using `[← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]`. Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hu, h]`. Conclude with `Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective K L)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩`.
-/
private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective K L)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

/- English proof (translation)
Establish `hc : IsClosed ((K.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω))` using `(hK.isCompact.image W.continuous_resP).isClosed`. Establish `hN : NS Ω V.S' ≤ (K.map (W.resP L Ω)).normalCore`. Use `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalCore_isClosed _ hc)` and prove the remaining obligations. Introduce `g hg b`. Simplify using `only [Set.mem_iUnion] at hg`.

Take `⟨v, hv, A, hA, hg⟩` from `hg`. Establish `hl : IsLift (RingEquiv.refl (W.Lp L)) (b⁻¹).toRingEquiv` using `fun x => (b⁻¹).commutes x`. Establish `hAA : ∀ x, (b⁻¹).toRingEquiv x ∈ A ↔ x ∈ A.comap (b⁻¹).toRingEquiv.toRingHom` using `fun x => Iff.rfl`. Establish `h1 : b * g * b⁻¹ ∈ Ine (F` using `W.Lp L) (A.comap (b⁻¹).toRingEquiv.toRingHom) := conjGal_mem_Ine hl hAA hg`. Establish `hA' : IsPlaceOver (A.comap (b⁻¹).toRingEquiv.toRingHom) v` using `fun x => by`.

Rewrite using `[← val_lt_one hAA, ← hA x]`. Conclude with `Iff.of_eq (congrArg (fun y => A.valuation y < 1) ((b⁻¹).commutes (x : W.Lp L)))`. Take `⟨t, ht⟩` from `s.unr _ _ hA' h1`. Take `⟨w, hw, hwv⟩` from `place_between (L := L) hA'`. Use `⟨t, hI w (by rw [hwv]; exact hv) _ hw ?_, ht⟩` and prove the remaining obligations.

Rewrite `h1` using `[← ht]`. Conclude with `h1`. Introduce `g hg`. Establish `h1 : W.resP L Ω g ∈ NS Ω V.S'` using `(QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hg)`. Take `⟨t, ht, e⟩` from `Subgroup.normalCore_le _ (hN h1)`.

Establish `: t = g` using `AlgEquiv.ext fun x => DFunLike.congr_fun e x`. Conclude with `this ▸ ht`.
-/
private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  have hc : IsClosed ((K.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    (hK.isCompact.image W.continuous_resP).isClosed
  have hN : NS Ω V.S' ≤ (K.map (W.resP L Ω)).normalCore := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.normalCore_isClosed _ hc)
    intro g hg b
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    have hl : IsLift (RingEquiv.refl (W.Lp L)) (b⁻¹).toRingEquiv := fun x => (b⁻¹).commutes x
    have hAA : ∀ x, (b⁻¹).toRingEquiv x ∈ A ↔ x ∈ A.comap (b⁻¹).toRingEquiv.toRingHom := fun x => Iff.rfl
    have h1 : b * g * b⁻¹ ∈ Ine (F := W.Lp L) (A.comap (b⁻¹).toRingEquiv.toRingHom) := conjGal_mem_Ine hl hAA hg
    have hA' : IsPlaceOver (A.comap (b⁻¹).toRingEquiv.toRingHom) v := fun x => by
      rw [← val_lt_one hAA, ← hA x]
      exact Iff.of_eq (congrArg (fun y => A.valuation y < 1) ((b⁻¹).commutes (x : W.Lp L)))
    obtain ⟨t, ht⟩ := s.unr _ _ hA' h1
    obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA'
    refine ⟨t, hI w (by rw [hwv]; exact hv) _ hw ?_, ht⟩
    rw [← ht] at h1
    exact h1
  intro g hg
  have h1 : W.resP L Ω g ∈ NS Ω V.S' := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hg)
  obtain ⟨t, ht, e⟩ := Subgroup.normalCore_le _ (hN h1)
  have : t = g := AlgEquiv.ext fun x => DFunLike.congr_fun e x
  exact this ▸ ht

/- English proof (translation)
Introduce `g` and use `by obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1 obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2) exact ⟨σ, Subtype.ext hτ⟩`.
-/
private theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

/- English proof (translation)
Establish `h : (r.ker : Set H) = {g | ∀ i j, (r g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j}` using `Set.ext fun g => ⟨fun hg i j => by rw [show r g = 1 from hg]; rfl, fun hg => Units.ext (Matrix.ext hg)⟩`. Rewrite using `[h, Set.setOf_forall]`. Use `isClosed_iInter fun i => ?_` and prove the remaining obligations. Rewrite using `[Set.setOf_forall]`. Use `isClosed_iInter fun j => isClosed_eq ?_ continuous_const` and prove the remaining obligations.

Establish `hv : Continuous fun g => (r g).val` using `Units.continuous_val.comp hr`. Conclude with `hv.matrix_elem i j`.
-/
private theorem ker_closed {H k : Type} [Group H] [TopologicalSpace H] [CommRing k] [TopologicalSpace k] [T2Space k] {n : ℕ}
    (r : H →* GL (Fin n) k) (hr : Continuous r) : IsClosed (r.ker : Set H) := by
  have h : (r.ker : Set H) = {g | ∀ i j, (r g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j} :=
    Set.ext fun g => ⟨fun hg i j => by rw [show r g = 1 from hg]; rfl, fun hg => Units.ext (Matrix.ext hg)⟩
  rw [h, Set.setOf_forall]
  refine isClosed_iInter fun i => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun j => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g => (r g).val := Units.continuous_val.comp hr
  exact hv.matrix_elem i j

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s n V c r hcont hI`. Establish `hker : V.pr.ker ≤ r.ker` using `ker_pr_le V _ (ker_closed r hcont) fun w hw A hA t ht => hI w hw A hA t ht`. Set `ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)` to `V.pr.liftOfSurjective (pr_surj V) ⟨r, hker⟩`. Establish `hρ : ∀ g, ρ (V.pr g) = r g` using `fun g => V.pr.liftOfRightInverse_comp_apply _ _ _ g`. Use `⟨ρ, ?_, MonoidHom.ext hρ, fun P hP g => ?_⟩` and prove the remaining obligations.

Use `haveI := isClosed_NS Ω V.S'`. Establish `hq : Topology.IsQuotientMap V.pr` using `(V.pr_cont W.continuous_resP).isClosedMap.isQuotientMap (V.pr_cont W.continuous_resP) (pr_surj V)`. Conclude with `hq.continuous_iff.2 (hcont.congr fun g => (hρ g).symm)`. Take `⟨t, rfl⟩` from `pr_surj V g`. Choose the witnesses or unpack the hypotheses as in `⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by`.

Rewrite using `[← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]`. Conclude with `(V.frame.conj (V.pr t)).2`. Establish `e1 : V.frame.conj (V.pr t) = V.pr t'` using `Subtype.ext (by show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')`. Rewrite using `[ht', map_mul, map_mul, map_inv])`. Establish `e2` using `hP t t' ht'`.

Establish `e3 : V.ε (V.pr t).1 = cycZ L Ω l t` using `DFunLike.congr_fun V.hε (W.resP L Ω t)`. Establish `e4 : V.frame.eps c.O (Qbar l) (V.pr t) = cycBar L Ω l t`. Use `Units.ext ?_` and prove the remaining obligations. Use `show ((algebraMap ℤ_[l] c.O (V.ε (V.pr t).1 : ℤ_[l]ˣ) : c.O) : Qbar l) = _`. Rewrite using `[e3]`.

Both sides reduce to the same expression. Rewrite using `[e1, e4]`. Use `show (ρ (V.pr t)).val.transpose * _ * (ρ (V.pr t')).val = _`. Rewrite using `[hρ, hρ]`. Conclude with `e2`.
-/
theorem UpperTheory.exists_descent_to_level_group_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, r g = 1) → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ ρ.comp V.pr = r ∧ ∀ P, Af.IsPairing s.c r (cycBar L Ω l ^ (1 - (n : ℤ))) P → V.frame.IsForm c.O n ρ P := by
  intro l _ L Ω _ _ _ _ _ _ s n V c r hcont hI
  have hker : V.pr.ker ≤ r.ker :=
    ker_pr_le V _ (ker_closed r hcont) fun w hw A hA t ht => hI w hw A hA t ht
  let ρ : V.frame.G₀ →* GL (Fin n) (Qbar l) := V.pr.liftOfSurjective (pr_surj V) ⟨r, hker⟩
  have hρ : ∀ g, ρ (V.pr g) = r g := fun g => V.pr.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨ρ, ?_, MonoidHom.ext hρ, fun P hP g => ?_⟩
  · haveI := isClosed_NS Ω V.S'
    have hq : Topology.IsQuotientMap V.pr :=
      (V.pr_cont W.continuous_resP).isClosedMap.isQuotientMap (V.pr_cont W.continuous_resP) (pr_surj V)
    exact hq.continuous_iff.2 (hcont.congr fun g => (hρ g).symm)
  · obtain ⟨t, rfl⟩ := pr_surj V g
    obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    have e1 : V.frame.conj (V.pr t) = V.pr t' := Subtype.ext (by
      show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
      rw [ht', map_mul, map_mul, map_inv])
    have e2 := hP t t' ht'
    have e3 : V.ε (V.pr t).1 = cycZ L Ω l t := DFunLike.congr_fun V.hε (W.resP L Ω t)
    have e4 : V.frame.eps c.O (Qbar l) (V.pr t) = cycBar L Ω l t := by
      refine Units.ext ?_
      show ((algebraMap ℤ_[l] c.O (V.ε (V.pr t).1 : ℤ_[l]ˣ) : c.O) : Qbar l) = _
      rw [e3]
      rfl
    rw [e1, e4]
    show (ρ (V.pr t)).val.transpose * _ * (ρ (V.pr t')).val = _
    rw [hρ, hρ]
    exact e2
