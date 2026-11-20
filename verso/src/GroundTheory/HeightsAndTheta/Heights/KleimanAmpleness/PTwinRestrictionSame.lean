import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts SameModel modVec resImage ResField)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_subringCongr {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : s) :
    ((RingEquiv.subringCongr h x : t) : R) = x :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_subringCongr_symm {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : t) :
    (((RingEquiv.subringCongr h).symm x : s) : R) = x :=
  rfl

section Transport

variable {S : Type*} [CommRing S] {L L' : Type*} [Field L] [Field L'] [Algebra S L] [Algebra S L']

/- English proof (translation)
Unfold `locIn`. Rewrite using `[RingHom.map_closure]`. Use `congr 1`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨a, b, hb, rfl⟩, rfl⟩`. Conclude with `⟨e a, e b, fun h => hb ((hpP b).mpr h), by simp [he, map_div₀]⟩`. Introduce and unpack `⟨a', b', hb', rfl⟩`. Use `⟨(e.symm a' : L) / e.symm b', ⟨e.symm a', e.symm b', fun h => hb' ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `using (hpP (e.symm b')).mp h`.

Simplify using `only [RingHom.coe_coe, map_div₀, ← he, AlgEquiv.apply_symm_apply]`.
-/
theorem locIn_map (φ : L ≃ₐ[S] L') (A : Subalgebra S L) (B : Subalgebra S L') (e : A ≃ₐ[S] B)
    (he : ∀ a, (e a : L') = φ a) (p : Ideal A) (P : Ideal B) (hpP : ∀ a, a ∈ p ↔ e a ∈ P) :
    (locIn A p).map (φ : L →+* L') = locIn B P := by
  unfold locIn
  rw [RingHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨a, b, hb, rfl⟩, rfl⟩
    exact ⟨e a, e b, fun h => hb ((hpP b).mpr h), by simp [he, map_div₀]⟩
  · rintro ⟨a', b', hb', rfl⟩
    refine ⟨(e.symm a' : L) / e.symm b', ⟨e.symm a', e.symm b', fun h => hb' ?_, rfl⟩, ?_⟩
    · simpa using (hpP (e.symm b')).mp h
    · simp only [RingHom.coe_coe, map_div₀, ← he, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Unfold `chartRingOver`. Rewrite using `[AlgHom.map_adjoin, ← Set.range_comp]`. Use `congr 1`. Use extensionality with `u`. Simplify using `[map_div₀]`.
-/
theorem chartRingOver_comp {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S (fun q => φ (v q)) c = (chartRingOver S v c).map (φ : L →ₐ[S] L') := by
  unfold chartRingOver
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  congr 1
  ext u
  simp [map_div₀]

noncomputable def chartEquiv {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S v c ≃ₐ[S] chartRingOver S (fun q => φ (v q)) c :=
  (φ.subalgebraMap (chartRingOver S v c)).trans (Subalgebra.equivOfEq _ _ (chartRingOver_comp φ v c).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chartEquiv_coe {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k)
    (a : chartRingOver S v c) : (chartEquiv φ v c a : L') = φ a :=
  rfl

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, P, hP, rfl⟩`. Establish `hc' : ∀ k, v ⟨k, c k⟩ ≠ 0` using `fun k h => hc k (by simp [h])`. Use `⟨_, ⟨c, hc', P.comap (chartEquiv φ v c : chartRingOver S v c →+* _), inferInstance, rfl⟩, ?_⟩` and prove the remaining obligations.

Conclude with `locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) _ P (fun a => Iff.rfl)`. Introduce and unpack `⟨_, ⟨c, hc, p, hp, rfl⟩, rfl⟩`. Establish `hc' : ∀ k, φ (v ⟨k, c k⟩) ≠ 0` using `fun k => by simpa using hc k`. Use `⟨c, hc', p.comap ((chartEquiv φ v c).symm : _ →+* chartRingOver S v c), inferInstance, ?_⟩` and prove the remaining obligations. Conclude with `locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) p _ (fun a => by rw [Ideal.mem_comap, RingHom.coe_coe, AlgEquiv.symm_apply_apply])`.
-/
theorem modelPts_comp {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) :
    modelPts S (fun q => φ (v q)) = Subring.map (φ : L →+* L') '' modelPts S v := by
  ext z
  constructor
  · rintro ⟨c, hc, P, hP, rfl⟩
    have hc' : ∀ k, v ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by simp [h])
    refine ⟨_, ⟨c, hc', P.comap (chartEquiv φ v c : chartRingOver S v c →+* _), inferInstance, rfl⟩, ?_⟩
    exact locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) _ P (fun a => Iff.rfl)
  · rintro ⟨_, ⟨c, hc, p, hp, rfl⟩, rfl⟩
    have hc' : ∀ k, φ (v ⟨k, c k⟩) ≠ 0 := fun k => by simpa using hc k
    refine ⟨c, hc', p.comap ((chartEquiv φ v c).symm : _ →+* chartRingOver S v c), inferInstance, ?_⟩
    exact locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) p _
      (fun a => by rw [Ideal.mem_comap, RingHom.coe_coe, AlgEquiv.symm_apply_apply])

/- English proof (translation)
Set `φ₀ : L ≃+* L'` to `(RingHom.quotientKerEquivOfSurjective hr).symm.trans ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hr'))`. Establish `hφ₀ : ∀ u, φ₀ (r u) = r' u` using `fun u => by`. Simplify using `only [φ₀, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]`. Use `⟨AlgEquiv.ofRingEquiv (f := φ₀) fun s => ?_, fun u => hφ₀ u⟩` and prove the remaining obligations. Take `⟨u, hu, hu'⟩` from `hS s`.

Rewrite using `[← hu, hφ₀, hu']`.
-/
theorem exists_algEquiv_of_ker_eq {R : Type*} [CommRing R] (r : R →+* L) (r' : R →+* L')
    (hr : Function.Surjective r) (hr' : Function.Surjective r') (hker : RingHom.ker r = RingHom.ker r')
    (hS : ∀ s : S, ∃ u, r u = algebraMap S L s ∧ r' u = algebraMap S L' s) :
    ∃ φ : L ≃ₐ[S] L', ∀ u, φ (r u) = r' u := by
  let φ₀ : L ≃+* L' := (RingHom.quotientKerEquivOfSurjective hr).symm.trans
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hr'))
  have hφ₀ : ∀ u, φ₀ (r u) = r' u := fun u => by
    simp only [φ₀, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  refine ⟨AlgEquiv.ofRingEquiv (f := φ₀) fun s => ?_, fun u => hφ₀ u⟩
  obtain ⟨u, hu, hu'⟩ := hS s
  rw [← hu, hφ₀, hu']

/- English proof (translation)
Rewrite using `[RingHom.map_closure, RingHom.coe_coe, h]`.
-/
theorem map_closure_of_image (φ : L ≃ₐ[S] L') {X : Set L} {Y : Set L'} (h : φ '' X = Y) :
    (Subring.closure X).map (φ : L →+* L') = Subring.closure Y := by
  rw [RingHom.map_closure, RingHom.coe_coe, h]

end Transport

/- English proof (translation)
Set `e` to `RingEquiv.subringCongr hloc.symm`. Use `exists_algEquiv_of_ker_eq (resMap y c p) ((resMap y' c' p').comp e.toRingHom) (resMap_surjective y c p) ((resMap_surjective y' c' p').comp e.surjective) ?_ ?_` and prove the remaining obligations. Use extensionality with `u`. Rewrite using `[RingHom.mem_ker, RingHom.mem_ker]`. Use `show resMap y c p u = 0 ↔ resMap y' c' p' (e u) = 0`.

Rewrite using `[resMap_eq_zero_iff, resMap_eq_zero_iff, isUnit_map_iff]`. Introduce `s`. Establish `hs : algebraMap S Ω s ∈ locIn (chartRingOver S y c) p` using `(mem_locIn_chart_iff y c p).mpr ⟨algebraMap S _ s, 1, Ideal.one_notMem p, by simp⟩`. Conclude with `⟨⟨_, hs⟩, resMap_algebraMap y c p s hs, resMap_algebraMap y' c' p' s _⟩`.
-/
theorem exists_resEquiv {S : Type} [CommRing S] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime]
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p) :
    ∃ φ : ResField S y c p ≃ₐ[S] ResField S y' c' p',
      ∀ u, φ (resMap y c p u) = resMap y' c' p' (RingEquiv.subringCongr hloc.symm u) := by
  let e := RingEquiv.subringCongr hloc.symm
  refine exists_algEquiv_of_ker_eq (resMap y c p) ((resMap y' c' p').comp e.toRingHom)
    (resMap_surjective y c p) ((resMap_surjective y' c' p').comp e.surjective) ?_ ?_
  · ext u
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show resMap y c p u = 0 ↔ resMap y' c' p' (e u) = 0
    rw [resMap_eq_zero_iff, resMap_eq_zero_iff, isUnit_map_iff]
  · intro s
    have hs : algebraMap S Ω s ∈ locIn (chartRingOver S y c) p :=
      (mem_locIn_chart_iff y c p).mpr ⟨algebraMap S _ s, 1, Ideal.one_notMem p, by simp⟩
    exact ⟨⟨_, hs⟩, resMap_algebraMap y c p s hs, resMap_algebraMap y' c' p' s _⟩

/- English proof (translation)
Establish `hz' : z ≤ locIn (chartRingOver S y' c') p'` using `hloc.symm ▸ hz`. Rewrite using `[resImage_eq y c p z hz, resImage_eq y' c' p' z hz']`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨u, hu, rfl⟩, rfl⟩`.

Use `⟨RingEquiv.subringCongr hloc.symm u, ?_, hφ u⟩` and prove the remaining obligations. Rewrite using `[coe_subringCongr]`. Conclude with `hu`. Introduce and unpack `⟨u', hu', rfl⟩`. Use `⟨resMap y c p ((RingEquiv.subringCongr hloc.symm).symm u'), ⟨_, ?_, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[coe_subringCongr_symm]`. Conclude with `hu'`. Rewrite using `[hφ, RingEquiv.apply_symm_apply]`.
-/
theorem image_resImage {S : Type} [CommRing S] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime]
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p)
    (φ : ResField S y c p ≃ₐ[S] ResField S y' c' p')
    (hφ : ∀ u, φ (resMap y c p u) = resMap y' c' p' (RingEquiv.subringCongr hloc.symm u))
    (z : Subring Ω) (hz : z ≤ locIn (chartRingOver S y c) p) :
    φ '' resImage S y c p z = resImage S y' c' p' z := by
  have hz' : z ≤ locIn (chartRingOver S y' c') p' := hloc.symm ▸ hz
  rw [resImage_eq y c p z hz, resImage_eq y' c' p' z hz']
  ext v
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨RingEquiv.subringCongr hloc.symm u, ?_, hφ u⟩
    rw [coe_subringCongr]
    exact hu
  · rintro ⟨u', hu', rfl⟩
    refine ⟨resMap y c p ((RingEquiv.subringCongr hloc.symm).symm u'), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [coe_subringCongr_symm]
      exact hu'
    · rw [hφ, RingEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[modelPts_comp φ (modVec S y c p), h S K ι Ω y c p hc, h S K' ι' Ω y' c' p' hc', hloc, ← hyy']`. Use extensionality with `z'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨z, hz, hzO, rfl⟩, rfl⟩`. Conclude with `⟨z, hz, hzO, map_closure_of_image φ (himg z hzO)⟩`.

Introduce and unpack `⟨z, hz, hzO, rfl⟩`. Conclude with `⟨_, ⟨z, hz, hzO, rfl⟩, map_closure_of_image φ (himg z hzO)⟩`.
-/
theorem sameModel_modVec (h : RestrictionPointsAll.Statement) {S : Type} [CommRing S] {K : Type} {ι : K → Type}
    {K' : Type} {ι' : K' → Type} {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (hyy' : modelPts S y = modelPts S y')
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime] (hc' : ∀ k, y' ⟨k, c' k⟩ ≠ 0)
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p)
    (φ : ResField S y c p ≃ₐ[S] ResField S y' c' p')
    (himg : ∀ z ≤ locIn (chartRingOver S y c) p, φ '' resImage S y c p z = resImage S y' c' p' z) :
    modelPts S (fun q => φ (modVec S y c p q)) = modelPts S (modVec S y' c' p') := by
  rw [modelPts_comp φ (modVec S y c p), h S K ι Ω y c p hc, h S K' ι' Ω y' c' p' hc', hloc, ← hyy']
  ext z'
  constructor
  · rintro ⟨_, ⟨z, hz, hzO, rfl⟩, rfl⟩
    exact ⟨z, hz, hzO, map_closure_of_image φ (himg z hzO)⟩
  · rintro ⟨z, hz, hzO, rfl⟩
    exact ⟨_, ⟨z, hz, hzO, rfl⟩, map_closure_of_image φ (himg z hzO)⟩

/- English proof (translation)
Introduce `S _ K _ ι K' ι' Ω _ _ y y' hyy' c p _ hc c' p' _ hc' hloc`. Take `⟨φ, hφ⟩` from `exists_resEquiv y y' c p c' p' hloc`. Establish `himg` using `image_resImage y y' c p c' p' hloc φ hφ`. Conclude with `⟨φ, fun z _ hz => himg z hz, sameModel_modVec h y y' hyy' c p hc c' p' hc' hloc φ himg⟩`.
-/
theorem RestrictionSame.proof (h : RestrictionPointsAll.Statement) : RestrictionSame.Statement := by
  intro S _ K _ ι K' ι' Ω _ _ y y' hyy' c p _ hc c' p' _ hc' hloc
  obtain ⟨φ, hφ⟩ := exists_resEquiv y y' c p c' p' hloc
  have himg := image_resImage y y' c p c' p' hloc φ hφ
  exact ⟨φ, fun z _ hz => himg z hz, sameModel_modVec h y y' hyy' c p hc c' p' hc' hloc φ himg⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
