import Mathlib
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.Cb.EtalePushouts

/- English proof (translation)
The claim follows from `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange`.
-/
private theorem etCobase : Et.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange

/- English proof (translation)
The claim follows from `haveI := etCobase MorphismProperty.IsStableUnderCobaseChange.of_isPushout s hg`.
-/
private theorem etOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : Et g) : Et u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout s hg

/- English proof (translation)
The claim follows from `haveI := etCobase MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := MorphismProperty.ind.{0} Et) s hg`.
-/
private theorem ieOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : IE g) : IE u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := MorphismProperty.ind.{0} Et) s hg

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f ≫ g).hom.Etale`. Rewrite using `[CommRingCat.hom_comp]`. Conclude with `RingHom.Etale.stableUnderComposition _ _ hf hg`.
-/
private theorem etComp {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : Et f) (hg : Et g) : Et (f ≫ g) := by
  change (f ≫ g).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hf hg

/- English proof (translation)
Use `letI := c.hom.toAlgebra`. Use `letI := f.hom.toAlgebra`. Use `letI := (c ≫ f).hom.toAlgebra`. Use `haveI : IsScalarTower R S W := .of_algebraMap_eq' rfl`. Use `haveI : Algebra.Etale R S := h1`.

Use `haveI : Algebra.Etale R W := h2`. Establish `h3 : Algebra.Etale S W` using `{ formallyEtale := Algebra.FormallyEtale.of_restrictScalars (R := R) finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S W }`. Conclude with `h3`.
-/
private theorem etRight {R S W : CommRingCat.{0}} {c : R ⟶ S} {f : S ⟶ W} (h1 : Et c) (h2 : Et (c ≫ f)) : Et f := by
  letI := c.hom.toAlgebra
  letI := f.hom.toAlgebra
  letI := (c ≫ f).hom.toAlgebra
  haveI : IsScalarTower R S W := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R S := h1
  haveI : Algebra.Etale R W := h2
  have h3 : Algebra.Etale S W := {
    formallyEtale := Algebra.FormallyEtale.of_restrictScalars (R := R)
    finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S W }
  exact h3

/- English proof (translation)
Establish `w : pC A ≫ CommRingCat.ofHom (Polynomial.mapRingHom f.hom) = f ≫ pC S`. Use extensionality with `a`. Simplify using the standard rewrite rules. Use `⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w (fun s => CommRingCat.ofHom (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X))) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s ext1`.

Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations. Use `congr($(s.condition).hom a)` as an intermediate fact. Simplify using `using this.symm`. Simplify using the standard rewrite rules. Introduce `s`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Introduce `s m h1 h2 ext1`. Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations. Use `congr($(h2).hom a)` as an intermediate fact.

Simplify using `using this`. Use `congr($(h1).hom Polynomial.X)` as an intermediate fact. Simplify using `using this`.
-/
private theorem polySq {A S : CommRingCat.{0}} (f : A ⟶ S) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC S) := by
  have w : pC A ≫ CommRingCat.ofHom (Polynomial.mapRingHom f.hom) = f ≫ pC S := by
    ext a; simp
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X))) ?_ ?_ ?_⟩⟩
  · intro s
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(s.condition).hom a)
      simpa using this.symm
    · simp
  · intro s
    ext a
    simp
  · intro s m h1 h2
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(h2).hom a)
      simpa using this
    · have := congr($(h1).hom Polynomial.X)
      simpa using this

/- English proof (translation)
Establish `sq` using `isPullback_SpecMap_of_isPushout _ _ _ _ h`. Set `x : Spec B` to `⟨r, hr⟩`. Set `y : Spec C` to `⟨s, hs⟩`. Establish `hxy : Spec.map f x = Spec.map g y` using `PrimeSpectrum.ext e`. Take `⟨z, h1, h2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Spec.map f) (g := Spec.map g) x y hxy`.

Set `z' : Spec D` to `sq.isoPullback.inv z`. Establish `e1 : Spec.map u z' = x`. Rewrite using `[← h1, ← sq.isoPullback_inv_fst]`. Both sides reduce to the same expression. Establish `e2 : Spec.map v z' = y`.

Rewrite using `[← h2, ← sq.isoPullback_inv_snd]`. Both sides reduce to the same expression. Conclude with `⟨z'.asIdeal, z'.isPrime, congrArg PrimeSpectrum.asIdeal e1, congrArg PrimeSpectrum.asIdeal e2⟩`.
-/
private theorem exPrime {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (h : IsPushout f g u v) (r : Ideal B) (s : Ideal C) [hr : r.IsPrime] [hs : s.IsPrime]
    (e : r.comap f.hom = s.comap g.hom) :
    ∃ p : Ideal D, p.IsPrime ∧ p.comap u.hom = r ∧ p.comap v.hom = s := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ h
  let x : Spec B := ⟨r, hr⟩
  let y : Spec C := ⟨s, hs⟩
  have hxy : Spec.map f x = Spec.map g y := PrimeSpectrum.ext e
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map f) (g := Spec.map g) x y hxy
  let z' : Spec D := sq.isoPullback.inv z
  have e1 : Spec.map u z' = x := by
    rw [← h1, ← sq.isoPullback_inv_fst]; rfl
  have e2 : Spec.map v z' = y := by
    rw [← h2, ← sq.isoPullback_inv_snd]; rfl
  exact ⟨z'.asIdeal, z'.isPrime, congrArg PrimeSpectrum.asIdeal e1, congrArg PrimeSpectrum.asIdeal e2⟩

variable {q : ℕ} {i : ℤ}

/- English proof (translation)
Introduce `_ _ _ s'` and use `h _ _ _ (s.paste_vert s')`.
-/
private theorem bcBack {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i k (a ≫ c)) : BC q i φ c :=
  fun _ _ _ s' => h _ _ _ (s.paste_vert s')

/- English proof (translation)
The claim follows from `BC.of_one (s.paste_vert (IsPushout.of_hasPushout φ c)) (h _ _ _ (IsPushout.of_hasPushout φ c))`.
-/
private theorem bcFwd {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i φ c) : BC q i k (a ≫ c) :=
  BC.of_one (s.paste_vert (IsPushout.of_hasPushout φ c)) (h _ _ _ (IsPushout.of_hasPushout φ c))

/- English proof (translation)
Establish `hqA : IsUnit (q : A)` using `by simpa using hq.map t.hom`. Establish `hqA' : IsUnit (q : A')` using `by simpa using hqA.map f.hom`. Establish `s0` using `IsPushout.of_hasPushout k t`. Establish `hL` using `hLimit H q i (pushout.inr k t) hqA (fun C c hc => bcBack s0 (hG C c hc)) A' f hf`. Establish `s1` using `IsPushout.of_hasPushout (pushout.inr k t) f`.

Establish `rψ` using `hL _ _ _ s1`. Establish `aψ` using `hAlg.2.2.1 _ _ _ _ s1 (hAlg.2.2.1 _ _ _ _ s0 hk)`. Establish `hU` using `hULA H q i h hqA' hA' hX hh hl _ _ aψ`. Establish `s2` using `IsPushout.of_hasPushout (pC A' ≫ h) (pushout.inr (pushout.inr k t) f)`. Establish `rθ` using `hU _ _ _ s2`.

Establish `rx` using `hSHE H q i (pC A' ≫ h) hqA' hA' hX`. Establish `rw₃` using `RE.of_comp_left rx (g := pushout.inl (pC A' ≫ h) (pushout.inr (pushout.inr k t) f)) (by rw [s2.w]; exact rψ.comp rθ)`. Conclude with `BC.of_one ((s0.paste_vert s1).paste_vert s2.flip) rw₃`.
-/
private theorem coh (hLimit : Limit) (hAlg : AlgResProps) (hSHE : SHEqv) (hULA : ULA) (H : Hyp)
    (q : ℕ) [NeZero q] (i : ℤ) {T K A A' X : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) (hq : IsUnit (q : T))
    (hk : AlgRes k) (hG : Good q i k t) (f : A ⟶ A') (hf : IE f) (hA' : SH A') (hX : SH X)
    (h : CommRingCat.of (Polynomial A') ⟶ X) (hh : IE h) (hl : IsLocalHom (pC A' ≫ h).hom) :
    BC q i k ((t ≫ f) ≫ pC A' ≫ h) := by
  have hqA : IsUnit (q : A) := by simpa using hq.map t.hom
  have hqA' : IsUnit (q : A') := by simpa using hqA.map f.hom
  have s0 := IsPushout.of_hasPushout k t
  have hL := hLimit H q i (pushout.inr k t) hqA (fun C c hc => bcBack s0 (hG C c hc)) A' f hf
  have s1 := IsPushout.of_hasPushout (pushout.inr k t) f
  have rψ := hL _ _ _ s1
  have aψ := hAlg.2.2.1 _ _ _ _ s1 (hAlg.2.2.1 _ _ _ _ s0 hk)
  have hU := hULA H q i h hqA' hA' hX hh hl _ _ aψ
  have s2 := IsPushout.of_hasPushout (pC A' ≫ h) (pushout.inr (pushout.inr k t) f)
  have rθ := hU _ _ _ s2
  have rx := hSHE H q i (pC A' ≫ h) hqA' hA' hX
  have rw₃ := RE.of_comp_left rx (g := pushout.inl (pC A' ≫ h) (pushout.inr (pushout.inr k t) f))
    (by rw [s2.w]; exact rψ.comp rθ)
  exact BC.of_one ((s0.paste_vert s1).paste_vert s2.flip) rw₃

/- English proof (translation)
Take `⟨A', f, hf, hA', hfr⟩` from `hSH A (r.comap (pC A ≫ c).hom) inferInstance`. Take `⟨_, -⟩` from `id hA'`. Establish `hsq` using `IsPushout.of_hasPushout (pC A ≫ c) f`. Take `⟨r', hr', e₁, e₂⟩` from `exPrime hsq r (IsLocalRing.maximalIdeal A') (by`. Use extensionality with `a`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hfr a)`. Take `⟨X, f₂, hf₂, hX, hfr₂⟩` from `hSH _ r' hr'`. Take `⟨_, -⟩` from `id hX`. Set `u₁` to `pushout.inl (pC A ≫ c) f`.

Set `u₂` to `pushout.inr (pC A ≫ c) f`. Set `h₀ : CommRingCat.of (Polynomial A') ⟶ pushout (pC A ≫ c) f` to `CommRingCat.ofHom (Polynomial.eval₂RingHom u₂.hom (u₁.hom (c.hom Polynomial.X)))`. Establish `e0 : pC A' ≫ h₀ = u₂`. Use extensionality with `a`. Simplify using `[h₀]`.

Establish `e1 : CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫ h₀ = c ≫ u₁` using `by ext1`. Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations. Use `congr($(hsq.w).hom a)` as an intermediate fact. Simplify `this.symm` using `[h₀, u₁, u₂]`. Simplify using `[h₀]`.

Establish `hpo : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) c h₀ u₁` using `IsPushout.of_top (by rw [e0]; exact hsq.flip) e1 (polySq f).flip`. Establish `hh₀ : Et h₀` using `etOfPushout hpo hc`. Establish `e3 : (IsLocalRing.maximalIdeal X).comap f₂.hom = r'`. Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `(hfr₂ a).symm`. Use `⟨A', X, f, h₀ ≫ f₂, u₁ ≫ f₂, IsLocalRing.maximalIdeal X, hf, hA', hX, hIE _ _ (MorphismProperty.le_ind _ _ hh₀) hf₂, ?_, hIE _ _ (ieOfPushout hsq hf) hf₂, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `hm : a ∈ IsLocalRing.maximalIdeal A'` using `hn`.

Rewrite `hm` using `[← e₂, Ideal.mem_comap]`. Use `(hfr₂ _).1 hm ?_` and prove the remaining obligations. Establish `e4 : (pC A' ≫ h₀ ≫ f₂) = u₂ ≫ f₂` using `by rw [← Category.assoc, e0]`. Rewrite `ha` using `[e4]`. Conclude with `ha`.

Rewrite using `[CommRingCat.hom_comp, ← Ideal.comap_comap, e3]`. Conclude with `e₁`. Rewrite using `[← Category.assoc (pC A') h₀ f₂, e0, ← Category.assoc f u₂ f₂]`. Establish `e5 : f ≫ u₂ = (pC A ≫ c) ≫ u₁` using `hsq.w.symm`. Rewrite using `[e5]`.

Simplify using `only [Category.assoc]`.
-/
private theorem geo (hSH : SHExists) (hIE : IEComp) {A U : CommRingCat.{0}}
    (c : CommRingCat.of (Polynomial A) ⟶ U) (hc : Et c) (r : Ideal U) (hr : r.IsPrime) :
    ∃ (A' X : CommRingCat.{0}) (f : A ⟶ A') (h : CommRingCat.of (Polynomial A') ⟶ X) (o : U ⟶ X) (Q : Ideal X),
      IE f ∧ SH A' ∧ SH X ∧ IE h ∧ IsLocalHom (pC A' ≫ h).hom ∧ IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
        pC A ≫ c ≫ o = f ≫ pC A' ≫ h := by
  obtain ⟨A', f, hf, hA', hfr⟩ := hSH A (r.comap (pC A ≫ c).hom) inferInstance
  obtain ⟨_, -⟩ := id hA'
  have hsq := IsPushout.of_hasPushout (pC A ≫ c) f
  obtain ⟨r', hr', e₁, e₂⟩ := exPrime hsq r (IsLocalRing.maximalIdeal A') (by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hfr a)
  obtain ⟨X, f₂, hf₂, hX, hfr₂⟩ := hSH _ r' hr'
  obtain ⟨_, -⟩ := id hX
  let u₁ := pushout.inl (pC A ≫ c) f
  let u₂ := pushout.inr (pC A ≫ c) f
  let h₀ : CommRingCat.of (Polynomial A') ⟶ pushout (pC A ≫ c) f :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom u₂.hom (u₁.hom (c.hom Polynomial.X)))
  have e0 : pC A' ≫ h₀ = u₂ := by
    ext a; simp [h₀]
  have e1 : CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫ h₀ = c ≫ u₁ := by
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(hsq.w).hom a)
      simpa [h₀, u₁, u₂] using this.symm
    · simp [h₀]
  have hpo : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) c h₀ u₁ :=
    IsPushout.of_top (by rw [e0]; exact hsq.flip) e1 (polySq f).flip
  have hh₀ : Et h₀ := etOfPushout hpo hc
  have e3 : (IsLocalRing.maximalIdeal X).comap f₂.hom = r' := by
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (hfr₂ a).symm
  refine ⟨A', X, f, h₀ ≫ f₂, u₁ ≫ f₂, IsLocalRing.maximalIdeal X, hf, hA', hX,
    hIE _ _ (MorphismProperty.le_ind _ _ hh₀) hf₂, ?_, hIE _ _ (ieOfPushout hsq hf) hf₂, inferInstance, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    by_contra hn
    have hm : a ∈ IsLocalRing.maximalIdeal A' := hn
    rw [← e₂, Ideal.mem_comap] at hm
    refine (hfr₂ _).1 hm ?_
    have e4 : (pC A' ≫ h₀ ≫ f₂) = u₂ ≫ f₂ := by rw [← Category.assoc, e0]
    rw [e4] at ha
    exact ha
  · rw [CommRingCat.hom_comp, ← Ideal.comap_comap, e3]
    exact e₁
  · rw [← Category.assoc (pC A') h₀ f₂, e0, ← Category.assoc f u₂ f₂]
    have e5 : f ≫ u₂ = (pC A ≫ c) ≫ u₁ := hsq.w.symm
    rw [e5]
    simp only [Category.assoc]

end UpperTheory.Cb.EtalePushouts

open UpperTheory.Cb.EtalePushouts in
/- English proof (translation)
Introduce `hStalk hLimit hSH hIE hAlg hSHE hULA H q _ i T K A k t hq hk hG B c hc`. Establish `hqP : IsUnit (q : CommRingCat.of (Polynomial A))` using `by simpa using hq.map (t ≫ pC A).hom`. Establish `s` using `IsPushout.of_hasPushout k (t ≫ pC A)`. Use `bcFwd s (hStalk H q i (pushout.inr k (t ≫ pC A)) hqP (fun _ c => Et c) ?_ ?_ ?_ B c hc)` and prove the remaining obligations. Introduce `C D E Z c f g u v sq hc hf hg`.

Rewrite using `[← Category.assoc]`. Conclude with `etComp hf (etOfPushout sq (etRight hc hg))`. Introduce `C D c f hc hf`. Conclude with `etComp hc hf`. Introduce `U c hc`.

Use `⟨U, 𝟙 U, ?_, fun r hr => ⟨r, hr, Ideal.comap_id r⟩, ?_, fun r hr => ?_⟩` and prove the remaining obligations. Conclude with `RingHom.isIntegral_of_surjective _ Function.surjective_id`. Simplify using `using hc`. Take `⟨A', X, f, h, o, Q, hf, hA', hX, hh, hl, ho, hQ, hQr, e⟩` from `geo hSH hIE c hc r hr`. Use `⟨X, o, Q, ho, hQ, hQr, bcBack s ?_⟩` and prove the remaining obligations.

Establish `hb` using `coh hLimit hAlg hSHE hULA H q i k t hq hk hG f hf hA' hX h hh hl`. Establish `e' : (t ≫ pC A) ≫ c ≫ 𝟙 U ≫ o = (t ≫ f) ≫ pC A' ≫ h`. Simplify using `only [Category.id_comp, Category.assoc]`. Rewrite using `[e]`. Rewrite using `[e']`.

Conclude with `hb`.
-/
theorem UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation :
    LateralTheory.E.t_E3Cut.Stalk → LateralTheory.E.t_E3Cut.Limit → LateralTheory.E.t_E3Cut.SHExists → LateralTheory.E.t_E3Cut.IEComp → LateralTheory.E.t_E3Cut.AlgResProps → LateralTheory.E.t_E3Cut.SHEqv → LateralTheory.E.t_E3Cut.ULA → LateralTheory.E.t_E3Cut.Step := by
  intro hStalk hLimit hSH hIE hAlg hSHE hULA H q _ i T K A k t hq hk hG B c hc
  have hqP : IsUnit (q : CommRingCat.of (Polynomial A)) := by simpa using hq.map (t ≫ pC A).hom
  have s := IsPushout.of_hasPushout k (t ≫ pC A)
  refine bcFwd s (hStalk H q i (pushout.inr k (t ≫ pC A)) hqP (fun _ c => Et c) ?_ ?_ ?_ B c hc)
  · intro C D E Z c f g u v sq hc hf hg
    rw [← Category.assoc]
    exact etComp hf (etOfPushout sq (etRight hc hg))
  · intro C D c f hc hf
    exact etComp hc hf
  · intro U c hc
    refine ⟨U, 𝟙 U, ?_, fun r hr => ⟨r, hr, Ideal.comap_id r⟩, ?_, fun r hr => ?_⟩
    · exact RingHom.isIntegral_of_surjective _ Function.surjective_id
    · simpa using hc
    · obtain ⟨A', X, f, h, o, Q, hf, hA', hX, hh, hl, ho, hQ, hQr, e⟩ := geo hSH hIE c hc r hr
      refine ⟨X, o, Q, ho, hQ, hQr, bcBack s ?_⟩
      have hb := coh hLimit hAlg hSHE hULA H q i k t hq hk hG f hf hA' hX h hh hl
      have e' : (t ≫ pC A) ≫ c ≫ 𝟙 U ≫ o = (t ≫ f) ≫ pC A' ≫ h := by
        simp only [Category.id_comp, Category.assoc]
        rw [e]
      rw [e']
      exact hb
