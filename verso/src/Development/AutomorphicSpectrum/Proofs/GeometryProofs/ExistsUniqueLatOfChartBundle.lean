import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieVB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

/- English proof (translation)
Establish `e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h` using `TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2`. Establish `e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) = X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ` using `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)`. Conclude with `congrArg (fun f => f.hom t) e2`.
-/
theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Establish `hu` using `hs.map (genMap ξ q)`. Use `⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hs`.

Use `⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩` and prove the remaining obligations. Establish `: genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Conclude with `eq_inv_of_mul_eq_one_right this`. Introduce and unpack `⟨h0, -, ⟨s', hs'⟩⟩`.

Establish `: s * s' = 1` using `hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])`. Conclude with `IsUnit.of_mul_eq_one _ this`.
-/
theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

/- English proof (translation)
Rewrite using `[Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]`.
-/
theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩`.
-/
theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, one_mem _, by simp [one_mem]⟩`.
-/
theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `hg.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Unfold `genMap`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`. Use `erw [Category.id_comp]`.

Both sides reduce to the same expression.
-/
theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

/- English proof (translation)
Take `⟨U, hU, hmem⟩` from `hT.affine c hc`. Establish `h : genPt ξ ∈ U` using `(hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩`. Establish `hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q` using `fun q hq => by`. Take `⟨h2, _⟩` from `(hmem q).1 hq`. Conclude with `h2`.

Establish `hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q` using `fun q => ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩`. Take `⟨hinj, hran⟩` from `GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U h hsp`. Use `⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hT.ring c hc a]`. Use `Iff.trans ?_ (hran a).symm` and prove the remaining obligations.

Conclude with `forall_congr' fun q => (by rw [hUq q])`.
-/
theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

/- English proof (translation)
Take `⟨U, h, hU, hUq, hsp, -, hran⟩` from `exists_chart hT hc`. Set `φ : Γ(X, U) →+* chartRing o x c` to `(secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩`. Set `y : PrimeSpectrum Γ(X, U)` to `⟨P.comap φ, inferInstance⟩`. Establish `hyU : hU.fromSpec y ∈ U`. Establish `: hU.fromSpec y ∈ Set.range hU.fromSpec` using `⟨y, rfl⟩`.

Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `q : Cpt ξ` to `⟨_, hsp _ hyU⟩`. Use `⟨q, (hUq q).1 hyU, fun s => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `(hran s).1 s.2`. Establish `hst : s = φ t` using `Subtype.ext ht.symm`.

Establish `key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ` using `by show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Establish `h2` using `mem_basicOpen_iff hT.gen U h q hyU t`. Establish `h3 : (s : Ω) = secVal ξ U h t` using `ht.symm`.

Rewrite using `[h3, ← h2, key, hst, Ideal.mem_comap, not_not]`.
-/
theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

/- English proof (translation)
The claim follows from `(hT.ring c hp.1 a).1 ha p hp`.
-/
theorem chart_le_regAt (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ chartRing o x c) : a ∈ regAt ξ p :=
  (hT.ring c hp.1 a).1 ha p hp

/- English proof (translation)
The claim follows from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x hT c p hp a).1 ha`.
-/
theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x hT c p hp a).1 ha

/- English proof (translation)
Set `I : Ideal (chartRing o x c)` to `{ carrier := {s | (s : Ω) * a ∈ chartRing o x c} add_mem' := fun {u v} hu hv => by show ((u + v : chartRing o x c) : Ω) * a ∈ chartRing o x c`. Establish `: ((u + v : chartRing o x c) : Ω) * a = (u : Ω) * a + (v : Ω) * a` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `add_mem hu hv`. Use the proof step `zero_mem' := by show ((0 : chartRing o x c) : Ω) * a ∈ chartRing o x c`.

Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun t u hu => by show ((t • u : chartRing o x c) : Ω) * a ∈ chartRing o x c`. Establish `: ((t • u : chartRing o x c) : Ω) * a = (t : Ω) * ((u : Ω) * a)`. Simplify using `[_root_.mul_assoc]`. Rewrite using `[this]`.

Conclude with `mul_mem t.2 hu }`. Establish `hrad : (⟨f, hf⟩ : chartRing o x c) ∈ I.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `P ⟨hle, hP⟩`. Assume the negation of the conclusion as `hfP`.

Take `⟨p, hp, hs⟩` from `exists_point hT hc P hP`. Establish `hu : unitAt ξ p f`. Assume the negation of the conclusion as `hn`. Conclude with `hfP ((hs ⟨f, hf⟩).2 hn)`. Take `⟨s, hsA, hsu, hsa⟩` from `exists_den hT hp (h p hp hu)`.

Conclude with `(hs ⟨s, hsA⟩).1 (hle hsa) hsu`. Take `⟨n, hn⟩` from `hrad`. Conclude with `⟨n, hn⟩`.
-/
theorem exists_pow_mul_mem (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {f a : Ω} (hf : f ∈ chartRing o x c)
    (h : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p f → a ∈ regAt ξ p) :
    ∃ n : ℕ, f ^ n * a ∈ chartRing o x c := by
  let I : Ideal (chartRing o x c) :=
    { carrier := {s | (s : Ω) * a ∈ chartRing o x c}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((u + v : chartRing o x c) : Ω) * a = (u : Ω) * a + (v : Ω) * a := by
          push_cast; ring
        rw [this]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing o x c) : Ω) * a ∈ chartRing o x c
        simp
      smul_mem' := fun t u hu => by
        show ((t • u : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((t • u : chartRing o x c) : Ω) * a = (t : Ω) * ((u : Ω) * a) := by
          simp [_root_.mul_assoc]
        rw [this]
        exact mul_mem t.2 hu }
  have hrad : (⟨f, hf⟩ : chartRing o x c) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    by_contra hfP
    obtain ⟨p, hp, hs⟩ := exists_point hT hc P hP
    have hu : unitAt ξ p f := by
      by_contra hn
      exact hfP ((hs ⟨f, hf⟩).2 hn)
    obtain ⟨s, hsA, hsu, hsa⟩ := exists_den hT hp (h p hp hu)
    exact (hs ⟨s, hsA⟩).1 (hle hsa) hsu
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, hn⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩`. Consider the case `zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨s, hs, hsu, hsM⟩` from `hu`.

Take `⟨t, ht, htu, htM⟩` from `hv`. Use `⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩` and prove the remaining obligations. Establish `h1 : (s * t) • (u + v) = t • s • u + s • t • v`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm t s]`. Rewrite using `[h1]`.

Conclude with `add_mem (hM t ht _ hsM) (hM s hs _ htM)`. Consider the case `smul r u _ hu`. Take `⟨s, hs, hsu, hsM⟩` from `hu`. Take `⟨t, ht, htu, htr⟩` from `exists_den hT hp r.2`. Use `⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩` and prove the remaining obligations.

Establish `h1 : (t * s) • r • u = (t * (r : Ω)) • s • u`. Rewrite using `[Subring.smul_def, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`.

Conclude with `hM _ htr _ hsM`.
-/
theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

end Chart

section Bundle

variable {κ : Type} {x : κ → Ω} {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

noncomputable def latOf (ξ : Spec (CommRingCat.of Ω) ⟶ X) (W : ChartBundle ℤ x r E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ c, InChart ξ x c p ∧ e ∈ W.lat c}

end Bundle

end GlobalTheory.CompanionTheory.Ar.TieVB

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
