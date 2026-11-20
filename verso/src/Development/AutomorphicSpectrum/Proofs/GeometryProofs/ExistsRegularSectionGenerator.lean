import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemRegAtOfCodimOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrOrderExistsUnitEqUnitMulZpowIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SurjectiveOfDualHomomorphismKernelKilled
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsMaxRatioCleared
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormalNoethLocalDimOneIsDVR

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ZLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def gp (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

/- English proof (translation)
Take `⟨x, hx⟩` from `h.bij.2 a`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `e0 : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _` using `X.presheaf.stalkSpecializes_refl _`. Establish `e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ = Scheme.stalkClosedPointTo ξ` using `(congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e0).trans (Category.id_comp _)`. Conclude with `(congrArg (fun f => f.hom x) e).trans hx`.
-/
theorem mem_regAt_gp (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (gp ξ) := by
  obtain ⟨x, hx⟩ := h.bij.2 a
  refine ⟨x, ?_⟩
  have e0 : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl _
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ = Scheme.stalkClosedPointTo ξ :=
    (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e0).trans (Category.id_comp _)
  exact (congrArg (fun f => f.hom x) e).trans hx

/- English proof (translation)
Assemble the required witnesses or components as `⟨ha, mem_regAt_gp h a, mem_regAt_gp h _⟩`.
-/
theorem unitAt_gp (h : IsCptGen ξ) {a : Ω} (ha : a ≠ 0) : unitAt ξ (gp ξ) a :=
  ⟨ha, mem_regAt_gp h a, mem_regAt_gp h _⟩

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `a.eq_nat_or_neg`. Rewrite using `[zpow_natCast]`. Conclude with `pow_mem ht.2.1 n`. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `pow_mem ht.2.2 n`.
-/
theorem zpow_mem_regAt {p : Cpt ξ} {t : Ω} (ht : unitAt ξ p t) (a : ℤ) : t ^ a ∈ regAt ξ p := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · rw [zpow_natCast]; exact pow_mem ht.2.1 n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem ht.2.2 n

/- English proof (translation)
Use `IsFractionRing.of_field _ _ fun a => ?_` and prove the remaining obligations. Take `⟨s, hs, hu, hsa⟩` from `(RegAtMono.regAt_mono X Ω ξ p (gp ξ) p.2).2 h a (mem_regAt_gp h a)`. Use `⟨⟨s * a, hsa⟩, ⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Use `show a = s * a / s`. Clear denominators, using `[hu.1]` for the nonvanishing conditions.
-/
theorem isFractionRing_regAt (h : IsCptGen ξ) (p : Cpt ξ) : IsFractionRing (regAt ξ p) Ω := by
  refine IsFractionRing.of_field _ _ fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ :=
    (RegAtMono.regAt_mono X Ω ξ p (gp ξ) p.2).2 h a (mem_regAt_gp h a)
  refine ⟨⟨s * a, hsa⟩, ⟨s, hs⟩, ?_⟩
  show a = s * a / s
  field_simp [hu.1]

/- English proof (translation)
Set `e : X.presheaf.stalk p.1 ≃+* regAt ξ p` to `RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨fun x y hxy => h.inj p (congrArg Subtype.val hxy), (genMap ξ p).rangeRestrict_surjective⟩`. Use `haveI := isFractionRing_regAt h p`. Use `haveI : IsLocalRing (regAt ξ p) := e.isLocalRing`. Use `haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ e`. Use `haveI : IsIntegrallyClosed (regAt ξ p) := (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, hn p x hx⟩, rfl⟩`.

Conclude with `normal_noeth_local_dim_one_isDVR _ ((ringKrullDim_eq_of_ringEquiv e).symm.trans hd)`.
-/
theorem isDVR_regAt [IsLocallyNoetherian X] (h : IsCptGen ξ) (hn : NormalCpt ξ) (p : Cpt ξ)
    (hd : ringKrullDim (X.presheaf.stalk p.1) = 1) : IsDiscreteValuationRing (regAt ξ p) := by
  let e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun x y hxy => h.inj p (congrArg Subtype.val hxy), (genMap ξ p).rangeRestrict_surjective⟩
  haveI := isFractionRing_regAt h p
  haveI : IsLocalRing (regAt ξ p) := e.isLocalRing
  haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ e
  haveI : IsIntegrallyClosed (regAt ξ p) :=
    (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, hn p x hx⟩, rfl⟩
  exact normal_noeth_local_dim_one_isDVR _ ((ringKrullDim_eq_of_ringEquiv e).symm.trans hd)

/- English proof (translation)
Use `haveI := isFractionRing_regAt h p`. Use `haveI := isDVR_regAt h hn p hd`. Establish `hw0 : (⟨t, ht⟩ : regAt ξ p) ≠ 0` using `fun e => ht0 (congrArg Subtype.val e)`. Establish `hwu : ¬ IsUnit (⟨t, ht⟩ : regAt ξ p)`. Introduce and unpack `⟨u, hu⟩`.

Use `hnu ⟨ht0, ht, ?_⟩` and prove the remaining obligations. Establish `e : ((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p).1 = t⁻¹`. Establish `e1 : ((u : regAt ξ p)).1 * ((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p).1 = 1` using `congrArg Subtype.val u.mul_inv`. Rewrite `e1` using `[hu]`. Conclude with `eq_inv_of_mul_eq_one_right e1`.

Conclude with `e ▸ (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p)).2`. Take `⟨m, n, hm, H⟩` from `dvr_order_integral_unit_iff (regAt ξ p) Ω ⟨t, ht⟩ s hw0 hwu hs`. Use `⟨m, n, hm, fun M a => ⟨fun hle => ?_, fun heq => ?_⟩⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `(H M a).1.2 hle`. Establish `hr' : (r : Ω) * s ^ M = t ^ a` using `hr`.

Rewrite using `[← hr', mul_div_assoc, div_self (pow_ne_zero M hs), mul_one]`. Conclude with `r.2`. Take `⟨r, hr⟩` from `(H M a).2.2 heq`. Establish `hr' : ((r : regAt ξ p) : Ω) * s ^ M = t ^ a` using `hr`. Establish `hr0 : ((r : regAt ξ p) : Ω) ≠ 0` using `fun e => r.ne_zero (Subtype.ext e)`.

Establish `hsM` using `pow_ne_zero M hs`. Establish `e2 : ((r : regAt ξ p) : Ω) * (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = 1` using `congrArg Subtype.val r.mul_inv`. Establish `hri : (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = ((r : regAt ξ p) : Ω)⁻¹` using `eq_inv_of_mul_eq_one_right e2`. Establish `e1 : s ^ M / t ^ a = ((r : regAt ξ p) : Ω)⁻¹`. Rewrite using `[← hr']`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Use `⟨inv_ne_zero hr0, hri ▸ (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p)).2, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_inv]`. Conclude with `(r : regAt ξ p).2`.
-/
theorem exists_orders [IsLocallyNoetherian X] (h : IsCptGen ξ) (hn : NormalCpt ξ) (p : Cpt ξ)
    (hd : ringKrullDim (X.presheaf.stalk p.1) = 1) {t s : Ω} (ht : t ∈ regAt ξ p) (ht0 : t ≠ 0)
    (hnu : ¬ unitAt ξ p t) (hs : s ≠ 0) :
    ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ),
      ((M : ℤ) * n ≤ a * m → t ^ a / s ^ M ∈ regAt ξ p) ∧
      ((M : ℤ) * n = a * m → unitAt ξ p (s ^ M / t ^ a)) := by
  haveI := isFractionRing_regAt h p
  haveI := isDVR_regAt h hn p hd
  have hw0 : (⟨t, ht⟩ : regAt ξ p) ≠ 0 := fun e => ht0 (congrArg Subtype.val e)
  have hwu : ¬ IsUnit (⟨t, ht⟩ : regAt ξ p) := by
    rintro ⟨u, hu⟩
    refine hnu ⟨ht0, ht, ?_⟩
    have e : ((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p).1 = t⁻¹ := by
      have e1 : ((u : regAt ξ p)).1 * ((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p).1 = 1 :=
        congrArg Subtype.val u.mul_inv
      rw [hu] at e1
      exact eq_inv_of_mul_eq_one_right e1
    exact e ▸ (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p)).2
  obtain ⟨m, n, hm, H⟩ := dvr_order_integral_unit_iff (regAt ξ p) Ω ⟨t, ht⟩ s hw0 hwu hs
  refine ⟨m, n, hm, fun M a => ⟨fun hle => ?_, fun heq => ?_⟩⟩
  · obtain ⟨r, hr⟩ := (H M a).1.2 hle
    have hr' : (r : Ω) * s ^ M = t ^ a := hr
    rw [← hr', mul_div_assoc, div_self (pow_ne_zero M hs), mul_one]
    exact r.2
  · obtain ⟨r, hr⟩ := (H M a).2.2 heq
    have hr' : ((r : regAt ξ p) : Ω) * s ^ M = t ^ a := hr
    have hr0 : ((r : regAt ξ p) : Ω) ≠ 0 := fun e => r.ne_zero (Subtype.ext e)
    have hsM := pow_ne_zero M hs
    have e2 : ((r : regAt ξ p) : Ω) * (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = 1 :=
      congrArg Subtype.val r.mul_inv
    have hri : (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = ((r : regAt ξ p) : Ω)⁻¹ :=
      eq_inv_of_mul_eq_one_right e2
    have e1 : s ^ M / t ^ a = ((r : regAt ξ p) : Ω)⁻¹ := by
      rw [← hr']
      field_simp
    rw [e1]
    refine ⟨inv_ne_zero hr0, hri ▸ (((r⁻¹ : (regAt ξ p)ˣ) : regAt ξ p)).2, ?_⟩
    rw [inv_inv]
    exact (r : regAt ξ p).2

namespace GlobalTheory.CompanionTheory.Ar.Flat.ZLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Take `⟨U, hU, hcl, hint⟩` from `GlobalTheory.CompanionTheory.Ar.Flat.cpt_open_integral X Ω ξ h`. Use `haveI := hint`. Use `haveI : CompactSpace U := isCompact_iff_compactSpace.mp hcl.isCompact`. Use `haveI : IsNoetherian U.toScheme := { }`. Set `g : U.toScheme ⟶ Spec (CommRingCat.of R)` to `U.ι ≫ s`.

Set `w : Γ(U.toScheme, ⊤)` to `(Scheme.Hom.app g ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom o)`. Establish `hb : ∀ x : U.toScheme, x ∉ U.toScheme.basicOpen w ↔ o ∈ (s x.1).asIdeal`. Introduce `x`. Establish `e` using `Scheme.preimage_basicOpen g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom o)`. Rewrite `e` using `[basicOpen_eq_of_affine]`.

Establish `e1 : x ∈ U.toScheme.basicOpen w ↔ g x ∈ PrimeSpectrum.basicOpen o`. Express the relevant statement in the definitionally equal form `x ∈ U.toScheme.basicOpen ((Scheme.Hom.app g ⊤).hom _) ↔ _`. Rewrite using `[← e]`. Both sides reduce to the same expression. Establish `hgx : g x = s x.1` using `by simp [g]; rfl`.

Establish `e2 : s x.1 ∈ PrimeSpectrum.basicOpen o ↔ o ∉ (s x.1).asIdeal` using `PrimeSpectrum.mem_basicOpen o (s x.1)`. Rewrite using `[e1, hgx]`. Conclude with `(not_congr e2).trans not_not`. Establish `hd : ∀ x : U.toScheme, ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk x.1)` using `fun x => ringKrullDim_eq_of_ringEquiv (Scheme.Opens.stalkIso U x).commRingCatIsoToRingEquiv`. Establish `hw : w ≠ 0`.

Introduce `e`. Establish `h0 : (⟨genPt ξ, (hU _).2 specializes_rfl⟩ : U.toScheme) ∉ U.toScheme.basicOpen w`. Rewrite using `[e, Scheme.basicOpen_zero]`. Conclude with `fun hh => (hh : False)`. Conclude with `ho ((hb _).1 h0)`.

Take `⟨hfin, hex⟩` from `finite_codim_one_zero_set_and_exists U.toScheme w hw`. Set `f : Cpt ξ → U.toScheme` to `fun p => ⟨p.1, (hU p.1).2 p.2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(hfin.preimage (f := f) (fun a _ b _ e => Subtype.ext (show a.1 = b.1 from congrArg (fun z : U.toScheme => (z.1 : X)) e))).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨h1, h2⟩`.

Conclude with `⟨(hb _).2 h1, (hd _).trans h2⟩`. Introduce `q hq`. Take `⟨x, hx, hx1, -⟩` from `hex (f q) ((hb _).2 hq)`. Conclude with `⟨⟨x.1, (hU _).1 x.2⟩, (hb x).1 hx, (hd x).symm.trans hx1⟩`.
-/
theorem finite_and_exists [IsLocallyNoetherian X] [CompactSpace X] (h : IsCptGen ξ) {R : Type} [CommRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) (o : R) (ho : o ∉ (s (genPt ξ)).asIdeal) :
    {p : Cpt ξ | o ∈ (s p.1).asIdeal ∧ ringKrullDim (X.presheaf.stalk p.1) = 1}.Finite ∧
    ∀ q : Cpt ξ, o ∈ (s q.1).asIdeal →
      ∃ p : Cpt ξ, o ∈ (s p.1).asIdeal ∧ ringKrullDim (X.presheaf.stalk p.1) = 1 := by
  obtain ⟨U, hU, hcl, hint⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cpt_open_integral X Ω ξ h
  haveI := hint
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hcl.isCompact
  haveI : IsNoetherian U.toScheme := { }
  let g : U.toScheme ⟶ Spec (CommRingCat.of R) := U.ι ≫ s
  let w : Γ(U.toScheme, ⊤) := (Scheme.Hom.app g ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom o)
  have hb : ∀ x : U.toScheme, x ∉ U.toScheme.basicOpen w ↔ o ∈ (s x.1).asIdeal := by
    intro x
    have e := Scheme.preimage_basicOpen g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom o)
    rw [basicOpen_eq_of_affine] at e
    have e1 : x ∈ U.toScheme.basicOpen w ↔ g x ∈ PrimeSpectrum.basicOpen o := by
      change x ∈ U.toScheme.basicOpen ((Scheme.Hom.app g ⊤).hom _) ↔ _
      rw [← e]
      rfl
    have hgx : g x = s x.1 := by simp [g]; rfl
    have e2 : s x.1 ∈ PrimeSpectrum.basicOpen o ↔ o ∉ (s x.1).asIdeal :=
      PrimeSpectrum.mem_basicOpen o (s x.1)
    rw [e1, hgx]
    exact (not_congr e2).trans not_not
  have hd : ∀ x : U.toScheme, ringKrullDim (U.toScheme.presheaf.stalk x) =
      ringKrullDim (X.presheaf.stalk x.1) := fun x =>
    ringKrullDim_eq_of_ringEquiv (Scheme.Opens.stalkIso U x).commRingCatIsoToRingEquiv
  have hw : w ≠ 0 := by
    intro e
    have h0 : (⟨genPt ξ, (hU _).2 specializes_rfl⟩ : U.toScheme) ∉ U.toScheme.basicOpen w := by
      rw [e, Scheme.basicOpen_zero]
      exact fun hh => (hh : False)
    exact ho ((hb _).1 h0)
  obtain ⟨hfin, hex⟩ := finite_codim_one_zero_set_and_exists U.toScheme w hw
  let f : Cpt ξ → U.toScheme := fun p => ⟨p.1, (hU p.1).2 p.2⟩
  refine ⟨?_, ?_⟩
  · refine (hfin.preimage (f := f) (fun a _ b _ e =>
      Subtype.ext (show a.1 = b.1 from congrArg (fun z : U.toScheme => (z.1 : X)) e))).subset ?_
    rintro p ⟨h1, h2⟩
    exact ⟨(hb _).2 h1, (hd _).trans h2⟩
  · intro q hq
    obtain ⟨x, hx, hx1, -⟩ := hex (f q) ((hb _).2 hq)
    exact ⟨⟨x.1, (hU _).1 x.2⟩, (hb x).1 hx, (hd x).symm.trans hx1⟩

/- English proof (translation)
Establish `hm : e' ∈ L p` using `by rw [h'.2]; exact Submodule.mem_span_singleton_self e'`. Rewrite `hm` using `[h.2, Submodule.mem_span_singleton]`. Take `⟨r, rfl⟩` from `hm`. Establish `e1 : r • e = (r : Ω) * e` using `rfl`. Rewrite using `[e1, mul_div_assoc, div_self h.1, mul_one]`.

Conclude with `r.2`.
-/
theorem gen_div_mem {L : Lat ξ Ω} {p : Cpt ξ} {e e' : Ω} (h : L.IsGenAt p e) (h' : L.IsGenAt p e') :
    e' / e ∈ regAt ξ p := by
  have hm : e' ∈ L p := by rw [h'.2]; exact Submodule.mem_span_singleton_self e'
  rw [h.2, Submodule.mem_span_singleton] at hm
  obtain ⟨r, rfl⟩ := hm
  have e1 : r • e = (r : Ω) * e := rfl
  rw [e1, mul_div_assoc, div_self h.1, mul_one]
  exact r.2

/- English proof (translation)
Take `⟨U, hp, b, -, hb⟩` from `h p (Set.mem_univ p)`. Use `⟨U, b 0, hp, fun q hq => ?_⟩` and prove the remaining obligations. Take `⟨hli, hspan⟩` from `hb q (Set.mem_univ q) hq`. Use `⟨hli.ne_zero 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hspan]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[eq_comm, Fin.exists_fin_one]`.
-/
theorem exists_local_gen {L : Lat ξ Ω} (h : L.IsVB 1 ⊤) (p : Cpt ξ) :
    ∃ (U : X.Opens) (e : Ω), p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q e := by
  obtain ⟨U, hp, b, -, hb⟩ := h p (Set.mem_univ p)
  refine ⟨U, b 0, hp, fun q hq => ?_⟩
  obtain ⟨hli, hspan⟩ := hb q (Set.mem_univ q) hq
  refine ⟨hli.ne_zero 0, ?_⟩
  rw [hspan]
  congr 1
  ext x
  simp [eq_comm, Fin.exists_fin_one]

/- English proof (translation)
Simplify using `only [div_pow]`. Establish `h1` using `pow_ne_zero M hσ`. Establish `h2` using `pow_ne_zero M he`. Establish `h3` using `pow_ne_zero M he'`. Clear the denominators using the available nonvanishing facts.
-/
theorem change_gen {t : Ω} {a : ℤ} {M : ℕ} {σ e e' : Ω} (hσ : σ ≠ 0) (he : e ≠ 0) (he' : e' ≠ 0) :
    t ^ a / (σ / e') ^ M = t ^ a / (σ / e) ^ M * (e' / e) ^ M := by
  simp only [div_pow]
  have h1 := pow_ne_zero M hσ
  have h2 := pow_ne_zero M he
  have h3 := pow_ne_zero M he'
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.ZLat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ZLat

/- English proof (translation)
Introduce `X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hz L σ hvb hgen`. Use `haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s`. Use `haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s`. Establish `hne : ∀ o : O, o ≠ 0 → algebraMap O Ω o ≠ 0` using `fun o ho e => ho (hinj (by rw [e, map_zero]))`. Establish `ht0 : algebraMap O Ω ϖ ≠ 0` using `hne ϖ hϖ.ne_zero`.

Establish `hreg : ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p` using `fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).1`. Establish `hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal` using `fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg`. Establish `hσ : σ ≠ 0` using `(hgen (gp ξ) fun o ho => unitAt_gp hg (hne o ho)).1`. Establish `hog : ϖ ∉ (s (genPt ξ)).asIdeal` using `(hunit (gp ξ) ϖ).1 (unitAt_gp hg ht0)`. Take `⟨hfin, hex⟩` from `finite_and_exists hg s ϖ hog`.

Establish `hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ`. Introduce `q hq o ho`. Rewrite using `[hunit]`. Introduce `hmem`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ`.

Establish `hP : (s q.1).asIdeal.IsPrime` using `(s q.1).isPrime`. Rewrite `hmem` using `[hu]`. Break down `hP.mem_or_mem hmem with h1 | h1` into its components or cases. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 (by`. Use `Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1` as an intermediate fact.

Rewrite using `[Units.inv_mul] at this))` and apply the resulting hypothesis. Conclude with `(hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)`. Set `S : Type` to `{p : Cpt ξ // ϖ ∈ (s p.1).asIdeal ∧ ringKrullDim (X.presheaf.stalk p.1) = 1}`. Use `haveI : Fintype S := hfin.fintype`. Use `haveI : Nonempty S := by`.

Take `⟨q, hq, hnu⟩` from `hz`. Establish `hq' : ϖ ∈ (s (⟨q, hq⟩ : Cpt ξ).1).asIdeal`. Assume the negation of the conclusion as `hc`. Conclude with `hnu ((hunit ⟨q, hq⟩ ϖ).2 hc)`. Take `⟨p, hp⟩` from `hex ⟨q, hq⟩ hq'`.

Conclude with `⟨⟨p, hp⟩⟩`. Establish `hgenAt : ∀ p : Cpt ξ, ∃ e : Ω, L.IsGenAt p e` using `fun p => by`. Take `⟨U, e, hp, he⟩` from `exists_local_gen hvb p`. Conclude with `⟨e, he p hp⟩`. Use `choose e he using hgenAt`.

Establish `hord : ∀ i : S, ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ), ((M : ℤ) * n ≤ a * m → algebraMap O Ω ϖ ^ a / (σ / e i.1) ^ M ∈ regAt ξ i.1) ∧ ((M : ℤ) * n = a * m → unitAt ξ i.1 ((σ / e i.1) ^ M / algebraMap O Ω ϖ ^ a))` using `fun i => exists_orders hg hn i.1 i.2.2 (hreg _ ϖ) ht0 (fun hu => (hunit _ ϖ).1 hu i.2.1) (div_ne_zero hσ (he i.1).1)`. Use `choose m n hm H using hord`. Take `⟨M, a, i₀, hM, hle, heq⟩` from `exists_max_ratio_cleared S n m hm`. Establish `hone : ∀ q : Cpt ξ, ringKrullDim (X.presheaf.stalk q.1) = 1 → ∀ e' : Ω, L.IsGenAt q e' → algebraMap O Ω ϖ ^ a / (σ / e') ^ M ∈ regAt ξ q`. Introduce `q hq e' he'`.

Distinguish the cases in `hu : unitAt ξ q (algebraMap O Ω ϖ)`. Establish `hσq` using `hgen q (hgf q hu)`. Establish `e1 : algebraMap O Ω ϖ ^ a / (σ / e') ^ M = algebraMap O Ω ϖ ^ a * (e' / σ) ^ M`. Rewrite using `[div_eq_mul_inv, ← inv_pow, inv_div]`. Rewrite using `[e1]`.

Conclude with `mul_mem (zpow_mem_regAt hu a) (pow_mem (gen_div_mem hσq he') M)`. Establish `hmem : ϖ ∈ (s q.1).asIdeal`. Assume the negation of the conclusion as `hc`. Conclude with `hu ((hunit q ϖ).2 hc)`. Set `i : S` to `⟨q, hmem, hq⟩`.

Establish `h1` using `(H i M a).1 (hle i)`. Establish `h2 : algebraMap O Ω ϖ ^ a / (σ / e') ^ M = algebraMap O Ω ϖ ^ a / (σ / e q) ^ M * (e' / e q) ^ M` using `change_gen hσ (he q).1 he'.1`. Rewrite using `[h2]`. Conclude with `mul_mem h1 (pow_mem (gen_div_mem (he q) he') M)`. Use `⟨M, a, hM, fun p e' he' => ?_, i₀.1, fun hu => (hunit _ ϖ).1 hu i₀.2.1, i₀.2.2, ?_⟩` and prove the remaining obligations.

Take `⟨U, b, hpU, hb⟩` from `exists_local_gen hvb p`. Establish `h0 : algebraMap O Ω ϖ ^ a / (σ / b) ^ M ∈ regAt ξ p` using `GlobalTheory.CompanionTheory.Ar.Flat.mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hq => hone q hq b (hb q (hqp.mem_open U.isOpen hpU))`. Rewrite using `[change_gen (e := b) hσ (hb p hpU).1 he'.1]`. Conclude with `mul_mem h0 (pow_mem (gen_div_mem (hb p hpU) he') M)`. Unfold `OrderAt`.

Use `⟨e i₀.1, σ / e i₀.1, (he i₀.1).1, (he i₀.1).2, ?_, (H i₀ M a).2 heq⟩` and prove the remaining obligations. Use `show σ = σ / e i₀.1 * e i₀.1`. Rewrite using `[div_mul_cancel₀ _ (he i₀.1).1]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_regular_section_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → (zeroSet ξ (algebraMap O Ω ϖ)).Nonempty → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → algebraMap O Ω ϖ ^ a / (σ / e) ^ M ∈ regAt ξ p) ∧ ∃ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ ringKrullDim (X.presheaf.stalk p.1) = 1 ∧ OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hz L σ hvb hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hne : ∀ o : O, o ≠ 0 → algebraMap O Ω o ≠ 0 := fun o ho e =>
    ho (hinj (by rw [e, map_zero]))
  have ht0 : algebraMap O Ω ϖ ≠ 0 := hne ϖ hϖ.ne_zero
  have hreg : ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := fun p o =>
    (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).1
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  have hσ : σ ≠ 0 := (hgen (gp ξ) fun o ho => unitAt_gp hg (hne o ho)).1
  have hog : ϖ ∉ (s (genPt ξ)).asIdeal := (hunit (gp ξ) ϖ).1 (unitAt_gp hg ht0)
  obtain ⟨hfin, hex⟩ := finite_and_exists hg s ϖ hog

  have hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ := by
    intro q hq o ho
    rw [hunit]
    intro hmem
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    have hP : (s q.1).asIdeal.IsPrime := (s q.1).isPrime
    rw [hu] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1
        rwa [Units.inv_mul] at this))
    · exact (hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)
  let S : Type := {p : Cpt ξ // ϖ ∈ (s p.1).asIdeal ∧ ringKrullDim (X.presheaf.stalk p.1) = 1}
  haveI : Fintype S := hfin.fintype
  haveI : Nonempty S := by
    obtain ⟨q, hq, hnu⟩ := hz
    have hq' : ϖ ∈ (s (⟨q, hq⟩ : Cpt ξ).1).asIdeal := by
      by_contra hc
      exact hnu ((hunit ⟨q, hq⟩ ϖ).2 hc)
    obtain ⟨p, hp⟩ := hex ⟨q, hq⟩ hq'
    exact ⟨⟨p, hp⟩⟩
  have hgenAt : ∀ p : Cpt ξ, ∃ e : Ω, L.IsGenAt p e := fun p => by
    obtain ⟨U, e, hp, he⟩ := exists_local_gen hvb p
    exact ⟨e, he p hp⟩
  choose e he using hgenAt
  have hord : ∀ i : S, ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ),
      ((M : ℤ) * n ≤ a * m → algebraMap O Ω ϖ ^ a / (σ / e i.1) ^ M ∈ regAt ξ i.1) ∧
      ((M : ℤ) * n = a * m → unitAt ξ i.1 ((σ / e i.1) ^ M / algebraMap O Ω ϖ ^ a)) := fun i =>
    exists_orders hg hn i.1 i.2.2 (hreg _ ϖ) ht0 (fun hu => (hunit _ ϖ).1 hu i.2.1)
      (div_ne_zero hσ (he i.1).1)
  choose m n hm H using hord
  obtain ⟨M, a, i₀, hM, hle, heq⟩ := exists_max_ratio_cleared S n m hm

  have hone : ∀ q : Cpt ξ, ringKrullDim (X.presheaf.stalk q.1) = 1 → ∀ e' : Ω, L.IsGenAt q e' →
      algebraMap O Ω ϖ ^ a / (σ / e') ^ M ∈ regAt ξ q := by
    intro q hq e' he'
    by_cases hu : unitAt ξ q (algebraMap O Ω ϖ)
    · have hσq := hgen q (hgf q hu)
      have e1 : algebraMap O Ω ϖ ^ a / (σ / e') ^ M = algebraMap O Ω ϖ ^ a * (e' / σ) ^ M := by
        rw [div_eq_mul_inv, ← inv_pow, inv_div]
      rw [e1]
      exact mul_mem (zpow_mem_regAt hu a) (pow_mem (gen_div_mem hσq he') M)
    · have hmem : ϖ ∈ (s q.1).asIdeal := by
        by_contra hc
        exact hu ((hunit q ϖ).2 hc)
      let i : S := ⟨q, hmem, hq⟩
      have h1 := (H i M a).1 (hle i)
      have h2 : algebraMap O Ω ϖ ^ a / (σ / e') ^ M =
          algebraMap O Ω ϖ ^ a / (σ / e q) ^ M * (e' / e q) ^ M :=
        change_gen hσ (he q).1 he'.1
      rw [h2]
      exact mul_mem h1 (pow_mem (gen_div_mem (he q) he') M)
  refine ⟨M, a, hM, fun p e' he' => ?_, i₀.1, fun hu => (hunit _ ϖ).1 hu i₀.2.1, i₀.2.2, ?_⟩
  · obtain ⟨U, b, hpU, hb⟩ := exists_local_gen hvb p
    have h0 : algebraMap O Ω ϖ ^ a / (σ / b) ^ M ∈ regAt ξ p :=
      GlobalTheory.CompanionTheory.Ar.Flat.mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hq =>
        hone q hq b (hb q (hqp.mem_open U.isOpen hpU))
    rw [change_gen (e := b) hσ (hb p hpU).1 he'.1]
    exact mul_mem h0 (pow_mem (gen_div_mem (hb p hpU) he') M)
  · unfold OrderAt
    refine ⟨e i₀.1, σ / e i₀.1, (he i₀.1).1, (he i₀.1).2, ?_, (H i₀ M a).2 heq⟩
    show σ = σ / e i₀.1 * e i₀.1
    rw [div_mul_cancel₀ _ (he i₀.1).1]

end GlobalTheory.CompanionTheory.Ar.Flat.ZLat
