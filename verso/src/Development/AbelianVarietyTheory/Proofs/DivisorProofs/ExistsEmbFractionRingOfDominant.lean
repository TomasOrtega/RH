import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

/- English proof (translation)
Use `(PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_` and prove the remaining obligations. Use `show Ideal.comap (algebraMap V (FractionRing V)) p.asIdeal ≤ w.asIdeal`. Establish `hp : p.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ p.asIdeal (PrimeSpectrum.isPrime p)`. Rewrite using `[hp]`. Introduce `x hx`.

Establish `hx' : algebraMap V (FractionRing V) x = 0` using `Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)`. Rewrite using `[(injective_iff_map_eq_zero _).1 (IsFractionRing.injective V (FractionRing V)) x hx']`. Conclude with `w.asIdeal.zero_mem`.
-/
theorem spMap_fractionRing_specializes (V : Type) [CommRing V] [IsDomain V] (w : Sp V) (p : Sp (FractionRing V)) :
    (spMap (algebraMap V (FractionRing V))) p ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
  show Ideal.comap (algebraMap V (FractionRing V)) p.asIdeal ≤ w.asIdeal
  have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal (PrimeSpectrum.isPrime p)
  rw [hp]
  intro x hx
  have hx' : algebraMap V (FractionRing V) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
  rw [(injective_iff_map_eq_zero _).1 (IsFractionRing.injective V (FractionRing V)) x hx']
  exact w.asIdeal.zero_mem

/- English proof (translation)
Introduce `o Ω _ _ _ M V _ _ _ ξ ⟨w, hw⟩`. Use `set z := ξ (IsLocalRing.closedPoint V) with hzdef`. Set `g0 : M.O z →+* V` to `(Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom.comp (M.stalkEquiv z).symm.toRingHom`. Establish `hg0 : ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)) (hz : z ∈ U), g0 ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = valR ξ U f`. Introduce `U f hz`.

Establish `h : ⊤ ≤ ξ ⁻¹ᵁ U` using `(GlobalTheory.Points.le_preimage_iff ξ U).2 hz`. Establish `e1 : (M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f`. Rewrite using `[RingEquiv.symm_apply_eq, RatModel.stalkEquiv_germ]`. Establish `e2` using `congrArg (fun φ => φ.hom f) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap ξ U h)`. Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom ((M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩) = _`.

Rewrite using `[e1]`. Rewrite using `[GlobalTheory.Points.valR_eq ξ U h]`. Conclude with `e2`. Establish `hinj0 : Function.Injective g0`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce and unpack `⟨x, hx⟩ h0`. Take `⟨U, f, hz, rfl⟩` from `RatModel.mem_O.1 hx`. Rewrite `h0` using `[hg0 U f hz]`. Establish `hU : (U : Set M.Z).Nonempty` using `⟨z, hz⟩`. Distinguish the cases in `hf : f = 0`.

Substitute `hf` using the available equality. Apply `Subtype.ext` to reduce the goal to its premises. Use `show valF M.pt U 0 = 0`. Rewrite using `[← M.res_apply U hU, map_zero]`. It suffices to derive a contradiction.

Establish `hb : M.Z.basicOpen f ≠ ⊥` using `fun hb => hf ((basicOpen_eq_bot_iff f).1 hb)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Conclude with `fun h => hb (SetLike.coe_injective h)`. Establish `hgen : genericPoint M.Z ∈ M.Z.basicOpen f` using `(genericPoint_specializes y).mem_open (M.Z.basicOpen f).isOpen hy`.

Set `eta : Sp (FractionRing V) ⟶ M.Z` to `spMap (algebraMap V (FractionRing V)) ≫ ξ`. Establish `heta : ⊤ ≤ eta ⁻¹ᵁ M.Z.basicOpen f`. Introduce `p _`. Establish `hs : eta p ⤳ genericPoint M.Z`. Rewrite using `[← hw]`.

Conclude with `(spMap_fractionRing_specializes V w p).map ξ.continuous`. Conclude with `hs.mem_open (M.Z.basicOpen f).isOpen hgen`. Establish `hetaU : ⊤ ≤ eta ⁻¹ᵁ U` using `heta.trans (eta.preimage_mono (M.Z.basicOpen_le f))`. Establish `hu` using `(GlobalTheory.Points.le_preimage_basicOpen_iff eta hetaU f).1 heta`. Rewrite `hu` using `[GlobalTheory.Points.valR_spMap_comp _ ξ U ((GlobalTheory.Points.le_preimage_iff ξ U).2 hz), h0, map_zero]`.

Conclude with `not_isUnit_zero hu`. Set `g : M.O z →+* FractionRing V` to `(algebraMap V (FractionRing V)).comp g0`. Establish `hinj : Function.Injective g` using `(IsFractionRing.injective V (FractionRing V)).comp hinj0`. Use `⟨IsFractionRing.lift hinj, fun U f hz => ?_⟩` and prove the remaining obligations. Establish `e : valF M.pt U f = algebraMap (M.O z) Ω ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩` using `rfl`.

Rewrite using `[e, IsFractionRing.lift_algebraMap]`. Use `show algebraMap V (FractionRing V) (g0 _) = _`. Rewrite using `[hg0 U f hz]`.
-/
theorem exists_emb_fractionRing_of_dominant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∃ emb : Ω →+* FractionRing V, ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U → emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f) := by
  intro o Ω _ _ _ M V _ _ _ ξ ⟨w, hw⟩
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  let g0 : M.O z →+* V :=
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom.comp (M.stalkEquiv z).symm.toRingHom
  have hg0 : ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)) (hz : z ∈ U),
      g0 ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = valR ξ U f := by
    intro U f hz
    have h : ⊤ ≤ ξ ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff ξ U).2 hz
    have e1 : (M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f := by
      rw [RingEquiv.symm_apply_eq, RatModel.stalkEquiv_germ]
    have e2 := congrArg (fun φ => φ.hom f) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap ξ U h)
    change (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom ((M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩) = _
    rw [e1]
    rw [GlobalTheory.Points.valR_eq ξ U h]
    exact e2
  have hinj0 : Function.Injective g0 := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    obtain ⟨U, f, hz, rfl⟩ := RatModel.mem_O.1 hx
    rw [hg0 U f hz] at h0
    have hU : (U : Set M.Z).Nonempty := ⟨z, hz⟩
    by_cases hf : f = 0
    · subst hf
      apply Subtype.ext
      show valF M.pt U 0 = 0
      rw [← M.res_apply U hU, map_zero]
    · exfalso
      have hb : M.Z.basicOpen f ≠ ⊥ := fun hb => hf ((basicOpen_eq_bot_iff f).1 hb)
      obtain ⟨y, hy⟩ : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        exact fun h => hb (SetLike.coe_injective h)
      have hgen : genericPoint M.Z ∈ M.Z.basicOpen f :=
        (genericPoint_specializes y).mem_open (M.Z.basicOpen f).isOpen hy
      let eta : Sp (FractionRing V) ⟶ M.Z := spMap (algebraMap V (FractionRing V)) ≫ ξ
      have heta : ⊤ ≤ eta ⁻¹ᵁ M.Z.basicOpen f := by
        intro p _
        have hs : eta p ⤳ genericPoint M.Z := by
          rw [← hw]
          exact (spMap_fractionRing_specializes V w p).map ξ.continuous
        exact hs.mem_open (M.Z.basicOpen f).isOpen hgen
      have hetaU : ⊤ ≤ eta ⁻¹ᵁ U := heta.trans (eta.preimage_mono (M.Z.basicOpen_le f))
      have hu := (GlobalTheory.Points.le_preimage_basicOpen_iff eta hetaU f).1 heta
      rw [GlobalTheory.Points.valR_spMap_comp _ ξ U ((GlobalTheory.Points.le_preimage_iff ξ U).2 hz), h0, map_zero] at hu
      exact not_isUnit_zero hu
  let g : M.O z →+* FractionRing V := (algebraMap V (FractionRing V)).comp g0
  have hinj : Function.Injective g := (IsFractionRing.injective V (FractionRing V)).comp hinj0
  refine ⟨IsFractionRing.lift hinj, fun U f hz => ?_⟩
  have e : valF M.pt U f = algebraMap (M.O z) Ω ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ := rfl
  rw [e, IsFractionRing.lift_algebraMap]
  show algebraMap V (FractionRing V) (g0 _) = _
  rw [hg0 U f hz]

end GlobalTheory.ZH.RatModel
