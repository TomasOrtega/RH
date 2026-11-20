import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnit

/- English proof (translation)
Introduce `F _ _ _ B _ ψ hker hd a T hT`. Use `letI : TopologicalSpace B := ⊥`. Use `haveI : DiscreteTopology B := ⟨rfl⟩`. Establish `hψ : Continuous ψ` using `continuous_of_isOpen_ker' ψ hker`. Set `ι : (InfiniteAdeleRing F)ˣ →* Ideles F` to `Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))`.

Establish `hι : Continuous ι` using `Continuous.units_map _ (continuous_id.prodMk continuous_const)`. Establish `hinf : ∀ u, ψ (ι u) = 1`. Introduce `u`. Take `⟨y, rfl⟩` from `GlobalTheory.HeckeInfTriv.infUnit_surj F u`. Establish `hc : Continuous fun y => ψ (ι (GlobalTheory.HeckeInfTriv.infUnit F y))` using `hψ.comp (hι.comp (GlobalTheory.HeckeInfTriv.continuous_infUnit F))`.

Establish `e` using `PreconnectedSpace.constant inferInstance hc (x := y) (y := 1)`. Rewrite using `[e, map_one, map_one, map_one]`. Set `P : Ideles F →* (InfiniteAdeleRing F)ˣ` to `Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))`. Set `u : (InfiniteAdeleRing F)ˣ` to `P (diagUnits F a)`. Set `av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ` to `fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a`.

Set `z : Ideles F` to `diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹`. Establish `hPι : P (ι u) = u` using `Units.ext rfl`. Establish `hPl : ∀ v, P (locUnit F v a) = 1` using `fun v => Units.ext rfl`. Establish `hz1 : (z : AdeleRing (𝓞 F) F).1 = 1`. Establish `h : P z = 1`.

Simplify using `only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]`. Conclude with `mul_inv_cancel u`. Conclude with `congrArg Units.val h`. Establish `hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v` using `fun v => Units.ext rfl`. Establish `hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1` using `fun v => Units.ext rfl`.

Establish `hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1`. Introduce `v w`. Apply `Units.ext` to reduce the goal to its premises. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `GlobalTheory.Mem.LocTriv.ev_local_self w _`. Conclude with `GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _`. Establish `hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1`. Introduce `v`. Establish `e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹`.

Simplify using `only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]`. Rewrite using `[e, Finset.prod_ite_eq' T v]`. Use `split_ifs with hv`. Rewrite using `[mul_inv_cancel, map_one, map_one]`. Rewrite using `[inv_one, mul_one]`.

Conclude with `hT v hv`. Establish `hz` using `GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl`. Simplify using `only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz`. Conclude with `inv_eq_one.mp hz`.
-/
theorem prod_locUnit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Ideles F →* B), IsOpen (ψ.ker : Set (Ideles F)) → (∀ k : Fˣ, ψ (diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  intro F _ _ _ B _ ψ hker hd a T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hι : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  have hinf : ∀ u, ψ (ι u) = 1 := by
    intro u
    obtain ⟨y, rfl⟩ := GlobalTheory.HeckeInfTriv.infUnit_surj F u
    have hc : Continuous fun y => ψ (ι (GlobalTheory.HeckeInfTriv.infUnit F y)) :=
      hψ.comp (hι.comp (GlobalTheory.HeckeInfTriv.continuous_infUnit F))
    have e := PreconnectedSpace.constant inferInstance hc (x := y) (y := 1)
    rw [e, map_one, map_one, map_one]
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Ideles F := diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnit
