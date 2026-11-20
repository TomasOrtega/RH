import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnitPos

/- English proof (translation)
Introduce `F _ _ B _ ψ hker hd hconn a ha T hT`. Use `letI : TopologicalSpace B := ⊥`. Use `haveI : DiscreteTopology B := ⟨rfl⟩`. Establish `hψ : Continuous ψ` using `continuous_of_isOpen_ker' ψ hker`. Set `ι : (InfiniteAdeleRing F)ˣ →* Ideles F` to `Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))`.

Set `P : Ideles F →* (InfiniteAdeleRing F)ˣ` to `Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))`. Set `u : (InfiniteAdeleRing F)ˣ` to `P (diagUnits F a)`. Establish `hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing F)ˣ` using `GlobalTheory.RayFromArtin.mem_connectedComponentOfOne_of_pos a ha`. Establish `hinf : ψ (ι u) = 1` using `hconn _ ⟨u, hu, rfl⟩`. Set `av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ` to `fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a`.

Set `z : Ideles F` to `diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹`. Establish `hPι : P (ι u) = u` using `Units.ext rfl`. Establish `hPl : ∀ v, P (locUnit F v a) = 1` using `fun v => Units.ext rfl`. Establish `hz1 : (z : AdeleRing (𝓞 F) F).1 = 1`. Establish `h : P z = 1`.

Simplify using `only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]`. Conclude with `mul_inv_cancel u`. Conclude with `congrArg Units.val h`. Establish `hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v` using `fun v => Units.ext rfl`. Establish `hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1` using `fun v => Units.ext rfl`.

Establish `hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1`. Introduce `v w`. Apply `Units.ext` to reduce the goal to its premises. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `GlobalTheory.Mem.LocTriv.ev_local_self w _`. Conclude with `GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _`. Establish `hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1`. Introduce `v`. Establish `e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹`.

Simplify using `only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]`. Rewrite using `[e, Finset.prod_ite_eq' T v]`. Use `split_ifs with hv`. Rewrite using `[mul_inv_cancel, map_one, map_one]`. Rewrite using `[inv_one, mul_one]`.

Conclude with `hT v hv`. Establish `hz` using `GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl`. Simplify using `only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz`. Conclude with `inv_eq_one.mp hz`.
-/
theorem prod_locUnit_eq_one_of_pos : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  intro F _ _ B _ ψ hker hd hconn a ha T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  have hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing F)ˣ :=
    GlobalTheory.RayFromArtin.mem_connectedComponentOfOne_of_pos a ha
  have hinf : ψ (ι u) = 1 := hconn _ ⟨u, hu, rfl⟩
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

end GlobalTheory.ProdLocUnitPos
