import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExistsPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

/- English proof (translation)
Establish `h` using `y.commutes a`. Simplify `h` using `[MvPowerSeries.algebraMap_apply]`.
-/
private theorem algHom_mvPowerSeries_C_eq_algebraMap {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {σ : Type}
    (y : MvPowerSeries σ A →ₐ[A] K) (a : A) : y (MvPowerSeries.C a) = algebraMap A K a := by
  have h := y.commutes a
  simpa [MvPowerSeries.algebraMap_apply] using h

/- English proof (translation)
Use `haveI hA : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin D) R) := UpperTheory.V.Alg.co_mvps R R (Fin D)`. Use `haveI hB : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin (D + 1)) R) := UpperTheory.V.Alg.co_mvps R R (Fin (D + 1))`. Use `haveI hP : UpperTheory.V.Alg.IsCO R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) := UpperTheory.V.Alg.co_mvps R (MvPowerSeries (Fin D) R) Unit`. Establish `nX : ∀ (τ : Type) (s : τ), MvPowerSeries.X s ∈ IsLocalRing.maximalIdeal (MvPowerSeries τ R)`. Introduce `τ s`.

Rewrite using `[IsLocalRing.mem_maximalIdeal]`. Introduce `h`. Rewrite `h` using `[MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]`. Conclude with `not_isUnit_zero h`. Establish `nX' : (MvPowerSeries.X () : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _`.

Rewrite using `[IsLocalRing.mem_maximalIdeal]`. Introduce `h`. Rewrite `h` using `[MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]`. Conclude with `not_isUnit_zero h`. Establish `hmem : ∀ s : Fin (D + 1), (Fin.lastCases (MvPowerSeries.X ()) (fun i => MvPowerSeries.C (MvPowerSeries.X i)) s : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _`.

Introduce `s`. Use `Fin.lastCases ?_ (fun i => ?_) s` and prove the remaining obligations. Rewrite using `[Fin.lastCases_last]`. Conclude with `nX'`. Rewrite using `[Fin.lastCases_castSucc, IsLocalRing.mem_maximalIdeal]`.

Introduce `h`. Rewrite `h` using `[MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (nX (Fin D) i) h`. Take `⟨S, ⟨hSC, hSX⟩, -⟩` from `UpperTheory.V.Alg.co_ev R R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) (Fin (D + 1)) (Algebra.ofId R _) _ hmem`. Take `⟨ι, ⟨hιC, hιX⟩, -⟩` from `UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin D) (Algebra.ofId R _) (fun i => MvPowerSeries.X i.castSucc) (fun i => nX _ _)`.

Take `⟨T, ⟨hTC, hTX⟩, -⟩` from `UpperTheory.V.Alg.co_ev R (MvPowerSeries (Fin D) R) (MvPowerSeries (Fin (D + 1)) R) Unit ι (fun _ => MvPowerSeries.X (Fin.last D)) (fun _ => nX _ _)`. Take `⟨F, -, hF⟩` from `UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin (D + 1)) (Algebra.ofId R _) MvPowerSeries.X (fun s => nX _ s)`. Establish `hTS : T.comp S = AlgHom.id R _`. Establish `e1` using `hF (T.comp S) ⟨fun x => ?_, fun s => ?_⟩`. Establish `e2` using `hF (AlgHom.id R _) ⟨fun x => ?_, fun s => rfl⟩`.

Rewrite using `[e1, e2]`. Simplify using `[Algebra.ofId_apply, MvPowerSeries.algebraMap_apply]`. Rewrite using `[AlgHom.comp_apply, hSC, Algebra.ofId_apply, AlgHom.commutes, Algebra.ofId_apply]`. Use `Fin.lastCases ?_ (fun i => ?_) s` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, hSX, Fin.lastCases_last, hTX]`.

Rewrite using `[AlgHom.comp_apply, hSX, Fin.lastCases_castSucc, hTC, hιX]`. Use `⟨S.toRingHom, fun x y h => ?_, fun a => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h' : T (S x) = T (S y)` using `congrArg T h`. Simplify `h'` using `[← AlgHom.comp_apply, hTS]`. Use `hSC a` as an intermediate fact.

Simplify using `only [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this`. Conclude with `this`. Conclude with `(hSX (Fin.last D)).trans (by rw [Fin.lastCases_last]; rfl)`. Conclude with `(hSX i.castSucc).trans (by rw [Fin.lastCases_castSucc]; rfl)`.
-/
private theorem exists_injective_mvPowerSeries_last_to_powerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : ℕ) :
    ∃ S : MvPowerSeries (Fin (D + 1)) R →+* PowerSeries (MvPowerSeries (Fin D) R),
      Function.Injective S ∧
      (∀ a : R, S (MvPowerSeries.C a) = PowerSeries.C (MvPowerSeries.C a)) ∧
      S (MvPowerSeries.X (Fin.last D)) = PowerSeries.X ∧
      ∀ i : Fin D, S (MvPowerSeries.X i.castSucc) = PowerSeries.C (MvPowerSeries.X i) := by
  haveI hA : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin D) R) := UpperTheory.V.Alg.co_mvps R R (Fin D)
  haveI hB : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin (D + 1)) R) :=
    UpperTheory.V.Alg.co_mvps R R (Fin (D + 1))
  haveI hP : UpperTheory.V.Alg.IsCO R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) :=
    UpperTheory.V.Alg.co_mvps R (MvPowerSeries (Fin D) R) Unit
  have nX : ∀ (τ : Type) (s : τ), MvPowerSeries.X s ∈
      IsLocalRing.maximalIdeal (MvPowerSeries τ R) := by
    intro τ s
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have nX' : (MvPowerSeries.X () : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have hmem : ∀ s : Fin (D + 1), (Fin.lastCases (MvPowerSeries.X ())
      (fun i => MvPowerSeries.C (MvPowerSeries.X i)) s :
        MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _ := by
    intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [Fin.lastCases_last]
      exact nX'
    · rw [Fin.lastCases_castSucc, IsLocalRing.mem_maximalIdeal]
      intro h
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h
      exact (IsLocalRing.mem_maximalIdeal _).1 (nX (Fin D) i) h
  obtain ⟨S, ⟨hSC, hSX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries Unit (MvPowerSeries (Fin D) R))
    (Fin (D + 1)) (Algebra.ofId R _) _ hmem
  obtain ⟨ι, ⟨hιC, hιX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin D)
    (Algebra.ofId R _) (fun i => MvPowerSeries.X i.castSucc) (fun i => nX _ _)
  obtain ⟨T, ⟨hTC, hTX⟩, -⟩ := UpperTheory.V.Alg.co_ev R (MvPowerSeries (Fin D) R)
    (MvPowerSeries (Fin (D + 1)) R) Unit ι (fun _ => MvPowerSeries.X (Fin.last D)) (fun _ => nX _ _)
  obtain ⟨F, -, hF⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin (D + 1))
    (Algebra.ofId R _) MvPowerSeries.X (fun s => nX _ s)
  have hTS : T.comp S = AlgHom.id R _ := by
    have e1 := hF (T.comp S) ⟨fun x => ?_, fun s => ?_⟩
    · have e2 := hF (AlgHom.id R _) ⟨fun x => ?_, fun s => rfl⟩
      · rw [e1, e2]
      · simp [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply]
    · rw [AlgHom.comp_apply, hSC, Algebra.ofId_apply, AlgHom.commutes, Algebra.ofId_apply]
    · refine Fin.lastCases ?_ (fun i => ?_) s
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_last, hTX]
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_castSucc, hTC, hιX]
  refine ⟨S.toRingHom, fun x y h => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have h' : T (S x) = T (S y) := congrArg T h
    simpa [← AlgHom.comp_apply, hTS] using h'
  · have := hSC a
    simp only [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    exact this
  · exact (hSX (Fin.last D)).trans (by rw [Fin.lastCases_last]; rfl)
  · exact (hSX i.castSucc).trans (by rw [Fin.lastCases_castSucc]; rfl)

/- English proof (translation)
Introduce `D`. Proceed by induction on `D with`. Consider the case `zero`. Introduce `c Z hZ hn f hf`. Take `⟨c', y, -, hy, -⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c (Fin 0) (fun i => i.elim0) (fun i => i.elim0)`.

Establish `h1 : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f)`. Use extensionality with `n`. Establish `hn0 : n = 0` using `Subsingleton.elim _ _`. Substitute `hn0` using the available equality. Simplify using the standard rewrite rules.

Establish `h2` using `hf c' y hy (fun i => i.elim0)`. Rewrite `h2` using `[h1, algHom_mvPowerSeries_C_eq_algebraMap]`. Establish `h3 : MvPowerSeries.constantCoeff f = 0` using `Subtype.ext h2`. Rewrite using `[h1, h3, map_zero]`. Consider the case `succ D ih`.

Introduce `c Z hZ hn f hf`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨hcpl, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Take `⟨S, hSi, hSC, hSl, hSc⟩` from `exists_injective_mvPowerSeries_last_to_powerSeries c.O D`.

Apply `hSi` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `PowerSeries.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Apply `ih c (fun i => Z i.castSucc) (fun i => hZ _) (fun i => hn _)` to reduce the goal to its premises.

Introduce `c'' y'' hint hX`. Use `haveI := c''.dvr`. Use `haveI := c''.fin`. Take `⟨hcpl'', -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c''.O`. Set `ycr : MvPowerSeries (Fin D) c.O →+* c''.O` to `y''.toRingHom.codRestrict c''.O hint`.

Establish `hycr : ∀ x, ((ycr x : c''.O) : PadicAlgCl l) = y'' x` using `fun x => rfl`. Establish `hg : PowerSeries.map ycr (S f) = 0`. Use `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar c''.O (PadicAlgCl l) c''.O.val.toRingHom Subtype.val_injective _ (Z (Fin.last D)) (hZ _) ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨c3, ev, -, hev, hevX⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c'' Unit (fun _ => z) (fun _ => hn _ z hz)`.

Establish `hevC : ∀ b : c''.O, ev (PowerSeries.C b) = b` using `fun b => algHom_mvPowerSeries_C_eq_algebraMap ev b`. Set `G : MvPowerSeries (Fin (D + 1)) c.O →ₐ[c.O] PadicAlgCl l` to `{ toRingHom := ev.toRingHom.comp ((PowerSeries.map ycr).comp S) commutes' := by`. Introduce `a`. Use `show ev (PowerSeries.map ycr (S (algebraMap c.O _ a))) = _`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hSC, PowerSeries.map_C, hevC, hycr, algHom_mvPowerSeries_C_eq_algebraMap] }`.

Establish `hG : G f = 0`. Use `hf c3 G (fun g => hev _) (fun i => ?_)` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Use `show ev (PowerSeries.map ycr (S (MvPowerSeries.X (Fin.last D)))) ∈ _`. Rewrite using `[hSl, PowerSeries.map_X]`.

Conclude with `(hevX ()).symm ▸ hz`. Use `show ev (PowerSeries.map ycr (S (MvPowerSeries.X j.castSucc))) ∈ _`. Rewrite using `[hSc, PowerSeries.map_C, hevC, hycr]`. Conclude with `hX j`. Conclude with `⟨ev.toRingHom, fun a => hevC a, hevX (), hG⟩`.

Establish `h4` using `congrArg (PowerSeries.coeff n) hg`. Rewrite `h4` using `[PowerSeries.coeff_map, map_zero]`. Establish `h5` using `congrArg Subtype.val h4`. Rewrite `h5` using `[hycr]`. Conclude with `h5`.
-/
private theorem eq_zero_of_eval_eq_zero_on_infinite_unit_ball (l : ℕ) [Fact l.Prime] : ∀ (D : ℕ) (c : Coef l)
    (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) →
    ∀ f : MvPowerSeries (Fin D) c.O,
      (∀ (c' : Coef l) (y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l),
        (∀ g, y g ∈ c'.O) → (∀ i, y (MvPowerSeries.X i) ∈ Z i) → y f = 0) → f = 0 := by
  intro D
  induction D with
  | zero =>
    intro c Z hZ hn f hf
    obtain ⟨c', y, -, hy, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c (Fin 0) (fun i => i.elim0)
      (fun i => i.elim0)
    have h1 : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      ext n
      have hn0 : n = 0 := Subsingleton.elim _ _
      subst hn0
      simp
    have h2 := hf c' y hy (fun i => i.elim0)
    rw [h1, algHom_mvPowerSeries_C_eq_algebraMap] at h2
    have h3 : MvPowerSeries.constantCoeff f = 0 := Subtype.ext h2
    rw [h1, h3, map_zero]
  | succ D ih =>
    intro c Z hZ hn f hf
    haveI := c.dvr
    haveI := c.fin
    obtain ⟨hcpl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    obtain ⟨S, hSi, hSC, hSl, hSc⟩ := exists_injective_mvPowerSeries_last_to_powerSeries c.O D
    apply hSi
    rw [map_zero]
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    apply ih c (fun i => Z i.castSucc) (fun i => hZ _) (fun i => hn _)
    intro c'' y'' hint hX
    haveI := c''.dvr
    haveI := c''.fin
    obtain ⟨hcpl'', -⟩ := UpperTheory.V.abelian₂.dvr_finite l c''.O
    let ycr : MvPowerSeries (Fin D) c.O →+* c''.O := y''.toRingHom.codRestrict c''.O hint
    have hycr : ∀ x, ((ycr x : c''.O) : PadicAlgCl l) = y'' x := fun x => rfl
    have hg : PowerSeries.map ycr (S f) = 0 := by
      refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar c''.O (PadicAlgCl l) c''.O.val.toRingHom
        Subtype.val_injective _ (Z (Fin.last D)) (hZ _) ?_
      intro z hz
      obtain ⟨c3, ev, -, hev, hevX⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c'' Unit (fun _ => z)
        (fun _ => hn _ z hz)
      have hevC : ∀ b : c''.O, ev (PowerSeries.C b) = b := fun b => algHom_mvPowerSeries_C_eq_algebraMap ev b
      let G : MvPowerSeries (Fin (D + 1)) c.O →ₐ[c.O] PadicAlgCl l :=
        { toRingHom := ev.toRingHom.comp ((PowerSeries.map ycr).comp S)
          commutes' := by
            intro a
            show ev (PowerSeries.map ycr (S (algebraMap c.O _ a))) = _
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hSC,
              PowerSeries.map_C, hevC, hycr, algHom_mvPowerSeries_C_eq_algebraMap] }
      have hG : G f = 0 := by
        refine hf c3 G (fun g => hev _) (fun i => ?_)
        refine Fin.lastCases ?_ (fun j => ?_) i
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X (Fin.last D)))) ∈ _
          rw [hSl, PowerSeries.map_X]
          exact (hevX ()).symm ▸ hz
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X j.castSucc))) ∈ _
          rw [hSc, PowerSeries.map_C, hevC, hycr]
          exact hX j
      exact ⟨ev.toRingHom, fun a => hevC a, hevX (), hG⟩
    have h4 := congrArg (PowerSeries.coeff n) hg
    rw [PowerSeries.coeff_map, map_zero] at h4
    have h5 := congrArg Subtype.val h4
    rw [hycr] at h5
    exact h5

/- English proof (translation)
Introduce `l _ c D Z hZ hn f hf`. Conclude with `eq_zero_of_eval_eq_zero_on_infinite_unit_ball l D c Z hZ hn f (fun c' y _ hX => hf y hX)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.denseBox :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (D : ℕ) (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) → Sep {y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l | ∀ i, y (MvPowerSeries.X i) ∈ Z i} := by
  intro l _ c D Z hZ hn f hf
  exact eq_zero_of_eval_eq_zero_on_infinite_unit_ball l D c Z hZ hn f (fun c' y _ hX => hf y hX)
