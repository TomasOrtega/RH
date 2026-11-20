import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrThick

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

/- English proof (translation)
Introduce `l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g hep hD`. Use `letI : CommRing g.AA := g.ring`. Use `letI : Algebra Bh g.AA := g.alg`. Use `letI : Ring H.E := H.ring`. Use `letI : Algebra Bh H.E := H.alg`.

Use `letI : Algebra B H.E := H.algB`. Use `haveI : IsScalarTower B Bh H.E := H.tower`. Use `letI algB : Algebra B g.AA := ((algebraMap Bh g.AA).comp (algebraMap B Bh)).toAlgebra`. Use `haveI tower : IsScalarTower B Bh g.AA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA` to `((g.φ.toRingHom.comp H.ι.toRingHom).toMonoidHom).comp (MonoidAlgebra.of Bh G.G₀)`.

Establish `hvr : ∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1))` using `fun _ => rfl`. Establish `key : ∀ w, GDet.repAlg vr g.AA (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA) w) = g.φ (H.ι (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh) w))`. Introduce `w`. Establish `hext : ((GDet.repAlg vr g.AA).toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA))) = (g.φ.toRingHom.comp (H.ι.toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh))))`. Apply `MonoidAlgebra.ringHom_ext` to reduce the goal to its premises.

Introduce `b`. Establish `hs : MonoidAlgebra.single (1 : G.G₀) (algebraMap B Bh b) = (algebraMap B Bh b) • (1 : MonoidAlgebra Bh G.G₀)`. Rewrite using `[MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]`. Simplify using `only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one, hs, map_smul]`. Conclude with `algebraMap_smul g.AA ((algebraMap B Bh) b) (1 : Matrix (Fin n) (Fin n) g.AA)`.

Introduce `a`. Simplify using `only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one]`. Rewrite using `[one_smul]`. Use `show (algebraMap g.AA g.AA).mapMatrix (vr a) = _`. Rewrite using `[Algebra.algebraMap_self, RingHom.mapMatrix_id]`.

Both sides reduce to the same expression. Conclude with `congrArg (fun f => f w) hext`. Set `f` to `g.φ.toLinearMap.restrictScalars B`. Use `⟨{ AA := g.AA` and prove the remaining obligations. Use `ring := g.ring`.

Use `alg := g.alg`. Use `algB := algB`. Use `tower := tower`. Use `fin := g.fin`. Use `inj := g.inj`.

Use `N := g.N`. Use `compl := g.compl`. Use `mul_mem := g.mul_mem`. Use `typeI := g.typeI`. Use `vr := vr`.

Use `span := ?_`. Use `det := gr_det H g hep hD vr hvr`. Use `form := ?_`. Use `red := ?_`. Use `kills := ?_`.

Use `thick := gr_thick H g`. Use `P := Submodule.map f H.P`. Use `ker_le_span_sub_sup_map := H.ker_le_span_sub_sup_map.map f`. Use `vr_mem := fun γ => Submodule.mem_map_of_mem (H.mem γ)`. Use `cont := ?_ }⟩`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨γ, rfl⟩`. Conclude with `(g.range _).mp ⟨_, rfl⟩`. Introduce `Y hY`.

Take `⟨y, rfl⟩` from `(g.range Y).mpr hY`. Take `⟨z, rfl⟩` from `H.surj y`. Use `clear hY`. Proceed by induction on `z using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `single γ c`. Establish `hc : (MonoidAlgebra.single γ c : MonoidAlgebra Bh G.G₀) = c • MonoidAlgebra.single γ 1`.

Rewrite using `[MonoidAlgebra.smul_single', mul_one]`. Rewrite using `[hc, map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ⟨γ, rfl⟩)`. Introduce `γ`. Establish `h1 : (vr γ)ᵀ = (algebraMap B Bh ↑(e γ ^ (1 - (n : ℤ)))) • vr (G.frame.conj γ)⁻¹`.

Rewrite using `[hvr, ← g.st, H.st, map_smul]`. Both sides reduce to the same expression. Rewrite using `[h1, smul_mul_assoc, ← map_mul, inv_mul_cancel, map_one, ← algebraMap_smul g.AA]`. Both sides reduce to the same expression. Introduce `γ i j b hb`.

Use `g.red (H.ι (MonoidAlgebra.single γ 1)) i j b hb` as an intermediate fact. Rewrite `this` using `[H.r_ι, Matrix.map_apply]`. Conclude with `this`. Introduce `z hz`. Rewrite using `[key, (H.ker _).mpr (TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩), map_zero]`.

Introduce `j`. Take `⟨V, hV⟩` from `H.cont j`. Use `⟨V, fun γ v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.map_smul'']`. Establish `hm` using `Submodule.mem_map_of_mem (f := f) (hV γ v hv)`.

Rewrite `hm` using `[map_sub]`. Conclude with `hm`.
-/
theorem UpperTheory.V.Pa.urep_of :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → Nonempty (URep h x D I Bh (algebraMap Bh (FractionRing x.A)) e) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g hep hD
  letI : CommRing g.AA := g.ring
  letI : Algebra Bh g.AA := g.alg
  letI : Ring H.E := H.ring
  letI : Algebra Bh H.E := H.alg
  letI : Algebra B H.E := H.algB
  haveI : IsScalarTower B Bh H.E := H.tower
  letI algB : Algebra B g.AA := ((algebraMap Bh g.AA).comp (algebraMap B Bh)).toAlgebra
  haveI tower : IsScalarTower B Bh g.AA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA :=
    ((g.φ.toRingHom.comp H.ι.toRingHom).toMonoidHom).comp (MonoidAlgebra.of Bh G.G₀)
  have hvr : ∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1)) := fun _ => rfl
  have key : ∀ w, GDet.repAlg vr g.AA (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA) w) =
      g.φ (H.ι (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh) w)) := by
    intro w
    have hext : ((GDet.repAlg vr g.AA).toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA))) =
        (g.φ.toRingHom.comp (H.ι.toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh)))) := by
      apply MonoidAlgebra.ringHom_ext
      · intro b
        have hs : MonoidAlgebra.single (1 : G.G₀) (algebraMap B Bh b) =
            (algebraMap B Bh b) • (1 : MonoidAlgebra Bh G.G₀) := by
          rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one, hs, map_smul]
        exact algebraMap_smul g.AA ((algebraMap B Bh) b) (1 : Matrix (Fin n) (Fin n) g.AA)
      · intro a
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one]
        rw [one_smul]
        show (algebraMap g.AA g.AA).mapMatrix (vr a) = _
        rw [Algebra.algebraMap_self, RingHom.mapMatrix_id]
        rfl
    exact congrArg (fun f => f w) hext
  let f := g.φ.toLinearMap.restrictScalars B
  refine ⟨{
    AA := g.AA
    ring := g.ring
    alg := g.alg
    algB := algB
    tower := tower
    fin := g.fin
    inj := g.inj
    N := g.N
    compl := g.compl
    mul_mem := g.mul_mem
    typeI := g.typeI
    vr := vr
    span := ?_
    det := gr_det H g hep hD vr hvr
    form := ?_
    red := ?_
    kills := ?_
    thick := gr_thick H g
    P := Submodule.map f H.P
    ker_le_span_sub_sup_map := H.ker_le_span_sub_sup_map.map f
    vr_mem := fun γ => Submodule.mem_map_of_mem (H.mem γ)
    cont := ?_ }⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact (g.range _).mp ⟨_, rfl⟩
    · intro Y hY
      obtain ⟨y, rfl⟩ := (g.range Y).mpr hY
      obtain ⟨z, rfl⟩ := H.surj y
      clear hY
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ ha hb
      | single γ c =>
        have hc : (MonoidAlgebra.single γ c : MonoidAlgebra Bh G.G₀) = c • MonoidAlgebra.single γ 1 := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hc, map_smul, map_smul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨γ, rfl⟩)
  · intro γ
    have h1 : (vr γ)ᵀ = (algebraMap B Bh ↑(e γ ^ (1 - (n : ℤ)))) • vr (G.frame.conj γ)⁻¹ := by
      rw [hvr, ← g.st, H.st, map_smul]
      rfl
    rw [h1, smul_mul_assoc, ← map_mul, inv_mul_cancel, map_one, ← algebraMap_smul g.AA]
    rfl
  · intro γ i j b hb
    have := g.red (H.ι (MonoidAlgebra.single γ 1)) i j b hb
    rw [H.r_ι, Matrix.map_apply] at this
    exact this
  · intro z hz
    rw [key, (H.ker _).mpr (TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩), map_zero]
  · intro j
    obtain ⟨V, hV⟩ := H.cont j
    refine ⟨V, fun γ v hv => ?_⟩
    rw [← Submodule.map_smul'']
    have hm := Submodule.mem_map_of_mem (f := f) (hV γ v hv)
    rw [map_sub] at hm
    exact hm
