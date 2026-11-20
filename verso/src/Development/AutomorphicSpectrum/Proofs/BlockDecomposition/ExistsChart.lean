import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ChartP

open GlobalTheory.CompanionTheory.ChartAlg

section Lift

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} {T : Fin d → Γ(X, V)}
  (𝓛 : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ)

def barI : R ⧸ I →+* 𝓛.D ⧸ I.map 𝓛.i := Ideal.quotientMap (I.map 𝓛.i) 𝓛.i Ideal.le_comap_map

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem barI_mk (r : R) : barI 𝓛 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (𝓛.i r) := rfl

/- English proof (translation)
Use `RingHom.ext fun o => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `Ideal.Quotient.mk_surjective (κ o)`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx, barI_mk]`.
-/
theorem j_strV : 𝓛.j.comp (strV q V) = (barI 𝓛).comp κ := by
  refine RingHom.ext fun o => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
  rw [RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx, barI_mk]

def ptL (hV : IsAffineOpen V) : PtOver X q κ (𝓛.D ⧸ I.map 𝓛.i) :=
  ⟨(barI 𝓛, Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec), by
    change (Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec) ≫ q = Spec.map (CommRingCat.ofHom ((barI 𝓛).comp κ))
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← j_strV]
    rfl⟩

/- English proof (translation)
Set `e' : Γ(X, V) →+* B` to `GlobalTheory.Cris.evalAt y'.1.2 V hy'`. Set `ψ' : R ⧸ I →+* B` to `y'.1.1`. Establish `hbase : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x`. Introduce `o x hx`. Rewrite using `[RingHom.comp_apply, hx]`.

Conclude with `evalAt_base q κ ψ' y'.1.2 y'.2 hy' o`. Take `⟨f, ⟨hf1, hf2⟩, hfu⟩` from `𝓛.univ B (ψ'.comp (Ideal.Quotient.mk I)) e' (fun x hx => by`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]) hbase`. Establish `hk : ∀ a ∈ I.map 𝓛.i, f a = 0`. Establish `hle : I.map 𝓛.i ≤ RingHom.ker f` using `Ideal.map_le_iff_le_comap.2 fun x hx => by`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]`. Conclude with `fun a ha => hle ha`. Set `φ : 𝓛.D ⧸ I.map 𝓛.i →+* B` to `Ideal.Quotient.lift _ f hk`. Establish `hφ : ∀ z, φ (Ideal.Quotient.mk _ z) = f z` using `fun z => rfl`. Establish `hφj : φ.comp 𝓛.j = e'`.

Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `Ideal.Quotient.mk_surjective (𝓛.j r)`. Rewrite using `[RingHom.comp_apply, ← hz, hφ]`. Conclude with `hf2 r z hz`. Establish `hφψ : φ.comp (barI 𝓛) = ψ'`.

Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (barI 𝓛 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)`. Rewrite using `[barI_mk, hφ]`. Conclude with `RingHom.congr_fun hf1 r`.

Use `⟨φ, ?_, ?_⟩` and prove the remaining obligations. Use `Subtype.ext (Prod.ext hφψ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]`. Conclude with `eq_specMap hV y'.1.2 hy'`.

Introduce `φ' h'`. Establish `h1 : φ'.comp (barI 𝓛) = ψ'` using `congrArg (fun z => z.1.1) h'`. Establish `h2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2` using `congrArg (fun z => z.1.2) h'`. Establish `h3 : e' = φ'.comp 𝓛.j`. Use `evalAt_specMap hV (φ'.comp 𝓛.j) y'.1.2 ?_ hy'` and prove the remaining obligations.

Rewrite using `[← h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `h4 : φ'.comp (Ideal.Quotient.mk _) = f`. Use `hfu _ ⟨?_, fun r z hz => ?_⟩` and prove the remaining obligations. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Conclude with `RingHom.congr_fun h1 (Ideal.Quotient.mk I r)`.

Rewrite using `[h3]`. Conclude with `congrArg φ' hz`. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Conclude with `h4`.
-/
theorem rep_lift (hV : IsAffineOpen V) (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : 𝓛.D ⧸ I.map 𝓛.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) (ptL 𝓛 hV) = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hbase : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := 𝓛.univ B (ψ'.comp (Ideal.Quotient.mk I)) e'
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]) hbase
  have hk : ∀ a ∈ I.map 𝓛.i, f a = 0 := by
    have hle : I.map 𝓛.i ≤ RingHom.ker f := Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact fun a ha => hle ha
  let φ : 𝓛.D ⧸ I.map 𝓛.i →+* B := Ideal.Quotient.lift _ f hk
  have hφ : ∀ z, φ (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have hφj : φ.comp 𝓛.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
    rw [RingHom.comp_apply, ← hz, hφ]
    exact hf2 r z hz
  have hφψ : φ.comp (barI 𝓛) = ψ' := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r => ?_
    change φ (barI 𝓛 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
    rw [barI_mk, hφ]
    exact RingHom.congr_fun hf1 r
  refine ⟨φ, ?_, ?_⟩
  · refine Subtype.ext (Prod.ext hφψ ?_)
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
    exact eq_specMap hV y'.1.2 hy'
  · intro φ' h'
    have h1 : φ'.comp (barI 𝓛) = ψ' := congrArg (fun z => z.1.1) h'
    have h2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2 :=
      congrArg (fun z => z.1.2) h'
    have h3 : e' = φ'.comp 𝓛.j := by
      refine evalAt_specMap hV (φ'.comp 𝓛.j) y'.1.2 ?_ hy'
      rw [← h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h4 : φ'.comp (Ideal.Quotient.mk _) = f := by
      refine hfu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        exact RingHom.congr_fun h1 (Ideal.Quotient.mk I r)
      · rw [h3]
        exact congrArg φ' hz
    apply Ideal.Quotient.ringHom_ext
    exact h4

variable (γ : DividedPowers I) (p : ℕ) (δ : DividedPowers (I.map 𝓛.i)) (hδ : IsDPMorphism γ δ 𝓛.i)
  (hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i))) (hV : IsAffineOpen V)

def thL : Thick (nlFun γ p X q κ) := mkT 𝓛.D 𝓛.i (I.map 𝓛.i) δ hadm hδ (ptL 𝓛 hV) (fun _ => rfl)

/- English proof (translation)
The claim follows from `top_le_specMap hV 𝓛.j`.
-/
theorem thL_inU : InU V (thL 𝓛 γ p δ hδ hadm hV) := top_le_specMap hV 𝓛.j

/- English proof (translation)
The claim follows from `evalAt_specMap hV 𝓛.j _ rfl _`.
-/
theorem ev_thL : ev (thL 𝓛 γ p δ hδ hadm hV) (thL_inU 𝓛 γ p δ hδ hadm hV) = 𝓛.j :=
  evalAt_specMap hV 𝓛.j _ rfl _

def chartL (het : (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t : MvPolynomial (Fin d) R →+* 𝓛.D).Etale) : Chart γ p q κ V d where
  D := thL 𝓛 γ p δ hδ hadm hV
  t := 𝓛.t
  etale := het
  J_eq := rfl
  inV := thL_inU 𝓛 γ p δ hδ hadm hV
  rep := rep_lift 𝓛 hV

end Lift

/- English proof (translation)
Introduce `O R _ _ I γ p hp hn X q κ V d c`. Take `⟨𝓛⟩` from `GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale`. Establish `hflat : 𝓛.i.Flat` using `(GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map 𝓛.i), IsDPMorphism γ δ 𝓛.i := by`. Use `letI := 𝓛.i.toAlgebra`.

Use `haveI : Module.Flat R 𝓛.D := hflat`. Conclude with `GlobalTheory.CompanionTheory.JLiftDP.dpFlat R 𝓛.D I γ`. Establish `hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i))` using `⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩`. Conclude with `⟨chartL 𝓛 γ p δ hδ hadm c.affine 𝓛.et, hflat, fun i => (RingHom.congr_fun (ev_thL 𝓛 γ p δ hδ hadm c.affine) (c.t i)).trans (𝓛.hT i)⟩`.
-/
theorem exists_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨𝓛⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hflat : 𝓛.i.Flat := (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map 𝓛.i), IsDPMorphism γ δ 𝓛.i := by
    letI := 𝓛.i.toAlgebra
    haveI : Module.Flat R 𝓛.D := hflat
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R 𝓛.D I γ
  have hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i)) :=
    ⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩
  exact ⟨chartL 𝓛 γ p δ hδ hadm c.affine 𝓛.et, hflat, fun i =>
    (RingHom.congr_fun (ev_thL 𝓛 γ p δ hδ hadm c.affine) (c.t i)).trans (𝓛.hT i)⟩

end GlobalTheory.CompanionTheory.ChartP
