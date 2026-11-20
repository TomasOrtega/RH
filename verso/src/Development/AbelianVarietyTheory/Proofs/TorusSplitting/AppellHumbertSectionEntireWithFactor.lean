import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

/- English proof (translation)
Introduce `U f`. Establish `h` using `he U f`. Establish `hd : Differentiable ℂ (fun z : W => ((0 : V), z))` using `(differentiable_const _).prodMk differentiable_id`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hs : {b ∈ (Set.univ : Set W) | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : W => ((0 : V), z)) ⁻¹' {b ∈ (Set.univ : Set V) ×ˢ (Set.univ : Set W) | ⊤ ≤ e b.2 ⁻¹ᵁ U}` using `Set.ext fun z => ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩`.

Rewrite using `[hs]`. Conclude with `h.1.preimage hd.continuous`. Conclude with `h.2.comp (f := fun z : W => ((0 : V), z)) hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)`.
-/
theorem isHolTo_snd_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {e : W → (Sp ℂ ⟶ X)}
    (he : IsHolTo ((Set.univ : Set V) ×ˢ (Set.univ : Set W)) (fun bz => e bz.2)) : IsHolTo Set.univ e := by
  intro U f
  have h := he U f
  have hd : Differentiable ℂ (fun z : W => ((0 : V), z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have hs : {b ∈ (Set.univ : Set W) | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : W => ((0 : V), z)) ⁻¹'
        {b ∈ (Set.univ : Set V) ×ˢ (Set.univ : Set W) | ⊤ ≤ e b.2 ⁻¹ᵁ U} :=
      Set.ext fun z => ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    rw [hs]
    exact h.1.preimage hd.continuous
  · exact h.2.comp (f := fun z : W => ((0 : V), z)) hd.differentiableOn
      (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

/- English proof (translation)
Conclude with `isHolTo_snd_slice (e := fun z => (Fu.ex i Pm z).left) (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2`.
-/
theorem isHolTo_ex_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) :
    IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) := by
  exact isHolTo_snd_slice (e := fun z => (Fu.ex i Pm z).left)
    (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF s θ hθ`. Take `⟨-, -, -, hdf, hne, -, -, hfac⟩` from `hF`. Set `pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (Fu.u i Pm))` to `fun z => (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left`. Establish `h1 : ∀ z, pt z ≫ gxFst (Fu.u i Pm) = (Fu.ex i Pm z).left` using `fun z => by`. Establish `: (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ snd _ _).left = (Fu.ex i Pm z).left`.

Rewrite using `[Out.ptSecT, lift_snd]`. Conclude with `this`. Establish `h2 : ∀ z, pt z ≫ gxSnd (Fu.u i Pm) = 𝟙 (Sp ℂ)` using `fun z => by`. Establish `: (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ fst _ _).left = 𝟙 (Sp ℂ)`. Rewrite using `[Out.ptSecT, lift_fst]`.

Both sides reduce to the same expression. Conclude with `this`. Establish `hex` using `isHolTo_ex_of_isPeriod Fu i Pm hP`. Establish `hpt : IsHolTo Set.univ pt`. Use `GlobalTheory.HolFibre.isHolTo_of_isPullback (p := gxSnd (Fu.u i Pm)) (q := gxFst (Fu.u i Pm)) (IsPullback.of_hasPullback (Fu.u i Pm) Xo.univ.t.G.hom) ?_ ?_` and prove the remaining obligations.

Simplify using `only [h2]`. Conclude with `GlobalTheory.HolFibre.isHolTo_const isOpen_univ _`. Simplify using `only [h1]`. Conclude with `hex`. Establish `hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `fun z => by`.

Establish `hm : (Fu.ex i Pm z).left (default : PrimeSpectrum ℂ) ∈ ⨆ j, Xo.univ.t.PP.L.U j`. Rewrite using `[Xo.univ.t.PP.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hm`. Conclude with `⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩`.

Establish `hU : ∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ⊤ ≤ pt z ⁻¹ᵁ (PPx (Fu.u i Pm)).U (fun _ => j)` using `fun j z h y hy => by`. Establish `h3` using `h hy`. Rewrite `h3` using `[← h1]`. Conclude with `Set.mem_iInter.2 fun _ => h3`. Use `⟨fun z₀ => ?_, fun a z => ?_⟩` and prove the remaining obligations.

Take `⟨j, hj⟩` from `hch z₀`. Establish `ho : IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}`. Establish `h0` using `(hex (Xo.univ.t.PP.L.U j) 0).1`. Simplify using `only [Set.mem_univ, true_and] at h0`. Conclude with `h0`.

Establish `hv : DifferentiableOn ℂ (fun z => valAt' (pt z) ((PPx (Fu.u i Pm)).U fun _ => j) (s.f fun _ => j)) {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}` using `(hpt _ (s.f (fun _ => j))).2.mono (fun z hz => ⟨trivial, hU j z hz⟩)`. Establish `hq : DifferentiableOn ℂ θ {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}`. Use `(hv.mul ((hdf j).inv (fun z hz => hne j z hz))).congr fun z hz => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, Pi.inv_apply, hθ j z (pt z) (h1 z) (h2 z) hz, mul_inv_cancel_right₀ (hne j z hz)]`. Conclude with `hq.differentiableAt (ho.mem_nhds hj)`.

Take `⟨j, hj⟩` from `hch z`. Establish `he : Fu.ex i Pm (z + Pm a) = Fu.ex i Pm z`. Rewrite using `[Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm a)).2 ⟨a, rfl⟩, _root_.mul_one]`. Establish `e1` using `hθ j z (pt z) (h1 z) (h2 z) hj`. Establish `e2` using `hθ j (z + Pm a) (pt z) (by rw [he]; exact h1 z) (h2 z) (by rw [he]; exact hj)`.

Establish `e3` using `(hfac a j z).2 hj`. Establish `n2` using `hne j (z + Pm a) (by rw [he]; exact hj)`. Apply `mul_right_cancel₀ n2` to reduce the goal to its premises. Rewrite using `[← e2, e1, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isFnOf_entire_factor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (s : LB.Sec (PPx (Fu.u i Pm))) (θ : (Fin g → ℂ) → ℂ), IsFnOf Fu i Pm fr (Fu.u i Pm) s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Pm a) = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF s θ hθ
  obtain ⟨-, -, -, hdf, hne, -, -, hfac⟩ := hF
  let pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (Fu.u i Pm)) := fun z =>
    (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left
  have h1 : ∀ z, pt z ≫ gxFst (Fu.u i Pm) = (Fu.ex i Pm z).left := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ snd _ _).left = (Fu.ex i Pm z).left := by
      rw [Out.ptSecT, lift_snd]
    exact this
  have h2 : ∀ z, pt z ≫ gxSnd (Fu.u i Pm) = 𝟙 (Sp ℂ) := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ fst _ _).left = 𝟙 (Sp ℂ) := by
      rw [Out.ptSecT, lift_fst]; rfl
    exact this
  have hex := isHolTo_ex_of_isPeriod Fu i Pm hP
  have hpt : IsHolTo Set.univ pt := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (p := gxSnd (Fu.u i Pm)) (q := gxFst (Fu.u i Pm))
      (IsPullback.of_hasPullback (Fu.u i Pm) Xo.univ.t.G.hom) ?_ ?_
    · simp only [h2]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
    · simp only [h1]
      exact hex
  have hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (Fu.ex i Pm z).left (default : PrimeSpectrum ℂ) ∈ ⨆ j, Xo.univ.t.PP.L.U j := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  have hU : ∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ pt z ⁻¹ᵁ (PPx (Fu.u i Pm)).U (fun _ => j) := fun j z h y hy => by
    have h3 := h hy
    rw [← h1] at h3
    exact Set.mem_iInter.2 fun _ => h3
  refine ⟨fun z₀ => ?_, fun a z => ?_⟩
  · obtain ⟨j, hj⟩ := hch z₀
    have ho : IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h0 := (hex (Xo.univ.t.PP.L.U j) 0).1
      simp only [Set.mem_univ, true_and] at h0
      exact h0
    have hv : DifferentiableOn ℂ (fun z => valAt' (pt z) ((PPx (Fu.u i Pm)).U fun _ => j) (s.f fun _ => j))
        {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
      (hpt _ (s.f (fun _ => j))).2.mono (fun z hz => ⟨trivial, hU j z hz⟩)
    have hq : DifferentiableOn ℂ θ {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      refine (hv.mul ((hdf j).inv (fun z hz => hne j z hz))).congr fun z hz => ?_
      rw [Pi.mul_apply, Pi.inv_apply, hθ j z (pt z) (h1 z) (h2 z) hz, mul_inv_cancel_right₀ (hne j z hz)]
    exact hq.differentiableAt (ho.mem_nhds hj)
  · obtain ⟨j, hj⟩ := hch z
    have he : Fu.ex i Pm (z + Pm a) = Fu.ex i Pm z := by
      rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm a)).2 ⟨a, rfl⟩, _root_.mul_one]
    have e1 := hθ j z (pt z) (h1 z) (h2 z) hj
    have e2 := hθ j (z + Pm a) (pt z) (by rw [he]; exact h1 z) (h2 z) (by rw [he]; exact hj)
    have e3 := (hfac a j z).2 hj
    have n2 := hne j (z + Pm a) (by rw [he]; exact hj)
    apply mul_right_cancel₀ n2
    rw [← e2, e1, e3]
    ring

end GlobalTheory.EtaAn
