import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨b', rfl⟩` from `Submodule.Quotient.mk_surjective _ c'`. Establish `h1` using `congrArg (· ≫ GlobalTheory.EqvAct.pullψ TF Z φ) h`. Simplify using `only [Category.assoc, etaSecL_ψ] at h1`. Use `set x' := x ≫ i₀ TF.Y Z with hx'`.

Establish `hsec : ∀ a : Dw.La, (TF.Y.oF.eta a).left ≫ TF.Y.oF.t.G.hom = (𝟙_ (Over _)).hom` using `fun a => Over.w (TF.Y.oF.eta a)`. Establish `h2 : x' ≫ (TF.Y.oF.eta b).left = x' ≫ (TF.Y.oF.eta b').left`. Use `TF.Y.m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations. Simplify `h1` using `[hx', Category.assoc]`. Simplify using `only [hx', Category.assoc, hsec]`.

Set `T : Over (Xo.XF c)` to `Over.mk x'`. Establish `h3 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b = CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b'`. Use `ext`. Simplify using `only [Over.comp_left]`. Conclude with `h2`.

Choose the witnesses or unpack the hypotheses as in `⟨β, hβ⟩ : ∃ β : KA l →+* Ω, x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β :=`. Set `f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (KA l))` to `x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s`. Use the proof step `⟨(Spec.preimage f).hom, by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, f]⟩`. Take `⟨-, I, -, -, hI⟩` from `TF.Y.oF.geom Ω x' β hβ`. Take `⟨d, hd⟩ : ∃ d : Dw.La, d = b - b'` from `⟨_, rfl⟩`.

Establish `hmul : TF.Y.oF.eta b = TF.Y.oF.eta b' * TF.Y.oF.eta d`. Rewrite using `[← TF.Y.oF.eta_add, hd, add_sub_cancel]`. Establish `hd1 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta d = 1`. Rewrite `h3` using `[hmul, MonObj.comp_mul]`. Conclude with `mul_left_cancel (h3.trans (mul_one _).symm)`.

Establish `h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.coprime]`. Conclude with `Submodule.mem_top`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 h1top`. Establish `hud : u • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)` using `Submodule.smul_mem_smul hu Submodule.mem_top`.

Establish `hvd : v • d ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La)` using `Submodule.smul_mem_smul hv Submodule.mem_top`. Establish `hsplit : d = u • d + v • d` using `by rw [← add_smul, huv, one_smul]`. Establish `hev : TF.Y.oF.eta d = TF.Y.oF.eta (v • d)` using `by conv_lhs => rw [hsplit]`. Rewrite using `[TF.Y.oF.eta_add, TF.Y.oF.eta_ker _ hud, one_mul]`. Establish `hI1 : I.ev l.M (v • d) = 1` using `(hI _ hvd).symm.trans (by rw [← hev]; exact hd1)`.

Take `⟨e, he⟩` from `(I.ker l.M (by have := l.three_le; omega) (v • d)).1 hI1`. Establish `hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb`. Establish `h0` using `Ideal.mem_span_singleton_self ((l.M : ℕ) : 𝓞 E)`. Rewrite `h0` using `[← l.prod]`. Conclude with `(Ideal.mul_le_inf.trans inf_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h0`.

Establish `hvd' : v • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)`. Rewrite using `[he, ← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hM Submodule.mem_top`. Rewrite using `[Submodule.Quotient.eq, ← hd, hsplit]`. Conclude with `Submodule.add_mem _ hud hvd'`.
-/
theorem etaSecL_injective_at (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (c c' : LevelMod Dw l)
    (h : x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c') : c = c' := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ c'

  have h1 := congrArg (· ≫ GlobalTheory.EqvAct.pullψ TF Z φ) h
  simp only [Category.assoc, etaSecL_ψ] at h1
  set x' := x ≫ i₀ TF.Y Z with hx'
  have hsec : ∀ a : Dw.La, (TF.Y.oF.eta a).left ≫ TF.Y.oF.t.G.hom = (𝟙_ (Over _)).hom := fun a =>
    Over.w (TF.Y.oF.eta a)
  have h2 : x' ≫ (TF.Y.oF.eta b).left = x' ≫ (TF.Y.oF.eta b').left := by
    refine TF.Y.m.cart.1.hom_ext ?_ ?_
    · simpa [hx', Category.assoc] using h1
    · simp only [hx', Category.assoc, hsec]
  let T : Over (Xo.XF c) := Over.mk x'
  have h3 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b = CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b' := by
    ext
    simp only [Over.comp_left]
    exact h2

  obtain ⟨β, hβ⟩ : ∃ β : KA l →+* Ω, x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β :=
    let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (KA l)) :=
      x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
    ⟨(Spec.preimage f).hom, by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, f]⟩
  obtain ⟨-, I, -, -, hI⟩ := TF.Y.oF.geom Ω x' β hβ
  obtain ⟨d, hd⟩ : ∃ d : Dw.La, d = b - b' := ⟨_, rfl⟩
  have hmul : TF.Y.oF.eta b = TF.Y.oF.eta b' * TF.Y.oF.eta d := by
    rw [← TF.Y.oF.eta_add, hd, add_sub_cancel]
  have hd1 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta d = 1 := by
    rw [hmul, MonObj.comp_mul] at h3
    exact mul_left_cancel (h3.trans (mul_one _).symm)
  have h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1top
  have hud : u • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hu Submodule.mem_top
  have hvd : v • d ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hsplit : d = u • d + v • d := by rw [← add_smul, huv, one_smul]
  have hev : TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := by
    conv_lhs => rw [hsplit]
    rw [TF.Y.oF.eta_add, TF.Y.oF.eta_ker _ hud, one_mul]
  have hI1 : I.ev l.M (v • d) = 1 := (hI _ hvd).symm.trans (by rw [← hev]; exact hd1)
  obtain ⟨e, he⟩ := (I.ker l.M (by have := l.three_le; omega) (v • d)).1 hI1
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h0 := Ideal.mem_span_singleton_self ((l.M : ℕ) : 𝓞 E)
    rw [← l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left :
      l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h0
  have hvd' : v • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [he, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  rw [Submodule.Quotient.eq, ← hd, hsplit]
  exact Submodule.add_mem _ hud hvd'

end GlobalTheory.TorsSpec
