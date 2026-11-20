import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.BlowArith

/- English proof (translation)
Use `hX.isNoetherianRing` as an intermediate fact. Take `⟨Y, b, hb, hproj, hiso⟩` from `ProjBlowup.exists_blowup p hX.isProjOver J`. Set `V : X.Opens` to `J.support.compl`. Establish `hbV : IsIso (b ∣_ V)` using `hiso V fun _ hx => hx`. Establish `: Nonempty V.toScheme` using `⟨⟨genericPoint X, hJ⟩⟩`.

Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`. Establish `: Nonempty (b ⁻¹ᵁ V).toScheme` using `⟨inv (b ∣_ V) (Classical.arbitrary _)⟩`. Establish `: IsIntegral (b ⁻¹ᵁ V).toScheme` using `isIntegral_of_isOpenImmersion (b ∣_ V)`. Establish `hU : (J.comap b).support.compl = b ⁻¹ᵁ V`. Use extensionality with `y`.

Conclude with `not_congr (ProjBlowup.mem_support_comap J b y)`. Establish `hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι` using `hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1`. Establish `: IsNoetherian Y` using `isNoetherian_of_isProjOver hproj`. Establish `: IsIntegral Y`. Establish `: IsReduced Y` using `IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι`.

Establish `h` using `((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _ (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure`. Rewrite `h` using `[Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range]`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def _).2 h`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`. Establish `hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι` using `(morphismRestrict_ι b V).symm`.

Establish `hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b)` using `by rw [hfac]; infer_instance`. Establish `hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y` using `genericPoint_eq_of_isOpenImmersion _`. Establish `hgen : b (genericPoint Y) = genericPoint X`. Rewrite using `[← hg, ← Scheme.Hom.comp_apply]`. Conclude with `genericPoint_eq_of_isOpenImmersion _`.

Establish `hdeg : b.residueDegree (genericPoint Y) ≠ 0`. Introduce `h0`. Establish `h1` using `CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)`. Rewrite `h1` using `[CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul]`. Conclude with `one_ne_zero h1`.

Establish `hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k))`. Rewrite using `[flat_int_iff_charZero]`. Use `hX.charZero` as an intermediate fact. Establish `: IsDominant b` using `⟨by`. Rewrite using `[DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]`.

Conclude with `closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩`. Use `IsSchemeTheoreticallyDominant.of_isDominant b` as an intermediate fact. Establish `hinj' : Function.Injective b.appTop` using `Scheme.Hom.app_injective b ⊤`. Conclude with `charZero_of_injective_ringHom (f := b.appTop.hom) hinj'`. Conclude with `⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat, DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩`.
-/
theorem exists_isArithVar_effCartier_isIso (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) D ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (ρ ∣_ V) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩

end GlobalTheory.BlowArith

namespace GlobalTheory.ArLieBase

/- English proof (translation)
Introduce `F _ _ G T s S d ι X W q jB πB ρ h n U m A N hU hN hA`. Establish `hX` using `h.1`. Use `hX.isIntegral` as an intermediate fact. Use `hX.isLocallyNoetherian` as an intermediate fact. Establish `hc` using `hX.charZero`.

Use `set p : ℕ := ∏ j, N j with hpdef`. Establish `hp0 : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hN j`. Establish `hpA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical`. Introduce `j`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem N (Finset.mem_univ j)`.

Rewrite using `[hpdef, hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (hA j)`. Take `⟨J, hJp, hJE⟩` from `GlobalTheory.Principalise.exists_idealSheaf_principalises X p n U m A hU hpA`. Establish `hgen : genericPoint X ∈ X.basicOpen (p : Γ(X, ⊤))`. Establish `hne : (p : Γ(X, ⊤)) ≠ 0` using `Nat.cast_ne_zero.2 hp0`.

Establish `hb : X.basicOpen (p : Γ(X, ⊤)) ≠ ⊥` using `fun h0 => hne ((basicOpen_eq_bot_iff _).1 h0)`. Establish `: Nonempty (X.basicOpen (p : Γ(X, ⊤)))`. Assume the negation of the conclusion as `h1`. Apply `hb` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Conclude with `(h1 ⟨⟨x, hx⟩⟩).elim`. Conclude with `((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).mpr (by simpa using this)`. Establish `hJg : genericPoint X ∉ J.support` using `fun hx => hJp _ hx hgen`. Take `⟨X', b, hX', hE, hiso⟩` from `GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso (𝓞 F) X q d hX J hJg`.

Set `V : X.Opens` to `J.support.compl`. Establish `hbV : IsIso (b ∣_ V)` using `hiso V fun _ hx => hx`. Establish `huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤))`. Use `(IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom` as an intermediate fact. Simplify using `using this`.

Establish `huW : IsUnit ((p : ℕ) : Γ(W, ⊤))`. Set `φ : Γ(Sp F, ⊤) →+* Γ(W, ⊤)` to `((πB ≫ s).app ⊤).hom`. Use `huF.map φ` as an intermediate fact. Rewrite `this` using `[map_natCast φ]`. Then use the resulting hypothesis. Establish `hrange : Set.range jB ⊆ Set.range V.ι`.

Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hw : w ∈ jB ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤))`. Simplify using `only [Scheme.preimage_basicOpen, map_natCast]`. Conclude with `(Scheme.basicOpen_of_isUnit W huW).ge (show w ∈ (⊤ : W.Opens) from trivial)`.

Conclude with `fun hx => hJp _ hx hw`. Set `jV : W ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι jB hrange`. Establish `hjV : jV ≫ V.ι = jB` using `IsOpenImmersion.lift_fac _ _ _`. Set `jB' : W ⟶ X'` to `jV ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι`. Establish `hjB' : jB' ≫ b = jB`.

Simplify using `only [jB', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]`. Establish `hsq : IsPullback jB' (𝟙 W) b jB`. Establish `h1 : IsPullback (jV ≫ inv (b ∣_ V)) (𝟙 W) (b ∣_ V) jV` using `IsPullback.of_vert_isIso ⟨by simp⟩`. Establish `h2` using `h1.paste_horiz (isPullback_morphismRestrict b V).flip`. Simplify `h2` using `[jB', Category.assoc, hjV]`.

Establish `hpb : IsPullback jB' (πB ≫ s) (b ≫ q) (spMap (algebraMap (𝓞 F) F))`. Simplify using `using hsq.paste_vert h.2.1`. Use `⟨X', W, b, jB', πB, ⟨hX', hpb, h.2.2.1, h.2.2.2.1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hjB']`. Conclude with `h.2.2.2.2`.

Introduce `Y ν w j hw`. Conclude with `hJE X' Y b ν hE w j hw`.
-/
theorem exists_blowup_principalises : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (N : Fin n → ℕ), (∀ j, IsAffineOpen (U j)) → (∀ j, N j ≠ 0) → (∀ j, (N j : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ (X' W' : Scheme.{0}) (b : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G), IsPre s S d ι (b ≫ q) jB' πB' (b ≫ ρ) ∧ ∀ (Y : Scheme.{0}) (ν : Y ⟶ X') (w : Y) (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : Y.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro F _ _ G T s S d ι X W q jB πB ρ h n U m A N hU hN hA
  have hX := h.1
  have := hX.isIntegral
  have := hX.isLocallyNoetherian
  have hc := hX.charZero
  set p : ℕ := ∏ j, N j with hpdef
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN j
  have hpA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical := by
    intro j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
    rw [hpdef, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hA j)
  obtain ⟨J, hJp, hJE⟩ := GlobalTheory.Principalise.exists_idealSheaf_principalises X p n U m A hU hpA
  have hgen : genericPoint X ∈ X.basicOpen (p : Γ(X, ⊤)) := by
    have hne : (p : Γ(X, ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have hb : X.basicOpen (p : Γ(X, ⊤)) ≠ ⊥ := fun h0 => hne ((basicOpen_eq_bot_iff _).1 h0)
    have : Nonempty (X.basicOpen (p : Γ(X, ⊤))) := by
      by_contra h1
      apply hb
      rw [eq_bot_iff]
      intro x hx
      exact (h1 ⟨⟨x, hx⟩⟩).elim
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).mpr
      (by simpa using this)
  have hJg : genericPoint X ∉ J.support := fun hx => hJp _ hx hgen
  obtain ⟨X', b, hX', hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso (𝓞 F) X q d hX J hJg
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤)) := by
    have := (IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    simpa using this
  have huW : IsUnit ((p : ℕ) : Γ(W, ⊤)) := by
    let φ : Γ(Sp F, ⊤) →+* Γ(W, ⊤) := ((πB ≫ s).app ⊤).hom
    have := huF.map φ
    rwa [map_natCast φ] at this
  have hrange : Set.range jB ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w ∈ jB ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      simp only [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit W huW).ge (show w ∈ (⊤ : W.Opens) from trivial)
    exact fun hx => hJp _ hx hw
  let jV : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι jB hrange
  have hjV : jV ≫ V.ι = jB := IsOpenImmersion.lift_fac _ _ _
  let jB' : W ⟶ X' := jV ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι
  have hjB' : jB' ≫ b = jB := by
    simp only [jB', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]
  have hsq : IsPullback jB' (𝟙 W) b jB := by
    have h1 : IsPullback (jV ≫ inv (b ∣_ V)) (𝟙 W) (b ∣_ V) jV :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict b V).flip
    simpa [jB', Category.assoc, hjV] using h2
  have hpb : IsPullback jB' (πB ≫ s) (b ≫ q) (spMap (algebraMap (𝓞 F) F)) := by
    simpa using hsq.paste_vert h.2.1
  refine ⟨X', W, b, jB', πB, ⟨hX', hpb, h.2.2.1, h.2.2.2.1, ?_⟩, ?_⟩
  · rw [← Category.assoc, hjB']
    exact h.2.2.2.2
  · intro Y ν w j hw
    exact hJE X' Y b ν hE w j hw

end GlobalTheory.ArLieBase
