import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealPartitionOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsomorphismCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomorphismTrivialOnKernelStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbDual in

/- English proof (translation)
Introduce `HG HR HD F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i hi hA hdim rm hrm P l hl hLB rig₁ rig₂ hred symm add smul pos c T x hx a ha`. Take `⟨n, d, a', hd, hsum⟩` from `GlobalTheory.T.fractional_ideal_partition_of_unity F 𝔠`. Establish `k₀ : ∀ (T₀ : Over (Sp R₀)) (y₀ : T₀ ⟶ X₀.A), (∀ j, HasGen ((X₀.P (d j)).pull (lift (fst X₀.A T₀) (snd X₀.A T₀ ≫ y₀)).left)) → y₀ = 1`. Introduce `T₀ y₀ hy`. Establish `h0 : X₀.rm.act 0 = 1`.

Establish `e` using `X₀.rm.add 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `left_eq_mul.1 e`. Establish `hs : ∀ s : Finset (Fin n), y₀ ≫ X₀.rm.act (∑ j ∈ s, a' j) = 1`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, h0, MonObj.comp_one]`. Consider the case `@insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, X₀.rm.add, MonObj.comp_mul, ih, X₀.ker (d j) T₀ y₀ (hy j) (a' j) (hd j), _root_.mul_one]`. Establish `e` using `hs Finset.univ`.

Rewrite `e` using `[hsum, X₀.rm.one, Category.comp_id]`. Then use the resulting hypothesis. Take `⟨N, hN⟩` from `GlobalTheory.AmpleNilThickening.exists_pow_eq_bot_of_isNilDP hκ`. Take `⟨D, _, Q, hDab, -, q, q'⟩` from `HD.1 _ A hA`. Take `⟨cp, hcp⟩` from `fracId_exists_totPos F 𝔠`. Establish `hL : ((P cp).pull (lift (𝟙 A) (𝟙 A)).left).IsLB` using `pull_isLB (hLB cp) _`.

Use `choose lam hlam hiff using fun j ↦ GlobalTheory.PoincarePull.exists_hom_triv_iff R A hA D Q q q' _ hL (pos cp hcp) (P (d j)) (hLB _) (rig₁ _) (rig₂ _)`. Establish `key : ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, HasGen ((P (d j)).pull (lift (fst A T) (snd A T ≫ y)).left)) → y = 1`. Introduce `T y hy`. Use `haveI := hDab.proper`. Use `haveI := hA.proper`.

Use `GlobalTheory.T.monomorphism_trivial_on_kernel R R₀ π hπ ⟨N, by rw [hI]; exact hN⟩ A inferInstance n D inferInstance lam hlam ?_ T y fun j ↦ (hiff j T y).1 (hy j)` and prove the remaining obligations. Introduce `T₀ z hz`. Set `z₀ : Over.mk T₀.hom ⟶ X₀.A` to `liftPt hi T₀.hom z.left (Over.w z)`. Establish `hz₀ : z₀.left ≫ i = z.left` using `liftPt_left hi _ _ _`. Establish `hpush : pushP hi (s` using `T₀.hom) rfl z₀ = z := Over.OverMorphism.ext hz₀`.

Establish `k₁ : z₀ = 1` using `k₀ _ z₀ fun j ↦ by`. Establish `hP` using `hLB (d j)`. Establish `hP'` using `X₀.isLB (d j)`. Establish `e` using `evc_trR hi hi hl.1 hl.2 hP hP' (hred (d j)) (Over.mk T₀.hom) z₀`. Establish `e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0` using `(triv_ev_iff hP _ _).1 ((hiff j _ z).2 (hz j))`.

Rewrite `e` using `[hpush]`. Take `⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _` from `⟨_, trR_section hi _⟩`. Establish `e2` using `congrArg (CechPic.pull s) (e.trans e0)`. Rewrite `e2` using `[← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero]`. Conclude with `(triv_ev_iff hP' _ _).2 e2`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← hz₀, k₁]`. Conclude with `one_left_comp hi (s := T₀.hom) rfl`. Use `key T (x ≫ rm.act a) fun j ↦ ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `ha (d j)`.

Conclude with `GlobalTheory.T.poincare_bundle_isomorphism_compat F 𝔠 _ A rm P hLB symm smul c (d j) a b hb T x hx`.
-/
theorem GlobalTheory.KerDeform.ker_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
  ∀ (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left),
    IsGrpPullback X₀.A A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
  ∀ (rm : OAct (𝓞 F) A), (∀ a, (X₀.rm.act a).left ≫ i = i ≫ (rm.act a).left) →
  ∀ (P : 𝔠.elt → LB (G2 A).left) (l : (G2 X₀.A).left ⟶ (G2 A).left), IsSquare i l → (∀ c, (P c).IsLB) →
    (∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)) → (∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)) →
    (∀ c, LBIso ((P c).pull l) (X₀.P c)) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    (∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)) →
  ∀ (c : 𝔠.elt) (T : Over (Sp R)) (x : T ⟶ A), HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1 := by
  intro HG HR HD F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i hi hA hdim rm hrm P l hl hLB rig₁ rig₂ hred symm add smul pos c T x hx a ha
  obtain ⟨n, d, a', hd, hsum⟩ := GlobalTheory.T.fractional_ideal_partition_of_unity F 𝔠
  have k₀ : ∀ (T₀ : Over (Sp R₀)) (y₀ : T₀ ⟶ X₀.A),
      (∀ j, HasGen ((X₀.P (d j)).pull (lift (fst X₀.A T₀) (snd X₀.A T₀ ≫ y₀)).left)) → y₀ = 1 := by
    intro T₀ y₀ hy
    have h0 : X₀.rm.act 0 = 1 := by
      have e := X₀.rm.add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    have hs : ∀ s : Finset (Fin n), y₀ ≫ X₀.rm.act (∑ j ∈ s, a' j) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, h0, MonObj.comp_one]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj, X₀.rm.add, MonObj.comp_mul, ih, X₀.ker (d j) T₀ y₀ (hy j) (a' j) (hd j), _root_.mul_one]
    have e := hs Finset.univ
    rwa [hsum, X₀.rm.one, Category.comp_id] at e
  obtain ⟨N, hN⟩ := GlobalTheory.AmpleNilThickening.exists_pow_eq_bot_of_isNilDP hκ
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := HD.1 _ A hA
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hL : ((P cp).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (hLB cp) _
  choose lam hlam hiff using fun j ↦ GlobalTheory.PoincarePull.exists_hom_triv_iff R A hA D Q q q' _ hL (pos cp hcp) (P (d j)) (hLB _) (rig₁ _) (rig₂ _)
  have key : ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (∀ j, HasGen ((P (d j)).pull (lift (fst A T) (snd A T ≫ y)).left)) → y = 1 := by
    intro T y hy
    haveI := hDab.proper
    haveI := hA.proper
    refine GlobalTheory.T.monomorphism_trivial_on_kernel R R₀ π hπ ⟨N, by rw [hI]; exact hN⟩ A inferInstance n D inferInstance lam hlam ?_ T y
      fun j ↦ (hiff j T y).1 (hy j)
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ X₀.A := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have hpush : pushP hi (s := T₀.hom) rfl z₀ = z := Over.OverMorphism.ext hz₀
    have k₁ : z₀ = 1 := k₀ _ z₀ fun j ↦ by
      have hP := hLB (d j)
      have hP' := X₀.isLB (d j)
      have e := evc_trR hi hi hl.1 hl.2 hP hP' (hred (d j)) (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff j _ z).2 (hz j))
      rw [hpush] at e
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (CechPic.pull s) (e.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP' _ _).2 e2
    apply Over.OverMorphism.ext
    rw [← hz₀, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  refine key T (x ≫ rm.act a) fun j ↦ ?_
  obtain ⟨b, hb⟩ := ha (d j)
  exact GlobalTheory.T.poincare_bundle_isomorphism_compat F 𝔠 _ A rm P hLB symm smul c (d j) a b hb T x hx
