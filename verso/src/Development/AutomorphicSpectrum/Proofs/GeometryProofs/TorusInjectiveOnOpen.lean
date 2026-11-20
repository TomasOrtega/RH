import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletionStatement
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StratLie

open GlobalTheory.CompanionTheory.Ar.TorusModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Substitute `ha` using the available equality. Conclude with `h A g t ht`.
-/
theorem killed_of_eq {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B : Type} [CommRing B] {b : Sp B ⟶ S}
    (h : KillsOver u Y b) {A : Type} [CommRing A] (g : B →+* A) {a : Sp A ⟶ S} (ha : a = spMap g ≫ b)
    (t : Over.mk a ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) : t ≫ u = 1 := by
  subst ha
  exact h A g t ht

/- English proof (translation)
Introduce `A _ g t ht`. Use `killed_of_eq h (g.comp c) ?_ t ht` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_comp_spMap]`.
-/
theorem killsOver_comp {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B C : Type} [CommRing B] [CommRing C]
    (c : B →+* C) {b : Sp B ⟶ S} (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  refine killed_of_eq h (g.comp c) ?_ t ht
  rw [← Category.assoc, spMap_comp_spMap]

/- English proof (translation)
Introduce `A _ g t ht`. Use `letI := g.toAlgebra`. Use `letI := c.toAlgebra`. Set `i : A →+* (A ⊗[κ] k)` to `Algebra.TensorProduct.includeLeftRingHom`. Set `j : k →+* (A ⊗[κ] k)` to `(Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom`.

Establish `hi : Function.Injective i` using `Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective`. Establish `hij : i.comp g = j.comp c`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `(algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Establish `hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b`. Simplify using `only [← Category.assoc, spMap_comp_spMap, hij]`. Set `φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b)` to `Over.homMk (spMap i) hw`. Establish `h1` using `h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])`. Establish `h2 : φ ≫ (t ≫ u) = φ ≫ 1` using `(Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)`.

Use `GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi` as an intermediate fact. Use `Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)` and prove the remaining obligations. Rewrite using `[Over.w, Over.w]`. Conclude with `congr($(h2).left)`.
-/
theorem killsOver_descent [IsSeparated G.hom] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {κ k : Type}
    [Field κ] [Field k] (c : κ →+* k) {b : Sp κ ⟶ S} (h : KillsOver u Y (spMap c ≫ b)) : KillsOver u Y b := by
  intro A _ g t ht
  letI := g.toAlgebra
  letI := c.toAlgebra
  let i : A →+* (A ⊗[κ] k) := Algebra.TensorProduct.includeLeftRingHom
  let j : k →+* (A ⊗[κ] k) := (Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective
  have hij : i.comp g = j.comp c := by
    ext a
    change (algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b := by
    simp only [← Category.assoc, spMap_comp_spMap, hij]
  let φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b) := Over.homMk (spMap i) hw
  have h1 := h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])
  have h2 : φ ≫ (t ≫ u) = φ ≫ 1 :=
    (Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)
  have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi
  refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)
  · rw [Over.w, Over.w]
  · exact congr($(h2).left)

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨t, ht⟩` from `exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b) (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))`. Establish `ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1` using `ht`. Establish `h1` using `hk _ _ t fun y hy => by`. Rewrite using `[ht', (AddMonoidHom.mem_ker).1 hy]`.

Both sides reduce to the same expression. Establish `h2` using `hinj _ _ t h1`. Take `⟨χ, hχ⟩` from `hψ 1`. Establish `h3` using `ht' χ`. Rewrite `h3` using `[h2, charVal_one, AddMonoidAlgebra.one_def, hχ]`.

Conclude with `one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm`.
-/
theorem false_of_killsOver {u : splitTorus S X ⟶ G} {K : Type} [Field K] (b : Sp K ⟶ S) {l : ℕ} (hl : l.Prime)
    (ψ : X →+ ZMod l) (hψ : Function.Surjective ψ) (hk : KillsOver u ψ.ker b)
    (hinj : ∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
      t ≫ u = 1 → t = 1) : False := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b)
    (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))
  have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1 := ht
  have h1 := hk _ _ t fun y hy => by
    rw [ht', (AddMonoidHom.mem_ker).1 hy]; rfl
  have h2 := hinj _ _ t h1
  obtain ⟨χ, hχ⟩ := hψ 1
  have h3 := ht' χ
  rw [h2, charVal_one, AddMonoidAlgebra.one_def, hχ] at h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm

/- English proof (translation)
Use `GlobalTheory.T.killsOver_of_adic_completion S G X u Y R b fun n => ?_` and prove the remaining obligations. Proceed by induction on `n with`. Consider the case `zero`. Set `e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1))` to `Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)`. Establish `he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _`.

Use extensionality with `a`. Both sides reduce to the same expression. Use `killsOver_comp e h` as an intermediate fact. Rewrite `this` using `[← Category.assoc, spMap_comp_spMap, he]`. Then use the resulting hypothesis. Consider the case `succ n ih => set m := IsLocalRing.maximalIdeal R with hm`.

Establish `hne : m ^ (n + 1 + 1) ≠ ⊤` using `fun htop => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))`. Set `q` to `Ideal.Quotient.mk (m ^ (n + 1 + 1))`. Use `haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne`. Use `haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective`. Set `I : Ideal (R ⧸ m ^ (n + 1 + 1))` to `(m ^ (n + 1)).map q`.

Establish `hI : I ^ 2 = ⊥`. Rewrite using `[← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]`. Conclude with `Ideal.pow_le_pow_right (by omega)`. Use `GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ (spMap q ≫ b) I hI ?_` and prove the remaining obligations. Set `e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I` to `Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)`.

Establish `he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q`. Use extensionality with `a`. Both sides reduce to the same expression. Use `killsOver_comp e ih` as an intermediate fact. Rewrite `this` using `[← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc]`.

Conclude with `this`.
-/
theorem killsOver_of_residue [IsSeparated G.hom] {u : splitTorus S X ⟶ G} [IsMonHom u] {Y : AddSubgroup X}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) : KillsOver u Y b := by
  refine GlobalTheory.T.killsOver_of_adic_completion S G X u Y R b fun n => ?_
  induction n with
  | zero =>
    let e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)
    have he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext a; rfl
    have := killsOver_comp e h
    rwa [← Category.assoc, spMap_comp_spMap, he] at this
  | succ n ih =>
    set m := IsLocalRing.maximalIdeal R with hm
    have hne : m ^ (n + 1 + 1) ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))
    let q := Ideal.Quotient.mk (m ^ (n + 1 + 1))
    haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ m ^ (n + 1 + 1)) := (m ^ (n + 1)).map q
    have hI : I ^ 2 = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ (spMap q ≫ b) I hI ?_
    let e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q := by
      ext a; rfl
    have := killsOver_comp e ih
    rw [← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc] at this
    exact this

/- English proof (translation)
Introduce `Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ`. Assume the negation of the conclusion as `hne`. Take `⟨l, hl, ψ, hψ, hk⟩` from `GlobalTheory.T.torus_kernel_prime_quotient Z G X u k x M hM δ hne hδ`. Take `⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k), x = Spec.map f ≫ Z.fromSpecResidueField z` from `⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩`. Distinguish the cases in `hz : z ∈ U`.

Establish `hU' : ⊤ ≤ x ⁻¹ᵁ U` using `fun p _ => by`. Substitute `hx` using the available equality. Express the relevant statement in the definitionally equal form `(Z.fromSpecResidueField z) _ ∈ U`. Rewrite using `[Scheme.fromSpecResidueField_apply]` and apply the resulting hypothesis. Conclude with `false_of_killsOver x hl ψ hψ hk (hinj k x hU')`.

Establish `hgen : genericPoint Z ∈ U` using `((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)`. Establish `hzg : z ≠ genericPoint Z` using `fun h => hz (h ▸ hgen)`. Establish `hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z)` using `killsOver_descent f.hom (hx ▸ hk)`. Take `⟨V, hV, hA, hdom⟩` from `GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg`. Set `jv : Z.presheaf.stalk z →+* V` to `(algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA`.

Use `haveI : IsLocalHom jv := ⟨fun a ha => by`. Assume the negation of the conclusion as `hna`. Conclude with `((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩`. Set `b : Sp V ⟶ Z` to `spMap jv ≫ Z.fromSpecStalk z`. Set `rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V` to `IsLocalRing.ResidueField.map jv`.

Establish `e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b`. Establish `e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv`. Rewrite using `[spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]`. Both sides reduce to the same expression. Simplify using `only [b, Scheme.fromSpecResidueField]`.

Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))`. Establish `kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b)` using `e1 ▸ killsOver_comp rm hkκ`. Establish `kV` using `killsOver_of_residue b kres`. Establish `kK` using `killsOver_comp V.subtype kV`. Establish `hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U`.

Establish `e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z)`. Simplify using `only [b]`. Rewrite using `[← Category.assoc, spMap_comp_spMap]`. Conclude with `Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)`. Introduce `p _`.

Express the relevant statement in the definitionally equal form `(spMap V.subtype ≫ b) p ∈ U`. Rewrite using `[e2]`. Establish `hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z))` using `⟨p, rfl⟩`. Rewrite `hp` using `[Scheme.range_fromSpecStalk]`. Conclude with `Specializes.mem_open hp U.isOpen hgen`.

Conclude with `false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')`.
-/
theorem lie_injective : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient Z G X u k x M hM δ hne hδ
  obtain ⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k),
      x = Spec.map f ≫ Z.fromSpecResidueField z :=
    ⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩
  by_cases hz : z ∈ U
  · have hU' : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
      subst hx
      change (Z.fromSpecResidueField z) _ ∈ U
      rwa [Scheme.fromSpecResidueField_apply]
    exact false_of_killsOver x hl ψ hψ hk (hinj k x hU')
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hzg : z ≠ genericPoint Z := fun h => hz (h ▸ hgen)
  have hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z) :=
    killsOver_descent f.hom (hx ▸ hk)
  obtain ⟨V, hV, hA, hdom⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg
  let jv : Z.presheaf.stalk z →+* V := (algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA
  haveI : IsLocalHom jv := ⟨fun a ha => by
    by_contra hna
    exact ((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩
  let b : Sp V ⟶ Z := spMap jv ≫ Z.fromSpecStalk z
  let rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V :=
    IsLocalRing.ResidueField.map jv
  have e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b := by
    have e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv := by
      rw [spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]
      rfl
    simp only [b, Scheme.fromSpecResidueField]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))
  have kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b) := e1 ▸ killsOver_comp rm hkκ
  have kV := killsOver_of_residue b kres
  have kK := killsOver_comp V.subtype kV
  have hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U := by
    have e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z) := by
      simp only [b]
      rw [← Category.assoc, spMap_comp_spMap]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
    intro p _
    change (spMap V.subtype ≫ b) p ∈ U
    rw [e2]
    have hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact Specializes.mem_open hp U.isOpen hgen
  exact false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')

end GlobalTheory.CompanionTheory.Ar.StratLie
