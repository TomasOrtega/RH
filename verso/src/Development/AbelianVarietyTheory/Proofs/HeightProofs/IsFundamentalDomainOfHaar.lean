import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHyperbolicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankAddTwoMulOfHyperbolicPairsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOneStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNormStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Topology

namespace GlobalTheory.VolHeckeCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption`.
-/
theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

/- English proof (translation)
The claim follows from `funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ)`.
-/
theorem infFam_unique {D : D7} {θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨⟨θ, hθ⟩, h⟩ => ⟨θ, hθ, h θ hθ⟩, fun ⟨θ, hθ, h⟩ => ⟨⟨θ, hθ⟩, fun _ hθ' => infFam_unique hθ hθ' ▸ h⟩⟩`.
-/
theorem allSome_infFam_iff {D : D7} (Q : (D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) → Prop) :
    AllSome (IsInfFam (D := D)) Q ↔ ∃ θ, IsInfFam θ ∧ Q θ :=
  ⟨fun ⟨⟨θ, hθ⟩, h⟩ => ⟨θ, hθ, h θ hθ⟩,
    fun ⟨θ, hθ, h⟩ => ⟨⟨θ, hθ⟩, fun _ hθ' => infFam_unique hθ hθ' ▸ h⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infPart_eq (D : D7) : infPart D = UnitaryVolumePairs.infPart D := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_eq (D : D7) : finPart D = UnitaryVolumePairs.finPart D := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem idF_eq (D : D7) : idF D = UnitaryVolumePairs.resF D := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isHeckeChar_iff (D : D7) (χ : (AE D)ˣ →* Circle) : IsHeckeChar D χ ↔ χ ∈ UnitaryVolumePairs.HeckeChar D := Iff.rfl

/- English proof (translation)
Unfold `HasInfExp UnitaryVolumePairs.HasExponent`. Use `exists_congr fun n => and_congr Iff.rfl ?_` and prove the remaining obligations. Rewrite using `[allSome_infFam_iff]`. Use `exists_congr fun θ => and_congr Iff.rfl (forall_congr' fun x => ?_)` and prove the remaining obligations. Conclude with `⟨fun h hx => h hx.1 hx.2, fun h h1 h2 => h ⟨h1, h2⟩⟩`.
-/
theorem hasInfExp_iff (D : D7) (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a : ℚ) :
    HasInfExp D χ τ a ↔ UnitaryVolumePairs.HasExponent χ τ a := by
  unfold HasInfExp UnitaryVolumePairs.HasExponent
  refine exists_congr fun n => and_congr Iff.rfl ?_
  rw [allSome_infFam_iff]
  refine exists_congr fun θ => and_congr Iff.rfl (forall_congr' fun x => ?_)
  exact ⟨fun h hx => h hx.1 hx.2, fun h h1 h2 => h ⟨h1, h2⟩⟩

/- English proof (translation)
The claim follows from `forall_congr' fun _ => ⟨fun h hx => h hx.1 hx.2.1 hx.2.2, fun h h1 h2 h3 => h ⟨h1, h2, h3⟩⟩`.
-/
theorem unramEverywhere_iff (D : D7) (χ : (AE D)ˣ →* Circle) :
    UnramEverywhere D χ ↔ UnitaryVolumePairs.IsUnramified χ :=
  forall_congr' fun _ => ⟨fun h hx => h hx.1 hx.2.1 hx.2.2, fun h h1 h2 h3 => h ⟨h1, h2, h3⟩⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hs : Function.Surjective (algebraMap D.host.F D.host.E)` using `fun x => (D.sp.cm.fixed x).1 (h x)`. Establish `h1 : Module.finrank D.host.F D.host.E = 1`. Rewrite using `[← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E) ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]`.

Establish `h2` using `D.sp.cm.deg2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_not_fixed (D : D7) : ∃ x, D.sp.cm.sig x ≠ x := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
  have h1 : Module.finrank D.host.F D.host.E = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
      ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
  have h2 := D.sp.cm.deg2
  omega

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective`.
-/
theorem algebraMap_AE_injective (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext (algebraMap_AE_injective D (congrArg Units.val h))`.
-/
theorem resF_injective (D : D7) : Function.Injective (UnitaryVolumePairs.resF D) := fun _ _ h =>
  Units.ext (algebraMap_AE_injective D (congrArg Units.val h))

abbrev normU (D : D7) : (AE D)ˣ →* (AF D.host.F)ˣ := Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)

/- English proof (translation)
Take `⟨δ, hδ, h⟩` from `GlobalTheory.T.quadraticExt_norm_form_over_algebra D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) (exists_not_fixed D)`. Take `⟨h1, h2⟩` from `h (AF D.host.F)`. Establish `hN : ∀ z : AE D, algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * sigR (AF D.host.F) D.sp.cm.sig z` using `fun z => by`. Take `⟨x, y, e1, e2⟩` from `h1 z`. Rewrite using `[e1, e2]`.

Use `⟨δ, hδ, fun x => Units.ext (hN x), fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨z, rfl⟩`. Take `⟨x, y, e1, -⟩` from `h1 z`. Conclude with `⟨x, y, e1⟩`. Introduce and unpack `⟨x, y, e⟩`.

Take `⟨z, hz⟩` from `h2 x y`. Rewrite `hz` using `[← e]`. Establish `hu : IsUnit z` using `isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)`. Use `⟨hu.unit, Units.ext (algebraMap_AE_injective D ?_)⟩` and prove the remaining obligations. Conclude with `(hN z).trans hz`.
-/
theorem exists_form (D : D7) : ∃ δ : D.host.F, ¬ IsSquare δ ∧
    (∀ x, UnitaryVolumePairs.resF D (normU D x) = UnitaryVolumePairs.normId D x) ∧
    ∀ a : (AF D.host.F)ˣ, a ∈ (normU D).range ↔
      ∃ x y : AF D.host.F, (a : AF D.host.F) = x ^ 2 - algebraMap D.host.F (AF D.host.F) δ * y ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
    (exists_not_fixed D)
  obtain ⟨h1, h2⟩ := h (AF D.host.F)
  have hN : ∀ z : AE D, algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) =
      z * sigR (AF D.host.F) D.sp.cm.sig z := fun z => by
    obtain ⟨x, y, e1, e2⟩ := h1 z
    rw [e1, e2]
  refine ⟨δ, hδ, fun x => Units.ext (hN x), fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, y, e1, -⟩ := h1 z
    exact ⟨x, y, e1⟩
  · rintro ⟨x, y, e⟩
    obtain ⟨z, hz⟩ := h2 x y
    rw [← e] at hz
    have hu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)
    refine ⟨hu.unit, Units.ext (algebraMap_AE_injective D ?_)⟩
    exact (hN z).trans hz

/- English proof (translation)
Take `⟨-, -, h, -⟩` from `exists_form D`. Unfold `UnitaryVolumePairs.normGroup`. Use `congr 1`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨x, resF_injective D ((h x).trans hx)⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, (h x).symm⟩`.
-/
theorem normGroup_eq (D : D7) : UnitaryVolumePairs.normGroup D = (UnitaryVolumePairs.ratF D).range ⊔ (normU D).range := by
  obtain ⟨-, -, h, -⟩ := exists_form D
  unfold UnitaryVolumePairs.normGroup
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, resF_injective D ((h x).trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (h x).symm⟩

/- English proof (translation)
Take `⟨δ, hδ, -, h⟩` from `exists_form D`. Establish `h0 : δ ≠ 0` using `fun e => hδ (e ▸ IsSquare.zero)`. Use `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one D.host.F δ h0) fun a ha => ?_)` and prove the remaining obligations. Rewrite using `[normGroup_eq]`. Conclude with `Subgroup.mem_sup_right ((h a).2 ha)`.
-/
theorem isOpen_normGroup (D : D7) : IsOpen (UnitaryVolumePairs.normGroup D : Set (AF D.host.F)ˣ) := by
  obtain ⟨δ, hδ, -, h⟩ := exists_form D
  have h0 : δ ≠ 0 := fun e => hδ (e ▸ IsSquare.zero)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one D.host.F δ h0) fun a ha => ?_)
  rw [normGroup_eq]
  exact Subgroup.mem_sup_right ((h a).2 ha)

/- English proof (translation)
Take `⟨δ, hδ, -, h⟩` from `exists_form D`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare D.host.F δ hδ`. Introduce `e`. Establish `hm : a ∈ UnitaryVolumePairs.normGroup D` using `e ▸ Subgroup.mem_top a`. Rewrite `hm` using `[normGroup_eq]`.

Take `⟨_, ⟨t, rfl⟩, n, hn, rfl⟩` from `Subgroup.mem_sup.1 hm`. Take `⟨x, y, e⟩` from `(h n).1 hn`. Conclude with `ha t x y (by rw [Units.val_mul, e]; rfl)`.
-/
theorem normGroup_ne_top (D : D7) : UnitaryVolumePairs.normGroup D ≠ ⊤ := by
  obtain ⟨δ, hδ, -, h⟩ := exists_form D
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare D.host.F δ hδ
  intro e
  have hm : a ∈ UnitaryVolumePairs.normGroup D := e ▸ Subgroup.mem_top a
  rw [normGroup_eq] at hm
  obtain ⟨_, ⟨t, rfl⟩, n, hn, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨x, y, e⟩ := (h n).1 hn
  exact ha t x y (by rw [Units.val_mul, e]; rfl)

/- English proof (translation)
Take `⟨δ, -, -, h⟩` from `exists_form D`. Rewrite using `[normGroup_eq]`. Conclude with `Subgroup.mem_sup_right ((h _).2 ⟨a, 0, by simp [pow_two]⟩)`.
-/
theorem sq_mem_normGroup (D : D7) (a : (AF D.host.F)ˣ) : a * a ∈ UnitaryVolumePairs.normGroup D := by
  obtain ⟨δ, -, -, h⟩ := exists_form D
  rw [normGroup_eq]
  exact Subgroup.mem_sup_right ((h _).2 ⟨a, 0, by simp [pow_two]⟩)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h1, h2, h3⟩`. Use `⟨?_, h3⟩` and prove the remaining obligations. Rewrite using `[normGroup_eq]`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `h1 a`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `h2 a`. Introduce and unpack `⟨h, h3⟩`.

Use `⟨?_, fun a => h ?_, fun x => h ?_, h3⟩` and prove the remaining obligations. Use `continuous_of_continuousAt_one η ?_` and prove the remaining obligations. Use `(continuousAt_const (y := (1 : Circle))).congr ?_` and prove the remaining obligations. Use `filter_upwards [(isOpen_normGroup D).mem_nhds (one_mem _)] with a ha`. Conclude with `(h ha).symm`.

Rewrite using `[normGroup_eq]`. Conclude with `Subgroup.mem_sup_left ⟨a, rfl⟩`. Rewrite using `[normGroup_eq]`. Conclude with `Subgroup.mem_sup_right ⟨x, rfl⟩`.
-/
theorem isEta_iff_normGroup (D : D7) (η : (AF D.host.F)ˣ →* Circle) :
    IsEta D η ↔ UnitaryVolumePairs.normGroup D ≤ η.ker ∧ η ≠ 1 := by
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    rw [normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩; exact h1 a
    · rintro _ ⟨a, rfl⟩; exact h2 a
  · rintro ⟨h, h3⟩
    refine ⟨?_, fun a => h ?_, fun x => h ?_, h3⟩
    · refine continuous_of_continuousAt_one η ?_
      refine (continuousAt_const (y := (1 : Circle))).congr ?_
      filter_upwards [(isOpen_normGroup D).mem_nhds (one_mem _)] with a ha
      exact (h ha).symm
    · rw [normGroup_eq]; exact Subgroup.mem_sup_left ⟨a, rfl⟩
    · rw [normGroup_eq]; exact Subgroup.mem_sup_right ⟨x, rfl⟩

/- English proof (translation)
Establish `h2 : (z : ℂ) * z = 1` using `by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h`. Break down `mul_self_eq_one_iff.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd (Circle.ext h3) h1`. Conclude with `h3`.
-/
theorem circle_eq_neg_one {z : Circle} (h : z * z = 1) (h1 : z ≠ 1) : (z : ℂ) = -1 := by
  have h2 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h2 with h3 | h3
  · exact absurd (Circle.ext h3) h1
  · exact h3

/- English proof (translation)
Establish `hne : (QuotientGroup.mk a : G ⧸ N) ≠ 1` using `fun e => ha ((QuotientGroup.eq_one_iff a).1 e)`. Establish `h2 : ∀ x : Additive (G ⧸ N), 2 • x = 0` using `fun x => by`. Take `⟨g, hg⟩` from `QuotientGroup.mk_surjective (Additive.toMul x)`. Establish `hx : x = Additive.ofMul (QuotientGroup.mk g : G ⧸ N)` using `by rw [hg]; rfl`. Rewrite using `[hx, two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hN g)]`.

Both sides reduce to the same expression. Use `letI : Module (ZMod 2) (Additive (G ⧸ N)) := AddCommGroup.zmodModule h2`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_ne_zero (ZMod 2) (x := (Additive.ofMul (QuotientGroup.mk a : G ⧸ N))) hne`. Use `⟨{ toFun := fun g => ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N))) map_one' := by simp map_mul' := fun g g' => by` and prove the remaining obligations.

Rewrite using `[QuotientGroup.mk_mul, ofMul_mul, map_add, AddChar.map_add_eq_mul] }, fun g hg => ?_, ?_⟩`. Use `show ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N))) = 1`. Rewrite using `[(QuotientGroup.eq_one_iff g).2 hg]`. Simplify using the standard rewrite rules. Introduce `e`.

Apply `hφ` to reduce the goal to its premises. Apply `ZMod.injective_toCircle` to reduce the goal to its premises. Rewrite using `[AddChar.map_zero_eq_one]`. Conclude with `e`.
-/
theorem exists_char_of_not_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : ∀ a, a * a ∈ N) (a : G)
    (ha : a ∉ N) : ∃ η : G →* Circle, N ≤ η.ker ∧ η a ≠ 1 := by
  have hne : (QuotientGroup.mk a : G ⧸ N) ≠ 1 := fun e => ha ((QuotientGroup.eq_one_iff a).1 e)
  have h2 : ∀ x : Additive (G ⧸ N), 2 • x = 0 := fun x => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk g : G ⧸ N) := by rw [hg]; rfl
    rw [hx, two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hN g)]
    rfl
  letI : Module (ZMod 2) (Additive (G ⧸ N)) := AddCommGroup.zmodModule h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2)
    (x := (Additive.ofMul (QuotientGroup.mk a : G ⧸ N))) hne
  refine ⟨{ toFun := fun g => ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N)))
            map_one' := by simp
            map_mul' := fun g g' => by
              rw [QuotientGroup.mk_mul, ofMul_mul, map_add, AddChar.map_add_eq_mul] }, fun g hg => ?_, ?_⟩
  · show ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N))) = 1
    rw [(QuotientGroup.eq_one_iff g).2 hg]
    simp
  · intro e
    apply hφ
    apply ZMod.injective_toCircle
    rw [AddChar.map_zero_eq_one]
    exact e

/- English proof (translation)
Take `⟨η, h1, h2⟩` from `exists_char_of_not_mem _ (sq_mem_normGroup D) a ha`. Conclude with `⟨η, (isEta_iff_normGroup D η).2 ⟨h1, fun e => h2 (by rw [e]; rfl)⟩, h2⟩`.
-/
theorem exists_isEta_ne_one (D : D7) {a : (AF D.host.F)ˣ} (ha : a ∉ UnitaryVolumePairs.normGroup D) :
    ∃ η, IsEta D η ∧ η a ≠ 1 := by
  obtain ⟨η, h1, h2⟩ := exists_char_of_not_mem _ (sq_mem_normGroup D) a ha
  exact ⟨η, (isEta_iff_normGroup D η).2 ⟨h1, fun e => h2 (by rw [e]; rfl)⟩, h2⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, a ∉ UnitaryVolumePairs.normGroup D := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `normGroup_ne_top D (eq_top_iff.2 fun a _ => h a)`. Take `⟨η, h, -⟩` from `exists_isEta_ne_one D ha`.

Conclude with `⟨η, h⟩`.
-/
theorem exists_isEta (D : D7) : ∃ η, IsEta D η := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ UnitaryVolumePairs.normGroup D := by
    by_contra h
    push Not at h
    exact normGroup_ne_top D (eq_top_iff.2 fun a _ => h a)
  obtain ⟨η, h, -⟩ := exists_isEta_ne_one D ha
  exact ⟨η, h⟩

/- English proof (translation)
The claim follows from `if_pos ha`.
-/
theorem eta_of_mem {D : D7} {a : (AF D.host.F)ˣ} (ha : a ∈ UnitaryVolumePairs.normGroup D) : UnitaryVolumePairs.eta D a = 1 := if_pos ha
/- English proof (translation)
The claim follows from `if_neg ha`.
-/
theorem eta_of_not_mem {D : D7} {a : (AF D.host.F)ˣ} (ha : a ∉ UnitaryVolumePairs.normGroup D) : UnitaryVolumePairs.eta D a = -1 := if_neg ha

/- English proof (translation)
Rewrite using `[← map_mul]`. Conclude with `((isEta_iff_normGroup D η).1 h).1 (sq_mem_normGroup D a)`.
-/
theorem IsEta_mul_self {D : D7} {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) :
    η a * η a = 1 := by
  rw [← map_mul]
  exact ((isEta_iff_normGroup D η).1 h).1 (sq_mem_normGroup D a)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Use `le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `h1` using `e a`.

Rewrite `h1` using `[eta_of_not_mem hn, show η a = 1 from ha]`. Evaluate the numerical expressions using `at h1`. Introduce `e a`. Distinguish the cases in `ha : a ∈ UnitaryVolumePairs.normGroup D`. Rewrite using `[eta_of_mem ha, show η a = 1 from ((isEta_iff_normGroup D η).1 h).1 ha]`.

Both sides reduce to the same expression. Rewrite using `[eta_of_not_mem ha]`. Conclude with `circle_eq_neg_one (IsEta_mul_self h a) fun e1 => ha (e ▸ e1)`.
-/
theorem coe_eq_eta_iff {D : D7} {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) :
    (∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a) ↔ η.ker = UnitaryVolumePairs.normGroup D := by
  constructor
  · intro e
    refine le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1
    by_contra hn
    have h1 := e a
    rw [eta_of_not_mem hn, show η a = 1 from ha] at h1
    norm_num at h1
  · intro e a
    by_cases ha : a ∈ UnitaryVolumePairs.normGroup D
    · rw [eta_of_mem ha, show η a = 1 from ((isEta_iff_normGroup D η).1 h).1 ha]; rfl
    · rw [eta_of_not_mem ha]
      exact circle_eq_neg_one (IsEta_mul_self h a) fun e1 => ha (e ▸ e1)

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isEta_iff_normGroup D η).1 h`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, η b ≠ 1 := by`. Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Conclude with `h2 (MonoidHom.ext hh)`.

Establish `hbn : b ∉ UnitaryVolumePairs.normGroup D` using `fun hm => hb (h1 hm)`. Use `MonoidHom.ext fun a => Circle.ext ?_` and prove the remaining obligations. Rewrite using `[e a]`. Distinguish the cases in `ha : a ∈ UnitaryVolumePairs.normGroup D`. Rewrite using `[eta_of_mem ha, show η a = 1 from h1 ha]`.

Both sides reduce to the same expression. Rewrite using `[eta_of_not_mem ha]`. Establish `hab : a * b ∈ UnitaryVolumePairs.normGroup D`. Assume the negation of the conclusion as `hn`. Establish `h3` using `e (a * b)`.

Rewrite `h3` using `[map_mul, Circle.coe_mul, e a, e b, eta_of_not_mem ha, eta_of_not_mem hbn, eta_of_not_mem hn]`. Evaluate the numerical expressions using `at h3`. Establish `h4 : η a * η b = 1` using `by rw [← map_mul]; exact h1 hab`. Use `circle_eq_neg_one (IsEta_mul_self h a) fun e1 => hb ?_` and prove the remaining obligations. Rewrite `h4` using `[e1, one_mul]`. Then use the resulting hypothesis.
-/
theorem eq_of_coe_eq_eta {D : D7} {ψ η : (AF D.host.F)ˣ →* Circle} (e : ∀ a, (ψ a : ℂ) = UnitaryVolumePairs.eta D a)
    (h : IsEta D η) : η = ψ := by
  obtain ⟨h1, h2⟩ := (isEta_iff_normGroup D η).1 h
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact h2 (MonoidHom.ext hh)
  have hbn : b ∉ UnitaryVolumePairs.normGroup D := fun hm => hb (h1 hm)
  refine MonoidHom.ext fun a => Circle.ext ?_
  rw [e a]
  by_cases ha : a ∈ UnitaryVolumePairs.normGroup D
  · rw [eta_of_mem ha, show η a = 1 from h1 ha]; rfl
  · rw [eta_of_not_mem ha]
    have hab : a * b ∈ UnitaryVolumePairs.normGroup D := by
      by_contra hn
      have h3 := e (a * b)
      rw [map_mul, Circle.coe_mul, e a, e b, eta_of_not_mem ha, eta_of_not_mem hbn, eta_of_not_mem hn] at h3
      norm_num at h3
    have h4 : η a * η b = 1 := by rw [← map_mul]; exact h1 hab
    refine circle_eq_neg_one (IsEta_mul_self h a) fun e1 => hb ?_
    rwa [e1, one_mul] at h4

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hu⟩`. Use `(coe_eq_eta_iff h).2 (le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1)` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Take `⟨η', h', h1⟩` from `exists_isEta_ne_one D hn`.

Conclude with `h1 (hu η' h' ▸ ha)`. Introduce `e`. Take `⟨η₀, h₀⟩` from `exists_isEta D`. Conclude with `⟨eq_of_coe_eq_eta e h₀ ▸ h₀, fun η' h' => eq_of_coe_eq_eta e h'⟩`.
-/
theorem isEta_unique_iff (D : D7) (η : (AF D.host.F)ˣ →* Circle) :
    (IsEta D η ∧ ∀ η', IsEta D η' → η' = η) ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a := by
  constructor
  · rintro ⟨h, hu⟩
    refine (coe_eq_eta_iff h).2 (le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1)
    by_contra hn
    obtain ⟨η', h', h1⟩ := exists_isEta_ne_one D hn
    exact h1 (hu η' h' ▸ ha)
  · intro e
    obtain ⟨η₀, h₀⟩ := exists_isEta D
    exact ⟨eq_of_coe_eq_eta e h₀ ▸ h₀, fun η' h' => eq_of_coe_eq_eta e h'⟩

/- English proof (translation)
Use `⟨fun h => (coe_eq_eta_iff h).2 ?_, fun e => ((isEta_unique_iff D η).2 e).1⟩` and prove the remaining obligations. Take `⟨h1, h3⟩` from `(isEta_iff_normGroup D η).1 h`. Use `le_antisymm (fun a ha => ?_) h1` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Use `h3 (MonoidHom.ext fun b => ?_)` and prove the remaining obligations.

Distinguish the cases in `hb : b ∈ UnitaryVolumePairs.normGroup D`. Conclude with `h1 hb`. Establish `hab : a * b ∈ UnitaryVolumePairs.normGroup D` using `(Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hn hb)`. Establish `h4 : η a * η b = 1` using `by rw [← map_mul]; exact h1 hab`. Rewrite `h4` using `[show η a = 1 from ha, one_mul]`. Then use the resulting hypothesis.
-/
theorem isEta_iff_of_index_two (D : D7) (h2 : (UnitaryVolumePairs.normGroup D).index = 2) (η : (AF D.host.F)ˣ →* Circle) :
    IsEta D η ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a := by
  refine ⟨fun h => (coe_eq_eta_iff h).2 ?_, fun e => ((isEta_unique_iff D η).2 e).1⟩
  obtain ⟨h1, h3⟩ := (isEta_iff_normGroup D η).1 h
  refine le_antisymm (fun a ha => ?_) h1
  by_contra hn
  refine h3 (MonoidHom.ext fun b => ?_)
  by_cases hb : b ∈ UnitaryVolumePairs.normGroup D
  · exact h1 hb
  · have hab : a * b ∈ UnitaryVolumePairs.normGroup D := (Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hn hb)
    have h4 : η a * η b = 1 := by rw [← map_mul]; exact h1 hab
    rwa [show η a = 1 from ha, one_mul] at h4

/- English proof (translation)
Establish `hsq : ∀ a, UnitaryVolumePairs.eta D a ^ 2 = 1` using `fun a => by`. Unfold `UnitaryVolumePairs.eta`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hsq' : ∀ η, IsEta D η → ∀ a, η a ^ 2 = 1` using `fun η h a => by rw [pow_two]; exact IsEta_mul_self h a`. Break down `Nat.even_or_odd' n with ⟨k, rfl | rfl⟩` into its components or cases.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨η, hη⟩, h⟩ a`. Rewrite using `[pow_mul, hsq, one_pow, ← idF_eq, h η hη a, pow_mul, hsq' η hη, one_pow]`. Both sides reduce to the same expression. Introduce `h`.

Use `⟨exists_isEta D, fun η hη a => Circle.ext ?_⟩` and prove the remaining obligations. Rewrite using `[idF_eq, h a, pow_mul, hsq, one_pow, pow_mul, hsq' η hη, one_pow]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨η, hη⟩, h⟩ a`.

Establish `hu : ∀ η', IsEta D η' → η' = χ.comp (idF D)` using `fun η' h' => MonoidHom.ext fun b => by`. Rewrite using `[MonoidHom.comp_apply, h η' h' b, pow_succ, pow_mul, hsq' η' h', one_pow, one_mul]`. Rewrite using `[pow_succ, pow_mul, hsq, one_pow, one_mul]`. Conclude with `(isEta_unique_iff D (χ.comp (idF D))).1 ⟨hu η hη ▸ hη, hu⟩ a`. Introduce `h`.

Use `⟨exists_isEta D, fun η hη a => ?_⟩` and prove the remaining obligations. Establish `e : ∀ b, ((χ.comp (idF D)) b : ℂ) = UnitaryVolumePairs.eta D b` using `fun b => by`. Establish `hb` using `h b`. Rewrite `hb` using `[pow_succ, pow_mul, hsq, one_pow, one_mul]`. Then use the resulting hypothesis. Rewrite using `[pow_succ, pow_mul, hsq' η hη, one_pow, one_mul, eq_of_coe_eq_eta e hη]`.

Both sides reduce to the same expression.
-/
theorem resEta_iff (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) :
    ResEta D χ n ↔ UnitaryVolumePairs.RestrictsToEtaPow χ n := by
  have hsq : ∀ a, UnitaryVolumePairs.eta D a ^ 2 = 1 := fun a => by
    unfold UnitaryVolumePairs.eta
    split_ifs <;> norm_num
  have hsq' : ∀ η, IsEta D η → ∀ a, η a ^ 2 = 1 := fun η h a => by rw [pow_two]; exact IsEta_mul_self h a
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · constructor
    · rintro ⟨⟨η, hη⟩, h⟩ a
      rw [pow_mul, hsq, one_pow, ← idF_eq, h η hη a, pow_mul, hsq' η hη, one_pow]
      rfl
    · intro h
      refine ⟨exists_isEta D, fun η hη a => Circle.ext ?_⟩
      rw [idF_eq, h a, pow_mul, hsq, one_pow, pow_mul, hsq' η hη, one_pow]
      rfl
  · constructor
    · rintro ⟨⟨η, hη⟩, h⟩ a
      have hu : ∀ η', IsEta D η' → η' = χ.comp (idF D) := fun η' h' => MonoidHom.ext fun b => by
        rw [MonoidHom.comp_apply, h η' h' b, pow_succ, pow_mul, hsq' η' h', one_pow, one_mul]
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
      exact (isEta_unique_iff D (χ.comp (idF D))).1 ⟨hu η hη ▸ hη, hu⟩ a
    · intro h
      refine ⟨exists_isEta D, fun η hη a => ?_⟩
      have e : ∀ b, ((χ.comp (idF D)) b : ℂ) = UnitaryVolumePairs.eta D b := fun b => by
        have hb := h b
        rwa [pow_succ, pow_mul, hsq, one_pow, one_mul] at hb
      rw [pow_succ, pow_mul, hsq' η hη, one_pow, one_mul, eq_of_coe_eq_eta e hη]
      rfl

def colVec {D : D7} (V : HSp D) {i : ℕ} (C : Matrix (Fin V.rank) (Fin i) D.host.E) (a : Fin i) : V.V :=
  V.frame.equivFun.symm (C.transpose a)

/- English proof (translation)
Simplify using `only [colVec, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply, Formalism.UG.cT, HSpace.gram, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Establish `e : (D.sp.cm.sig : D.host.E →+* D.host.E) (M r a) = starRingEnd D.host.E (M r a)` using `rfl`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_entry {D : D7} (V : HSp D) {i j : ℕ} (M : Matrix (Fin V.rank) (Fin i) D.host.E)
    (N : Matrix (Fin V.rank) (Fin j) D.host.E) (a : Fin i) (b : Fin j) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N) a b = V.hT (colVec V M a) (colVec V N b) := by
  simp only [colVec, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, Matrix.mul_apply, Formalism.UG.cT, HSpace.gram, Matrix.transpose_apply, Matrix.map_apply,
    smul_eq_mul, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  have e : (D.sp.cm.sig : D.host.E →+* D.host.E) (M r a) = starRingEnd D.host.E (M r a) := rfl
  rw [e]
  ring

/- English proof (translation)
Apply `V.frame.equivFun.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `r`. Simplify using `[colVec, frameMat, LinearMap.toMatrix_apply]`.
-/
theorem colVec_frameMat {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (c : Fin V'.rank) :
    colVec V (frameMat V V' ι) c = ι (V'.frame c) := by
  apply V.frame.equivFun.injective
  funext r
  simp [colVec, frameMat, LinearMap.toMatrix_apply]

/- English proof (translation)
Rewrite using `[← V.herm.eq x y, h, map_zero]`.
-/
theorem hT_swap {D : D7} (V : HSp D) {x y : V.V} (h : V.hT x y = 0) : V.hT y x = 0 := by
  rw [← V.herm.eq x y, h, map_zero]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Apply `V'.nondeg.1` to reduce the goal to its premises. Introduce `y`. Rewrite using `[← h x y, hx]`.

Simplify using the standard rewrite rules.
-/
theorem isomEmb_injective {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (h : HSpace.IsIsomEmb V' V ι) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply V'.nondeg.1
  intro y
  rw [← h x y, hx]
  simp

/- English proof (translation)
Use `and_congr ?_ ⟨fun h a b => ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `(LinearMap.linearIndependent_iff_of_injOn V.frame.equivFun.symm.toLinearMap V.frame.equivFun.symm.injective.injOn).symm`. Rewrite using `[HSpace.hD, ← gram_entry, h]`. Both sides reduce to the same expression. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[gram_entry]`. Conclude with `h b a`.
-/
theorem isIsoSub_iff {D : D7} (V : HSp D) {i : ℕ} (C : Matrix (Fin V.rank) (Fin i) D.host.E) :
    IsIsoSub V C ↔ LinearIndependent D.host.E (colVec V C) ∧ ∀ a b, V.hD (colVec V C a) (colVec V C b) = 0 := by
  refine and_congr ?_ ⟨fun h a b => ?_, fun h => ?_⟩
  · exact (LinearMap.linearIndependent_iff_of_injOn V.frame.equivFun.symm.toLinearMap
      V.frame.equivFun.symm.injective.injOn).symm
  · rw [HSpace.hD, ← gram_entry, h]; rfl
  · refine Matrix.ext fun a b => ?_
    rw [gram_entry]
    exact h b a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `h a _ ⟨x, rfl⟩`. Apply `hT_swap` to reduce the goal to its premises. Establish `e : (V.hT (colVec V C a)).comp ι = 0` using `V'.frame.ext fun c => by`. Apply the tactic sequence `have h1 := gram_entry V (frameMat V V' ι) C c a`.

Rewrite `h1` using `[h, colVec_frameMat]`. Conclude with `hT_swap V h1.symm`. Conclude with `LinearMap.congr_fun e x`. Introduce `h`. Use `Matrix.ext fun c a => ?_` and prove the remaining obligations.

Rewrite using `[gram_entry, colVec_frameMat]`. Conclude with `h a _ ⟨_, rfl⟩`.
-/
theorem orth_iff {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {i : ℕ}
    (C : Matrix (Fin V.rank) (Fin i) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * C = 0 ↔
      ∀ a, ∀ x ∈ LinearMap.range ι, V.hT x (colVec V C a) = 0 := by
  constructor
  · rintro h a _ ⟨x, rfl⟩
    apply hT_swap
    have e : (V.hT (colVec V C a)).comp ι = 0 := V'.frame.ext fun c => by
      have h1 := gram_entry V (frameMat V V' ι) C c a
      rw [h, colVec_frameMat] at h1
      exact hT_swap V h1.symm
    exact LinearMap.congr_fun e x
  · intro h
    refine Matrix.ext fun c a => ?_
    rw [gram_entry, colVec_frameMat]
    exact h a _ ⟨_, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hr, ι, hι, C, hC, hO⟩`. Take `⟨h1, h2⟩` from `(isIsoSub_iff V C).1 hC`. Establish `h3` using `(orth_iff V V' ι C).1 hO`. Establish `hW : ∀ x ∈ LinearMap.range ι, (∀ y ∈ LinearMap.range ι, V.hT x y = 0) → x = 0`.

Introduce and unpack `_ ⟨x, rfl⟩ hx`. Rewrite using `[V'.nondeg.1 x fun y => (hι x y).symm.trans (hx _ ⟨y, rfl⟩), map_zero]`. Take `⟨f, f1, f2, f3, f4⟩` from `GlobalTheory.T.exists_hyperbolic_dual_family_of_finrank_add_two_mul D.host.E V.V V.hT V.herm V.nondeg (LinearMap.range ι) hW i (colVec V C) h1 (fun a b => h2 b a) h3 (by rw [LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq, hr])`. Use `⟨ι, colVec V C, f, hι, h2, fun a b => f1 b a, fun a b => ?_, fun a x => ⟨?_, ?_⟩, f4⟩` and prove the remaining obligations. Rewrite using `[HSpace.hD, f2 b a]`.

Simplify using `only [eq_comm]`. Conclude with `hT_swap V (h3 a _ ⟨x, rfl⟩)`. Conclude with `hT_swap V (f3 a _ ⟨x, rfl⟩)`. Introduce and unpack `⟨ι, e, f, hι, h1, h2, h3, h4, h5⟩`. Take `⟨k1, k2⟩` from `GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic D.host.E V.V V.hT V.herm (LinearMap.range ι) i e f (fun a b => h1 b a) (fun a b => h2 b a) (fun a b => by`.

Establish `h6` using `h3 b a`. Rewrite `h6` using `[HSpace.hD]`. Rewrite using `[h6]`. Simplify using `only [eq_comm])`. Use the proof step `(by`.

Introduce and unpack `a _ ⟨x, rfl⟩`. Conclude with `⟨hT_swap V (h4 a x).1, hT_swap V (h4 a x).2⟩) h5`. Establish `hc : colVec V (Matrix.of fun r a => V.frame.equivFun (e a) r) = e`. Use function extensionality and compare the values at `fun a => V.frame.equivFun.symm_apply_apply (e a)`. Use `⟨?_, ι, hι, Matrix.of fun r a => V.frame.equivFun (e a) r, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `k2` using `[LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq]`. Then use the resulting hypothesis. Rewrite using `[isIsoSub_iff, hc]`. Conclude with `⟨k1, h1⟩`. Rewrite using `[orth_iff, hc]`. Introduce and unpack `a _ ⟨x, rfl⟩`.

Conclude with `hT_swap V (h4 a x).1`.
-/
theorem isWittLower_iff {D : D7} (V V' : HSp D) (i : ℕ) : IsWittLower V V' i ↔ UnitaryVolumePairs.IsMinusHyp V i V' := by
  constructor
  · rintro ⟨hr, ι, hι, C, hC, hO⟩
    obtain ⟨h1, h2⟩ := (isIsoSub_iff V C).1 hC
    have h3 := (orth_iff V V' ι C).1 hO
    have hW : ∀ x ∈ LinearMap.range ι, (∀ y ∈ LinearMap.range ι, V.hT x y = 0) → x = 0 := by
      rintro _ ⟨x, rfl⟩ hx
      rw [V'.nondeg.1 x fun y => (hι x y).symm.trans (hx _ ⟨y, rfl⟩), map_zero]
    obtain ⟨f, f1, f2, f3, f4⟩ := GlobalTheory.T.exists_hyperbolic_dual_family_of_finrank_add_two_mul D.host.E V.V V.hT V.herm V.nondeg (LinearMap.range ι) hW i
      (colVec V C) h1 (fun a b => h2 b a) h3
      (by rw [LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq, hr])
    refine ⟨ι, colVec V C, f, hι, h2, fun a b => f1 b a, fun a b => ?_, fun a x => ⟨?_, ?_⟩, f4⟩
    · rw [HSpace.hD, f2 b a]
      simp only [eq_comm]
    · exact hT_swap V (h3 a _ ⟨x, rfl⟩)
    · exact hT_swap V (f3 a _ ⟨x, rfl⟩)
  · rintro ⟨ι, e, f, hι, h1, h2, h3, h4, h5⟩
    obtain ⟨k1, k2⟩ := GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic D.host.E V.V V.hT V.herm (LinearMap.range ι) i e f (fun a b => h1 b a)
      (fun a b => h2 b a) (fun a b => by
        have h6 := h3 b a
        rw [HSpace.hD] at h6
        rw [h6]
        simp only [eq_comm])
      (by
        rintro a _ ⟨x, rfl⟩
        exact ⟨hT_swap V (h4 a x).1, hT_swap V (h4 a x).2⟩) h5
    have hc : colVec V (Matrix.of fun r a => V.frame.equivFun (e a) r) = e :=
      funext fun a => V.frame.equivFun.symm_apply_apply (e a)
    refine ⟨?_, ι, hι, Matrix.of fun r a => V.frame.equivFun (e a) r, ?_, ?_⟩
    · rwa [LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq] at k2
    · rw [isIsoSub_iff, hc]
      exact ⟨k1, h1⟩
    · rw [orth_iff, hc]
      rintro a _ ⟨x, rfl⟩
      exact hT_swap V (h4 a x).1

/- English proof (translation)
Establish `h1 : ε * (1 - ε) = 0` using `by linear_combination -hε`. Establish `h2 : (1 - ε) * ε = 0` using `by linear_combination -hε`. Establish `h3 : (1 - ε) * (1 - ε) = 1 - ε` using `by linear_combination hε`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3, zero_smul, add_zero, zero_add]`.
-/
theorem idem_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {ε : A} (hε : ε * ε = ε)
    (X Y X' Y' : Matrix n n A) :
    (ε • X + (1 - ε) • Y) * (ε • X' + (1 - ε) • Y') = ε • (X * X') + (1 - ε) • (Y * Y') := by
  have h1 : ε * (1 - ε) = 0 := by linear_combination -hε
  have h2 : (1 - ε) * ε = 0 := by linear_combination -hε
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
    zero_smul, add_zero, zero_add]

/- English proof (translation)
Establish `hs : ∀ X : Matrix n n A, ε • X + (1 - ε) • X = X` using `fun X => by rw [← add_smul]; simp`. Use `⟨⟨ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A), ε • (1 : Matrix n n A) + (1 - ε) • ((h⁻¹ : GL n A) : Matrix n n A), ?_, ?_⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[idem_mul hε, Units.mul_inv, mul_one, hs]`. Rewrite using `[idem_mul hε, Units.inv_mul, mul_one, hs]`. Establish `hc : Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) = ε • (1 : Matrix n n A) + (1 - ε) • Formalism.UG.cT σ (h : Matrix n n A)`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using `[Formalism.UG.cT, hσ]`. Simplify using `[Formalism.UG.cT, hσ, Matrix.one_apply_ne e, Matrix.one_apply_ne' e]`.

Use `show Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) * J * (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) = J`. Establish `hh' : Formalism.UG.cT σ (h : Matrix n n A) * J * (h : Matrix n n A) = J` using `hh`. Rewrite using `[hc]`. Use `nth_rewrite 1 [← hs J]`. Rewrite using `[idem_mul hε, idem_mul hε, hh', one_mul, mul_one, hs]`.
-/
theorem exists_cut {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (J : Matrix n n A)
    {ε : A} (hε : ε * ε = ε) (hσ : σ ε = ε) (h : GL n A) (hh : h ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, (k : Matrix n n A) = ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A) := by
  have hs : ∀ X : Matrix n n A, ε • X + (1 - ε) • X = X := fun X => by rw [← add_smul]; simp
  refine ⟨⟨ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A),
    ε • (1 : Matrix n n A) + (1 - ε) • ((h⁻¹ : GL n A) : Matrix n n A), ?_, ?_⟩, ?_, rfl⟩
  · rw [idem_mul hε, Units.mul_inv, mul_one, hs]
  · rw [idem_mul hε, Units.inv_mul, mul_one, hs]
  · have hc : Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) =
        ε • (1 : Matrix n n A) + (1 - ε) • Formalism.UG.cT σ (h : Matrix n n A) := by
      refine Matrix.ext fun i j => ?_
      by_cases e : i = j
      · subst e; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne e, Matrix.one_apply_ne' e]
    show Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) * J *
      (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) = J
    have hh' : Formalism.UG.cT σ (h : Matrix n n A) * J * (h : Matrix n n A) = J := hh
    rw [hc]
    nth_rewrite 1 [← hs J]
    rw [idem_mul hε, idem_mul hε, hh', one_mul, mul_one, hs]

/- English proof (translation)
Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using `[h]`. Simplify using `[h, Matrix.one_apply_ne e]`.
-/
theorem map_cut_one {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (φ : A →+* B) {ε : A}
    (h : φ ε = 1) (X : Matrix n n A) (i j : n) :
    φ ((ε • (1 : Matrix n n A) + (1 - ε) • X) i j) = (1 : Matrix n n B) i j := by
  by_cases e : i = j
  · subst e; simp [h]
  · simp [h, Matrix.one_apply_ne e]

/- English proof (translation)
Simplify using `[h]`.
-/
theorem map_cut_zero {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (φ : A →+* B) {ε : A}
    (h : φ ε = 0) (X : Matrix n n A) (i j : n) :
    φ ((ε • (1 : Matrix n n A) + (1 - ε) • X) i j) = φ (X i j) := by
  simp [h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finMat_eq {D : D7} (V : HSp D) (h : GA D V) : finMat D.sp.cm.sig V.gram h = (finHom V h).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    infMat D.sp.cm.sig V.gram θ h = ((infHom V h).1).map θ := rfl

/- English proof (translation)
Set `ε : AE D` to `pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)`. Establish `hε : ε * ε = ε`. Simplify using `only [ε, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `congr 1`. Conclude with `Prod.ext (mul_one _) (mul_zero _)`.

Establish `hσ : sigR (AF D.host.F) D.sp.cm.sig ε = ε` using `by simp [ε, sigR]`. Establish `hi : infPart D ε = 1`. Simplify using `only [ε, infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Both sides reduce to the same expression. Establish `hf : finPart D ε = 0`.

Simplify using `only [ε, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Conclude with `TensorProduct.zero_tmul _ _`. Take `⟨k, hk, e⟩` from `exists_cut (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram) hε hσ (matHom V h) h.2`. Use `⟨⟨k, hk⟩, Units.ext (Matrix.ext fun i j => ?_), Units.ext (Matrix.ext fun i j => ?_)⟩` and prove the remaining obligations. Use `show infPart D (k.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j`.

Rewrite using `[e]`. Conclude with `map_cut_one (infPart D) hi _ i j`. Use `show finPart D (k.1 i j) = finPart D ((matHom V h).1 i j)`. Rewrite using `[e]`. Conclude with `map_cut_zero (finPart D) hf _ i j`.
-/
theorem exists_finite_part {D : D7} (V : HSp D) (h : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V h := by
  let ε : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hε : ε * ε = ε := by
    simp only [ε, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_one _) (mul_zero _)
  have hσ : sigR (AF D.host.F) D.sp.cm.sig ε = ε := by simp [ε, sigR]
  have hi : infPart D ε = 1 := by
    simp only [ε, infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hf : finPart D ε = 0 := by
    simp only [ε, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact TensorProduct.zero_tmul _ _
  obtain ⟨k, hk, e⟩ := exists_cut (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram) hε hσ (matHom V h) h.2
  refine ⟨⟨k, hk⟩, Units.ext (Matrix.ext fun i j => ?_), Units.ext (Matrix.ext fun i j => ?_)⟩
  · show infPart D (k.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
    rw [e]
    exact map_cut_one (infPart D) hi _ i j
  · show finPart D (k.1 i j) = finPart D ((matHom V h).1 i j)
    rw [e]
    exact map_cut_zero (finPart D) hf _ i j

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, ⟨hk, hl, -⟩, g, hg, rfl, hb⟩`. Establish `e1 : finHom V (k * g) = finHom V k` using `by rw [map_mul, show finHom V g = 1 from hg, mul_one]`. Establish `e2 : infHom V (k * g) = infHom V g` using `by rw [map_mul, show infHom V k = 1 from hk, one_mul]`.

Use `⟨fun y => ?_, fun ρ => ?_⟩` and prove the remaining obligations. Rewrite using `[finMat_eq, e1]`. Conclude with `hl y`. Rewrite using `[infMat_eq, e2]`. Conclude with `hb ρ`.

Introduce and unpack `⟨hl, hb⟩`. Take `⟨k, hk, e⟩` from `exists_finite_part V h`. Use `⟨k, ⟨hk, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, k⁻¹ * h, ?_, by group, fun ρ => ?_⟩` and prove the remaining obligations. Rewrite using `[finMat_eq, e]`. Conclude with `hl y`.

Use `show finHom V (k⁻¹ * h) = 1`. Rewrite using `[map_mul, map_inv, e, inv_mul_cancel]`. Rewrite using `[infMat_eq, map_mul, map_inv, show infHom V k = 1 from hk, inv_one, one_mul]`. Conclude with `hb ρ`.
-/
theorem volBox_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (B : D.what₂.Tau → Set (UpqT P Q)) :
    UnitaryVolumePairs.volBox θ V A B = {h : GA D V | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
                       (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
  ext h
  constructor
  · rintro ⟨k, ⟨hk, hl, -⟩, g, hg, rfl, hb⟩
    have e1 : finHom V (k * g) = finHom V k := by rw [map_mul, show finHom V g = 1 from hg, mul_one]
    have e2 : infHom V (k * g) = infHom V g := by rw [map_mul, show infHom V k = 1 from hk, one_mul]
    refine ⟨fun y => ?_, fun ρ => ?_⟩
    · rw [finMat_eq, e1]; exact hl y
    · rw [infMat_eq, e2]; exact hb ρ
  · rintro ⟨hl, hb⟩
    obtain ⟨k, hk, e⟩ := exists_finite_part V h
    refine ⟨k, ⟨hk, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, k⁻¹ * h, ?_, by group, fun ρ => ?_⟩
    · rw [finMat_eq, e]; exact hl y
    · show finHom V (k⁻¹ * h) = 1
      rw [map_mul, map_inv, e, inv_mul_cancel]
    · rw [infMat_eq, map_mul, map_inv, show infHom V k = 1 from hk, inv_one, one_mul]
      exact hb ρ

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, e⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hv` to reduce the goal to its premises. Establish `h1 : V.frame.equivFun.symm v = 0` using `V.nondeg.2 _ fun x => by`. Apply `hT_swap` to reduce the goal to its premises.

Establish `e2 : V.hT (V.frame.equivFun.symm v) = 0` using `V.frame.ext fun c => by`. Apply `hT_swap` to reduce the goal to its premises. Establish `h2` using `congrFun e c`. Simplify `h2` using `[Matrix.mulVec, dotProduct, HSpace.gram, Module.Basis.equivFun_symm_apply, mul_comm]`. Rewrite using `[e2]`.

Both sides reduce to the same expression. Conclude with `V.frame.equivFun.symm.map_eq_zero_iff.1 h1`.
-/
theorem gram_det_ne_zero {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := V.nondeg.2 _ fun x => by
    apply hT_swap
    have e2 : V.hT (V.frame.equivFun.symm v) = 0 := V.frame.ext fun c => by
      apply hT_swap
      have h2 := congrFun e c
      simpa [Matrix.mulVec, dotProduct, HSpace.gram, Module.Basis.equivFun_symm_apply, mul_comm] using h2
    rw [e2]; rfl
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

/- English proof (translation)
Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.2 hG`. Establish `e : Fin n ≃ Fin P ⊕ Fin Q` using `(finCongr hn.symm).trans finSumFinEquiv.symm`. Establish `hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ, Xᴴ * Formalism.UG.Jpq P Q * X = G → (G⁻¹ * Xᴴ * Formalism.UG.Jpq P Q) * X = 1` using `fun X hX => by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX, Matrix.nonsing_inv_mul _ hu]`. Use `set L := G⁻¹ * Aᴴ * Formalism.UG.Jpq P Q`.

Use `set L' := G⁻¹ * A'ᴴ * Formalism.UG.Jpq P Q`. Establish `l1 : L * A = 1` using `hl A hA`. Establish `l2 : L' * A' = 1` using `hl A' hA'`. Establish `r1 : A * L = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 l1`. Establish `r2 : A' * L' = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 l2`.

Use `⟨(⟨⟨A' * L, A * L', ?_, ?_⟩, ?_⟩ : Formalism.UG.Upq P Q), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc L, l1, Matrix.one_mul, r2]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc L', l2, Matrix.one_mul, r1]`. Use `show (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by`. Rewrite using `[hA', ← hA, Matrix.conjTranspose_mul A L]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [r1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Use `show A' = A' * L * A`. Rewrite using `[Matrix.mul_assoc, l1, Matrix.mul_one]`.
-/
theorem exists_change {P Q n : ℕ} (hn : P + Q = n) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.det ≠ 0)
    (A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G)
    (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) : ∃ u : UpqT P Q, A' = UpqT.mat u * A := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have e : Fin n ≃ Fin P ⊕ Fin Q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ, Xᴴ * Formalism.UG.Jpq P Q * X = G →
      (G⁻¹ * Xᴴ * Formalism.UG.Jpq P Q) * X = 1 := fun X hX => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX, Matrix.nonsing_inv_mul _ hu]
  set L := G⁻¹ * Aᴴ * Formalism.UG.Jpq P Q
  set L' := G⁻¹ * A'ᴴ * Formalism.UG.Jpq P Q
  have l1 : L * A = 1 := hl A hA
  have l2 : L' * A' = 1 := hl A' hA'
  have r1 : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 l1
  have r2 : A' * L' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 l2
  refine ⟨(⟨⟨A' * L, A * L', ?_, ?_⟩, ?_⟩ : Formalism.UG.Upq P Q), ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, l1, Matrix.one_mul, r2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L', l2, Matrix.one_mul, r1]
  · show (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q
    calc (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
          rw [hA', ← hA, Matrix.conjTranspose_mul A L]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [r1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · show A' = A' * L * A
    rw [Matrix.mul_assoc, l1, Matrix.mul_one]

/- English proof (translation)
Use `haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))`. Use `haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩`. Use `infer_instance`.
-/
theorem measurableMul_UpqT (P Q : ℕ) : MeasurableMul (UpqT P Q) := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  infer_instance

/- English proof (translation)
Establish `hG : ∀ ρ, (gramAt D V ρ).det ≠ 0` using `fun ρ => by`. Establish `e` using `(tauE D ρ).map_det V.gram`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[gramAt, ← e]`. Conclude with `(map_ne_zero _).2 (gram_det_ne_zero V)`.

Use `choose u hu using fun ρ => exists_change hA.1 _ (hG ρ) (A ρ) (A' ρ) (hA.2 ρ) (hA'.2 ρ)`. Use `haveI := measurableMul_UpqT P Q`. Use `haveI := D.cd.haar P Q`. Use `haveI := GlobalTheory.T.haar_upq_is_mul_right_invariant P Q (D.cd.cd P Q) (D.cd.haar P Q)`. Introduce `B hB`.

Establish `hm : ∀ ρ, MeasurableSet ((fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ))` using `fun ρ => measurable_mul_const _ (measurable_const_mul _ (hB ρ))`. Establish `h1` using `h _ hm`. Simplify using `only [measure_preimage_mul_right, measure_preimage_mul] at h1`. Rewrite using `[← h1]`. Use `congr 1`.

Establish `key : ∀ ρ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), (∃ b ∈ B ρ, UpqT.mat b * A' ρ = A' ρ * g) ↔ ∃ b ∈ (fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ), UpqT.mat b * A ρ = A ρ * g` using `fun ρ g => by`. Establish `e2 : UpqT.mat (u ρ)⁻¹ * UpqT.mat (u ρ) = 1`. Rewrite using `[← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, e⟩`.

Use `⟨(u ρ)⁻¹ * b * u ρ, by simpa [mul_assoc] using hb, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Matrix.mul_assoc, ← hu ρ, Matrix.mul_assoc, e, hu ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]`. Introduce and unpack `⟨b, hb, e⟩`. Use `⟨_, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, hu ρ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (UpqT.mat (u ρ)⁻¹), e2, Matrix.one_mul, e, Matrix.mul_assoc]`.

Simplify using `only [UnitaryVolumePairs.volBox, key]`.
-/
theorem isProductForm_change {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    {P Q : ℕ} {A A' : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ} (hA : UnitaryVolumePairs.IsRealFrames V P Q A)
    (hA' : UnitaryVolumePairs.IsRealFrames V P Q A') {μ : Measure (GA D V)} (h : UnitaryVolumePairs.IsProductForm θ V A μ) :
    UnitaryVolumePairs.IsProductForm θ V A' μ := by
  have hG : ∀ ρ, (gramAt D V ρ).det ≠ 0 := fun ρ => by
    have e := (tauE D ρ).map_det V.gram
    rw [RingHom.mapMatrix_apply] at e
    rw [gramAt, ← e]
    exact (map_ne_zero _).2 (gram_det_ne_zero V)
  choose u hu using fun ρ => exists_change hA.1 _ (hG ρ) (A ρ) (A' ρ) (hA.2 ρ) (hA'.2 ρ)
  haveI := measurableMul_UpqT P Q
  haveI := D.cd.haar P Q
  haveI := GlobalTheory.T.haar_upq_is_mul_right_invariant P Q (D.cd.cd P Q) (D.cd.haar P Q)
  intro B hB
  have hm : ∀ ρ, MeasurableSet ((fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ)) := fun ρ =>
    measurable_mul_const _ (measurable_const_mul _ (hB ρ))
  have h1 := h _ hm
  simp only [measure_preimage_mul_right, measure_preimage_mul] at h1
  rw [← h1]
  congr 1
  have key : ∀ ρ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), (∃ b ∈ B ρ, UpqT.mat b * A' ρ = A' ρ * g) ↔
      ∃ b ∈ (fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ), UpqT.mat b * A ρ = A ρ * g := fun ρ g => by
    have e2 : UpqT.mat (u ρ)⁻¹ * UpqT.mat (u ρ) = 1 := by
      rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_one]
    constructor
    · rintro ⟨b, hb, e⟩
      refine ⟨(u ρ)⁻¹ * b * u ρ, by simpa [mul_assoc] using hb, ?_⟩
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Matrix.mul_assoc, ← hu ρ,
        Matrix.mul_assoc, e, hu ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    · rintro ⟨b, hb, e⟩
      refine ⟨_, hb, ?_⟩
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, hu ρ, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Matrix.mul_assoc (UpqT.mat (u ρ)⁻¹), e2, Matrix.one_mul, e, Matrix.mul_assoc]
  simp only [UnitaryVolumePairs.volBox, key]

/- English proof (translation)
Unfold `IsVolMeasG UnitaryVolumePairs.IsVolMeasure`. Rewrite using `[allSome_infFam_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hr, hμ, θ, hθ, ⟨A, hA⟩, h⟩`. Use `⟨hμ, θ, hθ, A, ⟨hr, hA⟩, fun B hB => ?_⟩` and prove the remaining obligations.

Rewrite using `[volBox_eq]`. Conclude with `h A hA B hB`. Introduce and unpack `⟨hμ, θ, hθ, A, hA, h⟩`. Use `⟨hA.1, hμ, θ, hθ, ⟨A, hA.2⟩, fun A' hA' B hB => ?_⟩` and prove the remaining obligations. Establish `h1` using `isProductForm_change θ V hA ⟨hA.1, hA'⟩ h B hB`.

Rewrite `h1` using `[volBox_eq]`. Conclude with `h1`.
-/
theorem isVolMeasG_iff {D : D7} (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)) :
    P + Q = V.rank ∧ IsVolMeasG D V (fun _ => P) (fun _ => Q) μ ↔ UnitaryVolumePairs.IsVolMeasure V P Q μ := by
  unfold IsVolMeasG UnitaryVolumePairs.IsVolMeasure
  rw [allSome_infFam_iff]
  constructor
  · rintro ⟨hr, hμ, θ, hθ, ⟨A, hA⟩, h⟩
    refine ⟨hμ, θ, hθ, A, ⟨hr, hA⟩, fun B hB => ?_⟩
    rw [volBox_eq]
    exact h A hA B hB
  · rintro ⟨hμ, θ, hθ, A, hA, h⟩
    refine ⟨hA.1, hμ, θ, hθ, ⟨A, hA.2⟩, fun A' hA' B hB => ?_⟩
    have h1 := isProductForm_change θ V hA ⟨hA.1, hA'⟩ h B hB
    rw [volBox_eq] at h1
    exact h1

/- English proof (translation)
Take `⟨e, -⟩` from `h τ`. Simplify using `using (Fintype.card_congr e).symm`.
-/
theorem sig_add_of_sigOK {D : D7} {V : HSp D} (h : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).1 + (V.sig τ).2 = V.rank := by
  obtain ⟨e, -⟩ := h τ
  simpa using (Fintype.card_congr e).symm

/- English proof (translation)
Establish `hr : P + Q = V.rank` using `by simpa [h.2] using sig_add_of_sigOK h.1 D.host.φ₀`. Rewrite using `[← isVolMeasG_iff]`. Simplify using `only [h.2, hr, true_and]`.
-/
theorem isVolMeasG_iff_of_kind {D : D7} {V : HSp D} {P Q : ℕ} (h : UnitaryVolumePairs.IsOfKind V P Q) (μ : Measure (GA D V)) :
    IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ ↔
      UnitaryVolumePairs.IsVolMeasure V P Q μ := by
  have hr : P + Q = V.rank := by simpa [h.2] using sig_add_of_sigOK h.1 D.host.φ₀
  rw [← isVolMeasG_iff]
  simp only [h.2, hr, true_and]

/- English proof (translation)
The claim follows from `and_congr (isVolMeasG_iff_of_kind h μ) Iff.rfl`.
-/
theorem isVolPair_iff {D : D7} {V : HSp D} {P Q : ℕ} (h : UnitaryVolumePairs.IsOfKind V P Q) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) : IsVolPair D V μ 𝓕 ↔ UnitaryVolumePairs.IsVolPair V P Q μ 𝓕 :=
  and_congr (isVolMeasG_iff_of_kind h μ) Iff.rfl

/- English proof (translation)
Take `⟨i1, i2, i3⟩` from `GlobalTheory.T.lcsc_adelic_unitary_group D.host.F D.host.E D.sp.cm.sig V.rank V.gram`. Use `haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram`. Use `haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram`. Conclude with `h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure μ' μ)`.
-/
theorem isFundamentalDomain_of_haar {D : D7} (V : HSp D) {μ μ' : Measure (GA D V)} (h : μ.IsHaarMeasure)
    (h' : μ'.IsHaarMeasure) {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IsFundamentalDomain (GQ V) 𝓕 μ' := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.lcsc_adelic_unitary_group D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  exact h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure μ' μ)

def VolTieAt (D : D7) (W : HSp D) : Prop :=
  AllSome (IsVolMeasG D W (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2)) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (GQ W) 𝓕 μ) fun 𝓕 => μ 𝓕 = ENNReal.ofReal (D.vol W)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h V P Q hk`. Take `⟨⟨μ, hμ⟩, h1⟩` from `h V hk.1 ⟨_, hk.2⟩`. Take `⟨⟨𝓕, h𝓕⟩, -⟩` from `h1 μ hμ`. Use `⟨⟨μ, 𝓕, (isVolPair_iff hk μ 𝓕).1 ⟨hμ, h𝓕⟩⟩, fun μ' 𝓕' h' => ?_⟩` and prove the remaining obligations.

Take `⟨h2, h3⟩` from `(isVolPair_iff hk μ' 𝓕').2 h'`. Conclude with `(h1 μ' h2).2 𝓕' h3`. Introduce and unpack `h V hV ⟨⟨P, Q⟩, hs⟩`. Establish `hk : UnitaryVolumePairs.IsOfKind V P Q` using `⟨hV, hs⟩`. Take `⟨⟨μ, 𝓕, h0⟩, h1⟩` from `h V P Q hk`.

Take `⟨h2, h3⟩` from `(isVolPair_iff hk μ 𝓕).2 h0`. Conclude with `⟨⟨μ, h2⟩, fun μ' h' => ⟨⟨𝓕, isFundamentalDomain_of_haar V h2.1 h'.1 h3⟩, fun 𝓕' h4 => h1 μ' 𝓕' ((isVolPair_iff hk μ' 𝓕').1 ⟨h', h4⟩)⟩⟩`.
-/
theorem volumeTie_iff_at (D : D7) :
    (∀ W : HSp D, W.SigOK → (∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) ↔ UnitaryVolumePairs.VolumeTie D := by
  constructor
  · intro h V P Q hk
    obtain ⟨⟨μ, hμ⟩, h1⟩ := h V hk.1 ⟨_, hk.2⟩
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := h1 μ hμ
    refine ⟨⟨μ, 𝓕, (isVolPair_iff hk μ 𝓕).1 ⟨hμ, h𝓕⟩⟩, fun μ' 𝓕' h' => ?_⟩
    obtain ⟨h2, h3⟩ := (isVolPair_iff hk μ' 𝓕').2 h'
    exact (h1 μ' h2).2 𝓕' h3
  · rintro h V hV ⟨⟨P, Q⟩, hs⟩
    have hk : UnitaryVolumePairs.IsOfKind V P Q := ⟨hV, hs⟩
    obtain ⟨⟨μ, 𝓕, h0⟩, h1⟩ := h V P Q hk
    obtain ⟨h2, h3⟩ := (isVolPair_iff hk μ 𝓕).2 h0
    exact ⟨⟨μ, h2⟩, fun μ' h' => ⟨⟨𝓕, isFundamentalDomain_of_haar V h2.1 h'.1 h3⟩,
      fun 𝓕' h4 => h1 μ' 𝓕' ((isVolPair_iff hk μ' 𝓕').1 ⟨h', h4⟩)⟩⟩

/- English proof (translation)
The claim follows from `(volumeTie_iff_at D).1 fun W hW _ => h W hW`.
-/
theorem volumeTie_of_volTieG (D : D7) (h : VolTieG D) : UnitaryVolumePairs.VolumeTie D :=
  (volumeTie_iff_at D).1 fun W hW _ => h W hW

/- English proof (translation)
Use `⟨fun h => ⟨volumeTie_of_volTieG D h, fun W hW _ => h W hW⟩, fun ⟨h1, h2⟩ W hW => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : ∃ s, ∀ τ, W.sig τ = s`. Conclude with `(volumeTie_iff_at D).2 h1 W hW hs`. Conclude with `h2 W hW hs`.
-/
theorem volTieG_iff (D : D7) : VolTieG D ↔
    UnitaryVolumePairs.VolumeTie D ∧ ∀ W : HSp D, W.SigOK → (¬ ∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W := by
  refine ⟨fun h => ⟨volumeTie_of_volTieG D h, fun W hW _ => h W hW⟩, fun ⟨h1, h2⟩ W hW => ?_⟩
  by_cases hs : ∃ s, ∀ τ, W.sig τ = s
  · exact (volumeTie_iff_at D).2 h1 W hW hs
  · exact h2 W hW hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun χ => ⟨isHeckeChar_iff D χ, hasInfExp_iff D χ, unramEverywhere_iff D χ, resEta_iff D χ⟩, fun η => ⟨isEta_iff_normGroup D η, isEta_unique_iff D η, fun h => isEta_iff_of_index_two D h η⟩, fun V _ C => isIsoSub_iff V C, isWittLower_iff, fun V P Q μ => …`.
-/
theorem compare (D : D7) :
    (AE D = UnitaryVolumePairs.AE D ∧ infPart D = UnitaryVolumePairs.infPart D ∧ finPart D = UnitaryVolumePairs.finPart D ∧ idF D = UnitaryVolumePairs.resF D ∧
      intAE D = UnitaryVolumePairs.intAfE D) ∧
    (∀ χ : (AE D)ˣ →* Circle, (IsHeckeChar D χ ↔ χ ∈ UnitaryVolumePairs.HeckeChar D) ∧
      (∀ τ a, HasInfExp D χ τ a ↔ UnitaryVolumePairs.HasExponent χ τ a) ∧
      (UnramEverywhere D χ ↔ UnitaryVolumePairs.IsUnramified χ) ∧
      ∀ n, ResEta D χ n ↔ UnitaryVolumePairs.RestrictsToEtaPow χ n) ∧
    (∀ η : (AF D.host.F)ˣ →* Circle, (IsEta D η ↔ UnitaryVolumePairs.normGroup D ≤ η.ker ∧ η ≠ 1) ∧
      ((IsEta D η ∧ ∀ η', IsEta D η' → η' = η) ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a) ∧
      ((UnitaryVolumePairs.normGroup D).index = 2 → (IsEta D η ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a))) ∧
    (∀ (V : HSp D) (i : ℕ) (C : Matrix (Fin V.rank) (Fin i) D.host.E), IsIsoSub V C ↔
      LinearIndependent D.host.E (colVec V C) ∧ ∀ a b, V.hD (colVec V C a) (colVec V C b) = 0) ∧
    (∀ (V V' : HSp D) (i : ℕ), IsWittLower V V' i ↔ UnitaryVolumePairs.IsMinusHyp V i V') ∧
    (∀ (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)),
      (P + Q = V.rank ∧ IsVolMeasG D V (fun _ => P) (fun _ => Q) μ ↔ UnitaryVolumePairs.IsVolMeasure V P Q μ) ∧
      (UnitaryVolumePairs.IsOfKind V P Q → ∀ 𝓕, IsVolPair D V μ 𝓕 ↔ UnitaryVolumePairs.IsVolPair V P Q μ 𝓕)) ∧
    ((∀ W : HSp D, W.SigOK → (∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) ↔ UnitaryVolumePairs.VolumeTie D) ∧
    (VolTieG D ↔
      UnitaryVolumePairs.VolumeTie D ∧ ∀ W : HSp D, W.SigOK → (¬ ∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun χ => ⟨isHeckeChar_iff D χ, hasInfExp_iff D χ, unramEverywhere_iff D χ, resEta_iff D χ⟩,
    fun η => ⟨isEta_iff_normGroup D η, isEta_unique_iff D η, fun h => isEta_iff_of_index_two D h η⟩,
    fun V _ C => isIsoSub_iff V C, isWittLower_iff,
    fun V P Q μ => ⟨isVolMeasG_iff V P Q μ, fun h 𝓕 => isVolPair_iff h μ 𝓕⟩,
    volumeTie_iff_at D, volTieG_iff D⟩

end GlobalTheory.VolHeckeCompare

end
