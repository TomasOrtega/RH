import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `hT` using `GlobalTheory.thetaUnifAV_all`. Take `⟨g, ty, hfn⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H p q`. Take `⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩` from `hT T.pol T.t.PP.rig T.t.PP.rigGen`. Take `⟨D, Pe, F, hp, hq, hP, hF, hEF, hact⟩` from `GlobalTheory.CM.PureTriple.exists_datum_period hT GlobalTheory.firstFiveLaws.1 T hfn hty u hAH`. Use `⟨D, hp, hq, ?_, ?_⟩` and prove the remaining obligations.

Establish `hgg : g = T.g` using `by simpa using F.finrank_eq`. Set `j : Fin g` to `⟨0, by omega⟩`. Establish `: Nonempty {i // ty i = ty j}` using `⟨⟨j, rfl⟩⟩`. Establish `hc : 0 < Nat.card {i // ty i = ty j}` using `Nat.card_pos`. Distinguish the cases in `h : ty j (H.rt : E) = H.rt0`.

Use `(hfn _).1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `(hfn _).2 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨I, -⟩` from `GlobalTheory.UnifObj.exists_tateIso D D ty Pe (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c)) (fun z => u.ex (F z)) (fun _ => LinearMap.id) hP.1 hP.2.1 (fun z z' => by rw [map_add, u.ex_add]) (u.ex_onto. …`.

Establish `ha : F (Pe a) ∈ u.Λ` using `(hF _).2 ⟨a, rfl⟩`. Establish `hb : F (Pe b) ∈ u.Λ` using `(hF _).2 ⟨b, rfl⟩`. Establish `e : Ef ⟨_, ha⟩ ⟨_, hb⟩ = D.EF a b`. Use `(hE ⟨_, ha⟩ ⟨_, hb⟩).trans (hEF a b)` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Use `hW k ⟨_, ha⟩ ⟨_, hb⟩ c hk (by rw [e]; exact hc)` as an intermediate fact. Simplify using `only [map_smul]`. Conclude with `this)`. Use the proof step `(fun n m _ _ a => ⟨0, by simp⟩) (fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩)`. Use the proof step `(fun n _ a a' => by simp)`.

Conclude with `⟨I⟩`.
-/
theorem exists_datum_tate_complex (T : GlobalTheory.CM.PAT H (Sp ℂ)) (hg : 1 ≤ T.g) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hT := GlobalTheory.thetaUnifAV_all
  obtain ⟨g, ty, hfn⟩ := GlobalTheory.AllClasses.exists_isTypeFn H p q
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT T.pol T.t.PP.rig T.t.PP.rigGen
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hEF, hact⟩ :=
    GlobalTheory.CM.PureTriple.exists_datum_period hT GlobalTheory.firstFiveLaws.1 T hfn hty u hAH
  refine ⟨D, hp, hq, ?_, ?_⟩
  · have hgg : g = T.g := by simpa using F.finrank_eq
    let j : Fin g := ⟨0, by omega⟩
    have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
    have hc : 0 < Nat.card {i // ty i = ty j} := Nat.card_pos
    by_cases h : ty j (H.rt : E) = H.rt0
    · have := (hfn _).1 h
      omega
    · have := (hfn _).2 h
      omega
  · obtain ⟨I, -⟩ := GlobalTheory.UnifObj.exists_tateIso D D ty Pe (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))
      (fun z => u.ex (F z)) (fun _ => LinearMap.id) hP.1 hP.2.1 (fun z z' => by rw [map_add, u.ex_add])
      (u.ex_onto.comp F.surjective) (fun z => (u.ker _).trans (hF z)) hact
      (fun k a b c hk hc => by
        have ha : F (Pe a) ∈ u.Λ := (hF _).2 ⟨a, rfl⟩
        have hb : F (Pe b) ∈ u.Λ := (hF _).2 ⟨b, rfl⟩
        have e : Ef ⟨_, ha⟩ ⟨_, hb⟩ = D.EF a b := by
          have := (hE ⟨_, ha⟩ ⟨_, hb⟩).trans (hEF a b)
          exact_mod_cast this
        have := hW k ⟨_, ha⟩ ⟨_, hb⟩ c hk (by rw [e]; exact hc)
        simp only [map_smul]
        exact this)
      (fun n m _ _ a => ⟨0, by simp⟩) (fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩)
      (fun n _ a a' => by simp)
    exact ⟨I⟩

/- English proof (translation)
Set `F` to `Subfield.closure s`. Establish `hF : Countable F`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Use `(Subfield.cardinalMk_closure_le_max s).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Conclude with `Cardinal.mk_le_aleph0_iff.2 hs.to_subtype`.

Use `⟨(algebraicClosure F Ω).toSubfield, fun x hx => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(algebraicClosure F Ω).algebraMap_mem (⟨x, Subfield.subset_closure hx⟩ : F)`. Use `show Countable (algebraicClosure F Ω)`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Conclude with `(Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le Cardinal.mk_le_aleph0 le_rfl)`.

Use `show IsAlgClosed (algebraicClosure F Ω)`. Conclude with `IsAlgClosure.isAlgClosed F`.
-/
theorem exists_countable_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Set Ω) (hs : s.Countable) :
    ∃ K₀ : Subfield Ω, s ⊆ K₀ ∧ Countable K₀ ∧ IsAlgClosed K₀ := by
  let F := Subfield.closure s
  have hF : Countable F := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max s).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hs.to_subtype
  refine ⟨(algebraicClosure F Ω).toSubfield, fun x hx => ?_, ?_, ?_⟩
  · exact (algebraicClosure F Ω).algebraMap_mem (⟨x, Subfield.subset_closure hx⟩ : F)
  · show Countable (algebraicClosure F Ω)
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  · show IsAlgClosed (algebraicClosure F Ω)
    exact IsAlgClosure.isAlgClosed F

/- English proof (translation)
Establish `hL` using `GlobalTheory.firstFiveLaws.1`. Take `⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩` from `GlobalTheory.KeyCountableDescent.exists_polAV_descent hL Ω T.pol`. Use `P₁.isAb.proper` as an intermediate fact. Use `P₁.isAb.smooth` as an intermediate fact. Use `choose S hS using fun a : 𝓞 E => GlobalTheory.morphism_descends_to_subring Ω R₁ T.t.G.left P₁.A.left P₁.A.left T.t.G.hom P₁.A.hom P₁.A.hom j ((T.t.act.act a).left ≫ j) hG.1 (by`.

Establish `w : j ≫ P₁.A.hom = T.t.G.hom ≫ spMap R₁.subtype` using `hG.1.w`. Rewrite using `[Category.assoc, w, ← Category.assoc, Over.w])`. Establish `hcE : Countable (𝓞 E)` using `(RingOfIntegers.basis E).repr.injective.countable`. Take `⟨K₀, hsub, hcK, hK⟩` from `exists_countable_algClosed ((R₁ : Set Ω) ∪ ⋃ a, (S a : Set Ω)) ((Set.countable_coe_iff.1 hc₁).union (Set.countable_iUnion fun a => (S a).countable_toSet))`. Establish `h₁ : R₁ ≤ K₀.toSubring` using `fun x hx => hsub (Or.inl hx)`.

Set `f : R₁ →+* K₀` to `Subring.inclusion h₁`. Take `⟨P₂, π, hπ⟩` from `GlobalTheory.exists_isPolFibre hL.polBaseChange f P₁`. Take `⟨ψ, hψ, hψ'⟩` from `GlobalTheory.CM.EllComp.exists_isPolFibre_lift (g := K₀.subtype) (P'' := T.pol) (χ := j) hπ ⟨hgg, hG, hiso.symm⟩`. Establish `hψG : IsGrpPullback T.t.G P₂.A (spMap K₀.subtype) ψ` using `hψ'.2.1`. Establish `hfl` using `GlobalTheory.FieldBaseChange.flat_spMap K₀.subtype`.

Establish `hsj` using `GlobalTheory.FieldBaseChange.surjective_spMap K₀.subtype`. Take `⟨r, hr⟩` from `GlobalTheory.ActDescent.exists_oAct hψG T.t.act fun a => by`. Take `⟨b, b₁, b₂⟩` from `hS a K₀.toSubring h₁ (fun x hx => hsub (Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))) P₂.A.left P₂.A.hom π ψ hπ.2.1.1 hψ hψG.1.w`. Establish `w : b ≫ P₁.A.hom = P₂.A.hom ≫ spMap f` using `b₂.trans hπ.2.1.1.w`. Use `⟨Over.homMk (hπ.2.1.1.lift b _ w) (hπ.2.1.1.lift_snd _ _ _), hπ.2.1.1.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Use `show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ π`. Rewrite using `[Category.assoc, hψ, Category.assoc, IsPullback.lift_fst, b₁]`. Use `show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, IsPullback.lift_snd, hψG.1.w, ← Category.assoc, Over.w]`. Take `⟨τ₀, e, he, heL, heact⟩` from `GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ Ω K₀.subtype T.t P₂.A ψ P₂.L r P₂.isAb hψG P₂.isLB hψ'.2.2.symm hr`.

Establish `hE` using `isGrpPullback_of_iso e`. Take `⟨h₁', h₂, h₃⟩` from `GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ P₂.A τ₀.G _ _ P₂.L τ₀.PP.L P₂.isLB τ₀.PP.isLB P₂.isAb hE heL`. Establish `hs : Out.Sym τ₀.G τ₀.PP.L`. Take `⟨-, w, hw, -⟩` from `τ₀.sym`. Conclude with `fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩`.

Establish `hd : SmoothOfRelativeDimension P₂.g τ₀.G.hom`. Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} P₂.g` as an intermediate fact. Use the proof step `MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P₂.g) hE.1 P₂.smoothDim`. Establish `hinv : (ψ ≫ e.inv.left) ≫ e.hom.left = ψ`. Rewrite using `[Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]`.

Establish `: IsMonHom e.symm.hom` using `inferInstanceAs (IsMonHom e.inv)`. Use `⟨K₀, ⟨τ₀, h₁', P₂.g, hd, hs, h₂ P₂.ample, h₃ P₂.ktriv⟩, ψ ≫ e.inv.left, hcK, hK, hψ'.1.symm, (hψG.comp (isGrpPullback_of_iso e.symm)).congr (Category.comp_id _) rfl, ?_, fun a => ?_⟩` and prove the remaining obligations. Use `LBIso.trans T.t.PP.isLB (pull_isLB P₂.isLB ψ) (pull_isLB τ₀.PP.isLB _) hψ'.2.2.symm ?_` and prove the remaining obligations. Use `GlobalTheory.CM.EllComp.lbIso_pull_comp heL.symm (ψ ≫ e.inv.left)` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis.

Establish `e₁ : r.act a ≫ e.inv = e.inv ≫ τ₀.act.act a`. Rewrite using `[Iso.comp_inv_eq, Category.assoc, heact, Iso.inv_hom_id_assoc]`. Use `show _ = (ψ ≫ e.inv.left) ≫ (τ₀.act.act a).left`. Rewrite using `[← Category.assoc, hr, Category.assoc, Category.assoc, ← Over.comp_left, e₁, Over.comp_left]`.
-/
theorem exists_pat_descent {Ω : Type} [Field Ω] [IsAlgClosed Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) :
    ∃ (K₀ : Subfield Ω) (T₀ : GlobalTheory.CM.PAT H (Sp K₀)) (φ : T.t.G.left ⟶ T₀.t.G.left), Countable K₀ ∧ IsAlgClosed K₀ ∧
      T₀.g = T.g ∧ IsGrpPullback T.t.G T₀.t.G (spMap K₀.subtype) φ ∧ LBIso T.t.PP.L (T₀.t.PP.L.pull φ) ∧
      ∀ a, (T.t.act.act a).left ≫ φ = φ ≫ (T₀.t.act.act a).left := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩ := GlobalTheory.KeyCountableDescent.exists_polAV_descent hL Ω T.pol
  have := P₁.isAb.proper
  have := P₁.isAb.smooth
  choose S hS using fun a : 𝓞 E => GlobalTheory.morphism_descends_to_subring Ω R₁ T.t.G.left P₁.A.left P₁.A.left T.t.G.hom
    P₁.A.hom P₁.A.hom j ((T.t.act.act a).left ≫ j) hG.1 (by
      have w : j ≫ P₁.A.hom = T.t.G.hom ≫ spMap R₁.subtype := hG.1.w
      rw [Category.assoc, w, ← Category.assoc, Over.w])
  have hcE : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.injective.countable
  obtain ⟨K₀, hsub, hcK, hK⟩ := exists_countable_algClosed ((R₁ : Set Ω) ∪ ⋃ a, (S a : Set Ω))
    ((Set.countable_coe_iff.1 hc₁).union (Set.countable_iUnion fun a => (S a).countable_toSet))
  have h₁ : R₁ ≤ K₀.toSubring := fun x hx => hsub (Or.inl hx)
  let f : R₁ →+* K₀ := Subring.inclusion h₁
  obtain ⟨P₂, π, hπ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange f P₁
  obtain ⟨ψ, hψ, hψ'⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift (g := K₀.subtype) (P'' := T.pol) (χ := j) hπ
    ⟨hgg, hG, hiso.symm⟩
  have hψG : IsGrpPullback T.t.G P₂.A (spMap K₀.subtype) ψ := hψ'.2.1
  have hfl := GlobalTheory.FieldBaseChange.flat_spMap K₀.subtype
  have hsj := GlobalTheory.FieldBaseChange.surjective_spMap K₀.subtype
  obtain ⟨r, hr⟩ := GlobalTheory.ActDescent.exists_oAct hψG T.t.act fun a => by
    obtain ⟨b, b₁, b₂⟩ := hS a K₀.toSubring h₁ (fun x hx => hsub (Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))) P₂.A.left P₂.A.hom
      π ψ hπ.2.1.1 hψ hψG.1.w
    have w : b ≫ P₁.A.hom = P₂.A.hom ≫ spMap f := b₂.trans hπ.2.1.1.w
    refine ⟨Over.homMk (hπ.2.1.1.lift b _ w) (hπ.2.1.1.lift_snd _ _ _), hπ.2.1.1.hom_ext ?_ ?_⟩
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ π
      rw [Category.assoc, hψ, Category.assoc, IsPullback.lift_fst, b₁]
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ _
      rw [Category.assoc, Category.assoc, IsPullback.lift_snd, hψG.1.w, ← Category.assoc, Over.w]
  obtain ⟨τ₀, e, he, heL, heact⟩ := GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ Ω K₀.subtype T.t P₂.A ψ P₂.L r P₂.isAb
    hψG P₂.isLB hψ'.2.2.symm hr
  have hE := isGrpPullback_of_iso e
  obtain ⟨h₁', h₂, h₃⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ P₂.A τ₀.G _ _
    P₂.L τ₀.PP.L P₂.isLB τ₀.PP.isLB P₂.isAb hE heL
  have hs : Out.Sym τ₀.G τ₀.PP.L := by
    obtain ⟨-, w, hw, -⟩ := τ₀.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension P₂.g τ₀.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} P₂.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P₂.g) hE.1 P₂.smoothDim
  have hinv : (ψ ≫ e.inv.left) ≫ e.hom.left = ψ := by
    rw [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨K₀, ⟨τ₀, h₁', P₂.g, hd, hs, h₂ P₂.ample, h₃ P₂.ktriv⟩, ψ ≫ e.inv.left, hcK, hK, hψ'.1.symm,
    (hψG.comp (isGrpPullback_of_iso e.symm)).congr (Category.comp_id _) rfl, ?_, fun a => ?_⟩
  · refine LBIso.trans T.t.PP.isLB (pull_isLB P₂.isLB ψ) (pull_isLB τ₀.PP.isLB _) hψ'.2.2.symm ?_
    have := GlobalTheory.CM.EllComp.lbIso_pull_comp heL.symm (ψ ≫ e.inv.left)
    rwa [hinv] at this
  · have e₁ : r.act a ≫ e.inv = e.inv ≫ τ₀.act.act a := by
      rw [Iso.comp_inv_eq, Category.assoc, heact, Iso.inv_hom_id_assoc]
    show _ = (ψ ≫ e.inv.left) ≫ (τ₀.act.act a).left
    rw [← Category.assoc, hr, Category.assoc, Category.assoc, ← Over.comp_left, e₁, Over.comp_left]

/- English proof (translation)
Take `⟨σ⟩` from `GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K`. Establish `h : σ ρ ^ 2 = H.rt0 ^ 2` using `by rw [← map_pow, hρ, map_neg, map_natCast, H.sqrt_neg_disc_sq]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h` into its components or cases. Conclude with `⟨σ, h⟩`. Use `⟨(starRingEnd ℂ).comp σ, ?_⟩` and prove the remaining obligations.

Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h₁` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `h₂` using `congrArg Complex.im H.sqrt_neg_disc_sq`. Simplify using `[sq] at h₁ h₂`. Establish `hre : H.rt0.re = 0`.

Assume the negation of the conclusion as `hne`. Establish `: H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `h₁` using `[this]`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Rewrite using `[RingHom.comp_apply, h]`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
-/
theorem exists_embedding {K : Type} [Field K] [CharZero K] [Countable K] (ρ : K) (hρ : ρ ^ 2 = -(H.d : K)) :
    ∃ σ : K →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  have h : σ ρ ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, hρ, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ, ?_⟩
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have h₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h₁ h₂
    have hre : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at h₁
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

/- English proof (translation)
Establish `hL` using `GlobalTheory.firstFiveLaws.1`. Take `⟨K₀, T₀, φ, hc, hK, hgg, hG, hiso, hact⟩` from `exists_pat_descent T`. Choose the witnesses or unpack the hypotheses as in `⟨ρ₀, hρ₀, hρ₁⟩ : ∃ ρ₀ : K₀, ρ₀ ^ 2 = -(H.d : K₀) ∧ K₀.subtype ρ₀ = ρ := by`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (-(H.d : K₀)) two_pos`. Establish `h : K₀.subtype z ^ 2 = ρ ^ 2` using `by rw [← map_pow, hz, map_neg, map_natCast, hρ]`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h` into its components or cases. Conclude with `⟨z, hz, h⟩`. Conclude with `⟨-z, by rw [neg_sq, hz], by rw [map_neg, h, neg_neg]⟩`. Take `⟨σ, hσ⟩` from `exists_embedding ρ₀ hρ₀`. Take `⟨T₁, m, hg₁⟩` from `GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap σ) T₀`.

Establish `hsm` using `T₀.ab.smooth`. Establish `hm : LBIso T₁.t.PP.L (T₀.t.PP.L.pull m.φ)`. Take `⟨w, hw, -⟩` from `m.lin`. Conclude with `⟨w, hw⟩`. Establish `sq : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B), spMap f ≫ 𝟙 _ = 𝟙 _ ≫ spMap f` using `fun f => by simp`.

Establish `key : ∀ (τ : 𝓞 E →+* K₀) (n : ℕ), LieMult T₁.t.act (𝟙 _) (σ.comp τ) n ↔ LieMult T.t.act (𝟙 _) (K₀.subtype.comp τ) n` using `fun τ n => by`. Rewrite using `[GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T₁.t.act m.cart m.act, GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T.t.act hG hact, ← sq, ← sq, GlobalTheory.DetExtend.lieMult_extend, GlobalTheory.DetExtend.lieMult_extend]`. Take `⟨D, hp, hq, hpq, ⟨I₁⟩⟩` from `exists_datum_tate_complex T₁ (by omega) p q fun τ => by`. Take `⟨τ₀, rfl⟩` from `GlobalTheory.DetExtend.exists_factor σ τ`. Rewrite using `[key, key, ← hσ, RingHom.comp_apply]`.

Use `hty (K₀.subtype.comp τ₀)` as an intermediate fact. Rewrite `this` using `[← hρ₁, RingHom.comp_apply]`. Conclude with `⟨fun h => this.1 (congrArg _ (σ.injective h)), fun h => this.2 fun h' => h (congrArg _ (K₀.subtype.injective h'))⟩`. Use `⟨D, hp, hq, hpq, ?_⟩` and prove the remaining obligations. Take `⟨I₂, -⟩` from `(GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T₁.t.PP.isLB m.cart hm T₀.t.act.act T₁.t.act.act m.act _ _ (sq σ)).1 I₁`.

Take `⟨I₃, -⟩` from `(GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ ℂ σ (𝟙 _)).2 I₂ T₀.t.act.hom`. Take `⟨I₄, -⟩` from `(GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ Ω K₀.subtype (𝟙 _)).1 I₃`. Take `⟨I₅, -⟩` from `(GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T.t.PP.isLB hG hiso T₀.t.act.act T.t.act.act hact _ _ (sq K₀.subtype)).2 I₄`. Conclude with `⟨I₅⟩`.
-/
theorem exists_datum_tate {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) (hg : 1 ≤ T.g)
    (ρ : Ω) (hρ : ρ ^ 2 = -(H.d : Ω)) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* Ω, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ p) ∧ (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D Ω (Over.mk (𝟙 (Sp Ω)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨K₀, T₀, φ, hc, hK, hgg, hG, hiso, hact⟩ := exists_pat_descent T
  obtain ⟨ρ₀, hρ₀, hρ₁⟩ : ∃ ρ₀ : K₀, ρ₀ ^ 2 = -(H.d : K₀) ∧ K₀.subtype ρ₀ = ρ := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-(H.d : K₀)) two_pos
    have h : K₀.subtype z ^ 2 = ρ ^ 2 := by rw [← map_pow, hz, map_neg, map_natCast, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
    · exact ⟨z, hz, h⟩
    · exact ⟨-z, by rw [neg_sq, hz], by rw [map_neg, h, neg_neg]⟩
  obtain ⟨σ, hσ⟩ := exists_embedding ρ₀ hρ₀
  obtain ⟨T₁, m, hg₁⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap σ) T₀
  have hsm := T₀.ab.smooth
  have hm : LBIso T₁.t.PP.L (T₀.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have sq : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B), spMap f ≫ 𝟙 _ = 𝟙 _ ≫ spMap f := fun f => by simp
  have key : ∀ (τ : 𝓞 E →+* K₀) (n : ℕ), LieMult T₁.t.act (𝟙 _) (σ.comp τ) n ↔
      LieMult T.t.act (𝟙 _) (K₀.subtype.comp τ) n := fun τ n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T₁.t.act m.cart m.act,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T.t.act hG hact, ← sq, ← sq,
      GlobalTheory.DetExtend.lieMult_extend, GlobalTheory.DetExtend.lieMult_extend]
  obtain ⟨D, hp, hq, hpq, ⟨I₁⟩⟩ := exists_datum_tate_complex T₁ (by omega) p q fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.DetExtend.exists_factor σ τ
    rw [key, key, ← hσ, RingHom.comp_apply]
    have := hty (K₀.subtype.comp τ₀)
    rw [← hρ₁, RingHom.comp_apply] at this
    exact ⟨fun h => this.1 (congrArg _ (σ.injective h)), fun h => this.2 fun h' => h (congrArg _ (K₀.subtype.injective h'))⟩
  refine ⟨D, hp, hq, hpq, ?_⟩
  obtain ⟨I₂, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T₁.t.PP.isLB m.cart hm T₀.t.act.act T₁.t.act.act m.act
    _ _ (sq σ)).1 I₁
  obtain ⟨I₃, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ ℂ σ (𝟙 _)).2 I₂ T₀.t.act.hom
  obtain ⟨I₄, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ Ω K₀.subtype (𝟙 _)).1 I₃
  obtain ⟨I₅, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T.t.PP.isLB hG hiso T₀.t.act.act T.t.act.act hact
    _ _ (sq K₀.subtype)).2 I₄
  exact ⟨I₅⟩

end PositivityTheory.HtPt.Kftwo
