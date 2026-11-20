import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGenCurve

/- English proof (translation)
Assume the negation of the conclusion as `hl`. Establish `hm : (i ≫ p) z ∈ (Sp k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k))`. Rewrite using `[basicOpen_eq_of_affine]`. Conclude with `hl`. Use `(Scheme.preimage_basicOpen (i ≫ p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k))).le hm` as an intermediate fact.

Rewrite `this` using `[map_natCast, map_natCast]`. Use `erw [h, Scheme.basicOpen_zero] at this`. Conclude with `this`.
-/
theorem natCast_mem_asIdeal {k : Type} [CommRing k] {X Z : Scheme.{0}} (p : X ⟶ Sp k) (i : Z ⟶ X) (l : ℕ)
    (h : (l : Γ(Z, ⊤)) = 0) (z : Z) : (l : k) ∈ (p (i z)).asIdeal := by
  by_contra hl
  have hm : (i ≫ p) z ∈ (Sp k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k)) := by
    rw [basicOpen_eq_of_affine]
    exact hl
  have := (Scheme.preimage_basicOpen (i ≫ p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (l : k))).le hm
  rw [map_natCast, map_natCast] at this
  erw [h, Scheme.basicOpen_zero] at this
  exact this

/- English proof (translation)
Use `hX.finite` as an intermediate fact. Establish `: IsProper p` using `(isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1`. Take `⟨H, hH⟩` from `exists_isAmpleLB_of_isProjOver hX.isProjOver`. Establish `hA` using `hH.pull_of_isClosedImmersion i`. Establish `: IsFinite (spMap (Int.castRingHom k))`.

Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ))` using `by rw [e]; infer_instance`. Establish `: IsProper (strHom κ Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom κ))`.

Establish `h` using `(isNef_iff_isClosedImmersion.1 (hB.isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd (by rw [Category.id_comp]; infer_instance)`. Rewrite `h` using `[interNumOn_id]`. Use `h.trans_eq (congrArg _ (funext fun j => ?_))` and prove the remaining obligations. Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem topSelf_nonneg_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) {B : LB X} (hB : IsGenerated (B.pull i)) :
    0 ≤ topSelfIntersection κ (B.pull i) 1 := by
  have := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hB.isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

/- English proof (translation)
Rewrite using `[gs_eq (𝟙 X) x U hx]`. Conclude with `algebraMap_germ hx a`.
-/
theorem algebraMap_gs {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (gs (𝟙 X) x U a) = fnOf U (gen_mem hx) a := by
  rw [gs_eq (𝟙 X) x U hx]
  exact algebraMap_germ hx a

/- English proof (translation)
Set `O : V → Z.Opens` to `fun z => i ⁻¹ᵁ W z.1`. Set `a : ∀ z : V, Γ(Z, O z)` to `fun z => (i.app (W z.1)).hom (f z.1)`. Establish `ga : ∀ (z : V) (y : Z) (hy : y ∈ O z), gs (𝟙 Z) y (O z) (a z) = gs i y (W z.1) (f z.1)` using `fun z y hy => (gs_pull (𝟙 Z) i y _ hy _).trans (by rw [Category.id_comp])`. Establish `hcov : V ≤ iSup O` using `fun z hzV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hzV⟩, hz z hzV⟩`. Establish `hcomp : TopCat.Presheaf.IsCompatible Z.presheaf O a`.

Introduce `z₁ z₂`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

Establish `hyO : y ∈ O z₁ ⊓ O z₂` using `Z.basicOpen_le _ hy`. Establish `hu` using `(LBGerm.isUnit_gs_iff (𝟙 Z) y _ hyO _).2 hy`. Rewrite `hu` using `[LBGerm.gs_sub (𝟙 Z) y _ hyO]`. Use `erw [gs_res (𝟙 Z) y inf_le_left hyO, gs_res (𝟙 Z) y inf_le_right hyO] at hu`. Rewrite `hu` using `[ga z₁ y hyO.1, ga z₂ y hyO.2, gs_stalkMap i y _ hyO.1, gs_stalkMap i y _ hyO.2, ← map_sub, isUnit_map_iff]`.

Conclude with `hd z₁.1 z₁.2 z₂.1 z₂.2 y hyO.1 hyO.2 hu`. Take `⟨g, hg, -⟩` from `Z.sheaf.existsUnique_gluing' O V (fun z => homOfLE (hWV z.1 z.2)) hcov a hcomp`. Use `⟨g, fun z hzV => ?_⟩` and prove the remaining obligations. Establish `hzO : z ∈ O ⟨z, hzV⟩` using `hz z hzV`. Rewrite using `[← gs_res (𝟙 Z) z (hWV z hzV) hzO g]`.

Use `erw [hg ⟨z, hzV⟩]`. Conclude with `ga _ z hzO`.
-/
theorem exists_glue {X Z : Scheme.{0}} [IsReduced Z] (i : Z ⟶ X) (V : Z.Opens) (W : Z → X.Opens)
    (f : ∀ z, Γ(X, W z)) (hz : ∀ z ∈ V, i z ∈ W z) (hWV : ∀ z ∈ V, i ⁻¹ᵁ W z ≤ V)
    (hd : ∀ z₁ ∈ V, ∀ z₂ ∈ V, ∀ y : Z, ∀ (h₁ : i y ∈ W z₁) (h₂ : i y ∈ W z₂),
      ¬ IsUnit (gs (𝟙 X) (i y) (W z₁) (f z₁) - gs (𝟙 X) (i y) (W z₂) (f z₂))) :
    ∃ g : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V g = gs i z (W z) (f z) := by
  let O : V → Z.Opens := fun z => i ⁻¹ᵁ W z.1
  let a : ∀ z : V, Γ(Z, O z) := fun z => (i.app (W z.1)).hom (f z.1)
  have ga : ∀ (z : V) (y : Z) (hy : y ∈ O z), gs (𝟙 Z) y (O z) (a z) = gs i y (W z.1) (f z.1) := fun z y hy =>
    (gs_pull (𝟙 Z) i y _ hy _).trans (by rw [Category.id_comp])
  have hcov : V ≤ iSup O := fun z hzV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hzV⟩, hz z hzV⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.presheaf O a := by
    intro z₁ z₂
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    have hyO : y ∈ O z₁ ⊓ O z₂ := Z.basicOpen_le _ hy
    have hu := (LBGerm.isUnit_gs_iff (𝟙 Z) y _ hyO _).2 hy
    rw [LBGerm.gs_sub (𝟙 Z) y _ hyO] at hu
    erw [gs_res (𝟙 Z) y inf_le_left hyO, gs_res (𝟙 Z) y inf_le_right hyO] at hu
    rw [ga z₁ y hyO.1, ga z₂ y hyO.2, gs_stalkMap i y _ hyO.1, gs_stalkMap i y _ hyO.2, ← map_sub,
      isUnit_map_iff] at hu
    exact hd z₁.1 z₁.2 z₂.1 z₂.2 y hyO.1 hyO.2 hu
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' O V (fun z => homOfLE (hWV z.1 z.2)) hcov a hcomp
  refine ⟨g, fun z hzV => ?_⟩
  have hzO : z ∈ O ⟨z, hzV⟩ := hz z hzV
  rw [← gs_res (𝟙 Z) z (hWV z hzV) hzO g]
  erw [hg ⟨z, hzV⟩]
  exact ga _ z hzO

/- English proof (translation)
Introduce `k _ X _ p D hX L R hR l n U s hU hloc Z i _ _ κ _ _ _ _ hd`. Establish `hl0 : (l : Γ(Z, ⊤)) = 0`. Rewrite using `[← map_natCast (algebraMap κ Γ(Z, ⊤)), CharP.cast_eq_zero, map_zero]`. Establish `hZl : ∀ z, (l : k) ∈ (p (i z)).asIdeal` using `natCast_mem_asIdeal p i l hl0`. Establish `hdata : ∀ (a : L.B.ι) (J : Fin n) (z : Z), ∃ (W : X.Opens) (f : Γ(X, W)), W ≤ U (i z) ⊓ L.B.U a ∧ (i z ∈ L.B.U a → i z ∈ W) ∧ ∀ h, fnOf W h f = s (i z) J * R a`.

Introduce `a J z`. Distinguish the cases in `hz : i z ∈ L.B.U a`. Take `⟨W, hW, f, hf⟩` from `((hloc (i z) a (i z) (hU _) hz (hZl z)).1 J).exists_fnOf`. Use `⟨W ⊓ (U (i z) ⊓ L.B.U a), resG X inf_le_left f, inf_le_right, fun _ => ⟨hW, hU _, hz⟩, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[fnOf_resG, hf]`.

Conclude with `⟨⊥, 0, bot_le, fun h => (hz h).elim, fun h => absurd h (by simp)⟩`. Use `choose W f hW hWz hf using hdata`. Establish `hglue : ∀ (j : (L.B.pull i).ι) (J : Fin n), ∃ g : Γ(Z, (L.B.pull i).U j), ∀ z ∈ (L.B.pull i).U j, gs (𝟙 Z) z _ g = gs i z (W (j PUnit.unit) J z) (f (j PUnit.unit) J z)`. Introduce `j J`. Use `exists_glue i _ (fun z => W (j PUnit.unit) J z) (fun z => f (j PUnit.unit) J z) (fun z hz => hWz _ _ _ (mem_pull.1 hz)) (fun z _ y hy => mem_pull.2 (hW _ _ _ hy).2) (fun z₁ _ z₂ _ y h₁ h₂ hu => ?_)` and prove the remaining obligations.

Establish `m₁` using `hW _ _ _ h₁`. Establish `m₂` using `hW _ _ _ h₂`. Use `(hloc (i z₁) (j PUnit.unit) (i y) m₁.1 m₁.2 (hZl y)).2.2 (i z₂) m₂.1 J ⟨_, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, algebraMap_gs h₁, algebraMap_gs h₂, hf, hf, sub_mul]`. Use `choose g hg using hglue`.

Establish `hsec : ∀ (J : Fin n) (y : Z) (j j' : (L.B.pull i).ι), y ∈ (L.B.pull i).U j → y ∈ (L.B.pull i).U j' → gs (𝟙 Z) y _ (g j J) = (gm (𝟙 Z) y ((L.B.pull i).U j ⊓ (L.B.pull i).U j') ((L.B.pull i).g j j')).val * gs (𝟙 Z) y _ (g j' J)`. Introduce `J y j j' hj hj'`. Establish `ha` using `mem_pull.1 hj`. Establish `ha'` using `mem_pull.1 hj'`. Establish `hm : i y ∈ L.B.U (j PUnit.unit) ⊓ L.B.U (j' PUnit.unit)` using `⟨ha, ha'⟩`.

Rewrite using `[hg j J y hj, hg j' J y hj', gm_pull_g L.B i (𝟙 Z) y j j' hj hj', Category.id_comp, ← gs_unit i y _ hm, gs_stalkMap i y _ (hWz _ _ _ ha), gs_stalkMap i y _ (hWz _ _ _ ha'), gs_stalkMap i y _ hm, ← map_mul]`. Use `congr 1`. Apply `IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField` to reduce the goal to its premises. Rewrite using `[map_mul, algebraMap_gs (hWz _ _ _ ha), algebraMap_gs hm, algebraMap_gs (hWz _ _ _ ha'), hf, hf, hR _ _ (gen_mem hm)]`. Expand and normalize the polynomial expressions, which then agree.

Set `t : Fin n → (L.B.pull i).Sec` to `fun J => LBGerm.secOfGerm (fun j => g j J) (hsec J)`. Use `topSelf_nonneg_of_isGenerated hX i κ hd (isGenerated_of_finite t (top_le_iff.1 fun y _ => ?_))` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_chart L.isLB (i y)`. Take `⟨J, b, hb, e⟩` from `(hloc (i y) a (i y) (hU _) ha (hZl y)).2.1`. Establish `hy : y ∈ (L.B.pull i).U (fun _ => a)` using `mem_pull.2 ha`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨J, (mem_nonzeroLocus_iff_isUnit (t J) hy).2 ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsUnit (gs (𝟙 Z) y _ (g (fun _ => a) J))`. Rewrite using `[hg _ J y hy, gs_stalkMap i y _ (hWz _ _ _ ha)]`. Establish `hb' : b = gs (𝟙 X) (i y) _ (f a J y)` using `IsFractionRing.injective _ X.functionField (by rw [e, algebraMap_gs (hWz _ _ _ ha), hf])`. Conclude with `hb' ▸ hb.map _`.
-/
theorem nefOver_of_localGen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (R : L.B.ι → X.functionFieldˣ), IsRatSec L.B R → ∀ (l n : ℕ)
    (U : X → X.Opens) (s : X → Fin n → X.functionField), (∀ x, x ∈ U x) →
    (∀ (x : X) (i : L.B.ι) (x₀ : X), x₀ ∈ U x → x₀ ∈ L.B.U i → (l : k) ∈ (p x₀).asIdeal →
      (∀ J, RegAt x₀ (s x J * R i)) ∧ (∃ J, UnitAt x₀ (s x J * R i)) ∧
        ∀ x', x₀ ∈ U x' → ∀ J, ¬ UnitAt x₀ ((s x J - s x' J) * R i)) → NefOver L l := by
  intro k _ X _ p D hX L R hR l n U s hU hloc Z i _ _ κ _ _ _ _ hd
  have hl0 : (l : Γ(Z, ⊤)) = 0 := by
    rw [← map_natCast (algebraMap κ Γ(Z, ⊤)), CharP.cast_eq_zero, map_zero]
  have hZl : ∀ z, (l : k) ∈ (p (i z)).asIdeal := natCast_mem_asIdeal p i l hl0
  have hdata : ∀ (a : L.B.ι) (J : Fin n) (z : Z), ∃ (W : X.Opens) (f : Γ(X, W)), W ≤ U (i z) ⊓ L.B.U a ∧
      (i z ∈ L.B.U a → i z ∈ W) ∧ ∀ h, fnOf W h f = s (i z) J * R a := by
    intro a J z
    by_cases hz : i z ∈ L.B.U a
    · obtain ⟨W, hW, f, hf⟩ := ((hloc (i z) a (i z) (hU _) hz (hZl z)).1 J).exists_fnOf
      refine ⟨W ⊓ (U (i z) ⊓ L.B.U a), resG X inf_le_left f, inf_le_right, fun _ => ⟨hW, hU _, hz⟩, fun h => ?_⟩
      rw [fnOf_resG, hf]
    · exact ⟨⊥, 0, bot_le, fun h => (hz h).elim, fun h => absurd h (by simp)⟩
  choose W f hW hWz hf using hdata
  have hglue : ∀ (j : (L.B.pull i).ι) (J : Fin n), ∃ g : Γ(Z, (L.B.pull i).U j),
      ∀ z ∈ (L.B.pull i).U j, gs (𝟙 Z) z _ g = gs i z (W (j PUnit.unit) J z) (f (j PUnit.unit) J z) := by
    intro j J
    refine exists_glue i _ (fun z => W (j PUnit.unit) J z) (fun z => f (j PUnit.unit) J z)
      (fun z hz => hWz _ _ _ (mem_pull.1 hz)) (fun z _ y hy => mem_pull.2 (hW _ _ _ hy).2)
      (fun z₁ _ z₂ _ y h₁ h₂ hu => ?_)
    have m₁ := hW _ _ _ h₁
    have m₂ := hW _ _ _ h₂
    refine (hloc (i z₁) (j PUnit.unit) (i y) m₁.1 m₁.2 (hZl y)).2.2 (i z₂) m₂.1 J ⟨_, hu, ?_⟩
    rw [map_sub, algebraMap_gs h₁, algebraMap_gs h₂, hf, hf, sub_mul]
  choose g hg using hglue
  have hsec : ∀ (J : Fin n) (y : Z) (j j' : (L.B.pull i).ι), y ∈ (L.B.pull i).U j → y ∈ (L.B.pull i).U j' →
      gs (𝟙 Z) y _ (g j J) =
        (gm (𝟙 Z) y ((L.B.pull i).U j ⊓ (L.B.pull i).U j') ((L.B.pull i).g j j')).val * gs (𝟙 Z) y _ (g j' J) := by
    intro J y j j' hj hj'
    have ha := mem_pull.1 hj
    have ha' := mem_pull.1 hj'
    have hm : i y ∈ L.B.U (j PUnit.unit) ⊓ L.B.U (j' PUnit.unit) := ⟨ha, ha'⟩
    rw [hg j J y hj, hg j' J y hj', gm_pull_g L.B i (𝟙 Z) y j j' hj hj', Category.id_comp, ← gs_unit i y _ hm,
      gs_stalkMap i y _ (hWz _ _ _ ha), gs_stalkMap i y _ (hWz _ _ _ ha'), gs_stalkMap i y _ hm, ← map_mul]
    congr 1
    apply IsFractionRing.injective (X.presheaf.stalk (i y)) X.functionField
    rw [map_mul, algebraMap_gs (hWz _ _ _ ha), algebraMap_gs hm, algebraMap_gs (hWz _ _ _ ha'), hf, hf,
      hR _ _ (gen_mem hm)]
    ring
  let t : Fin n → (L.B.pull i).Sec := fun J => LBGerm.secOfGerm (fun j => g j J) (hsec J)
  refine topSelf_nonneg_of_isGenerated hX i κ hd (isGenerated_of_finite t (top_le_iff.1 fun y _ => ?_))
  obtain ⟨a, ha⟩ := exists_chart L.isLB (i y)
  obtain ⟨J, b, hb, e⟩ := (hloc (i y) a (i y) (hU _) ha (hZl y)).2.1
  have hy : y ∈ (L.B.pull i).U (fun _ => a) := mem_pull.2 ha
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨J, (mem_nonzeroLocus_iff_isUnit (t J) hy).2 ?_⟩
  change IsUnit (gs (𝟙 Z) y _ (g (fun _ => a) J))
  rw [hg _ J y hy, gs_stalkMap i y _ (hWz _ _ _ ha)]
  have hb' : b = gs (𝟙 X) (i y) _ (f a J y) :=
    IsFractionRing.injective _ X.functionField (by rw [e, algebraMap_gs (hWz _ _ _ ha), hf])
  exact hb' ▸ hb.map _

end GlobalTheory.HtGenCurve
