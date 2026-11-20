import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SFamCompl

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings`.
-/
theorem glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e :=
  GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings

/- English proof (translation)
Introduce `R _ I hI A _ f f' h`. Rewrite using `[← Spec.map_preimage f, ← Spec.map_preimage f']`. Use `congr 1`. Use extensionality with `a`. Use `(IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_` and prove the remaining obligations.

Consider the cases of `k with`. Consider the case `zero`. Rewrite using `[SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]`. Discharge the goal by the elementary cases of `trivial`. Consider the case `succ e`.

Establish `he` using `h e`. Rewrite `he` using `[← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp]`. Establish `he'` using `congrArg (fun q => q.hom a) (Spec.map_injective he)`. Simplify using `only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'`. Rewrite using `[SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]`.

Conclude with `Ideal.Quotient.eq.1 he'`.
-/
theorem ext_affine : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (A : Type) [CommRing A]
    (f f' : Sp R ⟶ Sp A), (∀ e, Out.thick R I e ≫ f = Out.thick R I e ≫ f') → f = f' := by
  intro R _ I hI A _ f f' h
  rw [← Spec.map_preimage f, ← Spec.map_preimage f']
  congr 1
  ext a
  refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_
  cases k with
  | zero =>
    rw [SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
    trivial
  | succ e =>
    have he := h e
    rw [← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp] at he
    have he' := congrArg (fun q => q.hom a) (Spec.map_injective he)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'
    rw [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 he'

/- English proof (translation)
Take `⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩` from `m`. Take `⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩` from `m'`. Simplify using `only [pow_one] at hl hl' ⊢`. Use `⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]`.

Rewrite using `[Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]`. Conclude with `(hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)`. Rewrite using `[pow_one, pow_one]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))`.
-/
theorem srel_comp {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
    {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · rw [pow_one, pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

/- English proof (translation)
Introduce `g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ`. Establish `key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e`. Introduce `e`. Establish `h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e)` using `GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩) (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)`. Take `⟨β, hβ⟩` from `(sRel_one_one_iff _ _ _).2 h1`.

Use `⟨β, ?_, ?_⟩` and prove the remaining obligations. Use `srel_comp (hφ (e + 1)) hβ` as an intermediate fact. Rewrite `this` using `[Out.thickTrans_comp]`. Conclude with `GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)`. Use `srel_comp (hψ (e + 1)) hβ` as an intermediate fact.

Rewrite `this` using `[Out.thickTrans_comp]`. Conclude with `GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)`. Use `choose β hβ using key`. Conclude with `⟨β, hβ⟩`.
-/
theorem tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] (I : Ideal R) (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s) (c' : SiegPre g n (b.ζ : B) s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n (b.ζ : B) (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left), 3 ≤ n → Odd n → c.Principal → c'.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → ∃ β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left, ∀ e, β e ≫ φ (e + 1) = φ e ∧ β e ≫ ψ (e + 1) = ψ e := by
  intro g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  have key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e) :=
      GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩)
        (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)
    obtain ⟨β, hβ⟩ := (sRel_one_one_iff _ _ _).2 h1
    refine ⟨β, ?_, ?_⟩
    · have := srel_comp (hφ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)
    · have := srel_comp (hψ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)
  choose β hβ using key
  exact ⟨β, hβ⟩

/- English proof (translation)
The claim follows from `GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic`.
-/
theorem assemble : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) :=
  GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic

/- English proof (translation)
Introduce `g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h`. Use `choose t ce hce hce' using h`. Use `choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)`. Use `choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)`. Take `⟨β, hβ⟩` from `tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ`.

Conclude with `assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)`.
-/
theorem alg : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), IsAdicComplete I R → 3 ≤ n → Odd n → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s)
    (c' : SiegPre g n (b.ζ : B) s'), c.Principal → c'.Principal →
    (∀ e, ∃ (t : Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : SiegPre g n (b.ζ : B) t),
      SiegPB ce c (Out.thick R I e) ∧ SiegPB ce c' (Out.thick R I e)) → SiegPB c c' (𝟙 _) := by
  intro g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h
  choose t ce hce hce' using h
  choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)
  choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)
  obtain ⟨β, hβ⟩ := tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  exact assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)

/- English proof (translation)
The claim follows from `have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e))) IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjecti …`.
-/
theorem quot_local (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/- English proof (translation)
Establish `: Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1))`. Use `Ring.KrullDimLE.mk₀ fun P hP => ?_` and prove the remaining obligations. Establish `h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1)))`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]`.

Conclude with `P.zero_mem`. Establish `hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1)))` using `hp.le_of_pow_le h1`. Establish `h3` using `hm.eq_of_le hp.ne_top h2`. Establish `h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal` using `h3 ▸ hm`.

Establish `h5` using `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1))) Ideal.Quotient.mk_surjective h4`. Rewrite `h5` using `[Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Conclude with `h5.resolve_left hP.ne_top`. Conclude with `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`.
-/
theorem quot_artin {R : Type} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m.IsMaximal)
    (N : ℕ) : IsArtinianRing (R ⧸ m ^ (N + 1)) := by
  have : Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1)) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    have hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := hp.le_of_pow_le h1
    have h3 := hm.eq_of_le hp.ne_top h2
    have h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal := h3 ▸ hm
    have h5 := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1)))
      Ideal.Quotient.mk_surjective h4
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h5
    exact h5.resolve_left hP.ne_top
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/- English proof (translation)
Simplify using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_id_ {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

end GlobalTheory.SFamCompl

namespace GlobalTheory.SFamCompl

/- English proof (translation)
Introduce `g n hg hn hodd F R _ _ _ hR β c hc`. Establish `hn0 : n ≠ 0` using `by omega`. Use `set m := IsLocalRing.maximalIdeal R with hm`. Use `haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e`. Use `haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e`.

Set `βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1))` to `fun e => (Ideal.Quotient.mk _).comp β`. Establish `hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n))`. Introduce `e`. Rewrite using `[spMap_id_, Category.comp_id]`. Conclude with `(spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm`.

Establish `hpull` using `fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)`. Use `choose ce hce using fun e => (hpull e).1 c`. Establish `hcep : ∀ e, (ce e).Principal` using `fun e => (hpull e).2.1 c (ce e) (hce e) hc`. Use `choose x hxs hxpb using fun e => GlobalTheory.T.siegel_point_lifts_to_artinian g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)`. Establish `hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e`.

Introduce `e`. Establish `h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e)` using `GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)`. Use `GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e) (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)` and prove the remaining obligations. Rewrite using `[Category.assoc, hxs (e + 1)]`. Conclude with `(spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))`.

Take `⟨f, hf⟩` from `glue R hR F.X x hcomp`. Establish `hfs : f ≫ F.s = spMap β`. Use `ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]`. Establish `hpf` using `GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])`.

Take `⟨c', hc'⟩` from `hpf.1 F.univ`. Establish `hc'p : c'.Principal` using `hpf.2.1 F.univ c' hc' F.princ`. Establish `key : SiegPB c c' (𝟙 _)`. Use `alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_` and prove the remaining obligations. Use `⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩` and prove the remaining obligations.

Rewrite using `[hf e]`. Conclude with `hxpb e`. Use `⟨f, hfs, ?_⟩` and prove the remaining obligations. Simplify using `using GlobalTheory.SiegelPullComp.pb_comp hc' key`.
-/
theorem classified_of_complete : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ hR β c hc
  have hn0 : n ≠ 0 := by omega
  set m := IsLocalRing.maximalIdeal R with hm
  haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e
  haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e
  let βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1)) := fun e => (Ideal.Quotient.mk _).comp β
  have hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n)) := by
    intro e
    rw [spMap_id_, Category.comp_id]
    exact (spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm
  have hpull := fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)
  choose ce hce using fun e => (hpull e).1 c
  have hcep : ∀ e, (ce e).Principal := fun e => (hpull e).2.1 c (ce e) (hce e) hc
  choose x hxs hxpb using fun e => GlobalTheory.T.siegel_point_lifts_to_artinian g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)
  have hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e) :=
      GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e)
      (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)
    rw [Category.assoc, hxs (e + 1)]
    exact (spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))
  obtain ⟨f, hf⟩ := glue R hR F.X x hcomp
  have hfs : f ≫ F.s = spMap β := by
    refine ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_
    rw [← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]
  have hpf := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])
  obtain ⟨c', hc'⟩ := hpf.1 F.univ
  have hc'p : c'.Principal := hpf.2.1 F.univ c' hc' F.princ
  have key : SiegPB c c' (𝟙 _) := by
    refine alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_
    refine ⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩
    rw [hf e]
    exact hxpb e
  refine ⟨f, hfs, ?_⟩
  simpa using GlobalTheory.SiegelPullComp.pb_comp hc' key

end GlobalTheory.SFamCompl
