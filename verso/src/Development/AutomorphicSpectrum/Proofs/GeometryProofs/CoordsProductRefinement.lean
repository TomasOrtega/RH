import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AddBlock

open TopologicalSpace Opposite

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

def val (V : X.Opens) (hV : genPt ξ ∈ V) : Γ(X, V) →+* Ω :=
  (X.presheaf.germ V (genPt ξ) hV ≫ Scheme.stalkClosedPointTo ξ).hom

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ V p.1 hp f)) = _`. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_apply]`. Both sides reduce to the same expression.
-/
theorem genMap_germ (V : X.Opens) (hV : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = val ξ V hV f := by
  change (Scheme.stalkClosedPointTo ξ).hom
    (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ V p.1 hp f)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, genMap_germ ξ V hV p hp f⟩`.
-/
theorem val_mem (V : X.Opens) (hV : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    val ξ V hV f ∈ regAt ξ p :=
  ⟨_, genMap_germ ξ V hV p hp f⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V _ hV (X.presheaf.map (homOfLE h).op f)) = _`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Both sides reduce to the same expression.
-/
theorem val_res {V V' : X.Opens} (h : V ≤ V') (hV : genPt ξ ∈ V) (f : Γ(X, V')) :
    val ξ V hV (X.presheaf.map (homOfLE h).op f) = val ξ V' (h hV) f := by
  change (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V _ hV (X.presheaf.map (homOfLE h).op f)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {ξ}

/- English proof (translation)
Introduce `f g hfg`. Use `TopCat.Presheaf.section_ext X.sheaf V f g fun q hq => ?_` and prove the remaining obligations. Apply `hgen.inj ⟨q, hcl q hq⟩` to reduce the goal to its premises. Conclude with `(genMap_germ ξ V hV ⟨q, hcl q hq⟩ hq f).trans (hfg.trans (genMap_germ ξ V hV ⟨q, hcl q hq⟩ hq g).symm)`.
-/
theorem val_injective (hgen : IsCptGen ξ) (V : X.Opens) (hV : genPt ξ ∈ V)
    (hcl : ∀ q ∈ V, genPt ξ ⤳ q) : Function.Injective (val ξ V hV) := by
  intro f g hfg
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun q hq => ?_
  apply hgen.inj ⟨q, hcl q hq⟩
  exact (genMap_germ ξ V hV ⟨q, hcl q hq⟩ hq f).trans
    (hfg.trans (genMap_germ ξ V hV ⟨q, hcl q hq⟩ hq g).symm)

/- English proof (translation)
Establish `key : ∀ q : V, ∃ (O : X.Opens) (_ : q.1 ∈ O) (hle : O ≤ V) (hξ : genPt ξ ∈ O) (f : Γ(X, O)), val ξ O hξ f = a`. Introduce and unpack `⟨q, hq⟩`. Take `⟨g, hg⟩` from `ha ⟨q, hcl q hq⟩ hq`. Take `⟨O, hqO, f, hf⟩` from `TopCat.Presheaf.germ_exist X.presheaf g`. Establish `hξ : genPt ξ ∈ O ⊓ V` using `(hcl q hq).mem_open (O ⊓ V).2 ⟨hqO, hq⟩`.

Use `⟨O ⊓ V, ⟨hqO, hq⟩, inf_le_right, hξ, X.presheaf.map (homOfLE inf_le_left).op f, ?_⟩` and prove the remaining obligations. Rewrite using `[val_res, ← genMap_germ ξ O _ ⟨q, hcl q hq⟩ hqO, hf]`. Conclude with `hg`. Use `choose O hqO hle hξ f hf using key`. Take `⟨s, hs, -⟩` from `X.sheaf.existsUnique_gluing' O V (fun i => homOfLE (hle i)) (fun q hq => Opens.mem_iSup.2 ⟨⟨q, hq⟩, hqO ⟨q, hq⟩⟩) f (by`.

Introduce `i j`. Distinguish the cases in `hne : genPt ξ ∈ O i ⊓ O j`. Apply `val_injective hgen (O i ⊓ O j) hne (fun q hq => hcl q (hle i hq.1))` to reduce the goal to its premises. Establish `e1` using `val_res ξ (inf_le_left : O i ⊓ O j ≤ O i) hne (f i)`. Establish `e2` using `val_res ξ (inf_le_right : O i ⊓ O j ≤ O j) hne (f j)`.

Conclude with `e1.trans ((hf i).trans ((hf j).symm.trans e2.symm))`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Conclude with `⟨hξ i, hξ j⟩)`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Use `val_res ξ (hle ⟨_, hV⟩) (hξ ⟨_, hV⟩) s` as an intermediate fact. Rewrite using `[← this]`. Establish `h2` using `hs ⟨_, hV⟩`. Conclude with `(congrArg _ h2).trans (hf ⟨_, hV⟩)`.
-/
theorem exists_val_eq (hgen : IsCptGen ξ) (V : X.Opens) (hV : genPt ξ ∈ V)
    (hcl : ∀ q ∈ V, genPt ξ ⤳ q) (a : Ω) (ha : ∀ p : Cpt ξ, p.1 ∈ V → a ∈ regAt ξ p) :
    ∃ f, val ξ V hV f = a := by
  have key : ∀ q : V, ∃ (O : X.Opens) (_ : q.1 ∈ O) (hle : O ≤ V) (hξ : genPt ξ ∈ O) (f : Γ(X, O)),
      val ξ O hξ f = a := by
    rintro ⟨q, hq⟩
    obtain ⟨g, hg⟩ := ha ⟨q, hcl q hq⟩ hq
    obtain ⟨O, hqO, f, hf⟩ := TopCat.Presheaf.germ_exist X.presheaf g
    have hξ : genPt ξ ∈ O ⊓ V := (hcl q hq).mem_open (O ⊓ V).2 ⟨hqO, hq⟩
    refine ⟨O ⊓ V, ⟨hqO, hq⟩, inf_le_right, hξ, X.presheaf.map (homOfLE inf_le_left).op f, ?_⟩
    rw [val_res, ← genMap_germ ξ O _ ⟨q, hcl q hq⟩ hqO, hf]
    exact hg
  choose O hqO hle hξ f hf using key
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O V (fun i => homOfLE (hle i))
    (fun q hq => Opens.mem_iSup.2 ⟨⟨q, hq⟩, hqO ⟨q, hq⟩⟩) f (by
      intro i j
      by_cases hne : genPt ξ ∈ O i ⊓ O j
      · apply val_injective hgen (O i ⊓ O j) hne (fun q hq => hcl q (hle i hq.1))
        have e1 := val_res ξ (inf_le_left : O i ⊓ O j ≤ O i) hne (f i)
        have e2 := val_res ξ (inf_le_right : O i ⊓ O j ≤ O j) hne (f j)
        exact e1.trans ((hf i).trans ((hf j).symm.trans e2.symm))
      · exfalso
        apply hne
        exact ⟨hξ i, hξ j⟩)
  refine ⟨s, ?_⟩
  have := val_res ξ (hle ⟨_, hV⟩) (hξ ⟨_, hV⟩) s
  rw [← this]
  have h2 := hs ⟨_, hV⟩
  exact (congrArg _ h2).trans (hf ⟨_, hV⟩)

/- English proof (translation)
Rewrite using `[X.mem_basicOpen f p.1 hp]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨u, hu⟩` from `h.exists_right_inv`. Establish `h1 : val ξ V hV f * genMap ξ p u = 1`.

Rewrite using `[← genMap_germ ξ V hV p hp f, ← map_mul, hu, map_one]`. Establish `h0 : val ξ V hV f ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Use `⟨h0, val_mem ξ V hV p hp f, ⟨u, ?_⟩⟩` and prove the remaining obligations. Conclude with `eq_inv_of_mul_eq_one_right h1`. Introduce and unpack `⟨h0, -, u, hu⟩`.

Use `IsUnit.of_mul_eq_one u ?_` and prove the remaining obligations. Apply `hgen.inj p` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, genMap_germ ξ V hV p hp f, hu]`. Conclude with `mul_inv_cancel₀ h0`.
-/
theorem mem_basicOpen_iff (hgen : IsCptGen ξ) (V : X.Opens) (hV : genPt ξ ∈ V) (f : Γ(X, V))
    (p : Cpt ξ) (hp : p.1 ∈ V) : p.1 ∈ X.basicOpen f ↔ unitAt ξ p (val ξ V hV f) := by
  rw [X.mem_basicOpen f p.1 hp]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have h1 : val ξ V hV f * genMap ξ p u = 1 := by
      rw [← genMap_germ ξ V hV p hp f, ← map_mul, hu, map_one]
    have h0 : val ξ V hV f ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, val_mem ξ V hV p hp f, ⟨u, ?_⟩⟩
    exact eq_inv_of_mul_eq_one_right h1
  · rintro ⟨h0, -, u, hu⟩
    refine IsUnit.of_mul_eq_one u ?_
    apply hgen.inj p
    rw [map_mul, map_one, genMap_germ ξ V hV p hp f, hu]
    exact mul_inv_cancel₀ h0

/- English proof (translation)
Take `⟨t, rfl⟩` from `ha`. Set `_` to `X.presheaf.algebra_section_stalk ⟨p.1, hp⟩`. Establish `hl` using `hU.isLocalization_stalk ⟨p.1, hp⟩`. Take `⟨⟨f, g⟩, h⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl t`. Establish `hu : IsUnit (X.presheaf.germ U p.1 hp g.1)` using `IsLocalization.map_units (X.presheaf.stalk p.1) g`.

Use `⟨f, g.1, (X.mem_basicOpen g.1 p.1 hp).2 hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← genMap_germ ξ U hV p hp, ← genMap_germ ξ U hV p hp, ← map_mul]`. Use `congr 1`. Rewrite using `[mul_comm]`. Conclude with `h`.
-/
theorem exists_den {U : X.Opens} (hU : IsAffineOpen U) (hV : genPt ξ ∈ U)
    (p : Cpt ξ) (hp : p.1 ∈ U) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ f g : Γ(X, U), p.1 ∈ X.basicOpen g ∧ val ξ U hV g * a = val ξ U hV f := by
  obtain ⟨t, rfl⟩ := ha
  let _ := X.presheaf.algebra_section_stalk ⟨p.1, hp⟩
  have hl := hU.isLocalization_stalk ⟨p.1, hp⟩
  obtain ⟨⟨f, g⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl t
  have hu : IsUnit (X.presheaf.germ U p.1 hp g.1) :=
    IsLocalization.map_units (X.presheaf.stalk p.1) g
  refine ⟨f, g.1, (X.mem_basicOpen g.1 p.1 hp).2 hu, ?_⟩
  rw [← genMap_germ ξ U hV p hp, ← genMap_germ ξ U hV p hp, ← map_mul]
  congr 1
  rw [mul_comm]
  exact h

/- English proof (translation)
Take `⟨b, rfl⟩` from `exists_val_eq hgen (X.basicOpen g) hg (fun q hq => hcl q (X.basicOpen_le g hq)) a ha`. Set `_` to `hU.isLocalization_basicOpen g`. Take `⟨N, f, h⟩` from `IsLocalization.Away.surj g b`. Use `⟨N, f, ?_⟩` and prove the remaining obligations. Establish `e : ∀ r : Γ(X, U), val ξ (X.basicOpen g) hg (algebraMap Γ(X, U) Γ(X, X.basicOpen g) r) = val ξ U hV r` using `fun r => val_res ξ (X.basicOpen_le g) hg r`.

Rewrite using `[← e g, ← e f, ← h, map_mul, map_pow, mul_comm]`.
-/
theorem exists_pow {U : X.Opens} (hgen : IsCptGen ξ) (hU : IsAffineOpen U) (hV : genPt ξ ∈ U)
    (hcl : ∀ q ∈ U, genPt ξ ⤳ q) (g : Γ(X, U)) (hg : genPt ξ ∈ X.basicOpen g) (a : Ω)
    (ha : ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → a ∈ regAt ξ p) :
    ∃ (N : ℕ) (f : Γ(X, U)), val ξ U hV g ^ N * a = val ξ U hV f := by
  obtain ⟨b, rfl⟩ := exists_val_eq hgen (X.basicOpen g) hg
    (fun q hq => hcl q (X.basicOpen_le g hq)) a ha
  let _ := hU.isLocalization_basicOpen g
  obtain ⟨N, f, h⟩ := IsLocalization.Away.surj g b
  refine ⟨N, f, ?_⟩
  have e : ∀ r : Γ(X, U), val ξ (X.basicOpen g) hg (algebraMap Γ(X, U) Γ(X, X.basicOpen g) r)
      = val ξ U hV r := fun r => val_res ξ (X.basicOpen_le g) hg r
  rw [← e g, ← e f, ← h, map_mul, map_pow, mul_comm]

/- English proof (translation)
Take `⟨t, ht⟩` from `hgen.bij.2 a`. Use `⟨t, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes h t) = a`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`. Conclude with `ht`.
-/
theorem mem_regAt_gen (hgen : IsCptGen ξ) (a : Ω) (h : genPt ξ ⤳ genPt ξ) :
    a ∈ regAt ξ ⟨genPt ξ, h⟩ := by
  obtain ⟨t, ht⟩ := hgen.bij.2 a
  refine ⟨t, ?_⟩
  change (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes h t) = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ht

/- English proof (translation)
Use `Fintype.ofFinite κ'` as an intermediate fact. Establish `key : ∀ T : Finset κ', ∃ g : Γ(X, U), p.1 ∈ X.basicOpen g ∧ ∀ l ∈ T, ∃ f, val ξ U hV g * a l = val ξ U hV f`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`.

Use `⟨1, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[X.mem_basicOpen _ _ hp, map_one]`. Conclude with `isUnit_one`. Consider the case `insert l T _ ih`. Take `⟨g, hg, h⟩` from `ih`.

Take `⟨f', g', hg', h'⟩` from `exists_den hU hV p hp (a l) (ha l)`. Use `⟨g * g', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `⟨hg, hg'⟩`. Introduce `m hm`.

Break down `Finset.mem_insert.1 hm with rfl | hm` into its components or cases. Conclude with `⟨g * f', by rw [map_mul, map_mul, _root_.mul_assoc, h']⟩`. Take `⟨f, hf⟩` from `h m hm`. Conclude with `⟨f * g', by rw [map_mul, map_mul, mul_right_comm, hf]⟩`. Take `⟨g, hg, h⟩` from `key Finset.univ`.

Conclude with `⟨g, hg, fun l => h l (Finset.mem_univ l)⟩`.
-/
theorem exists_common_den {κ' : Type} [Finite κ'] {U : X.Opens} (hU : IsAffineOpen U)
    (hV : genPt ξ ∈ U) (p : Cpt ξ) (hp : p.1 ∈ U) (a : κ' → Ω) (ha : ∀ l, a l ∈ regAt ξ p) :
    ∃ g : Γ(X, U), p.1 ∈ X.basicOpen g ∧ ∀ l, ∃ f, val ξ U hV g * a l = val ξ U hV f := by
  classical
  have := Fintype.ofFinite κ'
  have key : ∀ T : Finset κ', ∃ g : Γ(X, U), p.1 ∈ X.basicOpen g ∧
      ∀ l ∈ T, ∃ f, val ξ U hV g * a l = val ξ U hV f := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, by simp⟩
      rw [X.mem_basicOpen _ _ hp, map_one]
      exact isUnit_one
    | insert l T _ ih =>
      obtain ⟨g, hg, h⟩ := ih
      obtain ⟨f', g', hg', h'⟩ := exists_den hU hV p hp (a l) (ha l)
      refine ⟨g * g', ?_, ?_⟩
      · rw [Scheme.basicOpen_mul]
        exact ⟨hg, hg'⟩
      · intro m hm
        rcases Finset.mem_insert.1 hm with rfl | hm
        · exact ⟨g * f', by rw [map_mul, map_mul, _root_.mul_assoc, h']⟩
        · obtain ⟨f, hf⟩ := h m hm
          exact ⟨f * g', by rw [map_mul, map_mul, mul_right_comm, hf]⟩
  obtain ⟨g, hg, h⟩ := key Finset.univ
  exact ⟨g, hg, fun l => h l (Finset.mem_univ l)⟩

section Core

variable {κ' : Type} (U : X.Opens) (hξ : genPt ξ ∈ U) (s : κ' → Ω) (i : κ')

def denoms : Set Γ(X, U) := {g | ∀ j, ∃ f, val ξ U hξ g * (s j / s i) = val ξ U hξ f}

def chartOpen : X.Opens := ⨆ g : denoms U hξ s i, X.basicOpen g.1

def trace : Set Γ(X, U) :=
  {f | ∃ (h : Ω) (j : κ'), (∀ l, ∃ e, h * s l = val ξ U hξ e) ∧ val ξ U hξ f = h * s j}

variable {U hξ s i}

/- English proof (translation)
The claim follows from `iSup_le fun _ => X.basicOpen_le _`.
-/
theorem chartOpen_le : chartOpen U hξ s i ≤ U := iSup_le fun _ => X.basicOpen_le _

/- English proof (translation)
The claim follows from `le_iSup (fun g : denoms U hξ s i => X.basicOpen g.1) ⟨g, hg⟩`.
-/
theorem basicOpen_le_chartOpen {g : Γ(X, U)} (hg : g ∈ denoms U hξ s i) :
    X.basicOpen g ≤ chartOpen U hξ s i :=
  le_iSup (fun g : denoms U hξ s i => X.basicOpen g.1) ⟨g, hg⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hq`. Establish `hqU` using `chartOpen_le hq`. Use `⟨hqU, hcl q hqU, hsi, fun j => ?_⟩` and prove the remaining obligations. Take `⟨⟨g, hg⟩, hqg⟩` from `Opens.mem_iSup.1 hq`.

Take `⟨h0, -, hinv⟩` from `(mem_basicOpen_iff hgen U hξ g ⟨q, hcl q hqU⟩ hqU).1 hqg`. Take `⟨f, hf⟩` from `hg j`. Establish `e : s j / s i = (val ξ U hξ g)⁻¹ * val ξ U hξ f`. Rewrite using `[← hf]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `mul_mem hinv (val_mem ξ U hξ ⟨q, hcl q hqU⟩ hqU f)`. Introduce and unpack `⟨hqU, h, -, hreg⟩`. Take `⟨g, hg, hd⟩` from `exists_common_den hU hξ ⟨q, h⟩ hqU (fun j => s j / s i) hreg`. Conclude with `basicOpen_le_chartOpen (g := g) hd hg`.
-/
theorem mem_chartOpen [Finite κ'] (hgen : IsCptGen ξ) (hU : IsAffineOpen U)
    (hcl : ∀ q ∈ U, genPt ξ ⤳ q) (hsi : s i ≠ 0) (q : X) :
    q ∈ chartOpen U hξ s i ↔ q ∈ U ∧ ∃ h : genPt ξ ⤳ q, InChart ξ s i ⟨q, h⟩ := by
  constructor
  · intro hq
    have hqU := chartOpen_le hq
    refine ⟨hqU, hcl q hqU, hsi, fun j => ?_⟩
    obtain ⟨⟨g, hg⟩, hqg⟩ := Opens.mem_iSup.1 hq
    obtain ⟨h0, -, hinv⟩ := (mem_basicOpen_iff hgen U hξ g ⟨q, hcl q hqU⟩ hqU).1 hqg
    obtain ⟨f, hf⟩ := hg j
    have e : s j / s i = (val ξ U hξ g)⁻¹ * val ξ U hξ f := by
      rw [← hf]; field_simp
    rw [e]
    exact mul_mem hinv (val_mem ξ U hξ ⟨q, hcl q hqU⟩ hqU f)
  · rintro ⟨hqU, h, -, hreg⟩
    obtain ⟨g, hg, hd⟩ := exists_common_den hU hξ ⟨q, h⟩ hqU (fun j => s j / s i) hreg
    exact basicOpen_le_chartOpen (g := g) hd hg

/- English proof (translation)
Rewrite using `[← hU.iSup_basicOpen_eq_self_iff]`. Use `le_antisymm (iSup_le fun _ => X.basicOpen_le _) fun q hq => ?_` and prove the remaining obligations. Take `⟨j, hj0, hj⟩` from `hs ⟨q, hcl q hq⟩`. Take `⟨g, hg, hd⟩` from `exists_common_den hU hξ ⟨q, hcl q hq⟩ hq (fun l => s l / s j) hj`. Use `Opens.mem_iSup.2 ⟨⟨g, val ξ U hξ g / s j, j, fun l => ?_, ?_⟩, hg⟩` and prove the remaining obligations.

Take `⟨f, hf⟩` from `hd l`. Conclude with `⟨f, by rw [← hf]; ring⟩`. Clear the denominators using the available nonvanishing facts.
-/
theorem span_trace [Finite κ'] (hU : IsAffineOpen U) (hcl : ∀ q ∈ U, genPt ξ ⤳ q)
    (hs : ∀ p : Cpt ξ, ∃ j, InChart ξ s j p) : Ideal.span (trace U hξ s) = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun _ => X.basicOpen_le _) fun q hq => ?_
  obtain ⟨j, hj0, hj⟩ := hs ⟨q, hcl q hq⟩
  obtain ⟨g, hg, hd⟩ := exists_common_den hU hξ ⟨q, hcl q hq⟩ hq (fun l => s l / s j) hj
  refine Opens.mem_iSup.2 ⟨⟨g, val ξ U hξ g / s j, j, fun l => ?_, ?_⟩, hg⟩
  · obtain ⟨f, hf⟩ := hd l
    exact ⟨f, by rw [← hf]; ring⟩
  · field_simp

/- English proof (translation)
Take `⟨h, j, hh, hv⟩` from `hf`. Take `⟨a, ha⟩` from `hh i`. Use `⟨a, j, fun l => ?_, ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hh l`. Use `⟨e, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, ← he]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hv, ← ha]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_denom_of_trace (hsi : s i ≠ 0) {f : Γ(X, U)} (hf : f ∈ trace U hξ s) :
    ∃ (a : Γ(X, U)) (j : κ'), a ∈ denoms U hξ s i ∧ val ξ U hξ f = val ξ U hξ a * (s j / s i) := by
  obtain ⟨h, j, hh, hv⟩ := hf
  obtain ⟨a, ha⟩ := hh i
  refine ⟨a, j, fun l => ?_, ?_⟩
  · obtain ⟨e, he⟩ := hh l
    refine ⟨e, ?_⟩
    rw [← ha, ← he]
    field_simp
  · rw [hv, ← ha]
    field_simp

/- English proof (translation)
Use `set W := chartOpen U hξ s i with hWdef`. Establish `hWU : W ≤ U` using `chartOpen_le`. Establish `hclW : ∀ q ∈ W, genPt ξ ⤳ q` using `fun q hq => hcl q (hWU hq)`. Establish `hτ : ∀ j, ∃ τ : Γ(X, W), val ξ W hW τ = s j / s i`. Introduce `j`.

Use `exists_val_eq hgen W hW hclW _ fun p hp => ?_` and prove the remaining obligations. Take `⟨-, h, -, hreg⟩` from `(mem_chartOpen hgen hU hcl hsi p.1).1 hp`. Conclude with `hreg j`. Use `choose τ hτ using hτ`. Set `r` to `X.presheaf.map (homOfLE hWU).op`.

Use `isAffineOpen_of_isAffineOpen_basicOpen W (r '' denoms U hξ s i) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Establish `h1 : Ideal.map r.hom (Ideal.span (trace U hξ s)) = ⊤`. Rewrite using `[span_trace hU hcl hs, Ideal.map_top]`. Rewrite using `[← h1, Ideal.map_span, Ideal.span_le]`.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, j, ha, hv⟩` from `exists_denom_of_trace (i := i) hsi hf`. Establish `e : r.hom f = r a * τ j`. Apply `val_injective hgen W hW hclW` to reduce the goal to its premises. Rewrite using `[map_mul, hτ]`.

Conclude with `(val_res ξ hWU hW f).trans (hv.trans (congrArg (· * _) (val_res ξ hWU hW a).symm))`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ha, rfl⟩)`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[Scheme.basicOpen_res, inf_eq_right.2 (basicOpen_le_chartOpen ha)]`.

Conclude with `hU.basicOpen a`.
-/
theorem chartOpen_affine [Finite κ'] (hgen : IsCptGen ξ) (hU : IsAffineOpen U)
    (hcl : ∀ q ∈ U, genPt ξ ⤳ q) (hsi : s i ≠ 0) (hs : ∀ p : Cpt ξ, ∃ j, InChart ξ s j p)
    (hW : genPt ξ ∈ chartOpen U hξ s i) : IsAffineOpen (chartOpen U hξ s i) := by
  set W := chartOpen U hξ s i with hWdef
  have hWU : W ≤ U := chartOpen_le
  have hclW : ∀ q ∈ W, genPt ξ ⤳ q := fun q hq => hcl q (hWU hq)
  have hτ : ∀ j, ∃ τ : Γ(X, W), val ξ W hW τ = s j / s i := by
    intro j
    refine exists_val_eq hgen W hW hclW _ fun p hp => ?_
    obtain ⟨-, h, -, hreg⟩ := (mem_chartOpen hgen hU hcl hsi p.1).1 hp
    exact hreg j
  choose τ hτ using hτ
  let r := X.presheaf.map (homOfLE hWU).op
  refine isAffineOpen_of_isAffineOpen_basicOpen W (r '' denoms U hξ s i) ?_ ?_
  · rw [eq_top_iff]
    have h1 : Ideal.map r.hom (Ideal.span (trace U hξ s)) = ⊤ := by
      rw [span_trace hU hcl hs, Ideal.map_top]
    rw [← h1, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, j, ha, hv⟩ := exists_denom_of_trace (i := i) hsi hf
    have e : r.hom f = r a * τ j := by
      apply val_injective hgen W hW hclW
      rw [map_mul, hτ]
      exact (val_res ξ hWU hW f).trans (hv.trans (congrArg (· * _) (val_res ξ hWU hW a).symm))
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ha, rfl⟩)
  · rintro _ ⟨a, ha, rfl⟩
    rw [Scheme.basicOpen_res, inf_eq_right.2 (basicOpen_le_chartOpen ha)]
    exact hU.basicOpen a

/- English proof (translation)
Set `c : Ideal Γ(X, U)` to `{ carrier := {r | val ξ U hξ r * a ∈ B} add_mem' := fun {u v} hu hv => by`. Express the relevant statement in the definitionally equal form `val ξ U hξ (u + v) * a ∈ B`. Rewrite using `[map_add, add_mul]`. Conclude with `add_mem hu hv`. Use the proof step `zero_mem' := by`.

Express the relevant statement in the definitionally equal form `val ξ U hξ 0 * a ∈ B`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun u v hv => by`. Express the relevant statement in the definitionally equal form `val ξ U hξ (u * v) * a ∈ B`. Rewrite using `[map_mul, _root_.mul_assoc]`.

Conclude with `mul_mem (hA u) hv }`. Establish `hrad : Ideal.span (trace U hξ s) ≤ c.radical`. Rewrite using `[Ideal.span_le]`. Introduce `f hf`. Take `⟨b, j, hb, hv⟩` from `exists_denom_of_trace (i := i) hsi hf`.

Distinguish the cases in `hb0 : val ξ U hξ b = 0`. Use `⟨1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `val ξ U hξ (f ^ 1) * a ∈ B`. Rewrite using `[pow_one, hv, hb0]`. Simplify using the standard rewrite rules.

Establish `hbξ : genPt ξ ∈ X.basicOpen b`. Use `(mem_basicOpen_iff hgen U hξ b ⟨genPt ξ, specializes_rfl⟩ hξ).2 ⟨hb0, mem_regAt_gen hgen _ _, mem_regAt_gen hgen _ _⟩` and prove the remaining obligations. Take `⟨N, e, he⟩` from `exists_pow hgen hU hξ hcl b hbξ a fun p hp => ha p (basicOpen_le_chartOpen hb hp)`. Use `⟨N, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `val ξ U hξ (f ^ N) * a ∈ B`.

Rewrite using `[map_pow, hv, mul_pow, mul_right_comm, he]`. Conclude with `mul_mem (hA e) (pow_mem (ht j) N)`. Establish `htop : c.radical = ⊤`. Rewrite using `[eq_top_iff, ← span_trace (hξ := hξ) hU hcl hs]`. Conclude with `hrad`.

Establish `h1 : (1 : Γ(X, U)) ∈ c`. Rewrite using `[Ideal.radical_eq_top.1 htop]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2 : val ξ U hξ 1 * a ∈ B` using `h1`. Simplify using `using h2`.
-/
theorem mem_of_regular [Finite κ'] (hgen : IsCptGen ξ) (hU : IsAffineOpen U)
    (hcl : ∀ q ∈ U, genPt ξ ⤳ q) (hsi : s i ≠ 0) (hs : ∀ p : Cpt ξ, ∃ j, InChart ξ s j p)
    (B : Subring Ω) (hA : ∀ f, val ξ U hξ f ∈ B) (ht : ∀ j, s j / s i ∈ B) (a : Ω)
    (ha : ∀ p : Cpt ξ, p.1 ∈ chartOpen U hξ s i → a ∈ regAt ξ p) : a ∈ B := by
  let c : Ideal Γ(X, U) :=
    { carrier := {r | val ξ U hξ r * a ∈ B}
      add_mem' := fun {u v} hu hv => by
        change val ξ U hξ (u + v) * a ∈ B
        rw [map_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        change val ξ U hξ 0 * a ∈ B
        simp
      smul_mem' := fun u v hv => by
        change val ξ U hξ (u * v) * a ∈ B
        rw [map_mul, _root_.mul_assoc]
        exact mul_mem (hA u) hv }
  have hrad : Ideal.span (trace U hξ s) ≤ c.radical := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨b, j, hb, hv⟩ := exists_denom_of_trace (i := i) hsi hf
    by_cases hb0 : val ξ U hξ b = 0
    · refine ⟨1, ?_⟩
      change val ξ U hξ (f ^ 1) * a ∈ B
      rw [pow_one, hv, hb0]
      simp
    · have hbξ : genPt ξ ∈ X.basicOpen b := by
        refine (mem_basicOpen_iff hgen U hξ b ⟨genPt ξ, specializes_rfl⟩ hξ).2
          ⟨hb0, mem_regAt_gen hgen _ _, mem_regAt_gen hgen _ _⟩
      obtain ⟨N, e, he⟩ := exists_pow hgen hU hξ hcl b hbξ a
        fun p hp => ha p (basicOpen_le_chartOpen hb hp)
      refine ⟨N, ?_⟩
      change val ξ U hξ (f ^ N) * a ∈ B
      rw [map_pow, hv, mul_pow, mul_right_comm, he]
      exact mul_mem (hA e) (pow_mem (ht j) N)
  have htop : c.radical = ⊤ := by
    rw [eq_top_iff, ← span_trace (hξ := hξ) hU hcl hs]
    exact hrad
  have h1 : (1 : Γ(X, U)) ∈ c := by
    rw [Ideal.radical_eq_top.1 htop]
    trivial
  have h2 : val ξ U hξ 1 * a ∈ B := h1
  simpa using h2

end Core

/- English proof (translation)
Take `⟨c₀, hc₀, hx₀⟩` from `hx`. Take `⟨i₀, hi₀, hs₀⟩` from `hs`. Establish `hw` using `h c₀ i₀`. Establish `hu : (x c₀ / x c) = (x c₀ / x c * (s i₀ / s i)) * (s i / s i₀)` using `by field_simp`. Establish `hv : (s i₀ / s i) = (x c₀ / x c * (s i₀ / s i)) * (x c / x c₀)` using `by field_simp`.

Establish `hu' : x c₀ / x c ∈ regAt ξ p` using `hu ▸ mul_mem hw (hs₀ i)`. Establish `hv' : s i₀ / s i ∈ regAt ξ p` using `hv ▸ mul_mem hw (hx₀ c)`. Use `⟨⟨hxc, fun c' => ?_⟩, ⟨hsi, fun i' => ?_⟩⟩` and prove the remaining obligations. Establish `: x c' / x c = (x c' / x c₀) * (x c₀ / x c)` using `by field_simp`. Conclude with `this ▸ mul_mem (hx₀ c') hu'`.

Establish `: s i' / s i = (s i' / s i₀) * (s i₀ / s i)` using `by field_simp`. Conclude with `this ▸ mul_mem (hs₀ i') hv'`.
-/
theorem inChart_of_mul {κ κ' : Type} {x : κ → Ω} {s : κ' → Ω} {c : κ} {i : κ'} {p : Cpt ξ}
    (hx : ∃ c, InChart ξ x c p) (hs : ∃ i, InChart ξ s i p) (hxc : x c ≠ 0) (hsi : s i ≠ 0)
    (h : ∀ c' i', x c' / x c * (s i' / s i) ∈ regAt ξ p) :
    InChart ξ x c p ∧ InChart ξ s i p := by
  obtain ⟨c₀, hc₀, hx₀⟩ := hx
  obtain ⟨i₀, hi₀, hs₀⟩ := hs
  have hw := h c₀ i₀
  have hu : (x c₀ / x c) = (x c₀ / x c * (s i₀ / s i)) * (s i / s i₀) := by field_simp
  have hv : (s i₀ / s i) = (x c₀ / x c * (s i₀ / s i)) * (x c / x c₀) := by field_simp
  have hu' : x c₀ / x c ∈ regAt ξ p := hu ▸ mul_mem hw (hs₀ i)
  have hv' : s i₀ / s i ∈ regAt ξ p := hv ▸ mul_mem hw (hx₀ c)
  refine ⟨⟨hxc, fun c' => ?_⟩, ⟨hsi, fun i' => ?_⟩⟩
  · have : x c' / x c = (x c' / x c₀) * (x c₀ / x c) := by field_simp
    exact this ▸ mul_mem (hx₀ c') hu'
  · have : s i' / s i = (s i' / s i₀) * (s i₀ / s i) := by field_simp
    exact this ▸ mul_mem (hs₀ i') hv'

/- English proof (translation)
Establish `hratio : ∀ q q', z q' / z q = x (u q') / x (u q) * (s (v q') / s (v q))` using `fun q q' => by`. Rewrite using `[hz, hz, mul_div_mul_comm]`. Establish `hchart : ∀ (q : T) (p : Cpt ξ), InChart ξ z q p → InChart ξ x (u q) p ∧ InChart ξ s (v q) p`. Introduce `q p ⟨h0, h⟩`. Rewrite `h0` using `[hz]`.

Use `inChart_of_mul (hx.cover p) (hs p) (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0) fun c' i' => ?_` and prove the remaining obligations. Take `⟨q', rfl, rfl⟩` from `hsurj c' i'`. Rewrite using `[← hratio]`. Conclude with `h q'`. Establish `hchart' : ∀ (q : T) (p : Cpt ξ), InChart ξ x (u q) p → InChart ξ s (v q) p → InChart ξ z q p`.

Introduce `q p ⟨h1, h2⟩ ⟨h3, h4⟩`. Use `⟨by rw [hz]; exact mul_ne_zero h1 h3, fun q' => ?_⟩` and prove the remaining obligations. Rewrite using `[hratio]`. Conclude with `mul_mem (h2 _) (h4 _)`. Establish `hne : ∀ q, z q ≠ 0 → x (u q) ≠ 0 ∧ s (v q) ≠ 0` using `fun q h => by`.

Rewrite `h` using `[hz]`. Conclude with `⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩`. Establish `hdata : ∀ q, z q ≠ 0 → ∃ (U : X.Opens) (hξ : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q' ∈ U, genPt ξ ⤳ q') ∧ ∀ q' : X, q' ∈ U ↔ ∃ h : genPt ξ ⤳ q', InChart ξ x (u q) ⟨q', h⟩`. Introduce `q h`. Take `⟨U, hU, hm⟩` from `hx.affine (u q) (hne q h).1`.

Establish `hξ : genPt ξ ∈ U` using `(hm _).2 ⟨specializes_rfl, (hne q h).1, fun _ => mem_regAt_gen hx.gen _ _⟩`. Conclude with `⟨U, hξ, hU, fun q' hq' => ((hm q').1 hq').1, hm⟩`. Use `⟨hx.gen, fun p => ?_, fun q h => ?_, fun q h a => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hx.cover p`. Take `⟨i, hi⟩` from `hs p`.

Take `⟨q, rfl, rfl⟩` from `hsurj c i`. Conclude with `⟨q, hchart' q p hc hi⟩`. Take `⟨U, hξ, hU, hcl, hm⟩` from `hdata q h`. Establish `hmem` using `mem_chartOpen (hξ := hξ) (s := s) (i := v q) hx.gen hU hcl (hne q h).2`. Establish `hW : genPt ξ ∈ chartOpen U hξ s (v q)` using `(hmem _).2 ⟨hξ, specializes_rfl, (hne q h).2, fun _ => mem_regAt_gen hx.gen _ _⟩`.

Use `⟨_, chartOpen_affine hx.gen hU hcl (hne q h).2 hs hW, fun q' => ?_⟩` and prove the remaining obligations. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Take `⟨h4, h5⟩` from `(hm q').1 h1`.

Conclude with `⟨h2, hchart' q ⟨q', h2⟩ h5 h3⟩`. Introduce and unpack `⟨h2, h3⟩`. Take `⟨h4, h5⟩` from `hchart q _ h3`. Conclude with `⟨(hm q').2 ⟨h2, h4⟩, h2, h5⟩`. Take `⟨U, hξ, hU, hcl, hm⟩` from `hdata q h`.

Establish `hmem` using `mem_chartOpen (hξ := hξ) (s := s) (i := v q) hx.gen hU hcl (hne q h).2`. Prove the components needed by the constructor for the conclusion. Introduce `ha p hp`. Take `⟨h1, h2⟩` from `hchart q p hp`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem a ha`. Take `⟨q', rfl⟩` from `ha`. Conclude with `hp.2 q'`. Consider the case `algebraMap r`. Conclude with `(hx.ring (u q) (hne q h).1 _).1 (Subalgebra.algebraMap_mem _ r) p h1`.

Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`. Introduce `ha set S := Algebra.adjoin o (Set.range fun j => z j / z q) with hS`. Establish `hxS : ∀ c, x c / x (u q) ∈ S`. Introduce `c`.

Take `⟨q', hu, hv⟩` from `hsurj c (v q)`. Establish `e : x c / x (u q) = z q' / z q`. Rewrite using `[hratio, hu, hv, div_self (hne q h).2, _root_.mul_one]`. Rewrite using `[e]`. Conclude with `Algebra.subset_adjoin ⟨q', rfl⟩`.

Establish `hsS : ∀ i, s i / s (v q) ∈ S`. Introduce `i`. Take `⟨q', hu, hv⟩` from `hsurj (u q) i`. Establish `e : s i / s (v q) = z q' / z q`. Rewrite using `[hratio, hu, hv, div_self (hne q h).1, _root_.one_mul]`.

Rewrite using `[e]`. Conclude with `Algebra.subset_adjoin ⟨q', rfl⟩`. Establish `hle : Algebra.adjoin o (Set.range fun j => x j / x (u q)) ≤ S` using `Algebra.adjoin_le (by rintro _ ⟨c, rfl⟩; exact hxS c)`. Use `mem_of_regular (hξ := hξ) (s := s) (i := v q) (B := S.toSubring) hx.gen hU hcl (hne q h).2 hs (fun f => ?_) hsS a fun p hp => ?_` and prove the remaining obligations. Apply `hle` to reduce the goal to its premises.

Use `(hx.ring (u q) (hne q h).1 _).2 fun p hp => ?_` and prove the remaining obligations. Conclude with `val_mem ξ U hξ p ((hm p.1).2 ⟨p.2, hp⟩) f`. Take `⟨h1, h2, h3⟩` from `(hmem p.1).1 hp`. Take `⟨h4, h5⟩` from `(hm p.1).1 h1`. Conclude with `ha p (hchart' q p h5 h3)`.
-/
theorem coordTie_mul {o : Type} [CommRing o] [Algebra o Ω] {κ κ' : Type} [Finite κ'] {x : κ → Ω}
    {s : κ' → Ω} (hx : CoordTie o ξ x) (hs : ∀ p : Cpt ξ, ∃ i, InChart ξ s i p) {T : Type}
    (z : T → Ω) (u : T → κ) (v : T → κ') (hz : ∀ q, z q = x (u q) * s (v q))
    (hsurj : ∀ c i, ∃ q, u q = c ∧ v q = i) : CoordTie o ξ z := by
  have hratio : ∀ q q', z q' / z q = x (u q') / x (u q) * (s (v q') / s (v q)) := fun q q' => by
    rw [hz, hz, mul_div_mul_comm]
  have hchart : ∀ (q : T) (p : Cpt ξ), InChart ξ z q p →
      InChart ξ x (u q) p ∧ InChart ξ s (v q) p := by
    intro q p ⟨h0, h⟩
    rw [hz] at h0
    refine inChart_of_mul (hx.cover p) (hs p) (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)
      fun c' i' => ?_
    obtain ⟨q', rfl, rfl⟩ := hsurj c' i'
    rw [← hratio]
    exact h q'
  have hchart' : ∀ (q : T) (p : Cpt ξ), InChart ξ x (u q) p → InChart ξ s (v q) p →
      InChart ξ z q p := by
    intro q p ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [hz]; exact mul_ne_zero h1 h3, fun q' => ?_⟩
    rw [hratio]
    exact mul_mem (h2 _) (h4 _)
  have hne : ∀ q, z q ≠ 0 → x (u q) ≠ 0 ∧ s (v q) ≠ 0 := fun q h => by
    rw [hz] at h
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

  have hdata : ∀ q, z q ≠ 0 → ∃ (U : X.Opens) (hξ : genPt ξ ∈ U), IsAffineOpen U ∧
      (∀ q' ∈ U, genPt ξ ⤳ q') ∧ ∀ q' : X, q' ∈ U ↔ ∃ h : genPt ξ ⤳ q', InChart ξ x (u q) ⟨q', h⟩ := by
    intro q h
    obtain ⟨U, hU, hm⟩ := hx.affine (u q) (hne q h).1
    have hξ : genPt ξ ∈ U := (hm _).2 ⟨specializes_rfl, (hne q h).1,
      fun _ => mem_regAt_gen hx.gen _ _⟩
    exact ⟨U, hξ, hU, fun q' hq' => ((hm q').1 hq').1, hm⟩
  refine ⟨hx.gen, fun p => ?_, fun q h => ?_, fun q h a => ?_⟩
  · obtain ⟨c, hc⟩ := hx.cover p
    obtain ⟨i, hi⟩ := hs p
    obtain ⟨q, rfl, rfl⟩ := hsurj c i
    exact ⟨q, hchart' q p hc hi⟩
  · obtain ⟨U, hξ, hU, hcl, hm⟩ := hdata q h
    have hmem := mem_chartOpen (hξ := hξ) (s := s) (i := v q) hx.gen hU hcl (hne q h).2
    have hW : genPt ξ ∈ chartOpen U hξ s (v q) := (hmem _).2 ⟨hξ, specializes_rfl, (hne q h).2,
      fun _ => mem_regAt_gen hx.gen _ _⟩
    refine ⟨_, chartOpen_affine hx.gen hU hcl (hne q h).2 hs hW, fun q' => ?_⟩
    rw [hmem]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨h4, h5⟩ := (hm q').1 h1
      exact ⟨h2, hchart' q ⟨q', h2⟩ h5 h3⟩
    · rintro ⟨h2, h3⟩
      obtain ⟨h4, h5⟩ := hchart q _ h3
      exact ⟨(hm q').2 ⟨h2, h4⟩, h2, h5⟩
  · obtain ⟨U, hξ, hU, hcl, hm⟩ := hdata q h
    have hmem := mem_chartOpen (hξ := hξ) (s := s) (i := v q) hx.gen hU hcl (hne q h).2
    constructor
    · intro ha p hp
      obtain ⟨h1, h2⟩ := hchart q p hp
      induction ha using Algebra.adjoin_induction with
      | mem a ha =>
        obtain ⟨q', rfl⟩ := ha
        exact hp.2 q'
      | algebraMap r =>
        exact (hx.ring (u q) (hne q h).1 _).1 (Subalgebra.algebraMap_mem _ r) p h1
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    · intro ha
      set S := Algebra.adjoin o (Set.range fun j => z j / z q) with hS
      have hxS : ∀ c, x c / x (u q) ∈ S := by
        intro c
        obtain ⟨q', hu, hv⟩ := hsurj c (v q)
        have e : x c / x (u q) = z q' / z q := by
          rw [hratio, hu, hv, div_self (hne q h).2, _root_.mul_one]
        rw [e]
        exact Algebra.subset_adjoin ⟨q', rfl⟩
      have hsS : ∀ i, s i / s (v q) ∈ S := by
        intro i
        obtain ⟨q', hu, hv⟩ := hsurj (u q) i
        have e : s i / s (v q) = z q' / z q := by
          rw [hratio, hu, hv, div_self (hne q h).1, _root_.one_mul]
        rw [e]
        exact Algebra.subset_adjoin ⟨q', rfl⟩
      have hle : Algebra.adjoin o (Set.range fun j => x j / x (u q)) ≤ S :=
        Algebra.adjoin_le (by rintro _ ⟨c, rfl⟩; exact hxS c)
      refine mem_of_regular (hξ := hξ) (s := s) (i := v q) (B := S.toSubring) hx.gen hU hcl
        (hne q h).2 hs (fun f => ?_) hsS a fun p hp => ?_
      · apply hle
        refine (hx.ring (u q) (hne q h).1 _).2 fun p hp => ?_
        exact val_mem ξ U hξ p ((hm p.1).2 ⟨p.2, hp⟩) f
      · obtain ⟨h1, h2, h3⟩ := (hmem p.1).1 hp
        obtain ⟨h4, h5⟩ := (hm p.1).1 h1
        exact ha p (hchart' q p h5 h3)

end GlobalTheory.CompanionTheory.Ar.AddBlock

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `X Ω _ ξ o _ _ κ κ' x s hx hs _ _`. Use `⟨0, AddBlock.coordTie_mul hx hs _ (fun q => q.2.1) (fun q => q.2.2) (fun q => by simp) fun c i => ⟨(Fin.elim0, c, i), rfl, rfl⟩⟩` and prove the remaining obligations.
-/
theorem coordTie_add_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (s : κ' → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, ∃ i, InChart ξ s i p) → [Finite κ] → [Finite κ'] → ∃ n : ℕ, CoordTie o ξ fun q : (Fin n → κ) × κ × κ' => (∏ a, x (q.1 a)) * x q.2.1 * s q.2.2 := by
  intro X Ω _ ξ o _ _ κ κ' x s hx hs _ _
  refine ⟨0, AddBlock.coordTie_mul hx hs _ (fun q => q.2.1) (fun q => q.2.2) (fun q => by simp)
    fun c i => ⟨(Fin.elim0, c, i), rfl, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar
