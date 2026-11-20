import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
open scoped TensorProduct Classical

namespace GlobalTheory.LeviSign

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

section Comb

def Aset {k : ℕ} (u : SV k) : Finset (SignType × Fin k) := Finset.univ.filter fun x => x.1 * u x.2 = 1

/- English proof (translation)
Simplify using `[Aset]`.
-/
theorem mem_Aset {k : ℕ} {u : SV k} {x : SignType × Fin k} : x ∈ Aset u ↔ x.1 * u x.2 = 1 := by
  simp [Aset]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[vec]`.
-/
theorem vec_neg {k : ℕ} (u : SV k) : vec (-u) = -vec u := by
  ext i
  simp [vec]

/- English proof (translation)
Set `a : A0 k →ₗ[ℝ] ℝ` to `(s : ℝ) • EuclideanSpace.projₗ i - (t : ℝ) • EuclideanSpace.projₗ j`. Establish `ha : ∀ w : SV k, a (vec w) = ((s * w i : SignType) : ℝ) - ((t * w j : SignType) : ℝ)` using `fun w => by`. Simplify using `[a, vec, SignType.coe_mul]`. Establish `hle : aP P ≤ LinearMap.ker a` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Simplify using `[LinearMap.mem_ker, ha, h w hw])`. Establish `h0` using `hle hu`. Rewrite `h0` using `[LinearMap.mem_ker, ha, sub_eq_zero]`. Establish `inj : ∀ a b : SignType, (a : ℝ) = b → a = b`. Introduce `a b hab`.

Apply the tactic sequence `rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> first | rfl | (norm_num [SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one] at hab)`. Conclude with `inj _ _ h0`.
-/
theorem pattern {k : ℕ} {P : Finset (SV k)} {u : SV k} (hu : vec u ∈ aP P) {s t : SignType} {i j : Fin k}
    (h : ∀ w ∈ P, s * w i = t * w j) : s * u i = t * u j := by
  let a : A0 k →ₗ[ℝ] ℝ := (s : ℝ) • EuclideanSpace.projₗ i - (t : ℝ) • EuclideanSpace.projₗ j
  have ha : ∀ w : SV k, a (vec w) = ((s * w i : SignType) : ℝ) - ((t * w j : SignType) : ℝ) := fun w => by
    simp [a, vec, SignType.coe_mul]
  have hle : aP P ≤ LinearMap.ker a := Submodule.span_le.2 (by
    rintro _ ⟨w, hw, rfl⟩
    simp [LinearMap.mem_ker, ha, h w hw])
  have h0 := hle hu
  rw [LinearMap.mem_ker, ha, sub_eq_zero] at h0
  have inj : ∀ a b : SignType, (a : ℝ) = b → a = b := by
    intro a b hab
    rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> first | rfl | (norm_num [SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one] at hab)
  exact inj _ _ h0

/- English proof (translation)
Establish `hB : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Finset X), (∀ i ∈ s, S (f i)) → S (s.biUnion f)`. Introduce `ι _ s f hf`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h0`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.biUnion_insert]`. Conclude with `hU _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`. Set `U : X → Finset X` to `fun x => (𝒢.filter (x ∈ ·)).biUnion id`. Set `at' : X → Finset X` to `fun x => U x \ 𝒢.biUnion (fun G => if x ∈ G then U x \ G else G)`. Establish `hUS : ∀ x, S (U x)` using `fun x => hB _ _ fun G hG' => hG G (Finset.mem_filter.1 hG').1`.

Establish `hat : ∀ x, S (at' x)` using `fun x => hD _ _ (hUS x) (hB _ _ fun G hG' => by split_ifs`. Conclude with `hD _ _ (hUS x) (hG G hG')`. Conclude with `hG G hG')`. Establish `self_mem : ∀ x ∈ T, x ∈ at' x` using `fun x hx => by`. Take `⟨G, hG', hxG⟩` from `h1 x hx`.

Use `Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨G, Finset.mem_filter.2 ⟨hG', hxG⟩, hxG⟩, fun h => ?_⟩` and prove the remaining obligations. Take `⟨G', _, hx'⟩` from `Finset.mem_biUnion.1 h`. Use `split_ifs at hx' with h'`. Conclude with `(Finset.mem_sdiff.1 hx').2 h'`. Conclude with `h' hx'`.

Establish `patt : ∀ x y, y ∈ at' x → ∀ G ∈ 𝒢, (x ∈ G ↔ y ∈ G)` using `fun x y hy G hG' => by`. Take `⟨hyU, hyn⟩` from `Finset.mem_sdiff.1 hy`. Distinguish the cases in `hx : x ∈ G`. Use `iff_of_true hx (by_contra fun hyG => hyn (Finset.mem_biUnion.2 ⟨G, hG', ?_⟩))` and prove the remaining obligations. Rewrite using `[if_pos hx]`.

Conclude with `Finset.mem_sdiff.2 ⟨hyU, hyG⟩`. Use `iff_of_false hx fun hyG => hyn (Finset.mem_biUnion.2 ⟨G, hG', ?_⟩)` and prove the remaining obligations. Rewrite using `[if_neg hx]`. Conclude with `hyG`. Establish `e : T = T.biUnion at'`.

Use extensionality with `y`. Use `⟨fun hy => Finset.mem_biUnion.2 ⟨y, hy, self_mem y hy⟩, fun hy => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hyx⟩` from `Finset.mem_biUnion.1 hy`. Conclude with `h2 x hx y (patt x y hyx)`. Rewrite using `[e]`.

Conclude with `hB _ _ fun x _ => hat x`.
-/
theorem of_atoms {X : Type} [DecidableEq X] (S : Finset X → Prop) (h0 : S ∅)
    (hU : ∀ A B, S A → S B → S (A ∪ B)) (hD : ∀ A B, S A → S B → S (A \ B))
    (𝒢 : Finset (Finset X)) (hG : ∀ G ∈ 𝒢, S G) (T : Finset X)
    (h1 : ∀ x ∈ T, ∃ G ∈ 𝒢, x ∈ G) (h2 : ∀ x ∈ T, ∀ y, (∀ G ∈ 𝒢, (x ∈ G ↔ y ∈ G)) → y ∈ T) : S T := by
  have hB : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Finset X), (∀ i ∈ s, S (f i)) → S (s.biUnion f) := by
    intro ι _ s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      exact hU _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  let U : X → Finset X := fun x => (𝒢.filter (x ∈ ·)).biUnion id
  let at' : X → Finset X := fun x => U x \ 𝒢.biUnion (fun G => if x ∈ G then U x \ G else G)
  have hUS : ∀ x, S (U x) := fun x => hB _ _ fun G hG' => hG G (Finset.mem_filter.1 hG').1
  have hat : ∀ x, S (at' x) := fun x => hD _ _ (hUS x) (hB _ _ fun G hG' => by
    split_ifs
    · exact hD _ _ (hUS x) (hG G hG')
    · exact hG G hG')
  have self_mem : ∀ x ∈ T, x ∈ at' x := fun x hx => by
    obtain ⟨G, hG', hxG⟩ := h1 x hx
    refine Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨G, Finset.mem_filter.2 ⟨hG', hxG⟩, hxG⟩, fun h => ?_⟩
    obtain ⟨G', _, hx'⟩ := Finset.mem_biUnion.1 h
    split_ifs at hx' with h'
    · exact (Finset.mem_sdiff.1 hx').2 h'
    · exact h' hx'
  have patt : ∀ x y, y ∈ at' x → ∀ G ∈ 𝒢, (x ∈ G ↔ y ∈ G) := fun x y hy G hG' => by
    obtain ⟨hyU, hyn⟩ := Finset.mem_sdiff.1 hy
    by_cases hx : x ∈ G
    · refine iff_of_true hx (by_contra fun hyG => hyn (Finset.mem_biUnion.2 ⟨G, hG', ?_⟩))
      rw [if_pos hx]; exact Finset.mem_sdiff.2 ⟨hyU, hyG⟩
    · refine iff_of_false hx fun hyG => hyn (Finset.mem_biUnion.2 ⟨G, hG', ?_⟩)
      rw [if_neg hx]; exact hyG
  have e : T = T.biUnion at' := by
    ext y
    refine ⟨fun hy => Finset.mem_biUnion.2 ⟨y, hy, self_mem y hy⟩, fun hy => ?_⟩
    obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.1 hy
    exact h2 x hx y (patt x y hyx)
  rw [e]
  exact hB _ _ fun x _ => hat x

end Comb

section Ops

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V) (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem sign_cases : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[coordR]`.
-/
theorem coordR_zero' : coordR (F := F) V R 0 = 0 := by
  funext i; simp [coordR]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[coordR, map_add]`.
-/
theorem coordR_add' (x y : V.V) : coordR (F := F) V R (x + y) = coordR (F := F) V R x + coordR (F := F) V R y := by
  funext i; simp [coordR, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[coordR, map_mul]`.
-/
theorem coordR_smul' (c : E) (x : V.V) : coordR (F := F) V R (c • x) = inclR (F := F) R c • coordR (F := F) V R x := by
  funext i; simp [coordR, map_mul]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => rw [coordR_zero']`. Conclude with `N.zero_mem`. Consider the case `add x y _ _ hx hy => rw [coordR_add']`.

Conclude with `N.add_mem hx hy`. Consider the case `smul c x _ hx => rw [coordR_smul']`. Conclude with `N.smul_mem _ hx`.
-/
theorem span_coord (N : Submodule (R ⊗[F] E) (Fin V.rank → R ⊗[F] E)) (S : Set V.V)
    (hS : ∀ v ∈ S, coordR (F := F) V R v ∈ N) {v : V.V} (hv : v ∈ Submodule.span E S) : coordR (F := F) V R v ∈ N := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [coordR_zero']; exact N.zero_mem
  | add x y _ _ hx hy => rw [coordR_add']; exact N.add_mem hx hy
  | smul c x _ hx => rw [coordR_smul']; exact N.smul_mem _ hx

/- English proof (translation)
Simplify using `only [GlobalTheory.Cusp.hR_eq hc V, Pi.add_apply, map_add]`. Rewrite using `[← add_dotProduct]`. Both sides reduce to the same expression.
-/
theorem hR_add_l (a b y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram (a + b) y = hR R hc.sig V.gram a y + hR R hc.sig V.gram b y := by
  simp only [GlobalTheory.Cusp.hR_eq hc V, Pi.add_apply, map_add]
  rw [← add_dotProduct]; rfl

/- English proof (translation)
Simplify using `only [GlobalTheory.Cusp.hR_eq hc V, Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[← smul_eq_mul, ← smul_dotProduct]`. Both sides reduce to the same expression.
-/
theorem hR_smul_l (c : R ⊗[F] E) (a y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram (c • a) y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig c * hR R hc.sig V.gram a y := by
  simp only [GlobalTheory.Cusp.hR_eq hc V, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← smul_eq_mul, ← smul_dotProduct]; rfl

def cf (v : V.V) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y (coordR V R v)
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cf_apply (v : V.V) (y : Fin V.rank → R ⊗[F] E) : cf hc R v y = hR R hc.sig V.gram (coordR V R v) y := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]`. Simplify using `[hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]`.
-/
theorem cf_coordR (v x : V.V) : cf hc R v (coordR V R x) = inclR R (V.hD x v) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

def vecOf (s : SignType) (i : Fin (wittIndex V)) : V.V := if s = 1 then Φ.e i else Φ.f i

def dualOf (s : SignType) (i : Fin (wittIndex V)) : V.V := if s = 1 then Φ.f i else Φ.e i

/- English proof (translation)
Establish `hfe : ∀ i j, V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0` using `fun i j => by`. Establish `h` using `V.herm.eq (Φ.f i) (Φ.e j)`. Establish `h2` using `Φ.ef j i`. Simplify using `only [HSpace.hD] at h2 ⊢`. Rewrite using `[← h, h2]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij]`. Establish `n1 : (1 : SignType) ≠ -1` using `by decide`.

Apply the tactic sequence `rcases sign_cases s hs with rfl | rfl <;> rcases sign_cases t ht with rfl | rfl <;>`. Simplify using `[vecOf, dualOf, Φ.ef, Φ.ee, Φ.ff, hfe, n1, n1.symm]`.
-/
theorem hD_vecOf_dualOf {s t : SignType} (hs : s ≠ 0) (ht : t ≠ 0) (i j : Fin (wittIndex V)) :
    V.hD (vecOf Φ s i) (dualOf Φ t j) = if (s, i) = (t, j) then 1 else 0 := by
  have hfe : ∀ i j, V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := fun i j => by
    have h := V.herm.eq (Φ.f i) (Φ.e j)
    have h2 := Φ.ef j i
    simp only [HSpace.hD] at h2 ⊢
    rw [← h, h2]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have n1 : (1 : SignType) ≠ -1 := by decide
  rcases sign_cases s hs with rfl | rfl <;> rcases sign_cases t ht with rfl | rfl <;>
    simp [vecOf, dualOf, Φ.ef, Φ.ee, Φ.ff, hfe, n1, n1.symm]

def Eop (x : SignType × Fin (wittIndex V)) : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
  if x.1 = 0 then 0 else (cf hc R (dualOf Φ x.1 x.2)).smulRight (coordR V R (vecOf Φ x.1 x.2))

variable {hc Φ R}

/- English proof (translation)
Unfold `Eop`. Distinguish the cases in `hz : z.1 = 0`. Rewrite using `[if_pos hz, LinearMap.zero_apply, map_zero, if_neg]`. Introduce and unpack `rfl`. Conclude with `hx hz`.

Rewrite using `[if_neg hz, LinearMap.smulRight_apply, map_smul, cf_coordR, hD_vecOf_dualOf Φ hz hx, Prod.mk.eta, Prod.mk.eta, smul_eq_mul] split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[map_one, mul_one]`. Rewrite using `[map_zero, mul_zero]`.
-/
theorem cf_Eop {x z : SignType × Fin (wittIndex V)} (hx : x.1 ≠ 0) (y : Fin V.rank → R ⊗[F] E) :
    cf hc R (dualOf Φ x.1 x.2) (Eop hc Φ R z y) = if z = x then cf hc R (dualOf Φ x.1 x.2) y else 0 := by
  unfold Eop
  by_cases hz : z.1 = 0
  · rw [if_pos hz, LinearMap.zero_apply, map_zero, if_neg]
    rintro rfl; exact hx hz
  · rw [if_neg hz, LinearMap.smulRight_apply, map_smul, cf_coordR, hD_vecOf_dualOf Φ hz hx, Prod.mk.eta, Prod.mk.eta,
      smul_eq_mul]
    split_ifs with h
    · subst h; rw [map_one, mul_one]
    · rw [map_zero, mul_zero]

/- English proof (translation)
Unfold `Eop`. Distinguish the cases in `hz : z.1 = 0`. Rewrite using `[if_pos hz, LinearMap.zero_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hx hz`.

Rewrite using `[if_neg hz, LinearMap.smulRight_apply, cf_coordR, hD_vecOf_dualOf Φ hx hz, Prod.mk.eta, Prod.mk.eta]`. Distinguish the cases in `h : z = x`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h, map_zero, zero_smul]`.
-/
theorem Eop_coordR {x z : SignType × Fin (wittIndex V)} (hx : x.1 ≠ 0) :
    Eop hc Φ R z (coordR V R (vecOf Φ x.1 x.2)) = if z = x then coordR V R (vecOf Φ x.1 x.2) else 0 := by
  unfold Eop
  by_cases hz : z.1 = 0
  · rw [if_pos hz, LinearMap.zero_apply, if_neg]
    rintro rfl; exact hx hz
  · rw [if_neg hz, LinearMap.smulRight_apply, cf_coordR, hD_vecOf_dualOf Φ hx hz, Prod.mk.eta, Prod.mk.eta]
    by_cases h : z = x
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, zero_smul]

/- English proof (translation)
Distinguish the cases in `hx : x.1 = 0`. Establish `: Eop hc Φ R x = 0` using `if_pos hx`. Apply the tactic sequence `rw [this, zero_mul]; split_ifs <;> rfl`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`.

Use `conv_lhs => rw [Eop, if_neg hx, LinearMap.smulRight_apply, cf_Eop hx]`. Use `split_ifs with h`. Rewrite using `[Eop, if_neg hx, LinearMap.smulRight_apply]`. Rewrite using `[zero_smul, LinearMap.zero_apply]`.
-/
theorem Eop_mul (x z : SignType × Fin (wittIndex V)) :
    Eop hc Φ R x * Eop hc Φ R z = if z = x then Eop hc Φ R x else 0 := by
  by_cases hx : x.1 = 0
  · have : Eop hc Φ R x = 0 := if_pos hx
    rw [this, zero_mul]; split_ifs <;> rfl
  refine LinearMap.ext fun y => ?_
  rw [Module.End.mul_apply]
  conv_lhs => rw [Eop, if_neg hx, LinearMap.smulRight_apply, cf_Eop hx]
  split_ifs with h
  · rw [Eop, if_neg hx, LinearMap.smulRight_apply]
  · rw [zero_smul, LinearMap.zero_apply]

variable (hc Φ R) in

def EA (A : Finset (SignType × Fin (wittIndex V))) : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
  ∑ x ∈ A, Eop hc Φ R x

/- English proof (translation)
Simplify using `only [EA, Finset.sum_mul_sum, Eop_mul, Finset.sum_ite_eq', Finset.sum_ite_mem]`.
-/
theorem EA_mul (A B : Finset (SignType × Fin (wittIndex V))) : EA hc Φ R A * EA hc Φ R B = EA hc Φ R (A ∩ B) := by
  simp only [EA, Finset.sum_mul_sum, Eop_mul, Finset.sum_ite_eq', Finset.sum_ite_mem]

/- English proof (translation)
Rewrite using `[EA, LinearMap.sum_apply]`. Simplify using `only [Eop_coordR hx, Finset.sum_ite_eq', if_pos hxA]`.
-/
theorem EA_vecOf {A : Finset (SignType × Fin (wittIndex V))} {x : SignType × Fin (wittIndex V)} (hx : x.1 ≠ 0)
    (hxA : x ∈ A) : EA hc Φ R A (coordR V R (vecOf Φ x.1 x.2)) = coordR V R (vecOf Φ x.1 x.2) := by
  rw [EA, LinearMap.sum_apply]
  simp only [Eop_coordR hx, Finset.sum_ite_eq', if_pos hxA]

/- English proof (translation)
Rewrite using `[EA, LinearMap.sum_apply, map_sum]`. Simplify using `only [cf_Eop hx, Finset.sum_ite_eq', if_pos hxA]`.
-/
theorem cf_EA {A : Finset (SignType × Fin (wittIndex V))} {x : SignType × Fin (wittIndex V)} (hx : x.1 ≠ 0)
    (hxA : x ∈ A) (y : Fin V.rank → R ⊗[F] E) :
    cf hc R (dualOf Φ x.1 x.2) (EA hc Φ R A y) = cf hc R (dualOf Φ x.1 x.2) y := by
  rw [EA, LinearMap.sum_apply, map_sum]
  simp only [cf_Eop hx, Finset.sum_ite_eq', if_pos hxA]

end Ops

section Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {Φ : WittFrame V} {R : Type} [CommRing R] [Algebra F R]

variable (hc R) in

def Ag (g : HA R hc.sig V.gram) : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
  (HA.mat R hc.sig V.gram g).1.mulVecLin

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ag_apply (g : HA R hc.sig V.gram) (y : Fin V.rank → R ⊗[F] E) : Ag hc R g y = act hc V g y := rfl

/- English proof (translation)
Introduce `h`. Use `mem_Aset.1 hx` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `absurd this (by decide)`.
-/
theorem sign_ne_zero {k : ℕ} {w : SV k} {x : SignType × Fin k} (hx : x ∈ Aset w) : x.1 ≠ 0 := by
  intro h
  have := mem_Aset.1 hx
  rw [h, zero_mul] at this
  exact absurd this (by decide)

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem mul_eq_one : ∀ a b : SignType, a * b = 1 → (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by decide

/- English proof (translation)
Use `Submodule.subset_span ?_` and prove the remaining obligations. Break down `mul_eq_one _ _ (mem_Aset.1 hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Conclude with `Or.inl ⟨x.2, h2, by simp [vecOf, h1]⟩`. Conclude with `Or.inr ⟨x.2, h2, by simp [vecOf, h1, show (-1 : SignType) ≠ 1 by decide]⟩`.
-/
theorem vecOf_mem {w : SV (wittIndex V)} {x : SignType × Fin (wittIndex V)} (hx : x ∈ Aset w) :
    vecOf Φ x.1 x.2 ∈ Φ.sub w := by
  refine Submodule.subset_span ?_
  rcases mul_eq_one _ _ (mem_Aset.1 hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨x.2, h2, by simp [vecOf, h1]⟩
  · exact Or.inr ⟨x.2, h2, by simp [vecOf, h1, show (-1 : SignType) ≠ 1 by decide]⟩

/- English proof (translation)
Use `Submodule.subset_span ?_` and prove the remaining obligations. Break down `mul_eq_one _ _ (mem_Aset.1 hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Conclude with `Or.inr ⟨x.2, by simp [h2], by simp [dualOf, h1]⟩`. Conclude with `Or.inl ⟨x.2, by simp [h2], by simp [dualOf, h1, show (-1 : SignType) ≠ 1 by decide]⟩`.
-/
theorem dualOf_mem {w : SV (wittIndex V)} {x : SignType × Fin (wittIndex V)} (hx : x ∈ Aset w) :
    dualOf Φ x.1 x.2 ∈ Φ.sub (-w) := by
  refine Submodule.subset_span ?_
  rcases mul_eq_one _ _ (mem_Aset.1 hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨x.2, by simp [h2], by simp [dualOf, h1]⟩
  · exact Or.inl ⟨x.2, by simp [h2], by simp [dualOf, h1, show (-1 : SignType) ≠ 1 by decide]⟩

/- English proof (translation)
Rewrite using `[EA, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Eop, if_neg (sign_ne_zero hx), LinearMap.smulRight_apply]`. Conclude with `Submodule.smul_mem _ _ (GlobalTheory.Cusp.coordR_mem V R (vecOf_mem hx))`.
-/
theorem EA_mem (w : SV (wittIndex V)) (y : Fin V.rank → R ⊗[F] E) :
    EA hc Φ R (Aset w) y ∈ extSub V R (Φ.sub w) := by
  rw [EA, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [Eop, if_neg (sign_ne_zero hx), LinearMap.smulRight_apply]
  exact Submodule.smul_mem _ _ (GlobalTheory.Cusp.coordR_mem V R (vecOf_mem hx))

/- English proof (translation)
Establish `hle : extSub (F` using `F) V R (Φ.sub w) ≤ LinearMap.ker (EA hc Φ R (Aset w) - LinearMap.id) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `span_coord R _ _ (fun v hv => ?_) hv` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.

Break down `hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩` into its components or cases. Establish `hx : ((1 : SignType), i) ∈ Aset w` using `mem_Aset.2 (by simpa using hi)`. Use `EA_vecOf (hc := hc) (R := R) (Φ := Φ) (x := ((1 : SignType), i)) (show (1 : SignType) ≠ 0 by decide) hx` as an intermediate fact. Simplify `this` using `[vecOf]`. Establish `hi' : w i = -1` using `hi`.

Establish `hx : ((-1 : SignType), i) ∈ Aset w` using `mem_Aset.2 (by simp [hi'])`. Use `EA_vecOf (hc := hc) (R := R) (Φ := Φ) (x := ((-1 : SignType), i)) (show (-1 : SignType) ≠ 0 by decide) hx` as an intermediate fact. Simplify `this` using `[vecOf, show (-1 : SignType) ≠ 1 by decide]`. Use `hle hz` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem EA_fix (w : SV (wittIndex V)) {z : Fin V.rank → R ⊗[F] E} (hz : z ∈ extSub V R (Φ.sub w)) :
    EA hc Φ R (Aset w) z = z := by
  have hle : extSub (F := F) V R (Φ.sub w) ≤ LinearMap.ker (EA hc Φ R (Aset w) - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine span_coord R _ _ (fun v hv => ?_) hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have hx : ((1 : SignType), i) ∈ Aset w := mem_Aset.2 (by simpa using hi)
      have := EA_vecOf (hc := hc) (R := R) (Φ := Φ) (x := ((1 : SignType), i)) (show (1 : SignType) ≠ 0 by decide) hx
      simpa [vecOf] using this
    · have hi' : w i = -1 := hi
      have hx : ((-1 : SignType), i) ∈ Aset w := mem_Aset.2 (by simp [hi'])
      have := EA_vecOf (hc := hc) (R := R) (Φ := Φ) (x := ((-1 : SignType), i)) (show (-1 : SignType) ≠ 0 by decide) hx
      simpa [vecOf, show (-1 : SignType) ≠ 1 by decide] using this
  have := hle hz
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this

/- English proof (translation)
Use `(GlobalTheory.Cusp.mem_extSub_perp hc V).2 fun x hx => ?_` and prove the remaining obligations. Set `N : Submodule (R ⊗[F] E) (Fin V.rank → R ⊗[F] E)` to `{ carrier := {x | hR R hc.sig V.gram x z = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[hR_add_l, ha, hb, add_zero]`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_setOf_eq]`. Use `hR_smul_l hc R 0 0 z` as an intermediate fact. Rewrite `this` using `[zero_smul, map_zero, zero_mul]`. Then use the resulting hypothesis. Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Rewrite using `[hR_smul_l, ha, mul_zero] }`. Establish `hle : extSub (F` using `F) V R (Φ.sub (-w)) ≤ N := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `span_coord R N _ (fun v hv => ?_) hv` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `hR R hc.sig V.gram _ z = 0`. Break down `hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩` into its components or cases. Establish `hx : ((-1 : SignType), i) ∈ Aset w` using `mem_Aset.2 (by`. Establish `: w i = -1` using `by simpa using congrArg Neg.neg hi`. Simplify using `[this])`.

Use `hz _ hx` as an intermediate fact. Simplify `this` using `[cf_apply, dualOf, show (-1 : SignType) ≠ 1 by decide]`. Establish `hx : ((1 : SignType), i) ∈ Aset w` using `mem_Aset.2 (by`. Establish `: w i = 1` using `by simpa using congrArg Neg.neg hi`. Simplify using `[this])`.

Use `hz _ hx` as an intermediate fact. Simplify `this` using `[cf_apply, dualOf]`. Conclude with `hle hx`.
-/
theorem mem_perp_of_cf (w : SV (wittIndex V)) {z : Fin V.rank → R ⊗[F] E}
    (hz : ∀ x ∈ Aset w, cf hc R (dualOf Φ x.1 x.2) z = 0) : z ∈ extSub V R (perp V (Φ.sub (-w))) := by
  refine (GlobalTheory.Cusp.mem_extSub_perp hc V).2 fun x hx => ?_
  let N : Submodule (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
    { carrier := {x | hR R hc.sig V.gram x z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [hR_add_l, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have := hR_smul_l hc R 0 0 z
        rwa [zero_smul, map_zero, zero_mul] at this
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢; rw [hR_smul_l, ha, mul_zero] }
  have hle : extSub (F := F) V R (Φ.sub (-w)) ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine span_coord R N _ (fun v hv => ?_) hv
    change hR R hc.sig V.gram _ z = 0
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have hx : ((-1 : SignType), i) ∈ Aset w := mem_Aset.2 (by
        have : w i = -1 := by simpa using congrArg Neg.neg hi
        simp [this])
      have := hz _ hx
      simpa [cf_apply, dualOf, show (-1 : SignType) ≠ 1 by decide] using this
    · have hx : ((1 : SignType), i) ∈ Aset w := mem_Aset.2 (by
        have : w i = 1 := by simpa using congrArg Neg.neg hi
        simp [this])
      have := hz _ hx
      simpa [cf_apply, dualOf] using this
  exact hle hx

/- English proof (translation)
Rewrite using `[EA, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Eop, if_neg (sign_ne_zero hx), LinearMap.smulRight_apply, cf_apply, (GlobalTheory.Cusp.mem_extSub_perp hc V).1 hz _ (GlobalTheory.Cusp.coordR_mem V R (dualOf_mem hx)), zero_smul]`.
-/
theorem EA_perp (w : SV (wittIndex V)) {z : Fin V.rank → R ⊗[F] E} (hz : z ∈ extSub V R (perp V (Φ.sub (-w)))) :
    EA hc Φ R (Aset w) z = 0 := by
  rw [EA, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Eop, if_neg (sign_ne_zero hx), LinearMap.smulRight_apply, cf_apply,
    (GlobalTheory.Cusp.mem_extSub_perp hc V).1 hz _ (GlobalTheory.Cusp.coordR_mem V R (dualOf_mem hx)), zero_smul]

/- English proof (translation)
Use `show Ag hc R g * EA hc Φ R (Aset w) = EA hc Φ R (Aset w) * Ag hc R g`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, Ag_apply]`. Use `set p := EA hc Φ R (Aset w)`. Establish `hpy : p y ∈ extSub V R (Φ.sub w)` using `EA_mem w y`.

Establish `hq : y - p y ∈ extSub V R (perp V (Φ.sub (-w)))` using `mem_perp_of_cf w fun x hx => by rw [map_sub, cf_EA (sign_ne_zero hx) hx, sub_self]`. Establish `e1 : p (act hc V g (p y)) = act hc V g (p y)` using `EA_fix w (GlobalTheory.Cusp.mem_parab_iff_maps.1 h1 _ hpy)`. Establish `e2 : p (act hc V g (y - p y)) = 0` using `EA_perp w (GlobalTheory.Cusp.mem_parab_iff_maps.1 (GlobalTheory.Cusp.parab_le_perp h2) _ hq)`. Rewrite `e2` using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, map_sub, e1, sub_eq_zero]`. Conclude with `e2.symm`.
-/
theorem commute_gen (g : HA R hc.sig V.gram) (w : SV (wittIndex V)) (h1 : g ∈ parab hc V R (Φ.sub w))
    (h2 : g ∈ parab hc V R (Φ.sub (-w))) : Commute (Ag hc R g) (EA hc Φ R (Aset w)) := by
  show Ag hc R g * EA hc Φ R (Aset w) = EA hc Φ R (Aset w) * Ag hc R g
  refine LinearMap.ext fun y => ?_
  simp only [Module.End.mul_apply, Ag_apply]
  set p := EA hc Φ R (Aset w)
  have hpy : p y ∈ extSub V R (Φ.sub w) := EA_mem w y
  have hq : y - p y ∈ extSub V R (perp V (Φ.sub (-w))) :=
    mem_perp_of_cf w fun x hx => by rw [map_sub, cf_EA (sign_ne_zero hx) hx, sub_self]
  have e1 : p (act hc V g (p y)) = act hc V g (p y) := EA_fix w (GlobalTheory.Cusp.mem_parab_iff_maps.1 h1 _ hpy)
  have e2 : p (act hc V g (y - p y)) = 0 := EA_perp w (GlobalTheory.Cusp.mem_parab_iff_maps.1 (GlobalTheory.Cusp.parab_le_perp h2) _ hq)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, map_sub, e1, sub_eq_zero] at e2
  exact e2.symm

/- English proof (translation)
Establish `e : EA hc Φ R (A ∪ B) = EA hc Φ R A + EA hc Φ R B - EA hc Φ R A * EA hc Φ R B`. Rewrite using `[EA_mul, eq_sub_iff_add_eq]`. Conclude with `Finset.sum_union_inter`. Rewrite using `[e]`. Conclude with `(hA.add_right hB).sub_right (hA.mul_right hB)`.
-/
theorem commute_union (g : HA R hc.sig V.gram) (A B : Finset (SignType × Fin (wittIndex V)))
    (hA : Commute (Ag hc R g) (EA hc Φ R A)) (hB : Commute (Ag hc R g) (EA hc Φ R B)) :
    Commute (Ag hc R g) (EA hc Φ R (A ∪ B)) := by
  have e : EA hc Φ R (A ∪ B) = EA hc Φ R A + EA hc Φ R B - EA hc Φ R A * EA hc Φ R B := by
    rw [EA_mul, eq_sub_iff_add_eq]; exact Finset.sum_union_inter
  rw [e]; exact (hA.add_right hB).sub_right (hA.mul_right hB)

/- English proof (translation)
Establish `e : EA hc Φ R (A \ B) = EA hc Φ R A - EA hc Φ R A * EA hc Φ R B`. Rewrite using `[EA_mul, show A \ B = A \ (A ∩ B) by ext; simp]`. Conclude with `Finset.sum_sdiff_eq_sub Finset.inter_subset_left`. Rewrite using `[e]`. Conclude with `hA.sub_right (hA.mul_right hB)`.
-/
theorem commute_sdiff (g : HA R hc.sig V.gram) (A B : Finset (SignType × Fin (wittIndex V)))
    (hA : Commute (Ag hc R g) (EA hc Φ R A)) (hB : Commute (Ag hc R g) (EA hc Φ R B)) :
    Commute (Ag hc R g) (EA hc Φ R (A \ B)) := by
  have e : EA hc Φ R (A \ B) = EA hc Φ R A - EA hc Φ R A * EA hc Φ R B := by
    rw [EA_mul, show A \ B = A \ (A ∩ B) by ext; simp]
    exact Finset.sum_sdiff_eq_sub Finset.inter_subset_left
  rw [e]; exact hA.sub_right (hA.mul_right hB)

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem sgn_eq : ∀ a b : SignType, (a = 1 ↔ b = 1) → (-a = 1 ↔ -b = 1) → a = b := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem sgn_zero : ∀ a : SignType, ¬ a = 1 → ¬ -a = 1 → a = 0 := by decide

variable (Φ R) in

/- English proof (translation)
Introduce `g hg`. Establish `hgw : ∀ w ∈ P, g ∈ parab hc V R (Φ.sub w) ∧ g ∈ parab hc V R (Φ.sub (-w))` using `fun w hw => Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw)`. Set `𝒢 : Finset (Finset (SignType × Fin (wittIndex V)))` to `P.image Aset ∪ P.image fun w => Aset (-w)`. Establish `key : ∀ u', vec u' ∈ aP P → g ∈ parab hc V R (Φ.sub u')` using `fun u' hu' => by`. Establish `hcomm : Commute (Ag hc R g) (EA hc Φ R (Aset u'))`.

Use `of_atoms (fun A => Commute (Ag hc R g) (EA hc Φ R A)) ?_ (commute_union g) (commute_sdiff g) 𝒢 ?_ _ ?_ ?_` and prove the remaining obligations. Use `show Commute _ (∑ x ∈ ∅, _)`. Rewrite using `[Finset.sum_empty]`. Conclude with `Commute.zero_right _`. Introduce `G hG`.

Apply the tactic sequence `rcases Finset.mem_union.1 hG with hG | hG <;> obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hG`. Conclude with `commute_gen g w (hgw w hw).1 (hgw w hw).2`. Conclude with `commute_gen g (-w) (hgw w hw).2 (by rw [neg_neg]; exact (hgw w hw).1)`. Introduce and unpack `⟨s, i⟩ hx`. Assume the negation of the conclusion as `hn`.

Use `push_neg at hn`. Establish `h0 : ∀ w ∈ P, s * w i = 0 * w i` using `fun w hw => by`. Establish `a` using `hn (Aset w) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))`. Establish `b` using `hn (Aset (-w)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))`. Simplify using `only [mem_Aset, Pi.neg_apply, mul_neg] at a b`.

Rewrite using `[zero_mul]`. Conclude with `sgn_zero _ a b`. Use `pattern hu' h0` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Establish `hx'` using `mem_Aset.1 hx`.

Simplify using `only at hx'`. Rewrite `hx'` using `[this]`. Conclude with `absurd hx' (by decide)`. Introduce and unpack `⟨s, i⟩ hx ⟨t, j⟩ hxy`. Establish `hw : ∀ w ∈ P, s * w i = t * w j` using `fun w hw => by`.

Establish `a` using `hxy (Aset w) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))`. Establish `b` using `hxy (Aset (-w)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))`. Simplify using `only [mem_Aset, Pi.neg_apply, mul_neg] at a b`. Conclude with `sgn_eq _ _ a b`. Establish `hx'` using `mem_Aset.1 hx`.

Simplify using `only at hx'`. Conclude with `mem_Aset.2 ((pattern hu' hw).symm.trans hx')`. Use `GlobalTheory.Cusp.mem_parab_iff_maps.2 fun y hy => ?_` and prove the remaining obligations. Rewrite using `[← EA_fix (hc := hc) u' hy, ← Ag_apply (hc := hc) (R := R), ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]`. Conclude with `EA_mem u' _`.

Use `Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_singleton.1 hv]`. Conclude with `Subgroup.mem_inf.2 ⟨key u hu, key (-u) (by rw [vec_neg]; exact neg_mem hu)⟩`.
-/
theorem levi_le (P : Finset (SV (wittIndex V))) (u : SV (wittIndex V)) (hu : vec u ∈ aP P) :
    Φ.levi hc R P ≤ Φ.levi hc R {u} := by
  intro g hg
  have hgw : ∀ w ∈ P, g ∈ parab hc V R (Φ.sub w) ∧ g ∈ parab hc V R (Φ.sub (-w)) := fun w hw =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw)
  let 𝒢 : Finset (Finset (SignType × Fin (wittIndex V))) := P.image Aset ∪ P.image fun w => Aset (-w)
  have key : ∀ u', vec u' ∈ aP P → g ∈ parab hc V R (Φ.sub u') := fun u' hu' => by
    have hcomm : Commute (Ag hc R g) (EA hc Φ R (Aset u')) := by
      refine of_atoms (fun A => Commute (Ag hc R g) (EA hc Φ R A)) ?_ (commute_union g) (commute_sdiff g) 𝒢 ?_ _ ?_ ?_
      · show Commute _ (∑ x ∈ ∅, _); rw [Finset.sum_empty]; exact Commute.zero_right _
      · intro G hG
        rcases Finset.mem_union.1 hG with hG | hG <;> obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hG
        · exact commute_gen g w (hgw w hw).1 (hgw w hw).2
        · exact commute_gen g (-w) (hgw w hw).2 (by rw [neg_neg]; exact (hgw w hw).1)
      · rintro ⟨s, i⟩ hx
        by_contra hn
        push_neg at hn
        have h0 : ∀ w ∈ P, s * w i = 0 * w i := fun w hw => by
          have a := hn (Aset w) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))
          have b := hn (Aset (-w)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
          simp only [mem_Aset, Pi.neg_apply, mul_neg] at a b
          rw [zero_mul]; exact sgn_zero _ a b
        have := pattern hu' h0
        rw [zero_mul] at this
        have hx' := mem_Aset.1 hx
        simp only at hx'
        rw [this] at hx'
        exact absurd hx' (by decide)
      · rintro ⟨s, i⟩ hx ⟨t, j⟩ hxy
        have hw : ∀ w ∈ P, s * w i = t * w j := fun w hw => by
          have a := hxy (Aset w) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))
          have b := hxy (Aset (-w)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
          simp only [mem_Aset, Pi.neg_apply, mul_neg] at a b
          exact sgn_eq _ _ a b
        have hx' := mem_Aset.1 hx
        simp only at hx'
        exact mem_Aset.2 ((pattern hu' hw).symm.trans hx')
    refine GlobalTheory.Cusp.mem_parab_iff_maps.2 fun y hy => ?_
    rw [← EA_fix (hc := hc) u' hy, ← Ag_apply (hc := hc) (R := R), ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
    exact EA_mem u' _
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
  rw [Finset.mem_singleton.1 hv]
  exact Subgroup.mem_inf.2 ⟨key u hu, key (-u) (by rw [vec_neg]; exact neg_mem hu)⟩

end Levi

/- English proof (translation)
Introduce `_ _ Φ R _ _ P _ u hu` and use `levi_le Φ R P u hu`.
-/
theorem levi_le_levi_singleton : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (R : Type) [CommRing R] [Algebra D.host.F R] P,
    IsPar P → ∀ u, vec u ∈ aP P → Φ.levi D.sp.cm R P ≤ Φ.levi D.sp.cm R {u} :=
  fun _ _ Φ R _ _ P _ u hu => levi_le Φ R P u hu

end GlobalTheory.LeviSign
