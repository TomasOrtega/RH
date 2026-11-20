import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VarietyWithModels
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LevPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

/- English proof (translation)
Establish `h : archM V (C.θ τ.1) (a * u) = archM V (C.θ τ.1) a * archM V (C.θ τ.1) u`. Unfold `archM`. Rewrite using `[map_mul, Units.val_mul, Matrix.map_mul]`. Use `show Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) (a * u)) * C.x₀ τ.1 = _ * (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) u) * C.x₀ τ.1)`. Rewrite using `[h, ← Matrix.mul_assoc]`.

Use `congr 1`. Simplify using `[Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`.
-/
theorem fr_mul (C : Ctx Xo c σ V r) (a u : GA D V) (k : Fin C.F.n) (τ : (C.M.X k).Ψ) :
    mat (C.fr (a * u) k) τ = Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) a) * mat (C.fr u k) τ := by
  have h : archM V (C.θ τ.1) (a * u) = archM V (C.θ τ.1) a * archM V (C.θ τ.1) u := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  show Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) (a * u)) * C.x₀ τ.1 =
    _ * (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) u) * C.x₀ τ.1)
  rw [h, ← Matrix.mul_assoc]
  congr 1
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Take `⟨h1, -, -, -, -, -, h7⟩` from `GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC ((γ * h)⁻¹ * (γ' * h')) k`. Take `⟨u, hu, e⟩` from `h7 _ h1`. Establish `hm2` using `(GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC h k γ hm).2.2.1 u hu`. Establish `hfr : C.fr (γ * (h * u)) k = C.fr (γ' * h') k`. Use function extensionality and compare the values at `τ`.

Establish `e1` using `fr_mul C (γ * h) u k τ`. Establish `e2` using `fr_mul C (γ * h) ((γ * h)⁻¹ * (γ' * h')) k τ`. Rewrite `e1` using `[e, ← e2, mul_inv_cancel_left]`. Rewrite using `[← mul_assoc]`. Conclude with `e1`.

Establish `hk` using `GlobalTheory.T.mem_levelK_of_same_mark_and_frame D H Dw l Xo c σ V r C hC Kf hK _ _ k γ γ' hm2 hm' hfr`. Use `⟨γ'⁻¹ * γ, mul_mem (inv_mem hm'.1) hm.1, u, hu, _, hk, ?_⟩` and prove the remaining obligations. Use `group`.
-/
theorem exists_of_mark (C : Ctx Xo c σ V r) (hC : C.OK) {Kf : Subgroup (GA D V)} (hK : IsLevelK V l.M Kf)
    {h h' : GA D V} {k : Fin C.F.n} {γ γ' : GA D V} (hm : C.Mark h k γ) (hm' : C.Mark h' k γ') :
    ∃ δ ∈ GQ V, ∃ u ∈ GinfC V, ∃ κ ∈ Kf, h' = δ * h * u * κ := by
  obtain ⟨h1, -, -, -, -, -, h7⟩ := GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC ((γ * h)⁻¹ * (γ' * h')) k
  obtain ⟨u, hu, e⟩ := h7 _ h1
  have hm2 := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC h k γ hm).2.2.1 u hu
  have hfr : C.fr (γ * (h * u)) k = C.fr (γ' * h') k := by
    funext τ
    have e1 := fr_mul C (γ * h) u k τ
    have e2 := fr_mul C (γ * h) ((γ * h)⁻¹ * (γ' * h')) k τ
    rw [e, ← e2, mul_inv_cancel_left] at e1
    rw [← mul_assoc]
    exact e1
  have hk := GlobalTheory.T.mem_levelK_of_same_mark_and_frame D H Dw l Xo c σ V r C hC Kf hK _ _ k γ γ' hm2 hm' hfr
  refine ⟨γ'⁻¹ * γ, mul_mem (inv_mem hm'.1) hm.1, u, hu, _, hk, ?_⟩
  group

end Comp

section Abstract

/- English proof (translation)
Set `cl : G → Formalism.UG.ClassSet Q K'` to `fun h => DoubleCoset.mk Q K' (f h)`. Establish `cl_eq : ∀ h h', cl h = cl h' ↔ ∃ x ∈ Q, ∃ k ∈ K', f h' = x * f h * k` using `fun h h' => DoubleCoset.eq _ _ _ _`. Establish `cls_of : ∀ h h', (∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ) → cl h = cl h'`. Introduce and unpack `h _ ⟨δ, hδ, u, hu, κ, hκ, rfl⟩`. Use `(cl_eq _ _).2 ⟨f δ, hQ ▸ Subgroup.mem_map_of_mem _ hδ, f κ, hK κ hκ, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_mul, (hR u).2 hu, mul_one]`. Establish `of_cls : ∀ h h', cl h = cl h' → ∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ`. Introduce `h h' e`. Take `⟨x, hx, k, hk, e'⟩` from `(cl_eq _ _).1 e`. Rewrite `hx` using `[← hQ]`.

Take `⟨δ, hδ, rfl⟩` from `hx`. Take `⟨κ, hκ, rfl⟩` from `hK' _ hk`. Use `⟨δ, hδ, (δ * h)⁻¹ * h' * κ⁻¹, (hR _).1 ?_, κ, hκ, by group⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, map_inv, map_mul, e']`. Use `group`.

Use `choose rep hrep using hd`. Use `⟨Equiv.ofBijective (fun k => cl (rep k)) ⟨fun k k' e => ?_, fun x => ?_⟩⟩` and prove the remaining obligations. Use `inv _ _ (of_cls _ _ e)` as an intermediate fact. Rewrite `this` using `[hrep, hrep, eq_comm]`. Then use the resulting hypothesis. Take `⟨y, rfl⟩ : ∃ y, DoubleCoset.mk Q K' y = x` from `⟨_, DoubleCoset.out_eq' _ _ x⟩`.

Take `⟨h, rfl⟩` from `hf y`. Conclude with `⟨d h, cls_of (rep (d h)) h (same _ _ (hrep _))⟩`.
-/
theorem nonempty_equiv_classSet {G G' n : Type} [Group G] [Group G'] (f : G →* G') (Q K' : Subgroup G') (Γ K R : Subgroup G)
    (hf : Function.Surjective f) (hQ : Γ.map f = Q) (hR : ∀ h, f h = 1 ↔ h ∈ R) (hK : ∀ x ∈ K, f x ∈ K')
    (hK' : ∀ x ∈ K', ∃ y ∈ K, f y = x) (d : G → n) (hd : Function.Surjective d)
    (inv : ∀ h h', (∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ) → d h' = d h)
    (same : ∀ h h', d h = d h' → ∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ) :
    Nonempty (n ≃ Formalism.UG.ClassSet Q K') := by
  let cl : G → Formalism.UG.ClassSet Q K' := fun h => DoubleCoset.mk Q K' (f h)
  have cl_eq : ∀ h h', cl h = cl h' ↔ ∃ x ∈ Q, ∃ k ∈ K', f h' = x * f h * k := fun h h' => DoubleCoset.eq _ _ _ _
  have cls_of : ∀ h h', (∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ) → cl h = cl h' := by
    rintro h _ ⟨δ, hδ, u, hu, κ, hκ, rfl⟩
    refine (cl_eq _ _).2 ⟨f δ, hQ ▸ Subgroup.mem_map_of_mem _ hδ, f κ, hK κ hκ, ?_⟩
    rw [map_mul, map_mul, map_mul, (hR u).2 hu, mul_one]
  have of_cls : ∀ h h', cl h = cl h' → ∃ δ ∈ Γ, ∃ u ∈ R, ∃ κ ∈ K, h' = δ * h * u * κ := by
    intro h h' e
    obtain ⟨x, hx, k, hk, e'⟩ := (cl_eq _ _).1 e
    rw [← hQ] at hx
    obtain ⟨δ, hδ, rfl⟩ := hx
    obtain ⟨κ, hκ, rfl⟩ := hK' _ hk
    refine ⟨δ, hδ, (δ * h)⁻¹ * h' * κ⁻¹, (hR _).1 ?_, κ, hκ, by group⟩
    rw [map_mul, map_mul, map_inv, map_inv, map_mul, e']
    group
  choose rep hrep using hd
  refine ⟨Equiv.ofBijective (fun k => cl (rep k)) ⟨fun k k' e => ?_, fun x => ?_⟩⟩
  · have := inv _ _ (of_cls _ _ e)
    rwa [hrep, hrep, eq_comm] at this
  · obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk Q K' y = x := ⟨_, DoubleCoset.out_eq' _ _ x⟩
    obtain ⟨h, rfl⟩ := hf y
    exact ⟨d h, cls_of (rep (d h)) h (same _ _ (hrep _))⟩

end Abstract

section Classes

open GlobalTheory.Mass Formalism.IndefR.Lev Formalism.L2.DIV

def finP (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (GlobalTheory.LevSplit.finE_mem_UA V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_finP (V : HSp D) (h : GA D V) : (finP V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[coe_finP]`. Express the relevant statement in the definitionally equal form `_ = ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D))`. Rewrite using `[coe_swapPts, hπ h]`. Both sides reduce to the same expression.
-/
theorem finitePart_eq_of_isFiniteProjection (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finP V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  refine Subtype.ext ?_
  rw [coe_finP]
  change _ = ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D))
  rw [coe_swapPts, hπ h]
  rfl

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Rewrite using `[finitePart_eq_of_isFiniteProjection V hπ]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `e1 : π h = 1` using `(swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).injective (e.trans (map_one _).symm)`.

Establish `e2` using `hπ h`. Rewrite `e2` using `[e1]`. Conclude with `e2.symm`. Introduce `e`. Establish `e1 : π h = 1` using `Subtype.ext ((hπ h).trans e)`.

Rewrite using `[e1, map_one]`.
-/
theorem finitePart_eq_one_iff (V : HSp D) (h : GA D V) : finP V h = 1 ↔ h ∈ GinfC V := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rw [finitePart_eq_of_isFiniteProjection V hπ]
  constructor
  · intro e
    have e1 : π h = 1 := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).injective (e.trans (map_one _).symm)
    have e2 := hπ h
    rw [e1] at e2
    exact e2.symm
  · intro e
    have e1 : π h = 1 := Subtype.ext ((hπ h).trans e)
    rw [e1, map_one]

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Take `⟨y, hy⟩` from `(swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x`. Establish `h0 : ∃ g : GA D V, π g = y` using `hπ.surjective y`. Take `⟨g, hg⟩` from `h0`. Establish `h1 : ∃ a ∈ GinfC V, ∃ k ∈ GfC V, g = a * k` using `(GlobalTheory.UnitarySplit.real_finite_split D V).1 g`.

Take `⟨a, ha, k, hk, e⟩` from `h1`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Establish `e1 : finP V g = x` using `(finitePart_eq_of_isFiniteProjection V hπ g).trans (by rw [← hy, ← hg])`. Establish `e2 : finP V g = finP V a * finP V k` using `by rw [e]; exact (finP V).map_mul a k`. Rewrite using `[← e1, e2, (finitePart_eq_one_iff V a).2 ha, one_mul]`.
-/
theorem exists_finP (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finP V h = x := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨y, hy⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  have h0 : ∃ g : GA D V, π g = y := hπ.surjective y
  obtain ⟨g, hg⟩ := h0
  have h1 : ∃ a ∈ GinfC V, ∃ k ∈ GfC V, g = a * k := (GlobalTheory.UnitarySplit.real_finite_split D V).1 g
  obtain ⟨a, ha, k, hk, e⟩ := h1
  refine ⟨k, hk, ?_⟩
  have e1 : finP V g = x := (finitePart_eq_of_isFiniteProjection V hπ g).trans (by rw [← hy, ← hg])
  have e2 : finP V g = finP V a * finP V k := by rw [e]; exact (finP V).map_mul a k
  rw [← e1, e2, (finitePart_eq_one_iff V a).2 ha, one_mul]

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Establish `e : finP V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π` using `MonoidHom.ext (finitePart_eq_of_isFiniteProjection V hπ)`. Establish `h1` using `hπ.map_ratIn`. Establish `h2` using `map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram`. Rewrite `h2` using `[← h1, Subgroup.map_map]`.

Rewrite using `[e]`. Conclude with `h2`.
-/
theorem map_finiteProjection_rat (V : HSp D) : (GQ V).map (finP V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  have e : finP V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π := MonoidHom.ext (finitePart_eq_of_isFiniteProjection V hπ)
  have h1 := hπ.map_ratIn
  have h2 := map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram
  rw [← h1, Subgroup.map_map] at h2
  rw [e]
  exact h2

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

/- English proof (translation)
Establish `hU` using `dictIsUnif_of_isDict D H Dw l Xo c σ V r C hC dict hd Kf hK`. Take `⟨d1, d2, ⟨x0, -, d3⟩, -, -, -⟩` from `hU`. Use `nonempty_equiv_classSet (finP V) _ K (GQ V) Kf (GinfC V) (fun x => ?_) (map_finiteProjection_rat V) (finitePart_eq_one_iff V) hKK hKK' (fun h => (dict h).1) (fun k => ?_) ?_ ?_` and prove the remaining obligations. Take `⟨h, -, e⟩` from `exists_finP V x`. Conclude with `⟨h, e⟩`.

Take `⟨h, e⟩` from `hd.2 k`. Conclude with `⟨h, congrArg Sigma.fst e⟩`. Introduce and unpack `h _ ⟨δ, hδ, u, hu, κ, hκ, rfl⟩`. Take `⟨_, -, e3⟩` from `d2 κ hκ (δ * h * u)`. Take `⟨_, -, e2⟩` from `d3 (δ * h) u hu`.

Take `⟨_, -, e1⟩` from `d1 δ hδ h`. Establish `a3 : (dict (δ * h * u * κ)).1 = (dict (δ * h * u)).1` using `by rw [e3]`. Establish `a2 : (dict (δ * h * u)).1 = (dict (δ * h)).1` using `by rw [e2]`. Establish `a1 : (dict (δ * h)).1 = (dict h).1` using `by rw [e1]`. Conclude with `a3.trans (a2.trans a1)`.

Introduce `h h' e`. Take `⟨γ, hm, -⟩` from `hd.1 h`. Take `⟨γ', hm', -⟩` from `hd.1 h'`. Establish `e' : (dict h).1 = (dict h').1` using `e`. Rewrite `hm` using `[e']`.

Conclude with `exists_of_mark C hC hK hm hm'`.
-/
theorem nonempty_equiv_classes (C : Ctx Xo c σ V r) (hC : C.OK) (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r)
    (hd : C.IsDict dict) {Kf : Subgroup (GA D V)} (hK : IsLevelK V l.M Kf)
    (K : Subgroup (UA D.sp.cm V.gram))
    (hKK : ∀ x ∈ Kf, finP V x ∈ K) (hKK' : ∀ x ∈ K, ∃ y ∈ Kf, finP V y = x) :
    Nonempty (Fin C.F.n ≃ Formalism.UG.ClassSet (UQ D.sp.cm V.gram) K) := by
  have hU := dictIsUnif_of_isDict D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨d1, d2, ⟨x0, -, d3⟩, -, -, -⟩ := hU
  refine nonempty_equiv_classSet (finP V) _ K (GQ V) Kf (GinfC V) (fun x => ?_) (map_finiteProjection_rat V)
    (finitePart_eq_one_iff V) hKK hKK' (fun h => (dict h).1) (fun k => ?_) ?_ ?_
  · obtain ⟨h, -, e⟩ := exists_finP V x
    exact ⟨h, e⟩
  · obtain ⟨h, e⟩ := hd.2 k
    exact ⟨h, congrArg Sigma.fst e⟩
  · rintro h _ ⟨δ, hδ, u, hu, κ, hκ, rfl⟩
    obtain ⟨_, -, e3⟩ := d2 κ hκ (δ * h * u)
    obtain ⟨_, -, e2⟩ := d3 (δ * h) u hu
    obtain ⟨_, -, e1⟩ := d1 δ hδ h
    have a3 : (dict (δ * h * u * κ)).1 = (dict (δ * h * u)).1 := by rw [e3]
    have a2 : (dict (δ * h * u)).1 = (dict (δ * h)).1 := by rw [e2]
    have a1 : (dict (δ * h)).1 = (dict h).1 := by rw [e1]
    exact a3.trans (a2.trans a1)
  · intro h h' e
    obtain ⟨γ, hm, -⟩ := hd.1 h
    obtain ⟨γ', hm', -⟩ := hd.1 h'
    have e' : (dict h).1 = (dict h').1 := e
    rw [e'] at hm
    exact exists_of_mark C hC hK hm hm'

end Classes

section Local

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

/- English proof (translation)
The claim follows from `mem_latS_adele_iff Λ z`.
-/
theorem mem_hatL_iff [Module.Finite (𝓞 E) Λ] (z : Fin n → E ⊗[F] 𝔸) :
    z ∈ hatL (F := F) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (z i)) ∈ locL v Λ :=
  mem_latS_adele_iff Λ z

/- English proof (translation)
Set `u : Fin n → E ⊗[F] 𝔸` to `fun i => Formalism.UG.P.afsplitIE v (y i)`. Establish `h1 : (fun i => prV (E` using `E) v (u i)) = y := funext fun i => Formalism.UG.P.afsplit_prV_IE v _`. Establish `hu : u ∈ hatL (F` using `F) Λ := (mem_hatL_iff Λ u).2 fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[h1]` and apply the resulting hypothesis. Rewrite using `[show (fun i => prV (E := E) w (u i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w hw _]`. Conclude with `zero_mem _`. Take `⟨t, ht, e⟩` from `h u hu`. Use `⟨fun i => prV (E := E) v (t i), (mem_hatL_iff Λ t).1 ht v, ?_⟩` and prove the remaining obligations.

Establish `h2` using `prV_mulVec (E := E) v X u`. Rewrite `h2` using `[h1]`. Rewrite using `[← h2]`. Use function extensionality and compare the values at `i`. Use `congrFun e i` as an intermediate fact.

Simplify using `only [Pi.sub_apply, Pi.smul_apply] at this ⊢`. Rewrite using `[← map_nsmul, ← this, map_sub]`. Conclude with `congrArg _ (congrFun h1 i).symm`.
-/
theorem cong_loc [Module.Finite (𝓞 E) Λ] {X : Matrix (Fin n) (Fin n) (E ⊗[F] 𝔸)} {N : ℕ}
    (h : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, X *ᵥ z - z = N • w) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin n → E ⊗[F] v.adicCompletion F} (hy : y ∈ locL v Λ) :
    ∃ w ∈ locL v Λ, X.map (prV (E := E) v) *ᵥ y - y = N • w := by
  let u : Fin n → E ⊗[F] 𝔸 := fun i => Formalism.UG.P.afsplitIE v (y i)
  have h1 : (fun i => prV (E := E) v (u i)) = y := funext fun i => Formalism.UG.P.afsplit_prV_IE v _
  have hu : u ∈ hatL (F := F) Λ := (mem_hatL_iff Λ u).2 fun w => by
    by_cases hw : w = v
    · subst hw
      rwa [h1]
    · rw [show (fun i => prV (E := E) w (u i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w hw _]
      exact zero_mem _
  obtain ⟨t, ht, e⟩ := h u hu
  refine ⟨fun i => prV (E := E) v (t i), (mem_hatL_iff Λ t).1 ht v, ?_⟩
  have h2 := prV_mulVec (E := E) v X u
  rw [h1] at h2
  rw [← h2]
  funext i
  have := congrFun e i
  simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
  rw [← map_nsmul, ← this, map_sub]
  exact congrArg _ (congrFun h1 i).symm

/- English proof (translation)
Introduce `z hz`. Establish `hNE : (N : E) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Set `t : E ⊗[F] 𝔸` to `(N : E)⁻¹ ⊗ₜ[F] (1 : 𝔸)`. Establish `ht : (N : E ⊗[F] 𝔸) * t = 1`. Establish `: (N : E ⊗[F] 𝔸) = (N : E) ⊗ₜ[F] (1 : 𝔸)` using `(map_natCast (Algebra.TensorProduct.includeLeftRingHom) N).symm`.

Rewrite using `[this, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hNE, one_mul]`. Both sides reduce to the same expression. Use `⟨t • (X *ᵥ z - z), (mem_hatL_iff Λ _).2 fun v => ?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `h v _ ((mem_hatL_iff Λ z).1 hz v)`. Establish `ht' : (N : E ⊗[F] v.adicCompletion F) * prV (E` using `E) v t = 1 := by`.

Rewrite using `[← map_natCast (prV (E := E) v), ← map_mul, ht, map_one]`. Establish `: (fun i => prV (E` using `E) v ((t • (X *ᵥ z - z)) i)) = w := by`. Establish `h2` using `prV_mulVec (E := E) v X z`. Use function extensionality and compare the values at `i`. Establish `e'` using `congrFun e i`.

Rewrite `e'` using `[← h2]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_sub] at e' ⊢`. Rewrite using `[e', nsmul_eq_mul, ← mul_assoc, mul_comm _ (N : E ⊗[F] v.adicCompletion F), ht', one_mul]`. Rewrite using `[this]` and apply the resulting hypothesis. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]`. Rewrite using `[← mul_assoc, ht, one_mul]`.
-/
theorem cong_glob [Module.Finite (𝓞 E) Λ] {X : Matrix (Fin n) (Fin n) (E ⊗[F] 𝔸)} {N : ℕ} (hN : N ≠ 0)
    (h : ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ, X.map (prV (E := E) v) *ᵥ y - y = N • w) :
    ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, X *ᵥ z - z = N • w := by
  intro z hz
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN
  let t : E ⊗[F] 𝔸 := (N : E)⁻¹ ⊗ₜ[F] (1 : 𝔸)
  have ht : (N : E ⊗[F] 𝔸) * t = 1 := by
    have : (N : E ⊗[F] 𝔸) = (N : E) ⊗ₜ[F] (1 : 𝔸) := (map_natCast (Algebra.TensorProduct.includeLeftRingHom) N).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hNE, one_mul]
    rfl
  refine ⟨t • (X *ᵥ z - z), (mem_hatL_iff Λ _).2 fun v => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := h v _ ((mem_hatL_iff Λ z).1 hz v)
    have ht' : (N : E ⊗[F] v.adicCompletion F) * prV (E := E) v t = 1 := by
      rw [← map_natCast (prV (E := E) v), ← map_mul, ht, map_one]
    have : (fun i => prV (E := E) v ((t • (X *ᵥ z - z)) i)) = w := by
      have h2 := prV_mulVec (E := E) v X z
      funext i
      have e' := congrFun e i
      rw [← h2] at e'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_sub] at e' ⊢
      rw [e', nsmul_eq_mul, ← mul_assoc, mul_comm _ (N : E ⊗[F] v.adicCompletion F), ht', one_mul]
    rwa [this]
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, ht, one_mul]

/- English proof (translation)
Establish `hval : Valued.v (b : v.adicCompletion F) = 1`. Establish `e` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b : F)`. Rewrite `e` using `[show ((b : F) : v.adicCompletion F) = (b : v.adicCompletion F) from map_natCast (algebraMap F (v.adicCompletion F)) b, show (b : F) = algebraMap (𝓞 F) F ((b : ℕ) : 𝓞 F) from (map_natCast _ b).symm, v.valuation_of_algebraMap]`. Rewrite using `[e]`. Conclude with `le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hb ((v.intValuation_lt_one_iff_mem _).1 h))`.

Establish `hne : (b : v.adicCompletion F) ≠ 0` using `fun h => by`. Rewrite `hval` using `[h, map_zero]`. Conclude with `zero_ne_one hval`. Set `a : v.adicCompletion F` to `(b : v.adicCompletion F)⁻¹`. Establish `ha : a ∈ v.adicCompletionIntegers F` using `by show Valued.v a ≤ 1`.

Rewrite using `[map_inv₀, hval, inv_one]`. Establish `hint : (1 : E) ⊗ₜ[F] a ∈ intV E v` using `Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`. Use `⟨((1 : E) ⊗ₜ[F] a) • w, Submodule.smul_mem _ (⟨_, hint⟩ : intV E v) hw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `hb1 : (b : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] a) = 1`.

Establish `: (b : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (b : v.adicCompletion F)` using `(map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) b).symm`. Rewrite using `[this, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hne]`. Both sides reduce to the same expression. Simplify using `only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]`. Rewrite using `[← mul_assoc, hb1, one_mul]`.
-/
theorem exists_nsmul_eq {v : HeightOneSpectrum (𝓞 F)} {b : ℕ} (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {w : Fin n → E ⊗[F] v.adicCompletion F} (hw : w ∈ locL v Λ) : ∃ w' ∈ locL v Λ, w = b • w' := by
  have hval : Valued.v (b : v.adicCompletion F) = 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b : F)
    rw [show ((b : F) : v.adicCompletion F) = (b : v.adicCompletion F) from map_natCast (algebraMap F (v.adicCompletion F)) b,
      show (b : F) = algebraMap (𝓞 F) F ((b : ℕ) : 𝓞 F) from (map_natCast _ b).symm, v.valuation_of_algebraMap] at e
    rw [e]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hb ((v.intValuation_lt_one_iff_mem _).1 h))
  have hne : (b : v.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  let a : v.adicCompletion F := (b : v.adicCompletion F)⁻¹
  have ha : a ∈ v.adicCompletionIntegers F := by
    show Valued.v a ≤ 1
    rw [map_inv₀, hval, inv_one]
  have hint : (1 : E) ⊗ₜ[F] a ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  refine ⟨((1 : E) ⊗ₜ[F] a) • w, Submodule.smul_mem _ (⟨_, hint⟩ : intV E v) hw, ?_⟩
  funext i
  have hb1 : (b : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] a) = 1 := by
    have : (b : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (b : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) b).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hne]
    rfl
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, hb1, one_mul]

/- English proof (translation)
Establish `fwd : ∀ {M : Matrix (Fin n) (Fin n) (E ⊗[F] 𝔸)}, (∀ z ∈ hatL (F` using `F) Λ, ∃ w ∈ hatL (F := F) Λ, M *ᵥ z - z = N • w) → ∀ z ∈ hatL (F := F) Λ, M *ᵥ z ∈ hatL (F := F) Λ := by`. Introduce `M h z hz`. Take `⟨w, hw, e⟩` from `h z hz`. Rewrite using `[sub_eq_iff_eq_add.1 e]`. Conclude with `add_mem (AddSubmonoid.nsmul_mem _ hw _) hz`.

Use `Subgroup.mem_inf.2 ⟨hU, fun u => ⟨fwd h u, fun hx => ?_⟩⟩` and prove the remaining obligations. Use `fwd h' _ hx` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem mem_levelAfL_of_cong (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (x : GL (Fin n) (E ⊗[F] 𝔸)) (hU : x ∈ UPts σ J 𝔸) (N : ℕ)
    (h : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, x.1 *ᵥ z - z = N • w)
    (h' : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, (x⁻¹).1 *ᵥ z - z = N • w) : x ∈ levelAfL σ J Λ := by
  have fwd : ∀ {M : Matrix (Fin n) (Fin n) (E ⊗[F] 𝔸)},
      (∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, M *ᵥ z - z = N • w) →
      ∀ z ∈ hatL (F := F) Λ, M *ᵥ z ∈ hatL (F := F) Λ := by
    intro M h z hz
    obtain ⟨w, hw, e⟩ := h z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (AddSubmonoid.nsmul_mem _ hw _) hz
  refine Subgroup.mem_inf.2 ⟨hU, fun u => ⟨fwd h u, fun hx => ?_⟩⟩
  have := fwd h' _ hx
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨((mem_levelAfL_iff F E σ n J Λ inferInstance x).1 (mem_levelAfL_of_cong σ J Λ x hU N h h')).2 v, fun _ hy => cong_loc Λ h v hy⟩`.
-/
theorem loc_of_cong (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) [Module.Finite (𝓞 E) Λ]
    (x : GL (Fin n) (E ⊗[F] 𝔸)) (hU : x ∈ UPts σ J 𝔸) (N : ℕ)
    (h : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, x.1 *ᵥ z - z = N • w)
    (h' : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, (x⁻¹).1 *ᵥ z - z = N • w) (v : HeightOneSpectrum (𝓞 F)) :
    bc (prV (E := E) v) x ∈ levelVL σ J v Λ ∧ ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ,
      (bc (prV (E := E) v) x).1 *ᵥ y - y = N • w :=
  ⟨((mem_levelAfL_iff F E σ n J Λ inferInstance x).1 (mem_levelAfL_of_cong σ J Λ x hU N h h')).2 v,
    fun _ hy => cong_loc Λ h v hy⟩

/- English proof (translation)
Establish `h1` using `((Subgroup.mem_inf.1 hx).2 y).1 hy`. Conclude with `exists_nsmul_eq Λ hN (sub_mem h1 hy)`.
-/
theorem cong_of_stab {v : HeightOneSpectrum (𝓞 F)} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Λ) {N : ℕ} (hN : ((N : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {y : Fin n → E ⊗[F] v.adicCompletion F} (hy : y ∈ locL v Λ) : ∃ w ∈ locL v Λ, x.1 *ᵥ y - y = N • w := by
  have h1 := ((Subgroup.mem_inf.1 hx).2 y).1 hy
  exact exists_nsmul_eq Λ hN (sub_mem h1 hy)

/- English proof (translation)
Introduce `y hy`. Take `⟨w, hw, e⟩` from `h y hy`. Use `⟨b • w, AddSubmonoid.nsmul_mem _ hw _, ?_⟩` and prove the remaining obligations. Rewrite using `[e, mul_nsmul', Nat.cast_smul_eq_nsmul]`.
-/
theorem princ_of_cong {v : HeightOneSpectrum (𝓞 F)} {x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)} {a b : ℕ}
    (h : ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ, x *ᵥ y - y = (a * b) • w) :
    ∀ y ∈ locL v Λ, ∃ z ∈ locL v Λ, x *ᵥ y - y = (a : E ⊗[F] v.adicCompletion F) • z := by
  intro y hy
  obtain ⟨w, hw, e⟩ := h y hy
  refine ⟨b • w, AddSubmonoid.nsmul_mem _ hw _, ?_⟩
  rw [e, mul_nsmul', Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Introduce `y hy`. Take `⟨z, hz, e⟩` from `h y hy`. Take `⟨w, hw, rfl⟩` from `exists_nsmul_eq Λ hb hz`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[e, mul_nsmul', Nat.cast_smul_eq_nsmul]`.
-/
theorem cong_of_princ {v : HeightOneSpectrum (𝓞 F)} {x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)} {a b : ℕ}
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : ∀ y ∈ locL v Λ, ∃ z ∈ locL v Λ, x *ᵥ y - y = (a : E ⊗[F] v.adicCompletion F) • z) :
    ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ, x *ᵥ y - y = (a * b) • w := by
  intro y hy
  obtain ⟨z, hz, e⟩ := h y hy
  obtain ⟨w, hw, rfl⟩ := exists_nsmul_eq Λ hb hz
  refine ⟨w, hw, ?_⟩
  rw [e, mul_nsmul', Nat.cast_smul_eq_nsmul]

end Local

section LocalLevel

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (Λ : Submodule (𝓞 E) (Fin S.rank → E))

def InLocG (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL hc.sig S.gram v Λ ∧ ∀ i : Fin 2, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal → InPrinc hc S v (gp i) Λ x

variable {hc S gp Λ}

/- English proof (translation)
Take `⟨lev, cong⟩` from `loc_of_cong Λ hc.sig S.gram x hU N h h' v`. Use `⟨lev, fun i _ => ⟨lev, ?_⟩⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hcof i`. Rewrite `cong` using `[hb]`. Conclude with `princ_of_cong Λ cong`.
-/
theorem inLocG_of_cong [Module.Finite (𝓞 E) Λ] {N : ℕ}
    (hcof : ∀ i : Fin 2, ∃ b : ℕ, N = gp i * b)
    (x : GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hU : x ∈ UPts hc.sig S.gram (FiniteAdeleRing (𝓞 F) F))
    (h : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, x.1 *ᵥ z - z = N • w)
    (h' : ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, (x⁻¹).1 *ᵥ z - z = N • w) (v : HeightOneSpectrum (𝓞 F)) :
    InLocG hc S gp Λ v (bc (prV (E := E) v) x) := by
  obtain ⟨lev, cong⟩ := loc_of_cong Λ hc.sig S.gram x hU N h h' v
  refine ⟨lev, fun i _ => ⟨lev, ?_⟩⟩
  obtain ⟨b, hb⟩ := hcof i
  rw [hb] at cong
  exact princ_of_cong Λ cong

/- English proof (translation)
Use `cong_glob Λ hN fun v y hy => ?_` and prove the remaining obligations. Distinguish the cases in `hv : ∃ i : Fin 2, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal`. Take `⟨i, hi⟩` from `hv`. Take `⟨b, hb, hb'⟩` from `hcof v i hi`. Rewrite using `[hb]`.

Conclude with `cong_of_princ Λ hb' ((h v).2 i hi).2 y hy`. Conclude with `cong_of_stab Λ (h v).1 (hNv v fun i hi => hv ⟨i, hi⟩) hy`.
-/
theorem cong_of_inLocG [Module.Finite (𝓞 E) Λ] {N : ℕ} (hN : N ≠ 0)
    (hcof : ∀ (v : HeightOneSpectrum (𝓞 F)) (i : Fin 2), ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ∃ b : ℕ, N = gp i * b ∧ ((b : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hNv : ∀ v : HeightOneSpectrum (𝓞 F), (∀ i : Fin 2, ((gp i : ℕ) : 𝓞 F) ∉ v.asIdeal) → ((N : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (x : GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), InLocG hc S gp Λ v (bc (prV (E := E) v) x)) :
    ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, x.1 *ᵥ z - z = N • w := by
  refine cong_glob Λ hN fun v y hy => ?_
  by_cases hv : ∃ i : Fin 2, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal
  · obtain ⟨i, hi⟩ := hv
    obtain ⟨b, hb, hb'⟩ := hcof v i hi
    rw [hb]
    exact cong_of_princ Λ hb' ((h v).2 i hi).2 y hy
  · exact cong_of_stab Λ (h v).1 (hNv v fun i hi => hv ⟨i, hi⟩) hy

end LocalLevel

section Level

open Formalism.L2.Geo.Def Formalism.IndefR.Lev Formalism.L2.DIV
open Formalism.UG (levelVL levelAfL prV bc stabGL)

variable (D)

/- English proof (translation)
Establish `key : ∀ a b : ℕ, Nat.Coprime a b → ((a : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((b : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal`. Introduce `a b hab ha hb`. Establish `h1 : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b` using `Nat.gcd_eq_gcd_ab a b`. Rewrite `h1` using `[hab]`. Establish `h2` using `congrArg (Int.cast : ℤ → 𝓞 D.host.F) h1`.

Move the coercions through the operations in `at h2`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)))`. Establish `hc : Nat.Coprime (D.host.g 0) (D.host.g 1)` using `(Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne`. Use `fin_cases i`. Conclude with `⟨D.host.g 1, rfl, key _ _ hc⟩`.

Conclude with `⟨D.host.g 0, mul_comm _ _, key _ _ hc.symm⟩`.
-/
theorem exists_cofactor (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2) :
    ∃ b : ℕ, D.host.g 0 * D.host.g 1 = D.host.g i * b ∧
      (((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((b : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  have key : ∀ a b : ℕ, Nat.Coprime a b → ((a : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((b : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro a b hab ha hb
    have h1 : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
    rw [hab] at h1
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.host.F) h1
    push_cast at h2
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)))
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  fin_cases i
  · exact ⟨D.host.g 1, rfl, key _ _ hc⟩
  · exact ⟨D.host.g 0, mul_comm _ _, key _ _ hc.symm⟩

/- English proof (translation)
Introduce `z hz`. Take `⟨y, hy, e⟩` from `h _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)`. Use `⟨_, GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ y hy, funext fun i => ?_⟩` and prove the remaining obligations. Apply `(Algebra.TensorProduct.comm F _ E).injective` to reduce the goal to its premises. Use `congrFun e i` as an intermediate fact.

Simplify `this` using `only [Pi.sub_apply, Pi.smul_apply, map_sub, map_nsmul, Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply, Matrix.map_apply]`.
-/
theorem cong_swap_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      M.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), M *ᵥ z - z = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  refine ⟨_, GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ y hy, funext fun i => ?_⟩
  apply (Algebra.TensorProduct.comm F _ E).injective
  have := congrFun e i
  simpa only [Pi.sub_apply, Pi.smul_apply, map_sub, map_nsmul, Matrix.mulVec, dotProduct, map_sum, map_mul,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

variable {D}

def HatCong (V : HSp D) (N : ℕ) (y : GA D V) : Prop :=
  ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latC V), ∃ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latC V),
    (finE V y).1 *ᵥ z - z = N • w

/- English proof (translation)
Establish `hl` using `(latHat_eq_hat_and_gram D V).1`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Unfold `FinCong at ha`. Rewrite `ha` using `[hl]`.

Conclude with `GlobalTheory.PrincInLevel.cong_swap _ N _ ha`. Introduce `ha`. Unfold `FinCong`. Rewrite using `[hl]`. Conclude with `cong_swap_symm _ N _ ha`.
-/
theorem finCong_iff_hatCong (V : HSp D) (N : ℕ) (y : GA D V) : FinCong V N y ↔ HatCong V N y := by
  have hl := (latHat_eq_hat_and_gram D V).1
  constructor
  · intro ha
    unfold FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ N _ ha
  · intro ha
    unfold FinCong
    rw [hl]
    exact cong_swap_symm _ N _ ha

instance finite_latC (V : HSp D) : Module.Finite (𝓞 D.host.E) (latC V) :=
  Module.Finite.iff_fg.2 (latHat_eq_hat_and_gram D V).2.2.1

/- English proof (translation)
The claim follows from `mem_levelAfL_of_cong _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA V y) N h (by intro z hz obtain ⟨w, hw, e⟩ := h' z hz refine ⟨w, hw, ?_⟩ rw [← e, map_inv])`.
-/
theorem finE_mem_levelAfL (V : HSp D) {N : ℕ} {y : GA D V} (h : HatCong V N y) (h' : HatCong V N y⁻¹) :
    finE V y ∈ levelAfL D.sp.cm.sig V.gram (latC V) :=
  mem_levelAfL_of_cong _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA V y) N h (by
    intro z hz
    obtain ⟨w, hw, e⟩ := h' z hz
    refine ⟨w, hw, ?_⟩
    rw [← e, map_inv])

end Level

end GlobalTheory.LevPin
