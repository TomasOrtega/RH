import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.McCramer
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaSerre
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFlatten.Flatten

section Linear

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `h` using `b.det.toMultilinearMap.map_smul_univ (fun _ => t) g`. Simplify `h` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.
-/
theorem det_smul_cols {W : Type} [AddCommGroup W] [Module Ω W] {r : ℕ} (b : Module.Basis (Fin r) Ω W) (t : Ω)
    (g : Fin r → W) : b.det (fun k => t • g k) = t ^ r * b.det g := by
  have h := b.det.toMultilinearMap.map_smul_univ (fun _ => t) g
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

/- English proof (translation)
Set `φ : V →ₗ[A] E` to `V.subtype.restrictScalars A`. Establish `hφ : Function.Injective φ` using `Subtype.val_injective`. Establish `h : ∀ {ι : Type} (g : ι → V), Submodule.span A (Set.range fun k => (g k : E)) = (Submodule.span A (Set.range g)).map φ`. Introduce `ι g`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[h, h]`. Conclude with `(Submodule.map_injective_of_injective hφ).eq_iff`.
-/
theorem span_val_eq_iff (A : Subring Ω) (V : Submodule Ω E) {ι ι' : Type} (g : ι → V) (g' : ι' → V) :
    Submodule.span A (Set.range fun k => (g k : E)) = Submodule.span A (Set.range fun k => (g' k : E)) ↔
      Submodule.span A (Set.range g) = Submodule.span A (Set.range g') := by
  let φ : V →ₗ[A] E := V.subtype.restrictScalars A
  have hφ : Function.Injective φ := Subtype.val_injective
  have h : ∀ {ι : Type} (g : ι → V),
      Submodule.span A (Set.range fun k => (g k : E)) = (Submodule.span A (Set.range g)).map φ := by
    intro ι g
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h, h]
  exact (Submodule.map_injective_of_injective hφ).eq_iff

/- English proof (translation)
Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' Ω z`. Rewrite `hspan` using `[hs]`. Establish `: Finite κ` using `Finite.of_injective a ha`. Use `Fintype.ofFinite κ` as an intermediate fact. Set `B : Module.Basis κ Ω W` to `Module.Basis.mk hli hspan.ge`.

Establish `hcard : Fintype.card κ = r`. Establish `h1` using `Module.finrank_eq_card_basis B`. Establish `h2` using `Module.finrank_eq_card_basis b`. Rewrite `h2` using `[h1]`. Simplify using `using h2`.

Set `e : Fin r ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨a ∘ e, ?_⟩` and prove the remaining obligations. Establish `hli' : LinearIndependent Ω (z ∘ (a ∘ e))` using `hli.comp e e.injective`. Establish `hsp' : Submodule.span Ω (Set.range (z ∘ (a ∘ e))) = ⊤`. Rewrite using `[← Function.comp_assoc, EquivLike.range_comp]`.

Conclude with `hspan`. Establish `hu` using `b.isUnit_det (Module.Basis.mk hli' hsp'.ge)`. Rewrite `hu` using `[Module.Basis.coe_mk]`. Conclude with `hu.ne_zero`.
-/
theorem exists_det_ne {W : Type} [AddCommGroup W] [Module Ω W] {r n : ℕ} (b : Module.Basis (Fin r) Ω W)
    (z : Fin n → W) (hs : Submodule.span Ω (Set.range z) = ⊤) : ∃ c : Fin r → Fin n, b.det (z ∘ c) ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω z
  rw [hs] at hspan
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  let B : Module.Basis κ Ω W := Module.Basis.mk hli hspan.ge
  have hcard : Fintype.card κ = r := by
    have h1 := Module.finrank_eq_card_basis B
    have h2 := Module.finrank_eq_card_basis b
    rw [h1] at h2
    simpa using h2
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent Ω (z ∘ (a ∘ e)) := hli.comp e e.injective
  have hsp' : Submodule.span Ω (Set.range (z ∘ (a ∘ e))) = ⊤ := by
    rw [← Function.comp_assoc, EquivLike.range_comp]
    exact hspan
  have hu := b.isUnit_det (Module.Basis.mk hli' hsp'.ge)
  rw [Module.Basis.coe_mk] at hu
  exact hu.ne_zero

/- English proof (translation)
Establish `hbV : ∀ k, b k ∈ V` using `fun k => by`. Rewrite using `[← hV]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Set `bV : Fin r' → V` to `fun k => ⟨b k, hbV k⟩`. Establish `hliV : LinearIndependent Ω bV` using `LinearIndependent.of_comp V.subtype hb`.

Establish `hspV : Submodule.span Ω (Set.range bV) = ⊤`. Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]`. Conclude with `hV`. Establish `hrr : r' = r`.

Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hliV hspV.ge)`. Establish `h2` using `Module.finrank_eq_card_basis b₀`. Rewrite `h2` using `[h1]`. Simplify using `using h2`. Substitute `hrr` using the available equality.

Establish `hsp' : Submodule.span A (Set.range fun k => t • z k) = Submodule.span A (Set.range bV)` using `(span_val_eq_iff A V (fun k => t • z k) bV).1 hsp`. Take `⟨l, hl, hl2⟩` from `PositivityTheory.HtPt.Mc.frame_plucker Ω V A r' b₀ (Fin n) (fun k => t • z k) bV hliV hsp'`. Establish `hdet : ∀ c : Fin r' → Fin n, b₀.det ((fun k => t • z k) ∘ c) = t ^ r' * b₀.det (z ∘ c)` using `fun c => det_smul_cols b₀ t (z ∘ c)`. Establish `htr : t ^ r' ≠ 0` using `pow_ne_zero _ ht`. Use `⟨l, ?_, fun c => ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hl` to reduce the goal to its premises. Rewrite using `[hdet, h0, mul_zero]`. Establish `h3` using `hl2 c`. Rewrite `h3` using `[hdet, hdet, mul_div_mul_left _ _ htr]`. Then use the resulting hypothesis.
-/
theorem dominant_minor (A : Subring Ω) [IsLocalRing A] (V : Submodule Ω E) {r r' n : ℕ}
    (b₀ : Module.Basis (Fin r) Ω V) (z : Fin n → V) {t : Ω} (ht : t ≠ 0) (b : Fin r' → E)
    (hb : LinearIndependent Ω b) (hV : Submodule.span Ω (Set.range b) = V)
    (hsp : Submodule.span A (Set.range fun k => t • (z k : E)) = Submodule.span A (Set.range b)) :
    ∃ l : Fin r → Fin n, b₀.det (z ∘ l) ≠ 0 ∧ ∀ c : Fin r → Fin n, b₀.det (z ∘ c) / b₀.det (z ∘ l) ∈ A := by
  have hbV : ∀ k, b k ∈ V := fun k => by
    rw [← hV]
    exact Submodule.subset_span ⟨k, rfl⟩
  let bV : Fin r' → V := fun k => ⟨b k, hbV k⟩
  have hliV : LinearIndependent Ω bV := LinearIndependent.of_comp V.subtype hb
  have hspV : Submodule.span Ω (Set.range bV) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hV
  have hrr : r' = r := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hliV hspV.ge)
    have h2 := Module.finrank_eq_card_basis b₀
    rw [h1] at h2
    simpa using h2
  subst hrr
  have hsp' : Submodule.span A (Set.range fun k => t • z k) = Submodule.span A (Set.range bV) :=
    (span_val_eq_iff A V (fun k => t • z k) bV).1 hsp
  obtain ⟨l, hl, hl2⟩ := PositivityTheory.HtPt.Mc.frame_plucker Ω V A r' b₀ (Fin n) (fun k => t • z k) bV hliV hsp'
  have hdet : ∀ c : Fin r' → Fin n, b₀.det ((fun k => t • z k) ∘ c) = t ^ r' * b₀.det (z ∘ c) :=
    fun c => det_smul_cols b₀ t (z ∘ c)
  have htr : t ^ r' ≠ 0 := pow_ne_zero _ ht
  refine ⟨l, ?_, fun c => ?_⟩
  · intro h0
    apply hl
    rw [hdet, h0, mul_zero]
  · have h3 := hl2 c
    rwa [hdet, hdet, mul_div_mul_left _ _ htr] at h3

variable {Ω' : Type} [Field Ω'] {F : Type} [AddCommGroup F] [Module Ω' F]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Rewrite `he` using `[SetLike.mem_coe]`. Proceed by induction on `he using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y y' _ _ hy hy'`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hy'`.

Consider the case `smul a y _ hy`. Establish `e1 : j (a • y) = (⟨i a, hA a a.2⟩ : A) • j y` using `by show j ((a : Ω) • y) = i a • j y`. Conclude with `hj a y`. Rewrite using `[e1]`. Conclude with `Submodule.smul_mem _ _ hy`.

Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_image_span (i : Ω →+* Ω') (j : E →+ F) (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e)
    (A₀ : Subring Ω) (A : Subring Ω') (hA : ∀ a ∈ A₀, i a ∈ A) (S : Set E) :
    Submodule.span A (j '' ((Submodule.span A₀ S : Submodule A₀ E) : Set E)) = Submodule.span A (j '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    rw [SetLike.mem_coe] at he
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [map_add]
      exact Submodule.add_mem _ hy hy'
    | smul a y _ hy =>
      have e1 : j (a • y) = (⟨i a, hA a a.2⟩ : A) • j y := by
        show j ((a : Ω) • y) = i a • j y
        exact hj a y
      rw [e1]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Take `⟨hsm, hli⟩` from `hj`. Establish `hmem : ∀ e : V, j e ∈ Submodule.span Ω' (j '' (V : Set E))` using `fun e => Submodule.subset_span ⟨e, e.2, rfl⟩`. Set `J : V →+ Submodule.span Ω' (j '' (V : Set E))` to `{ toFun := fun e => ⟨j e, hmem e⟩ map_zero' := by ext; simp map_add' := by intro a b; ext; simp }`. Establish `hJs : ∀ (c : Ω) (v : V), J (c • v) = i c • J v` using `fun c v => Subtype.ext (hsm c v)`. Establish `hJsum : ∀ v : V, J v = ∑ k, i (b₀.repr v k) • J (b₀ k)`.

Introduce `v`. Use `conv_lhs => rw [← b₀.sum_repr v]`. Rewrite using `[map_sum]`. Simplify using `only [hJs]`. Establish `hJli : LinearIndependent Ω' (J ∘ b₀)`.

Apply `LinearIndependent.of_comp (Submodule.span Ω' (j '' (V : Set E))).subtype` to reduce the goal to its premises. Conclude with `hli r (fun k => (b₀ k : E)) (b₀.linearIndependent.map' V.subtype V.ker_subtype)`. Establish `hJsp : ⊤ ≤ Submodule.span Ω' (Set.range (J ∘ b₀))`. Introduce and unpack `⟨y, hy⟩ -`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨e, he, rfl⟩` from `hy`. Establish `e1 : (⟨j e, hmem ⟨e, he⟩⟩ : Submodule.span Ω' (j '' (V : Set E))) = J ⟨e, he⟩` using `rfl`. Rewrite using `[e1, hJsum]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => exact Submodule.add_mem _ hy hz`. Consider the case `smul a y _ hy => exact Submodule.smul_mem _ a hy`. Set `b'` to `Module.Basis.mk hJli hJsp`. Establish `hb' : ∀ k, b' k = J (b₀ k)` using `fun k => Module.Basis.mk_apply _ _ _`.

Establish `hrep : ∀ (v : V) (a : Fin r), b'.repr (J v) a = i (b₀.repr v a)`. Introduce `v a`. Establish `h1 : J v = ∑ k, i (b₀.repr v k) • b' k`. Rewrite using `[hJsum v]`. Simplify using `only [hb']`.

Rewrite using `[h1, Module.Basis.repr_sum_self]`. Use `⟨b', J, fun e => rfl, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a c`.

Simplify using `only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Function.comp, hrep]`.
-/
theorem ext_basis (i : Ω →+* Ω') (j : E →+ F) (hj : IsExtOver i j) (V : Submodule Ω E) {r : ℕ}
    (b₀ : Module.Basis (Fin r) Ω V) :
    ∃ (b' : Module.Basis (Fin r) Ω' (Submodule.span Ω' (j '' (V : Set E))))
      (J : V →+ Submodule.span Ω' (j '' (V : Set E))),
      (∀ e, (J e : F) = j e) ∧ ∀ g : Fin r → V, b'.det (J ∘ g) = i (b₀.det g) := by
  obtain ⟨hsm, hli⟩ := hj
  have hmem : ∀ e : V, j e ∈ Submodule.span Ω' (j '' (V : Set E)) := fun e =>
    Submodule.subset_span ⟨e, e.2, rfl⟩
  let J : V →+ Submodule.span Ω' (j '' (V : Set E)) :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hJs : ∀ (c : Ω) (v : V), J (c • v) = i c • J v := fun c v => Subtype.ext (hsm c v)
  have hJsum : ∀ v : V, J v = ∑ k, i (b₀.repr v k) • J (b₀ k) := by
    intro v
    conv_lhs => rw [← b₀.sum_repr v]
    rw [map_sum]
    simp only [hJs]
  have hJli : LinearIndependent Ω' (J ∘ b₀) := by
    apply LinearIndependent.of_comp (Submodule.span Ω' (j '' (V : Set E))).subtype
    exact hli r (fun k => (b₀ k : E)) (b₀.linearIndependent.map' V.subtype V.ker_subtype)
  have hJsp : ⊤ ≤ Submodule.span Ω' (Set.range (J ∘ b₀)) := by
    rintro ⟨y, hy⟩ -
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, rfl⟩ := hy
      have e1 : (⟨j e, hmem ⟨e, he⟩⟩ : Submodule.span Ω' (j '' (V : Set E))) = J ⟨e, he⟩ := rfl
      rw [e1, hJsum]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ a hy
  let b' := Module.Basis.mk hJli hJsp
  have hb' : ∀ k, b' k = J (b₀ k) := fun k => Module.Basis.mk_apply _ _ _
  have hrep : ∀ (v : V) (a : Fin r), b'.repr (J v) a = i (b₀.repr v a) := by
    intro v a
    have h1 : J v = ∑ k, i (b₀.repr v k) • b' k := by
      rw [hJsum v]
      simp only [hb']
    rw [h1, Module.Basis.repr_sum_self]
  refine ⟨b', J, fun e => rfl, fun g => ?_⟩
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext a c
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Function.comp, hrep]

end Linear

/- English proof (translation)
Use `choose U hU using fun t => PositivityTheory.HtPt.Ma.reg_open X Ω ξ p (a t) (h t)`. Use `⟨⟨⋂ t, (U t : Set X), isOpen_iInter_of_finite fun t => (U t).isOpen⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.2 fun t => (hU t).1`. Introduce `q hq t`. Conclude with `(hU t).2 q (Set.mem_iInter.1 hq t)`.
-/
theorem reg_near {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) {ι : Type}
    [Finite ι] (a : ι → Ω) (h : ∀ t, a t ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ t, a t ∈ regAt ξ q := by
  choose U hU using fun t => PositivityTheory.HtPt.Ma.reg_open X Ω ξ p (a t) (h t)
  refine ⟨⟨⋂ t, (U t : Set X), isOpen_iInter_of_finite fun t => (U t).isOpen⟩, ?_, ?_⟩
  · exact Set.mem_iInter.2 fun t => (hU t).1
  · intro q hq t
    exact (hU t).2 q (Set.mem_iInter.1 hq t)

/- English proof (translation)
Take `⟨b', J, hJ, hdetJ⟩` from `ext_basis i j hj V b₀`. Introduce `p' hp'`. Take `⟨hp'c, l, hl⟩` from `hp'`. Take `⟨p₀, ⟨hreg, -⟩, -, -⟩` from `PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i p' hp'c`. Take `⟨c, hc⟩` from `M.tie.cover p₀`.

Establish `hxc : x c ≠ 0` using `hc.1`. Take `⟨U, hpU, hU⟩` from `reg_near ξ' p' (Sum.elim (fun c' : Fin r → Fin n => i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l))) (fun k : κ => i (x k / x c))) (by`. Introduce and unpack `(c' | k)`. Conclude with `hl.2 c'`. Conclude with `hreg _ (hc.2 k))`.

Set `w : Fin n → Submodule.span Ω' (j '' (V : Set E))` to `fun k => i (x c ^ d)⁻¹ • J (z k)`. Establish `hcoe : ∀ k, ((w k : Submodule.span Ω' (j '' (V : Set E))) : F) = i (x c ^ d)⁻¹ • j (z k)`. Introduce `k`. Simplify using `only [w, Submodule.coe_smul, hJ]`. Establish `hdw : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') = i (x c ^ d)⁻¹ ^ r * i (b₀.det (z ∘ c'))`.

Introduce `c'`. Rewrite using `[← hdetJ]`. Conclude with `det_smul_cols b' (i (x c ^ d)⁻¹) (J ∘ (z ∘ c'))`. Establish `hit : i (x c ^ d)⁻¹ ^ r ≠ 0` using `pow_ne_zero _ ((map_ne_zero i).2 (inv_ne_zero (pow_ne_zero _ hxc)))`. Establish `hwl : b'.det (w ∘ l) ≠ 0`.

Rewrite using `[hdw]`. Conclude with `mul_ne_zero hit hl.1`. Establish `hratio : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') / b'.det (w ∘ l) = i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l))`. Introduce `c'`. Rewrite using `[hdw, hdw, mul_div_mul_left _ _ hit]`.

Establish `hbasis : Submodule.span Ω' (Set.range (w ∘ l)) = ⊤`. Conclude with `((Module.Basis.is_basis_iff_det b').2 (isUnit_iff_ne_zero.2 hwl)).2`. Use `⟨U, hpU, fun k => i (x c ^ d)⁻¹ • j (z (l k)), ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : (Set.range fun k => i (x c ^ d)⁻¹ • j (z (l k))) = (Submodule.span Ω' (j '' (V : Set E))).subtype '' Set.range (w ∘ l)`. Rewrite using `[← Set.range_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(hcoe (l k)).symm`. Rewrite using `[e1, ← Submodule.map_span, hbasis, Submodule.map_subtype_top]`. Introduce `q' hq' hqU`.

Take `⟨hq'c, -⟩` from `hq'`. Take `⟨q₀, hq₀, -, hchart⟩` from `PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i q' hq'c`. Establish `hqa` using `hU q' hqU`. Establish `hq0 : InChart M.ξ x c q₀` using `hchart c hxc fun k => hqa (Sum.inr k)`. Establish `hcr` using `PositivityTheory.HtPt.Mc.cramer_sub Ω' _ (regAt ξ' q') r b' (Fin n) w l hwl (fun c' => by rw [hratio]; exact hqa (Sum.inl c'))`.

Use `show LinearIndependent Ω' _ ∧ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h5` using `hcr.1.map' (Submodule.span Ω' (j '' (V : Set E))).subtype (Submodule.ker_subtype _)`. Establish `e4 : (fun k => i (x c ^ d)⁻¹ • j (z (l k))) = ⇑(Submodule.span Ω' (j '' (V : Set E))).subtype ∘ w ∘ l`. Use function extensionality and compare the values at `k`.

Conclude with `(hcoe (l k)).symm`. Rewrite using `[e4]`. Conclude with `h5`. Rewrite using `[PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j q₀ q' hcoh hq₀, hz c q₀ hq0, span_image_span i j hj.1 (regAt M.ξ q₀) (regAt ξ' q') hq₀.1, ← Set.range_comp]`. Establish `e2` using `(span_val_eq_iff (regAt ξ' q') (Submodule.span Ω' (j '' (V : Set E))) w (w ∘ l)).2 hcr.2`.

Establish `e3 : (⇑j ∘ fun k => (x c ^ d)⁻¹ • (z k : E)) = fun k => ((w k : _) : F)`. Use function extensionality and compare the values at `k`. Rewrite using `[hcoe]`. Conclude with `hj.1 _ _`. Rewrite using `[e3, e2]`.

Simplify using `only [Function.comp_apply, hcoe]`.
-/
theorem vb_on {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E)
    (hcoh : L.IsCohOn Set.univ) {d n r : ℕ} (b₀ : Module.Basis (Fin r) Ω V) (z : Fin n → V)
    (hz : ∀ c (p : Cpt M.ξ), InChart M.ξ x c p →
      L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • (z k : E)))
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    {F : Type} [AddCommGroup F] [Module Ω' F] (j : E →+ F) (hj : IsExtOver i j) :
    (L.pullLoc ξ' i j).IsVBOn
      {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (b₀.det (z ∘ l))) l p'} r
      (Submodule.span Ω' (j '' (V : Set E))) := by
  obtain ⟨b', J, hJ, hdetJ⟩ := ext_basis i j hj V b₀
  intro p' hp'
  obtain ⟨hp'c, l, hl⟩ := hp'
  obtain ⟨p₀, ⟨hreg, -⟩, -, -⟩ :=
    PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i p' hp'c
  obtain ⟨c, hc⟩ := M.tie.cover p₀
  have hxc : x c ≠ 0 := hc.1
  obtain ⟨U, hpU, hU⟩ := reg_near ξ' p'
    (Sum.elim (fun c' : Fin r → Fin n => i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l)))
      (fun k : κ => i (x k / x c)))
    (by
      rintro (c' | k)
      · exact hl.2 c'
      · exact hreg _ (hc.2 k))
  let w : Fin n → Submodule.span Ω' (j '' (V : Set E)) := fun k => i (x c ^ d)⁻¹ • J (z k)
  have hcoe : ∀ k, ((w k : Submodule.span Ω' (j '' (V : Set E))) : F) = i (x c ^ d)⁻¹ • j (z k) := by
    intro k
    simp only [w, Submodule.coe_smul, hJ]
  have hdw : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') = i (x c ^ d)⁻¹ ^ r * i (b₀.det (z ∘ c')) := by
    intro c'
    rw [← hdetJ]
    exact det_smul_cols b' (i (x c ^ d)⁻¹) (J ∘ (z ∘ c'))
  have hit : i (x c ^ d)⁻¹ ^ r ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero i).2 (inv_ne_zero (pow_ne_zero _ hxc)))
  have hwl : b'.det (w ∘ l) ≠ 0 := by
    rw [hdw]
    exact mul_ne_zero hit hl.1
  have hratio : ∀ c' : Fin r → Fin n, b'.det (w ∘ c') / b'.det (w ∘ l) =
      i (b₀.det (z ∘ c')) / i (b₀.det (z ∘ l)) := by
    intro c'
    rw [hdw, hdw, mul_div_mul_left _ _ hit]
  have hbasis : Submodule.span Ω' (Set.range (w ∘ l)) = ⊤ := by
    exact ((Module.Basis.is_basis_iff_det b').2 (isUnit_iff_ne_zero.2 hwl)).2
  refine ⟨U, hpU, fun k => i (x c ^ d)⁻¹ • j (z (l k)), ?_, ?_⟩
  · have e1 : (Set.range fun k => i (x c ^ d)⁻¹ • j (z (l k))) =
        (Submodule.span Ω' (j '' (V : Set E))).subtype '' Set.range (w ∘ l) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      exact (hcoe (l k)).symm
    rw [e1, ← Submodule.map_span, hbasis, Submodule.map_subtype_top]
  · intro q' hq' hqU
    obtain ⟨hq'c, -⟩ := hq'
    obtain ⟨q₀, hq₀, -, hchart⟩ :=
      PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre o Ω κ x M X' Ω' ξ' i q' hq'c
    have hqa := hU q' hqU
    have hq0 : InChart M.ξ x c q₀ := hchart c hxc fun k => hqa (Sum.inr k)
    have hcr := PositivityTheory.HtPt.Mc.cramer_sub Ω' _ (regAt ξ' q') r b' (Fin n) w l hwl
      (fun c' => by rw [hratio]; exact hqa (Sum.inl c'))
    show LinearIndependent Ω' _ ∧ _
    refine ⟨?_, ?_⟩
    · have h5 := hcr.1.map' (Submodule.span Ω' (j '' (V : Set E))).subtype (Submodule.ker_subtype _)
      have e4 : (fun k => i (x c ^ d)⁻¹ • j (z (l k))) =
          ⇑(Submodule.span Ω' (j '' (V : Set E))).subtype ∘ w ∘ l := by
        funext k
        exact (hcoe (l k)).symm
      rw [e4]
      exact h5
    · rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j q₀ q' hcoh hq₀, hz c q₀ hq0,
        span_image_span i j hj.1 (regAt M.ξ q₀) (regAt ξ' q') hq₀.1, ← Set.range_comp]
      have e2 := (span_val_eq_iff (regAt ξ' q') (Submodule.span Ω' (j '' (V : Set E))) w (w ∘ l)).2 hcr.2
      have e3 : (⇑j ∘ fun k => (x c ^ d)⁻¹ • (z k : E)) = fun k => ((w k : _) : F) := by
        funext k
        rw [hcoe]
        exact hj.1 _ _
      rw [e3, e2]
      simp only [Function.comp_apply, hcoe]

/- English proof (translation)
Take `⟨d, n, z, hz⟩` from `PositivityTheory.HtPt.Ma.serre o Ω κ x M E L hcoh`. Set `p₀ : Cpt M.ξ` to `⟨genPt M.ξ, specializes_refl _⟩`. Take `⟨c₀, hc₀⟩` from `M.tie.cover p₀`. Establish `hzV : ∀ k, z k ∈ V`. Introduce `k`.

Rewrite using `[← hgen p₀]`. Establish `h1 : (x c₀ ^ d)⁻¹ • z k ∈ L p₀`. Rewrite using `[hz c₀ p₀ hc₀]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Establish `h2 : (x c₀ ^ d)⁻¹ • z k ∈ Submodule.span Ω (L p₀ : Set E)` using `Submodule.subset_span h1`.

Establish `h3` using `Submodule.smul_mem (Submodule.span Ω (L p₀ : Set E)) (x c₀ ^ d) h2`. Rewrite `h3` using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hc₀.1), one_smul]`. Then use the resulting hypothesis. Establish `hspanE : Submodule.span Ω (Set.range z) = V`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hzV k`. Rewrite using `[← hgen p₀, hz c₀ p₀ hc₀, Submodule.span_span_of_tower, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Set `zV : Fin n → V` to `fun k => ⟨z k, hzV k⟩`. Establish `hspanV : Submodule.span Ω (Set.range zV) = ⊤`. Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]`. Conclude with `hspanE`.

Set `b₀` to `Module.finBasis Ω V`. Use `⟨Fin (Module.finrank Ω V) → Fin n, inferInstance, fun l => b₀.det (zV ∘ l), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `exists_det_ne b₀ zV hspanV`. Introduce and unpack `p ⟨r', b, hbli, hbL⟩`. Take `⟨c, hc⟩` from `M.tie.cover p`.

Establish `hV' : Submodule.span Ω (Set.range b) = V`. Rewrite using `[← hgen p, hbL, Submodule.span_span_of_tower]`. Establish `hloc : IsLocalRing (regAt M.ξ p)` using `(PositivityTheory.HtPt.Ma.reg_local _ _ M.ξ).1 p`. Establish `hsp : Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • ((zV k : V) : E)) = Submodule.span (regAt M.ξ p) (Set.range b)`. Rewrite using `[← hbL]`.

Conclude with `(hz c p hc).symm`. Take `⟨l, hl, hl2⟩` from `dominant_minor (regAt M.ξ p) V b₀ zV (inv_ne_zero (pow_ne_zero _ hc.1)) b hbli hV' hsp`. Conclude with `⟨l, show _ ∧ _ from ⟨hl, hl2⟩⟩`. Introduce `X' Ω' _ ξ' i F _ _ j hj`. Conclude with `vb_on M L V hcoh b₀ zV (fun c p hc => hz c p hc) ξ' i j hj`.
-/
theorem plucker_block (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E)
    [FiniteDimensional Ω V] (hcoh : L.IsCohOn Set.univ) (hgen : ∀ p, Submodule.span Ω (L p : Set E) = V) :
    ∃ (κ' : Type) (_ : Finite κ') (w : κ' → Ω), (∃ l, w l ≠ 0) ∧
      (∀ p : Cpt M.ξ, (∃ (r : ℕ) (b : Fin r → E), L.IsFrameAt b p) → ∃ l, InChart M.ξ w l p) ∧
      ∀ (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
        (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F), IsExtOver i j →
        (L.pullLoc ξ' i j).IsVBOn {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (w l)) l p'}
          (Module.finrank Ω V) (Submodule.span Ω' (j '' (V : Set E))) := by
  obtain ⟨d, n, z, hz⟩ := PositivityTheory.HtPt.Ma.serre o Ω κ x M E L hcoh
  let p₀ : Cpt M.ξ := ⟨genPt M.ξ, specializes_refl _⟩
  obtain ⟨c₀, hc₀⟩ := M.tie.cover p₀
  have hzV : ∀ k, z k ∈ V := by
    intro k
    rw [← hgen p₀]
    have h1 : (x c₀ ^ d)⁻¹ • z k ∈ L p₀ := by
      rw [hz c₀ p₀ hc₀]
      exact Submodule.subset_span ⟨k, rfl⟩
    have h2 : (x c₀ ^ d)⁻¹ • z k ∈ Submodule.span Ω (L p₀ : Set E) := Submodule.subset_span h1
    have h3 := Submodule.smul_mem (Submodule.span Ω (L p₀ : Set E)) (x c₀ ^ d) h2
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hc₀.1), one_smul] at h3
  have hspanE : Submodule.span Ω (Set.range z) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hzV k
    · rw [← hgen p₀, hz c₀ p₀ hc₀, Submodule.span_span_of_tower, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let zV : Fin n → V := fun k => ⟨z k, hzV k⟩
  have hspanV : Submodule.span Ω (Set.range zV) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hspanE
  let b₀ := Module.finBasis Ω V
  refine ⟨Fin (Module.finrank Ω V) → Fin n, inferInstance, fun l => b₀.det (zV ∘ l), ?_, ?_, ?_⟩
  · exact exists_det_ne b₀ zV hspanV
  · rintro p ⟨r', b, hbli, hbL⟩
    obtain ⟨c, hc⟩ := M.tie.cover p
    have hV' : Submodule.span Ω (Set.range b) = V := by
      rw [← hgen p, hbL, Submodule.span_span_of_tower]
    have hloc : IsLocalRing (regAt M.ξ p) := (PositivityTheory.HtPt.Ma.reg_local _ _ M.ξ).1 p
    have hsp : Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • ((zV k : V) : E)) =
        Submodule.span (regAt M.ξ p) (Set.range b) := by
      rw [← hbL]
      exact (hz c p hc).symm
    obtain ⟨l, hl, hl2⟩ := dominant_minor (regAt M.ξ p) V b₀ zV (inv_ne_zero (pow_ne_zero _ hc.1)) b hbli hV' hsp
    exact ⟨l, show _ ∧ _ from ⟨hl, hl2⟩⟩
  · intro X' Ω' _ ξ' i F _ _ j hj
    exact vb_on M L V hcoh b₀ zV (fun c p hc => hz c p hc) ξ' i j hj

end PositivityTheory.HtPt.Mb.LFlatten.Flatten

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Mb.LFlatten.Flatten.plucker_block`.
-/
theorem PositivityTheory.HtPt.Mb.flatten : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (V : Submodule Ω E) [FiniteDimensional Ω V], L.IsCohOn Set.univ → (∀ p, Submodule.span Ω (L p : Set E) = V) → ∃ (κ' : Type) (_ : Finite κ') (w : κ' → Ω), (∃ l, w l ≠ 0) ∧ (∀ p : Cpt M.ξ, (∃ (r : ℕ) (b : Fin r → E), L.IsFrameAt b p) → ∃ l, InChart M.ξ w l p) ∧ ∀ (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F), IsExtOver i j → (L.pullLoc ξ' i j).IsVBOn {p' | p' ∈ ctrSet o x i ξ' ∧ ∃ l, InChart ξ' (fun l => i (w l)) l p'} (Module.finrank Ω V) (Submodule.span Ω' (j '' (V : Set E))) :=
  @PositivityTheory.HtPt.Mb.LFlatten.Flatten.plucker_block
