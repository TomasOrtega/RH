import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.FnDeg

open GlobalTheory.ProjSpace

/- English proof (translation)
Establish `h1` using `Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)`. Establish `h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `appLE_pullRatio (hi := le_rfl) g le_rfl`. Conclude with `h1.trans (congrArg _ h2)`.
-/
theorem eval_pullRatio_comp {X Y : Scheme.{0}} {N : ℕ} (g : X ⟶ Y) (ψ : Y ⟶ PSpace ℤ N) (x : X)
    (i : Fin (N + 1)) (hx : g x ∈ ψ ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    (g.residueFieldMap x).hom ((Y.evaluation (ψ ⁻¹ᵁ chart ℤ N i) (g x) hx).hom (pullRatio ψ _ i le_rfl j)) =
      (X.evaluation ((g ≫ ψ) ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio (g ≫ ψ) _ i le_rfl j) := by
  have h1 := Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)
  have h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_pullRatio (hi := le_rfl) g le_rfl
  exact h1.trans (congrArg _ h2)

/- English proof (translation)
Use `set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))`. Establish `hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K`. Introduce `s`. Take `⟨q, rfl⟩` from `aeval_ratio_surjective ℤ N i s`. Proceed by induction on `q using MvPolynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[aeval_C]`. Simplify using `using K.intCast_mem a`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`.

Conclude with `K.add_mem ha hb`. Consider the case `mul_X a j ha`. Rewrite using `[map_mul, map_mul, aeval_X]`. Conclude with `K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)`. Set `ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K` to `CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K) (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)`.

Use `GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Establish `hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec = (PSpace ℤ N).fromSpecResidueField p`. Rewrite using `[Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]`. Conclude with `hev`.
-/
theorem closure_eval_ratio {N : ℕ} (p : PSpace ℤ N) (i : Fin (N + 1)) (hp : p ∈ chart ℤ N i) :
    Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j)) = ⊤ := by
  set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))
  have hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K := by
    intro s
    obtain ⟨q, rfl⟩ := aeval_ratio_surjective ℤ N i s
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      simpa using K.intCast_mem a
    | add a b ha hb =>
      rw [map_add, map_add]
      exact K.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul, aeval_X]
      exact K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)
  let ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K)
      (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)
  refine GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K
    (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_
  rw [← Category.assoc, ← Spec.map_comp]
  have hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec =
      (PSpace ℤ N).fromSpecResidueField p := by
    rw [Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp,
      IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]
  exact hev

/- English proof (translation)
Introduce and unpack `_ ⟨a, rfl⟩`. Establish `ha : a ∈ Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j))`. Establish `hc` using `closure_eval_ratio (φ x) i hx`. Rewrite using `[hc]`. Conclude with `Subfield.mem_top a`.

Establish `h1 : (φ.residueFieldMap x).hom a ∈ _` using `Subfield.mem_map.2 ⟨a, ha, rfl⟩`. Rewrite `h1` using `[RingHom.map_field_closure]`. Use `Subfield.closure_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Use `⟨j, ?_⟩` and prove the remaining obligations.

Establish `h2` using `Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)`. Rewrite `h2` using `[Scheme.Hom.app_eq_appLE]`. Conclude with `h2.symm`.
-/
theorem range_residueFieldMap_le {X : Scheme.{0}} {N : ℕ} (φ : X ⟶ PSpace ℤ N) (x : X) (i : Fin (N + 1))
    (hx : x ∈ φ ⁻¹ᵁ chart ℤ N i) :
    Set.range (φ.residueFieldMap x).hom ⊆
      Subfield.closure (Set.range fun j => (X.evaluation (φ ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio φ _ i le_rfl j)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subfield.closure (Set.range fun j =>
      ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j)) := by
    have hc := closure_eval_ratio (φ x) i hx
    rw [hc]
    exact Subfield.mem_top a
  have h1 : (φ.residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
  rw [RingHom.map_field_closure] at h1
  refine Subfield.closure_mono ?_ h1
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  have h2 := Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)
  rw [Scheme.Hom.app_eq_appLE] at h2
  exact h2.symm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Simplify using `only [ptCoord, pullRatio_self, map_one]`.
-/
theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp only [ptCoord, pullRatio_self, map_one]

/- English proof (translation)
Use `(range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_` and prove the remaining obligations. Use `Subfield.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩`.
-/
theorem range_prB_le (x : MP ℤ m n) (k : Fin (m + 1)) :
    Set.range ((prB n k).residueFieldMap x).hom ⊆ Subfield.closure (Set.range (ptCoord x)) := by
  refine (range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_
  refine Subfield.closure_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩

abbrev sndM (m : ℕ) (n : Fin (m + 2) → ℕ) : MP ℤ (m + 1) n ⟶ MP ℤ m (Fin.tail n) :=
  pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))

/- English proof (translation)
The claim follows from `eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j`.
-/
theorem residueFieldMap_ptCoord_sndM {n : Fin (m + 2) → ℕ} (x : MP ℤ (m + 1) n) (k : Fin (m + 1))
    (j : Bk (Fin.tail n) k) :
    ((sndM m n).residueFieldMap x).hom (ptCoord (sndM m n x) ⟨k, j⟩) = ptCoord x ⟨k.succ, j⟩ :=
  eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j

/- English proof (translation)
The claim follows from `| 0, n, x => by haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _)) refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_ exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a | m + 1, n, x => by have H : Subfield.closure (Set.range ( …`.
-/
theorem closure_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n),
    Subfield.closure (Set.range (ptCoord x)) = ⊤
  | 0, n, x => by
    haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _))
    refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_
    exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a
  | m + 1, n, x => by
    have H : Subfield.closure (Set.range ((prB n 0).residueFieldMap x).hom ∪
        Set.range ((sndM m n).residueFieldMap x).hom) = ⊤ :=
      GlobalTheory.closure_range_residueFieldMap_pullback_eq_top _ _ _ (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) x
    rw [eq_top_iff, ← H]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact range_prB_le x 0 ⟨a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      have ha : a ∈ Subfield.closure (Set.range (ptCoord (sndM m n x))) := by
        rw [closure_ptCoord m (Fin.tail n) (sndM m n x)]
        exact Subfield.mem_top a
      have h1 : ((sndM m n).residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
      rw [RingHom.map_field_closure] at h1
      refine Subfield.closure_mono ?_ h1
      rintro _ ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
      exact ⟨⟨k.succ, j⟩, (residueFieldMap_ptCoord_sndM x k j).symm⟩

/- English proof (translation)
Use `eq_top_iff.2 fun a _ => ?_` and prove the remaining obligations. Establish `hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield`. Use `Subfield.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Use `IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[ptCoord_ptChart, div_one]`. Conclude with `hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)`.
-/
theorem blockFnField_ptCoord (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)] :
    blockFnField (ptCoord x) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨p, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩
    rw [ptCoord_ptChart, div_one]
  exact hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)

/- English proof (translation)
Unfold `blockFnField`. Rewrite using `[IntermediateField.adjoin_map]`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, q, h, rfl⟩`. Conclude with `⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩`. Introduce and unpack `⟨_, ⟨p, q, h, rfl⟩, rfl⟩`. Conclude with `⟨p, q, h, by simp [map_div₀]⟩`.
-/
theorem blockFnField_comp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω Ω' : Type*} [Field Ω]
    [CharZero Ω] [Field Ω'] [CharZero Ω'] (g : Ω →ₐ[ℚ] Ω') (y : (Σ k, ι k) → Ω) :
    blockFnField (g ∘ y) = (blockFnField y).map g := by
  unfold blockFnField
  rw [IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp [map_div₀]⟩

/- English proof (translation)
The claim follows from `(residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm`.
-/
theorem ptCoord_sv (n' : ℕ) {m : ℕ} (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (p : Σ k, Bk n k) :
    ptCoord x (sv n' n p) = ((qpSnd n' m n).residueFieldMap x).hom (ptCoord ((qpSnd n' m n) x) p) :=
  (residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm

/- English proof (translation)
Introduce `n' m n x _`. Set `f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x` to `(qpSnd n' m n).residueFieldMap x`. Use `haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) := (RingHom.charZero_iff f.hom.injective).2 inferInstance`. Set `g` to `f.hom.toRatAlgHom`. Establish `e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x)` using `_root_.funext fun p => ptCoord_sv n' n x p`.

Rewrite using `[e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]`. Use `letI := f.hom.toAlgebra`. Set `i` to `(IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv`. Use `(Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm` and prove the remaining obligations. Use extensionality with `a`.

Both sides reduce to the same expression.
-/
theorem relfinrank_blockFnField_sv : ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)],
    IntermediateField.relfinrank (blockFnField (ptCoord x ∘ sv n' n)) (blockFnField (ptCoord x)) =
      (qpSnd n' m n).residueDegree x := by
  intro n' m n x _
  let f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x :=
    (qpSnd n' m n).residueFieldMap x
  haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) :=
    (RingHom.charZero_iff f.hom.injective).2 inferInstance
  let g := f.hom.toRatAlgHom
  have e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x) := _root_.funext fun p => ptCoord_sv n' n x p
  rw [e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]
  letI := f.hom.toAlgebra
  let i := (IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm
  ext a
  rfl

end GlobalTheory.CompanionTheory.MPDict.FnDeg
