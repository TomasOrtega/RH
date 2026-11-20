import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RingIndep
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MemColSpanIff

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section Poly

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/- English proof (translation)
Establish `h : (colAddGen B (r` using `r) l j).toRingHom.comp (map φ) = (map φ).comp (colAddGen A (r := r) l j).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[colAddGen]`. Introduce `x`.

Simplify using `only [colAddGen, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `RingHom.congr_fun h f`.
-/
theorem colAddGen_map {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) A) :
    colAddGen B l j (map φ f) = map φ (colAddGen A l j f) := by
  have h : (colAddGen B (r := r) l j).toRingHom.comp (map φ) = (map φ).comp (colAddGen A (r := r) l j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [colAddGen]
    · intro x
      simp only [colAddGen, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun h f

/- English proof (translation)
Establish `h : (rowAct B (n` using `n) (g.map φ)).toRingHom.comp (map φ) = (map φ).comp (rowAct A (n := n) g).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[rowAct]`. Introduce `x`.

Simplify using `[rowAct]`. Conclude with `RingHom.congr_fun h f`.
-/
theorem rowAct_map' {r n : ℕ} (g : Matrix (Fin r) (Fin r) A) (f : MvPolynomial (Fin r × Fin n) A) :
    rowAct B (g.map φ) (map φ f) = map φ (rowAct A g f) := by
  have h : (rowAct B (n := n) (g.map φ)).toRingHom.comp (map φ) = (map φ).comp (rowAct A (n := n) g).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h f

/- English proof (translation)
Unfold `dualWeyl at *`. Establish `h1` using `(Submodule.mem_inf.1 hf).1`. Establish `h2` using `(Submodule.mem_inf.1 hf).2`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `h1`, the goal using `[mem_weightedHomogeneousSubmodule]`.

Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Conclude with `h1 (fun h => hd (by rw [h, map_zero]))`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply] at h2 ⊢`. Introduce `l j h`.

Rewrite using `[colAddGen_map, h2 l j h, map_rename]`.
-/
theorem dualWeyl_map {r n : ℕ} {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) A} (hf : f ∈ dualWeyl A r n ν) :
    map φ f ∈ dualWeyl B r n ν := by
  unfold dualWeyl at *
  have h1 := (Submodule.mem_inf.1 hf).1
  have h2 := (Submodule.mem_inf.1 hf).2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    rw [coeff_map] at hd
    exact h1 (fun h => hd (by rw [h, map_zero]))
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply] at h2 ⊢
    intro l j h
    rw [colAddGen_map, h2 l j h, map_rename]

/- English proof (translation)
Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]`.
-/
theorem map_smul' {σ : Type*} (c : A) (f : MvPolynomial σ A) : map φ (c • f) = φ c • map φ f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

end Poly

/- English proof (translation)
Rewrite using `[map_map]`. Establish `: (φ.symm : B →+* A).comp (φ : A →+* B) = RingHom.id A` using `by ext; simp`. Rewrite using `[this, map_id]`.
-/
theorem map_symm_map {A B σ : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B) (f : MvPolynomial σ A) :
    map (φ.symm : B →+* A) (map (φ : A →+* B) f) = f := by
  rw [map_map]
  have : (φ.symm : B →+* A).comp (φ : A →+* B) = RingHom.id A := by ext; simp
  rw [this, map_id]

structure Iso2 (R₁ F₁ R₂ F₂ : Type) [CommRing R₁] [Field F₁] [Algebra R₁ F₁] [CommRing R₂] [Field F₂]
    [Algebra R₂ F₂] where
  φR : R₁ ≃+* R₂
  φF : F₁ ≃+* F₂
  h : ∀ x, φF (algebraMap R₁ F₁ x) = algebraMap R₂ F₂ (φR x)

section Sub

variable {R₁ F₁ R₂ F₂ : Type} [CommRing R₁] [Field F₁] [Algebra R₁ F₁] [CommRing R₂] [Field F₂] [Algebra R₂ F₂]

def Iso2.symm (J : Iso2 R₁ F₁ R₂ F₂) : Iso2 R₂ F₂ R₁ F₁ where
  φR := J.φR.symm
  φF := J.φF.symm
  h x := by
    apply J.φF.injective
    rw [RingEquiv.apply_symm_apply, J.h, RingEquiv.apply_symm_apply]

variable (J : Iso2 R₁ F₁ R₂ F₂) {k : ℕ}

def mapSub (L : Submodule R₁ (Fin k → F₁)) : Submodule R₂ (Fin k → F₂) where
  carrier := {y | (fun i => J.φF.symm (y i)) ∈ L}
  add_mem' := by
    intro x y hx hy
    have : (fun i => J.φF.symm ((x + y) i)) = (fun i => J.φF.symm (x i)) + fun i => J.φF.symm (y i) := by
      funext i; simp
    show (fun i => J.φF.symm ((x + y) i)) ∈ L
    rw [this]; exact L.add_mem hx hy
  zero_mem' := by
    have : (fun i => J.φF.symm ((0 : Fin k → F₂) i)) = 0 := by funext i; simp
    show (fun i => J.φF.symm ((0 : Fin k → F₂) i)) ∈ L
    rw [this]; exact L.zero_mem
  smul_mem' := by
    intro c x hx
    have : (fun i => J.φF.symm ((c • x) i)) = J.φR.symm c • fun i => J.φF.symm (x i) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rw [show J.φF.symm (algebraMap R₂ F₂ c) = algebraMap R₁ F₁ (J.φR.symm c) from J.symm.h c]
    show (fun i => J.φF.symm ((c • x) i)) ∈ L
    rw [this]; exact L.smul_mem _ hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_mapSub (L : Submodule R₁ (Fin k → F₁)) (y : Fin k → F₂) :
    y ∈ mapSub J L ↔ (fun i => J.φF.symm (y i)) ∈ L := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_mapSub]`. Simplify using the standard rewrite rules.
-/
theorem map_mem_mapSub (L : Submodule R₁ (Fin k → F₁)) (x : Fin k → F₁) :
    (fun i => J.φF (x i)) ∈ mapSub J L ↔ x ∈ L := by
  rw [mem_mapSub]
  simp

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_mapSub, mem_mapSub]`. Simplify using `[Iso2.symm]`.
-/
theorem mapSub_symm (L : Submodule R₁ (Fin k → F₁)) : mapSub J.symm (mapSub J L) = L := by
  ext x
  rw [mem_mapSub, mem_mapSub]
  simp [Iso2.symm]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_mapSub, mem_mapSub]`. Simplify using `[Iso2.symm]`.
-/
theorem mapSub_symm' (L : Submodule R₂ (Fin k → F₂)) : mapSub J (mapSub J.symm L) = L := by
  ext x
  rw [mem_mapSub, mem_mapSub]
  simp [Iso2.symm]

/- English proof (translation)
Introduce `_ hy` and use `h hy`.
-/
theorem mapSub_mono {L L' : Submodule R₁ (Fin k → F₁)} (h : L ≤ L') : mapSub J L ≤ mapSub J L' :=
  fun _ hy => h hy

/- English proof (translation)
Rewrite using `[← mapSub_symm J L, h, mapSub_symm]`.
-/
theorem mapSub_inj {L L' : Submodule R₁ (Fin k → F₁)} (h : mapSub J L = mapSub J L') : L = L' := by
  rw [← mapSub_symm J L, h, mapSub_symm]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Establish `key : ∀ x ∈ Submodule.span R₁ S, (fun i => J.φF (x i)) ∈ Submodule.span R₂ ((fun (x : Fin k → F₁) i => J.φF (x i)) '' S)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`. Establish `: (fun i => J.φF ((0 : Fin k → F₁) i)) = 0` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `: (fun i => J.φF ((x + y) i)) = (fun i => J.φF (x i)) + fun i => J.φF (y i)` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`.

Establish `: (fun i => J.φF ((c • x) i)) = J.φR c • fun i => J.φF (x i)`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, J.h]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.

Use `key _ hy` as an intermediate fact. Simplify using `using this`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(map_mem_mapSub J _ x).2 (Submodule.subset_span hx)`.
-/
theorem mapSub_span (S : Set (Fin k → F₁)) :
    mapSub J (Submodule.span R₁ S) = Submodule.span R₂ ((fun x i => J.φF (x i)) '' S) := by
  apply le_antisymm
  · intro y hy
    have key : ∀ x ∈ Submodule.span R₁ S, (fun i => J.φF (x i)) ∈
        Submodule.span R₂ ((fun (x : Fin k → F₁) i => J.φF (x i)) '' S) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => J.φF ((0 : Fin k → F₁) i)) = 0 := by funext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => J.φF ((x + y) i)) = (fun i => J.φF (x i)) + fun i => J.φF (y i) := by funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have : (fun i => J.φF ((c • x) i)) = J.φR c • fun i => J.φF (x i) := by
          funext i
          simp only [Pi.smul_apply, Algebra.smul_def, map_mul, J.h]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hy
    simpa using this
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (map_mem_mapSub J _ x).2 (Submodule.subset_span hx)

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[mapSub_span, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem mapSub_colSpan (g : Matrix (Fin k) (Fin k) F₁) :
    mapSub J (colSpan R₁ g) = colSpan R₂ (g.map J.φF) := by
  unfold colSpan
  rw [mapSub_span, ← Set.range_comp]
  rfl

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `h`. Use `⟨g.map J.φF, ?_, mapSub_colSpan J g⟩` and prove the remaining obligations. Establish `: (g.map J.φF).det = J.φF g.det`. Conclude with `(RingHom.map_det (J.φF : F₁ →+* F₂) g).symm`. Rewrite using `[this]`.

Conclude with `hg.map J.φF`.
-/
theorem isLattice_mapSub {L : Submodule R₁ (Fin k → F₁)} (h : IsLattice R₁ L) : IsLattice R₂ (mapSub J L) := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g.map J.φF, ?_, mapSub_colSpan J g⟩
  have : (g.map J.φF).det = J.φF g.det := by
    exact (RingHom.map_det (J.φF : F₁ →+* F₂) g).symm
  rw [this]
  exact hg.map J.φF

/- English proof (translation)
Assemble the required witnesses or components as `⟨isLattice_mapSub J, fun h => by have := isLattice_mapSub J.symm h; rwa [mapSub_symm] at this⟩`.
-/
theorem isLattice_mapSub_iff (L : Submodule R₁ (Fin k → F₁)) : IsLattice R₁ L ↔ IsLattice R₂ (mapSub J L) :=
  ⟨isLattice_mapSub J, fun h => by have := isLattice_mapSub J.symm h; rwa [mapSub_symm] at this⟩

def mapSubEquiv : Submodule R₁ (Fin k → F₁) ≃ Submodule R₂ (Fin k → F₂) where
  toFun := mapSub J
  invFun := mapSub J.symm
  left_inv := mapSub_symm J
  right_inv := mapSub_symm' J

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `h`. Use `⟨isLattice_mapSub J h1, isLattice_mapSub J h2, mapSub_mono J h3, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `h6` using `h4 _ hy`. Establish `: (fun i => J.φF.symm (((p : R₂) • y) i)) = (p : R₁) • fun i => J.φF.symm (y i)`.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def]`. Use `show (fun i => J.φF.symm (((p : R₂) • y) i)) ∈ e.src`. Rewrite using `[this]`. Conclude with `h6`.

Rewrite using `[← h5]`. Set `E : ↥(mapSub J e.tgt) ≃ ↥e.tgt` to `{ toFun := fun y => ⟨fun i => J.φF.symm (y.1 i), y.2⟩ invFun := fun x => ⟨fun i => J.φF (x.1 i), (map_mem_mapSub J _ _).2 x.2⟩ left_inv := fun y => Subtype.ext (by funext i; simp) right_inv := fun x => Subtype.ext (by funext i; simp) }`. Use `Nat.card_congr (Quotient.congr E fun a b => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]`. Use `show (a.1 - b.1) ∈ mapSub J e.src ↔ ((E a).1 - (E b).1) ∈ e.src`.

Rewrite using `[mem_mapSub]`. Establish `: (fun i => J.φF.symm ((a.1 - b.1) i)) = (E a).1 - (E b).1`. Use function extensionality and compare the values at `i`. Simplify using `[E]`. Rewrite using `[this]`.
-/
theorem isEdge_mapSub (p n' r : ℕ) {e : Edge R₁ F₁ k} (h : IsEdge p n' r e) :
    IsEdge p n' r (⟨mapSub J e.src, mapSub J e.tgt⟩ : Edge R₂ F₂ k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isLattice_mapSub J h1, isLattice_mapSub J h2, mapSub_mono J h3, ?_, ?_⟩
  · intro y hy
    have h6 := h4 _ hy
    have : (fun i => J.φF.symm (((p : R₂) • y) i)) = (p : R₁) • fun i => J.φF.symm (y i) := by
      funext i
      simp [Algebra.smul_def]
    show (fun i => J.φF.symm (((p : R₂) • y) i)) ∈ e.src
    rw [this]; exact h6
  · rw [← h5]
    let E : ↥(mapSub J e.tgt) ≃ ↥e.tgt :=
      { toFun := fun y => ⟨fun i => J.φF.symm (y.1 i), y.2⟩
        invFun := fun x => ⟨fun i => J.φF (x.1 i), (map_mem_mapSub J _ _).2 x.2⟩
        left_inv := fun y => Subtype.ext (by funext i; simp)
        right_inv := fun x => Subtype.ext (by funext i; simp) }
    refine Nat.card_congr (Quotient.congr E fun a b => ?_)
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
    show (a.1 - b.1) ∈ mapSub J e.src ↔ ((E a).1 - (E b).1) ∈ e.src
    rw [mem_mapSub]
    have : (fun i => J.φF.symm ((a.1 - b.1) i)) = (E a).1 - (E b).1 := by
      funext i
      simp [E]
    rw [this]

end Sub

end Formalism.MainNotions.flipOneThree.Pf

end
