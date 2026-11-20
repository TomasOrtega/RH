import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigProjMemOfFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames

section Summand

variable {A N : Type} [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N]

/- English proof (translation)
Establish `hs : Function.Surjective (Submodule.projectionOnto M C h)` using `Submodule.projectionOnto_surjective h`. Establish `: Module.Finite A M` using `Module.Finite.of_surjective _ hs`. Establish `: Module.Projective A M` using `Module.Projective.of_split M.subtype (Submodule.projectionOnto M C h) (LinearMap.ext fun x => Submodule.projectionOnto_apply_left h x)`. Conclude with `⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩`.
-/
theorem free_of_isCompl [Module.Free A N] [Module.Finite A N] {M C : Submodule A N} (h : IsCompl M C) :
    Module.Free A M ∧ Module.Finite A M := by
  have hs : Function.Surjective (Submodule.projectionOnto M C h) := Submodule.projectionOnto_surjective h
  have : Module.Finite A M := Module.Finite.of_surjective _ hs
  have : Module.Projective A M := Module.Projective.of_split M.subtype (Submodule.projectionOnto M C h)
    (LinearMap.ext fun x => Submodule.projectionOnto_apply_left h x)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end Summand

section Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (A : Subring K) [IsLocalRing A]

/- English proof (translation)
Use `set L := Submodule.span A (Set.range ℓ) with hLdef`. Set `f : L →ₗ[A] L` to `(e.restrictScalars A).restrict hL`. Establish `hfv : ∀ x : L, ((f x : L) : V) = e x` using `fun x => rfl`. Establish `hf : IsIdempotentElem f`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e (e x) = e x`. Conclude with `heW _ (he _)`. Establish `hc` using `LinearMap.IsIdempotentElem.isCompl hf`. Establish `hli : LinearIndependent A ℓ` using `hℓ.restrict_scalars fun a b h => Subtype.ext (by simpa [Subring.smul_def] using h)`. Set `bL : Module.Basis (Fin g) A L` to `Module.Basis.span hli`.

Establish `: Module.Free A L` using `Module.Free.of_basis bL`. Establish `: Module.Finite A L` using `Module.Finite.of_basis bL`. Take `⟨h1, h2⟩` from `free_of_isCompl hc`. Take `⟨h3, h4⟩` from `free_of_isCompl hc.symm`. Set `c₁` to `Module.Free.chooseBasis A (LinearMap.range f)`.

Set `c₂` to `Module.Free.chooseBasis A (LinearMap.ker f)`. Set `c : Module.Basis _ A L` to `(c₁.prod c₂).map (Submodule.prodEquivOfIsCompl _ _ hc)`. Set `v` to `fun x => ((c x : L) : V)`. Establish `hmem : ∀ x : L, (x : V) ∈ Submodule.span K (Set.range v)` using `fun x => by`. Rewrite using `[← c.sum_repr x, AddSubmonoidClass.coe_finsetSum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul_of_tower]`. Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hspan : Submodule.span K (Set.range v) = ⊤`. Rewrite using `[eq_top_iff, ← hsp, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hmem ⟨ℓ i, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex A (LinearMap.range f) ⊕ Module.Free.ChooseBasisIndex A (LinearMap.ker f)) = Module.finrank K V`. Rewrite using `[← Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis bL, ← finrank_top K V, ← hsp, finrank_span_eq_card hℓ]`. Establish `hv : LinearIndependent K v` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard`.

Set `v₁` to `fun i => (((c₁ i : LinearMap.range f) : L) : V)`. Establish `hvv : ∀ i, v₁ i = v (Sum.inl i)` using `fun i => by simp [v, v₁, c]`. Establish `hv₁ : LinearIndependent K v₁`. Use `hv.comp Sum.inl Sum.inl_injective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Conclude with `funext hvv`. Establish `hle : ∀ i, v₁ i ∈ L ⊓ W.restrictScalars A` using `fun i => by`. Take `⟨y, hy⟩` from `(c₁ i).2`. Use `⟨((c₁ i : LinearMap.range f) : L).2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v₁ i ∈ W`.

Express the relevant statement in the definitionally equal form `(((c₁ i : LinearMap.range f) : L) : V) ∈ W`. Rewrite using `[← hy]`. Conclude with `he _`. Establish `hge : L ⊓ W.restrictScalars A ≤ Submodule.span A (Set.range v₁)`. Introduce and unpack `x ⟨hxL, hxW⟩`.

Establish `hx : (⟨x, hxL⟩ : L) ∈ LinearMap.range f` using `⟨⟨x, hxL⟩, Subtype.ext (heW x hxW)⟩`. Establish `e1 : x = (((⟨⟨x, hxL⟩, hx⟩ : LinearMap.range f) : L) : V)` using `rfl`. Rewrite using `[e1, ← c₁.sum_repr ⟨⟨x, hxL⟩, hx⟩, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hA : Submodule.span A (Set.range v₁) = L ⊓ W.restrictScalars A` using `le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hle i)) hge`. Establish `hK : Submodule.span K (Set.range v₁) = W`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `(hle i).2`. Introduce `x hx`. Establish `h5 : ∀ y, e y ∈ Submodule.span K (Set.range v₁)` using `fun y => by`. Establish `hy : y ∈ Submodule.span K (Set.range ℓ)` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y h`. Take `⟨i, rfl⟩` from `h`. Establish `h6 : e (ℓ i) ∈ L ⊓ W.restrictScalars A` using `⟨hL _ (Submodule.subset_span ⟨i, rfl⟩), he _⟩`. Establish `h7` using `hge h6`. Conclude with `Submodule.span_subset_span A K _ h7`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.

Rewrite using `[← heW x hx]`. Conclude with `h5 x`. Establish `hcard₁ : Fintype.card (Module.Free.ChooseBasisIndex A (LinearMap.range f)) = p`. Rewrite using `[← finrank_span_eq_card hv₁, hK, hp]`. Set `eq` to `Fintype.equivFinOfCardEq hcard₁`.

Use `⟨v₁ ∘ eq.symm, hv₁.comp _ eq.symm.injective, ?_⟩` and prove the remaining obligations. Rewrite using `[eq.symm.surjective.range_comp, hA]`.
-/
theorem exists_frame {g p : ℕ} (ℓ : Fin g → V) (hℓ : LinearIndependent K ℓ)
    (hsp : Submodule.span K (Set.range ℓ) = ⊤) (e : Module.End K V) (W : Submodule K V) (he : ∀ x, e x ∈ W)
    (heW : ∀ x ∈ W, e x = x) (hL : ∀ x ∈ Submodule.span A (Set.range ℓ), e x ∈ Submodule.span A (Set.range ℓ))
    (hp : Module.finrank K W = p) :
    ∃ b : Fin p → V, LinearIndependent K b ∧
      Submodule.span A (Set.range b) = Submodule.span A (Set.range ℓ) ⊓ W.restrictScalars A := by
  classical
  set L := Submodule.span A (Set.range ℓ) with hLdef
  let f : L →ₗ[A] L := (e.restrictScalars A).restrict hL
  have hfv : ∀ x : L, ((f x : L) : V) = e x := fun x => rfl
  have hf : IsIdempotentElem f := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change e (e x) = e x
    exact heW _ (he _)
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  have hli : LinearIndependent A ℓ := hℓ.restrict_scalars fun a b h =>
    Subtype.ext (by simpa [Subring.smul_def] using h)
  let bL : Module.Basis (Fin g) A L := Module.Basis.span hli
  have : Module.Free A L := Module.Free.of_basis bL
  have : Module.Finite A L := Module.Finite.of_basis bL
  obtain ⟨h1, h2⟩ := free_of_isCompl hc
  obtain ⟨h3, h4⟩ := free_of_isCompl hc.symm
  let c₁ := Module.Free.chooseBasis A (LinearMap.range f)
  let c₂ := Module.Free.chooseBasis A (LinearMap.ker f)
  let c : Module.Basis _ A L := (c₁.prod c₂).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let v := fun x => ((c x : L) : V)
  have hmem : ∀ x : L, (x : V) ∈ Submodule.span K (Set.range v) := fun x => by
    rw [← c.sum_repr x, AddSubmonoidClass.coe_finsetSum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul_of_tower]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem ⟨ℓ i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A (LinearMap.range f) ⊕
      Module.Free.ChooseBasisIndex A (LinearMap.ker f)) = Module.finrank K V := by
    rw [← Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis bL, ← finrank_top K V, ← hsp,
      finrank_span_eq_card hℓ]
  have hv : LinearIndependent K v := linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard
  let v₁ := fun i => (((c₁ i : LinearMap.range f) : L) : V)
  have hvv : ∀ i, v₁ i = v (Sum.inl i) := fun i => by simp [v, v₁, c]
  have hv₁ : LinearIndependent K v₁ := by
    have := hv.comp Sum.inl Sum.inl_injective
    convert this using 1
    exact funext hvv
  have hle : ∀ i, v₁ i ∈ L ⊓ W.restrictScalars A := fun i => by
    obtain ⟨y, hy⟩ := (c₁ i).2
    refine ⟨((c₁ i : LinearMap.range f) : L).2, ?_⟩
    change v₁ i ∈ W
    change (((c₁ i : LinearMap.range f) : L) : V) ∈ W
    rw [← hy]
    exact he _
  have hge : L ⊓ W.restrictScalars A ≤ Submodule.span A (Set.range v₁) := by
    rintro x ⟨hxL, hxW⟩
    have hx : (⟨x, hxL⟩ : L) ∈ LinearMap.range f := ⟨⟨x, hxL⟩, Subtype.ext (heW x hxW)⟩
    have e1 : x = (((⟨⟨x, hxL⟩, hx⟩ : LinearMap.range f) : L) : V) := rfl
    rw [e1, ← c₁.sum_repr ⟨⟨x, hxL⟩, hx⟩, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hA : Submodule.span A (Set.range v₁) = L ⊓ W.restrictScalars A :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hle i)) hge
  have hK : Submodule.span K (Set.range v₁) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hle i).2
    · intro x hx
      have h5 : ∀ y, e y ∈ Submodule.span K (Set.range v₁) := fun y => by
        have hy : y ∈ Submodule.span K (Set.range ℓ) := hsp ▸ Submodule.mem_top
        induction hy using Submodule.span_induction with
        | mem y h =>
          obtain ⟨i, rfl⟩ := h
          have h6 : e (ℓ i) ∈ L ⊓ W.restrictScalars A := ⟨hL _ (Submodule.subset_span ⟨i, rfl⟩), he _⟩
          have h7 := hge h6
          exact Submodule.span_subset_span A K _ h7
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
      rw [← heW x hx]
      exact h5 x
  have hcard₁ : Fintype.card (Module.Free.ChooseBasisIndex A (LinearMap.range f)) = p := by
    rw [← finrank_span_eq_card hv₁, hK, hp]
  let eq := Fintype.equivFinOfCardEq hcard₁
  refine ⟨v₁ ∘ eq.symm, hv₁.comp _ eq.symm.injective, ?_⟩
  rw [eq.symm.surjective.range_comp, hA]

end Frame

section Main

variable {E : Type} [Field E] [NumberField E] {Ω Vs : Type} [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
  {ρ : 𝓞 E →+* Module.End Ω Vs} {ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)}

/- English proof (translation)
Simplify using `only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hact]`.
-/
theorem fst_eigProj (hact : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* Ω) (y : Vs × Module.Dual Ω Vs) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hact]

/- English proof (translation)
Establish `h3 : ∀ k z, φ (ρ (RingOfIntegers.basis E k) z) = σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) • φ z`. Introduce `k z`. Establish `h1` using `HT.LatBasic.mem_eigSp.1 h (bar (RingOfIntegers.basis E k))`. Rewrite `h1` using `[hinr, hb, ← hσ]`. Establish `h2` using `congrArg Prod.snd h1`.

Conclude with `LinearMap.congr_fun h2 z`. Establish `h2 : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1`. Rewrite using `[← map_one σ', ← HT.LatBasic.sum_dualInt_mul, map_sum]`. Simplify using the standard rewrite rules. Use extensionality with `z`.

Simplify using `only [HT.eigProj, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h3, smul_smul]`. Rewrite using `[← Finset.sum_smul, h2, one_smul]`.
-/
theorem comp_eigProj {bar : 𝓞 E ≃+* 𝓞 E} (hinr : ∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) {σ σ' : E →+* Ω}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual Ω Vs}
    (h : ((0 : Vs), φ) ∈ HT.eigSp ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have h3 : ∀ k z, φ (ρ (RingOfIntegers.basis E k) z) = σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) • φ z := by
    intro k z
    have h1 := HT.LatBasic.mem_eigSp.1 h (bar (RingOfIntegers.basis E k))
    rw [hinr, hb, ← hσ] at h1
    have h2 := congrArg Prod.snd h1
    exact LinearMap.congr_fun h2 z
  have h2 : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ', ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  ext z
  simp only [HT.eigProj, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h3,
    smul_smul]
  rw [← Finset.sum_smul, h2, one_smul]

/- English proof (translation)
Set `B` to `Module.Basis.span hb`. Set `π : Vs →ₗ[Ω] Submodule.span Ω (Set.range b)` to `(HT.eigProj ρ τ).codRestrict _ fun x => by`. Rewrite using `[hspan]`. Conclude with `HT.LatBasic.eigProj_mem ρ τ x`. Establish `hπ : ∀ x, ((π x : Submodule.span Ω (Set.range b)) : Vs) = HT.eigProj ρ τ x` using `fun x => rfl`.

Establish `hfix : ∀ x ∈ HT.eigSp ρ τ, HT.eigProj ρ τ x = x` using `fun x hx => HT.LatBasic.eigProj_of_mem hx`. Establish `h3 : ∀ j, (B.coord j ∘ₗ π) ∘ₗ HT.eigProj ρ τ = B.coord j ∘ₗ π` using `fun j => by`. Use extensionality with `x`. Establish `: π (HT.eigProj ρ τ x) = π x` using `Subtype.ext (hfix _ (HT.LatBasic.eigProj_mem ρ τ x))`. Simplify using `[this]`.

Use `⟨fun j => B.coord j ∘ₗ π, fun x => ?_, fun j j' => ?_, h3, fun j c => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val (B.sum_repr (π x))`. Rewrite `h1` using `[hπ]`. Rewrite using `[← h1, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[B, Module.Basis.span_apply]`. Establish `h1 : π (b j') = B j'` using `Subtype.ext (by`. Rewrite using `[hπ, Module.Basis.span_apply]`. Conclude with `hfix _ (hspan ▸ Submodule.subset_span ⟨j', rfl⟩))`. Simplify using `[h1, Finsupp.single_apply, eq_comm]`.

Use extensionality with `x`. Establish `h1` using `LinearMap.congr_fun (h3 j) (ρ c x)`. Rewrite `h1` using `[LinearMap.comp_apply, HodgeDeterminantLattice.eigProj_act, map_smul, ← LinearMap.comp_apply (B.coord j ∘ₗ π), h3]`. Simplify using `using h1.symm`.
-/
theorem exists_dualFrame {q : ℕ} {b : Fin q → Vs} (hb : LinearIndependent Ω b) {τ : E →+* Ω}
    (hspan : Submodule.span Ω (Set.range b) = HT.eigSp ρ τ) :
    ∃ f : Fin q → Module.Dual Ω Vs, (∀ x, HT.eigProj ρ τ x = ∑ j, f j x • b j) ∧
      (∀ j j', f j (b j') = if j = j' then 1 else 0) ∧ (∀ j, f j ∘ₗ HT.eigProj ρ τ = f j) ∧
      ∀ j (c : 𝓞 E), f j ∘ₗ ρ c = τ (c : E) • f j := by
  classical
  let B := Module.Basis.span hb
  let π : Vs →ₗ[Ω] Submodule.span Ω (Set.range b) := (HT.eigProj ρ τ).codRestrict _ fun x => by
    rw [hspan]
    exact HT.LatBasic.eigProj_mem ρ τ x
  have hπ : ∀ x, ((π x : Submodule.span Ω (Set.range b)) : Vs) = HT.eigProj ρ τ x := fun x => rfl
  have hfix : ∀ x ∈ HT.eigSp ρ τ, HT.eigProj ρ τ x = x := fun x hx => HT.LatBasic.eigProj_of_mem hx
  have h3 : ∀ j, (B.coord j ∘ₗ π) ∘ₗ HT.eigProj ρ τ = B.coord j ∘ₗ π := fun j => by
    ext x
    have : π (HT.eigProj ρ τ x) = π x := Subtype.ext (hfix _ (HT.LatBasic.eigProj_mem ρ τ x))
    simp [this]
  refine ⟨fun j => B.coord j ∘ₗ π, fun x => ?_, fun j j' => ?_, h3, fun j c => ?_⟩
  · have h1 := congrArg Subtype.val (B.sum_repr (π x))
    rw [hπ] at h1
    rw [← h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [B, Module.Basis.span_apply]
  · have h1 : π (b j') = B j' := Subtype.ext (by
      rw [hπ, Module.Basis.span_apply]
      exact hfix _ (hspan ▸ Submodule.subset_span ⟨j', rfl⟩))
    simp [h1, Finsupp.single_apply, eq_comm]
  · ext x
    have h1 := LinearMap.congr_fun (h3 j) (ρ c x)
    rw [LinearMap.comp_apply, HodgeDeterminantLattice.eigProj_act, map_smul, ← LinearMap.comp_apply (B.coord j ∘ₗ π), h3] at h1
    simpa using h1.symm

end Main

/- English proof (translation)
Introduce `E _ _ Ω Vs _ _ _ _ _ ρ ρH bar R' _ g p q ℓ t HL σ σ' hact hinr hσσ' hbar hσ hσ' hℓ hsp hH hp hq`. Take `⟨hfree, hmap, hdual⟩` from `hH`. Establish `hstab : ∀ τ : E →+* Ω, (∀ e, τ e ∈ R') → ∀ h ∈ HL, HT.eigProj ρH τ h ∈ HL` using `fun τ hτ h hh => QuotEig.eigProj_mem_of_free hfree τ hτ hh`. Establish `hL : ∀ {z}, z ∈ Submodule.span R' (Set.range ℓ) ↔ ∃ h ∈ HL, h.1 = z`. Introduce `z`.

Rewrite using `[← hmap]`. Conclude with `Iff.rfl`. Establish `hLs : ∀ τ : E →+* Ω, (∀ e, τ e ∈ R') → ∀ z ∈ Submodule.span R' (Set.range ℓ), HT.eigProj ρ τ z ∈ Submodule.span R' (Set.range ℓ)`. Introduce `τ hτ z hz`. Take `⟨h, hh, rfl⟩` from `hL.1 hz`.

Conclude with `hL.2 ⟨_, hstab τ hτ h hh, fst_eigProj hact τ h⟩`. Take `⟨b₁, hb₁, hs₁⟩` from `exists_frame R' ℓ hℓ hsp (HT.eigProj ρ σ) (HT.eigSp ρ σ) (HT.LatBasic.eigProj_mem ρ σ) (fun x hx => HT.LatBasic.eigProj_of_mem hx) (hLs σ hσ) hp`. Take `⟨b₂, hb₂, hs₂⟩` from `exists_frame R' ℓ hℓ hsp (HT.eigProj ρ σ') (HT.eigSp ρ σ') (HT.LatBasic.eigProj_mem ρ σ') (fun x hx => HT.LatBasic.eigProj_of_mem hx) (hLs σ' hσ') hq`. Establish `hm₁ : ∀ i, b₁ i ∈ Submodule.span R' (Set.range ℓ) ∧ b₁ i ∈ HT.eigSp ρ σ` using `fun i => by`. Establish `h : b₁ i ∈ Submodule.span R' (Set.range b₁)` using `Submodule.subset_span ⟨i, rfl⟩`.

Rewrite `h` using `[hs₁]`. Conclude with `h`. Establish `hm₂ : ∀ j, b₂ j ∈ Submodule.span R' (Set.range ℓ) ∧ b₂ j ∈ HT.eigSp ρ σ'` using `fun j => by`. Establish `h : b₂ j ∈ Submodule.span R' (Set.range b₂)` using `Submodule.subset_span ⟨j, rfl⟩`. Rewrite `h` using `[hs₂]`.

Conclude with `h`. Establish `hw : Submodule.span Ω (Set.range b₂) = HT.eigSp ρ σ'`. Use `Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_eq_card hb₂, hq, Fintype.card_fin])` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `(hm₂ j).2`. Take `⟨f, hf1, hf2, hf3, hf4⟩` from `exists_dualFrame hb₂ hw`. Use `choose h₁ hh₁ he₁ using fun i => hL.1 (hm₁ i).1`. Establish `hfint : ∀ j, ∀ z ∈ Submodule.span R' (Set.range ℓ), f j z ∈ R'`. Introduce `j z hz`.

Establish `h1 : HT.eigProj ρ σ' z ∈ Submodule.span R' (Set.range b₂)`. Rewrite using `[hs₂]`. Conclude with `⟨hLs σ' hσ' z hz, HT.LatBasic.eigProj_mem ρ σ' z⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R').1 h1`. Establish `h2` using `LinearMap.congr_fun (hf3 j) z`.

Rewrite `h2` using `[LinearMap.comp_apply, ← hc, map_sum]`. Establish `h3 : f j z = c j`. Rewrite using `[← h2]`. Simplify using `[Subring.smul_def, hf2]`. Rewrite using `[h3]`.

Conclude with `(c j).2`. Set `u : Fin (p + q) → Vs × Module.Dual Ω Vs` to `Fin.addCases (fun i => HT.eigProj ρH σ (h₁ i)) (fun j => ((0 : Vs), f j))`. Establish `hul : ∀ i, u (Fin.castAdd q i) = HT.eigProj ρH σ (h₁ i)` using `fun i => by simp [u]`. Establish `hur : ∀ j, u (Fin.natAdd p j) = ((0 : Vs), f j)` using `fun j => by simp [u]`. Establish `hu1 : ∀ i, (u (Fin.castAdd q i)).1 = b₁ i` using `fun i => by`.

Rewrite using `[hul, fst_eigProj hact, he₁]`. Conclude with `HT.LatBasic.eigProj_of_mem (hm₁ i).2`. Establish `hueig : ∀ i, u i ∈ HT.eigSp ρH σ`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i`. Rewrite using `[hul]`. Conclude with `HT.LatBasic.eigProj_mem _ _ _`. Consider the case `right j`. Rewrite using `[hur, HT.LatBasic.mem_eigSp]`.

Introduce `a`. Establish `h1` using `hf4 j (bar a)`. Rewrite `h1` using `[hσσ', hbar]`. Rewrite using `[hinr, h1]`. Simplify using the standard rewrite rules.

Establish `huHL : ∀ i, u i ∈ HL`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`. Rewrite using `[hul]`.

Conclude with `hstab σ hσ _ (hh₁ i)`. Consider the case `right j`. Rewrite using `[hur]`. Conclude with `(hdual _).2 (hfint j)`. Establish `hgen : ∀ y ∈ HL, y ∈ HT.eigSp ρH σ → ∃ c : Fin (p + q) → R', y = ∑ i, (c i : Ω) • u i`.

Introduce `y hy hye`. Establish `hy1 : y.1 ∈ Submodule.span R' (Set.range b₁)`. Rewrite using `[hs₁]`. Use `⟨hL.2 ⟨y, hy, rfl⟩, HT.LatBasic.mem_eigSp.2 fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← hact, HT.LatBasic.mem_eigSp.1 hye a]`.

Both sides reduce to the same expression. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R').1 hy1`. Take `⟨w, hw0⟩ : ∃ w, w = y - ∑ i, (c i : Ω) • u (Fin.castAdd q i)` from `⟨_, rfl⟩`. Establish `hwH : w ∈ HL`. Rewrite using `[hw0]`.

Conclude with `HL.sub_mem hy (HL.sum_mem fun i _ => HL.smul_mem (c i) (huHL _))`. Establish `hwe : w ∈ HT.eigSp ρH σ`. Rewrite using `[hw0]`. Conclude with `Submodule.sub_mem _ hye (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hueig _))`. Establish `hw1 : w.1 = 0`.

Rewrite using `[hw0, Prod.fst_sub, Prod.fst_sum, sub_eq_zero, ← hc]`. Simplify using `[hu1, Subring.smul_def]`. Establish `hwz : ((0 : Vs), w.2) = w` using `Prod.ext hw1.symm rfl`. Establish `hw2 : ∀ z ∈ Submodule.span R' (Set.range ℓ), w.2 z ∈ R'` using `(hdual _).1 (hwz ▸ hwH)`. Establish `hcomp : w.2 ∘ₗ HT.eigProj ρ σ' = w.2` using `comp_eigProj hinr hσσ' hbar (hwz.symm ▸ hwe)`.

Establish `hd : w.2 = ∑ j, w.2 (b₂ j) • f j`. Use extensionality with `x`. Establish `h1` using `LinearMap.congr_fun hcomp x`. Rewrite `h1` using `[LinearMap.comp_apply, hf1, map_sum]`. Rewrite using `[← h1]`.

Simplify using `[LinearMap.sum_apply, mul_comm]`. Use `⟨Fin.addCases c (fun j => ⟨w.2 (b₂ j), hw2 _ (hm₂ j).1⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.addCases_left, Fin.addCases_right, hur]`. Establish `e2 : ∑ j, (w.2 (b₂ j)) • (((0 : Vs), f j) : Vs × Module.Dual Ω Vs) = w`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Prod.fst_sum, hw1]`. Rewrite using `[Prod.snd_sum]`. Simplify using `using hd.symm`. Rewrite using `[e2, hw0]`.

Normalize the expressions using the abelian group laws. Establish `hqt` using `HodgeDeterminantLattice.eigQuot_eq_span (A := R') σ hfree (fun a => ⟨⟨_, hσ _⟩, rfl⟩)`. Establish `hT : ∀ i, HT.eigProj ρH σ (t i) ∈ HL` using `fun i => by`. Establish `h1 : HT.eigProj ρH σ (t i) ∈ HT.eigQuot ρH σ HL`. Rewrite using `[hqt]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Take `⟨y, hy, e⟩` from `h1`. Rewrite using `[← e]`. Conclude with `hstab σ hσ y hy`. Use `choose A hA using fun i => hgen _ (hT i) (HT.LatBasic.eigProj_mem _ _ _)`.

Establish `hB : ∀ j, ∃ c : Fin (p + q) → R', ∑ k, c k • HT.eigProj ρH σ (t k) = u j` using `fun j => by`. Establish `h1 : u j ∈ HT.eigQuot ρH σ HL` using `⟨u j, huHL j, HT.LatBasic.eigProj_of_mem (hueig j)⟩`. Rewrite `h1` using `[hqt]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun R').1 h1`. Use `choose B hB using hB`.

Set `AΩ : Matrix (Fin (p + q)) (Fin (p + q)) Ω` to `Matrix.of fun i j => (A i j : Ω)`. Set `BΩ : Matrix (Fin (p + q)) (Fin (p + q)) Ω` to `Matrix.of fun i j => (B i j : Ω)`. Establish `key : AΩ * BΩ = 1`. Use extensionality with `i k`. Establish `h1` using `HodgeDeterminantLattice.sum_smul_sum AΩ BΩ (fun k => HT.eigProj ρH σ (t k)) i`.

Establish `h2 : ∑ j, AΩ i j • ∑ k, BΩ j k • HT.eigProj ρH σ (t k) = HT.eigProj ρH σ (t i)`. Rewrite using `[hA i]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hB j]`. Both sides reduce to the same expression.

Establish `h3 : ∑ k, ((AΩ * BΩ) i k - (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) i k) • HT.eigProj ρH σ (t k) = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, ← h1, h2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj σ hfree) _ h3 k)`. Establish `hAB : Matrix.of A * Matrix.of B = 1`. Use extensionality with `i k`.

Establish `h1` using `congrFun (congrFun key i) k`. Simplify `h1` using `[Matrix.mul_apply, Matrix.one_apply, AΩ, BΩ, apply_ite]`. Use `⟨b₁, b₂, u, Matrix.of A, hb₁, hs₁, hb₂, hs₂, ⟨hueig, hu1, fun j => ?_⟩, huHL, Matrix.isUnit_det_of_right_inverse hAB, hA⟩` and prove the remaining obligations. Rewrite using `[hur]`. Conclude with `⟨rfl, hf2 j⟩`.
-/
theorem adapted_frames : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (bar : 𝓞 E ≃+* 𝓞 E) (R' : Subring Ω) [IsLocalRing R'] (g p q : ℕ) (ℓ : Fin g → Vs)
    (t : Fin (p + q) → Vs × Module.Dual Ω Vs) (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (σ σ' : E →+* Ω),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ e, σ e ∈ R') → (∀ e, σ' e ∈ R') →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ → HodgeAt ρH HL ℓ t →
    Module.finrank Ω (HT.eigSp ρ σ) = p → Module.finrank Ω (HT.eigSp ρ σ') = q →
    ∃ (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
      (A : Matrix (Fin (p + q)) (Fin (p + q)) R'),
      LinearIndependent Ω b₁ ∧ Submodule.span R' (Set.range b₁) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) ∧
      LinearIndependent Ω b₂ ∧ Submodule.span R' (Set.range b₂) = HT.eigSub ρ σ' (Submodule.span R' (Set.range ℓ)) ∧
      IsAdapted ρH σ b₁ b₂ u ∧ (∀ i, u i ∈ HL) ∧ IsUnit A.det ∧
      ∀ i, HT.eigProj ρH σ (t i) = ∑ j, (A i j : Ω) • u j := by
  intro E _ _ Ω Vs _ _ _ _ _ ρ ρH bar R' _ g p q ℓ t HL σ σ' hact hinr hσσ' hbar hσ hσ' hℓ hsp hH hp hq
  classical
  obtain ⟨hfree, hmap, hdual⟩ := hH
  have hstab : ∀ τ : E →+* Ω, (∀ e, τ e ∈ R') → ∀ h ∈ HL, HT.eigProj ρH τ h ∈ HL :=
    fun τ hτ h hh => QuotEig.eigProj_mem_of_free hfree τ hτ hh
  have hL : ∀ {z}, z ∈ Submodule.span R' (Set.range ℓ) ↔ ∃ h ∈ HL, h.1 = z := by
    intro z
    rw [← hmap]
    exact Iff.rfl
  have hLs : ∀ τ : E →+* Ω, (∀ e, τ e ∈ R') → ∀ z ∈ Submodule.span R' (Set.range ℓ),
      HT.eigProj ρ τ z ∈ Submodule.span R' (Set.range ℓ) := by
    intro τ hτ z hz
    obtain ⟨h, hh, rfl⟩ := hL.1 hz
    exact hL.2 ⟨_, hstab τ hτ h hh, fst_eigProj hact τ h⟩
  obtain ⟨b₁, hb₁, hs₁⟩ := exists_frame R' ℓ hℓ hsp (HT.eigProj ρ σ) (HT.eigSp ρ σ)
    (HT.LatBasic.eigProj_mem ρ σ) (fun x hx => HT.LatBasic.eigProj_of_mem hx) (hLs σ hσ) hp
  obtain ⟨b₂, hb₂, hs₂⟩ := exists_frame R' ℓ hℓ hsp (HT.eigProj ρ σ') (HT.eigSp ρ σ')
    (HT.LatBasic.eigProj_mem ρ σ') (fun x hx => HT.LatBasic.eigProj_of_mem hx) (hLs σ' hσ') hq
  have hm₁ : ∀ i, b₁ i ∈ Submodule.span R' (Set.range ℓ) ∧ b₁ i ∈ HT.eigSp ρ σ := fun i => by
    have h : b₁ i ∈ Submodule.span R' (Set.range b₁) := Submodule.subset_span ⟨i, rfl⟩
    rw [hs₁] at h
    exact h
  have hm₂ : ∀ j, b₂ j ∈ Submodule.span R' (Set.range ℓ) ∧ b₂ j ∈ HT.eigSp ρ σ' := fun j => by
    have h : b₂ j ∈ Submodule.span R' (Set.range b₂) := Submodule.subset_span ⟨j, rfl⟩
    rw [hs₂] at h
    exact h
  have hw : Submodule.span Ω (Set.range b₂) = HT.eigSp ρ σ' := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_eq_card hb₂, hq, Fintype.card_fin])
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hm₂ j).2
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_dualFrame hb₂ hw
  choose h₁ hh₁ he₁ using fun i => hL.1 (hm₁ i).1
  have hfint : ∀ j, ∀ z ∈ Submodule.span R' (Set.range ℓ), f j z ∈ R' := by
    intro j z hz
    have h1 : HT.eigProj ρ σ' z ∈ Submodule.span R' (Set.range b₂) := by
      rw [hs₂]
      exact ⟨hLs σ' hσ' z hz, HT.LatBasic.eigProj_mem ρ σ' z⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 h1
    have h2 := LinearMap.congr_fun (hf3 j) z
    rw [LinearMap.comp_apply, ← hc, map_sum] at h2
    have h3 : f j z = c j := by
      rw [← h2]
      simp [Subring.smul_def, hf2]
    rw [h3]
    exact (c j).2
  let u : Fin (p + q) → Vs × Module.Dual Ω Vs :=
    Fin.addCases (fun i => HT.eigProj ρH σ (h₁ i)) (fun j => ((0 : Vs), f j))
  have hul : ∀ i, u (Fin.castAdd q i) = HT.eigProj ρH σ (h₁ i) := fun i => by simp [u]
  have hur : ∀ j, u (Fin.natAdd p j) = ((0 : Vs), f j) := fun j => by simp [u]
  have hu1 : ∀ i, (u (Fin.castAdd q i)).1 = b₁ i := fun i => by
    rw [hul, fst_eigProj hact, he₁]
    exact HT.LatBasic.eigProj_of_mem (hm₁ i).2
  have hueig : ∀ i, u i ∈ HT.eigSp ρH σ := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [hul]
      exact HT.LatBasic.eigProj_mem _ _ _
    | right j =>
      rw [hur, HT.LatBasic.mem_eigSp]
      intro a
      have h1 := hf4 j (bar a)
      rw [hσσ', hbar] at h1
      rw [hinr, h1]
      simp
  have huHL : ∀ i, u i ∈ HL := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [hul]
      exact hstab σ hσ _ (hh₁ i)
    | right j =>
      rw [hur]
      exact (hdual _).2 (hfint j)
  have hgen : ∀ y ∈ HL, y ∈ HT.eigSp ρH σ → ∃ c : Fin (p + q) → R', y = ∑ i, (c i : Ω) • u i := by
    intro y hy hye
    have hy1 : y.1 ∈ Submodule.span R' (Set.range b₁) := by
      rw [hs₁]
      refine ⟨hL.2 ⟨y, hy, rfl⟩, HT.LatBasic.mem_eigSp.2 fun a => ?_⟩
      rw [← hact, HT.LatBasic.mem_eigSp.1 hye a]
      rfl
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 hy1
    obtain ⟨w, hw0⟩ : ∃ w, w = y - ∑ i, (c i : Ω) • u (Fin.castAdd q i) := ⟨_, rfl⟩
    have hwH : w ∈ HL := by
      rw [hw0]
      exact HL.sub_mem hy (HL.sum_mem fun i _ => HL.smul_mem (c i) (huHL _))
    have hwe : w ∈ HT.eigSp ρH σ := by
      rw [hw0]
      exact Submodule.sub_mem _ hye (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hueig _))
    have hw1 : w.1 = 0 := by
      rw [hw0, Prod.fst_sub, Prod.fst_sum, sub_eq_zero, ← hc]
      simp [hu1, Subring.smul_def]
    have hwz : ((0 : Vs), w.2) = w := Prod.ext hw1.symm rfl
    have hw2 : ∀ z ∈ Submodule.span R' (Set.range ℓ), w.2 z ∈ R' := (hdual _).1 (hwz ▸ hwH)
    have hcomp : w.2 ∘ₗ HT.eigProj ρ σ' = w.2 := comp_eigProj hinr hσσ' hbar (hwz.symm ▸ hwe)
    have hd : w.2 = ∑ j, w.2 (b₂ j) • f j := by
      ext x
      have h1 := LinearMap.congr_fun hcomp x
      rw [LinearMap.comp_apply, hf1, map_sum] at h1
      rw [← h1]
      simp [LinearMap.sum_apply, mul_comm]
    refine ⟨Fin.addCases c (fun j => ⟨w.2 (b₂ j), hw2 _ (hm₂ j).1⟩), ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, hur]
    have e2 : ∑ j, (w.2 (b₂ j)) • (((0 : Vs), f j) : Vs × Module.Dual Ω Vs) = w := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, hw1]
      · rw [Prod.snd_sum]
        simpa using hd.symm
    rw [e2, hw0]
    abel
  have hqt := HodgeDeterminantLattice.eigQuot_eq_span (A := R') σ hfree (fun a => ⟨⟨_, hσ _⟩, rfl⟩)
  have hT : ∀ i, HT.eigProj ρH σ (t i) ∈ HL := fun i => by
    have h1 : HT.eigProj ρH σ (t i) ∈ HT.eigQuot ρH σ HL := by
      rw [hqt]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := h1
    rw [← e]
    exact hstab σ hσ y hy
  choose A hA using fun i => hgen _ (hT i) (HT.LatBasic.eigProj_mem _ _ _)
  have hB : ∀ j, ∃ c : Fin (p + q) → R', ∑ k, c k • HT.eigProj ρH σ (t k) = u j := fun j => by
    have h1 : u j ∈ HT.eigQuot ρH σ HL := ⟨u j, huHL j, HT.LatBasic.eigProj_of_mem (hueig j)⟩
    rw [hqt] at h1
    exact (Submodule.mem_span_range_iff_exists_fun R').1 h1
  choose B hB using hB
  let AΩ : Matrix (Fin (p + q)) (Fin (p + q)) Ω := Matrix.of fun i j => (A i j : Ω)
  let BΩ : Matrix (Fin (p + q)) (Fin (p + q)) Ω := Matrix.of fun i j => (B i j : Ω)
  have key : AΩ * BΩ = 1 := by
    ext i k
    have h1 := HodgeDeterminantLattice.sum_smul_sum AΩ BΩ (fun k => HT.eigProj ρH σ (t k)) i
    have h2 : ∑ j, AΩ i j • ∑ k, BΩ j k • HT.eigProj ρH σ (t k) = HT.eigProj ρH σ (t i) := by
      rw [hA i]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hB j]
      rfl
    have h3 : ∑ k, ((AΩ * BΩ) i k - (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) i k) •
        HT.eigProj ρH σ (t k) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1, h2, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj σ hfree) _ h3 k)
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    ext i k
    have h1 := congrFun (congrFun key i) k
    simpa [Matrix.mul_apply, Matrix.one_apply, AΩ, BΩ, apply_ite] using h1
  refine ⟨b₁, b₂, u, Matrix.of A, hb₁, hs₁, hb₂, hs₂, ⟨hueig, hu1, fun j => ?_⟩, huHL,
    Matrix.isUnit_det_of_right_inverse hAB, hA⟩
  rw [hur]
  exact ⟨rfl, hf2 j⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames
