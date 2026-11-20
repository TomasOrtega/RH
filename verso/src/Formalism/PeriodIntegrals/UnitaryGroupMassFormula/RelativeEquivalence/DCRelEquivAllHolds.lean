import Mathlib
import Formalism.PeriodIntegrals.DCRelEquiv

noncomputable section

open scoped Classical

namespace PI.DCRelEquiv.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

/- English proof (translation)
Normalize the expressions using the abelian group laws.
-/
theorem add_sub_self' {V : Type*} [AddCommGroup V] (a b : V) : a + (b - a) = b := by
  abel

/- English proof (translation)
Introduce `x hx`. Set `f : U →ₗ[K] U` to `(n : V →ₗ[K] V).restrict h`. Establish `hinj : Function.Injective f`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h1` using `congrArg Subtype.val hab`. Simplify using `only [f, LinearMap.restrict_apply, LinearEquiv.coe_coe] at h1`. Conclude with `n.injective h1`. Establish `hsurj : Function.Surjective f` using `LinearMap.injective_iff_surjective.mp hinj`. Take `⟨y, hy⟩` from `hsurj ⟨x, hx⟩`.

Establish `hy' : n y.1 = x`. Establish `h1` using `congrArg Subtype.val hy`. Simplify `h1` using `[f]`. Rewrite using `[← hy', LinearEquiv.symm_apply_apply]`. Conclude with `y.2`.
-/
theorem symm_mem_of_maps {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : V ≃ₗ[K] V) (U : Submodule K V) (h : ∀ x ∈ U, n x ∈ U) : ∀ x ∈ U, n.symm x ∈ U := by
  intro x hx
  let f : U →ₗ[K] U := (n : V →ₗ[K] V).restrict h
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    simp only [f, LinearMap.restrict_apply, LinearEquiv.coe_coe] at h1
    exact n.injective h1
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hy' : n y.1 = x := by
    have h1 := congrArg Subtype.val hy
    simpa [f] using h1
  rw [← hy', LinearEquiv.symm_apply_apply]
  exact y.2

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Simplify using `only [Xflag, FlagG.Xa]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Use `⟨i, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hi ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Xflag_mono (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  simp only [Xflag, FlagG.Xa]
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨i, ?_, rfl⟩
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

/- English proof (translation)
Simplify using `only [Xflag, Xsp, FlagG.Xa, FlagG.X]`. Conclude with `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem Xflag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F := by
  simp only [Xflag, Xsp, FlagG.Xa, FlagG.X]
  exact Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
Simplify using `only [Xflag, FlagG.Xa]`. Conclude with `Submodule.subset_span ⟨i, by simp, rfl⟩`.
-/
theorem e_mem_Xflag (F : LFlag S r T) (i : Fin r) : F.fl.e i ∈ Xflag F (i.1 + 1) := by
  simp only [Xflag, FlagG.Xa]
  exact Submodule.subset_span ⟨i, by simp, rfl⟩

/- English proof (translation)
Conclude with `Xflag_le_X F (i.1 + 1) (e_mem_Xflag F i)`.
-/
theorem e_mem_X (F : LFlag S r T) (i : Fin r) : F.fl.e i ∈ Xsp F := by
  exact Xflag_le_X F (i.1 + 1) (e_mem_Xflag F i)

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth_iff {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Conclude with `(show ∀ x y, S.hT (g x) (g y) = S.hT x y from h) x y`.
-/
theorem isom_app {g : S.V ≃ₗ[E] S.V} (h : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (g x) (g y) = S.hT x y := by
  exact (show ∀ x y, S.hT (g x) (g y) = S.hT x y from h) x y

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem gmap_mul' (n m : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (n * m) L = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.gmap m L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Conclude with `Submodule.map_id L`.
-/
theorem gmap_one' (L : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.map_id L

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem gmap_inv' {n : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} (hg : Formalism.HermitianLatticesTheory.gmap n L = L) :
    Formalism.HermitianLatticesTheory.gmap n⁻¹ L = L := by
  calc Formalism.HermitianLatticesTheory.gmap n⁻¹ L = Formalism.HermitianLatticesTheory.gmap n⁻¹ (Formalism.HermitianLatticesTheory.gmap n L) := by rw [hg]
    _ = L := by rw [← gmap_mul', inv_mul_cancel, gmap_one']

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Unfold `IsAutLam at hn hm ⊢`. Conclude with `⟨Subgroup.mul_mem _ hn.1 hm.1, by rw [gmap_mul', hm.2, hn.2]⟩`.
-/
theorem autLam_mul {n m : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (hm : IsAutLam S Λ m) :
    IsAutLam S Λ (n * m) := by
  unfold IsAutLam at hn hm ⊢
  exact ⟨Subgroup.mul_mem _ hn.1 hm.1, by rw [gmap_mul', hm.2, hn.2]⟩

/- English proof (translation)
Unfold `IsAutLam at hn ⊢`. Conclude with `⟨Subgroup.inv_mem _ hn.1, gmap_inv' hn.2⟩`.
-/
theorem autLam_inv {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) : IsAutLam S Λ n⁻¹ := by
  unfold IsAutLam at hn ⊢
  exact ⟨Subgroup.inv_mem _ hn.1, gmap_inv' hn.2⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨-, hF, -⟩` from `hn`. Establish `h2` using `add_mem (Xflag_mono F j (hF j x hx)) hx`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem nlam_maps_Xflag {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n x ∈ Xflag F (j + 1) := by
  intro x hx
  obtain ⟨-, hF, -⟩ := hn
  have h2 := add_mem (Xflag_mono F j (hF j x hx)) hx
  rwa [sub_add_cancel] at h2

/- English proof (translation)
Establish `hle : Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V)` using `by show Submodule.span E (Set.range F.fl.e) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Xflag_le_X F (i.1 + 1) (nlam_maps_Xflag hn i.1 _ (e_mem_Xflag F i))`. Introduce `x hx`.

Conclude with `hle hx`.
-/
theorem nlam_maps_X {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  have hle : Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Xflag_le_X F (i.1 + 1) (nlam_maps_Xflag hn i.1 _ (e_mem_Xflag F i))
  intro x hx
  exact hle hx

/- English proof (translation)
Take `⟨hA, hF, hO⟩` from `id hn`. Take `⟨hiso, -⟩` from `id hA`. Simplify using `only [NLam, Set.mem_setOf_eq]`. Use `⟨autLam_inv hA, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`.

Establish `hy : n.symm x ∈ Xflag F (j + 1)` using `symm_mem_of_maps n _ (nlam_maps_Xflag hn j) x hx`. Establish `h1` using `hF j _ hy`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Establish `h2` using `neg_mem h1`. Rewrite `h2` using `[neg_sub]`.

Conclude with `h2`. Introduce `x hx`. Establish `hy : n.symm x ∈ orth S (Xsp F)`. Rewrite `hx`, the goal using `[mem_orth_iff]`. Introduce `u hu`.

Establish `hnu : n u ∈ Xsp F` using `nlam_maps_X hn u hu`. Rewrite using `[← isom_app hiso u (n.symm x), LinearEquiv.apply_symm_apply]`. Conclude with `hx (n u) hnu`. Establish `h1` using `hO _ hy`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`.

Establish `h2` using `neg_mem h1`. Rewrite `h2` using `[neg_sub]`. Conclude with `h2`.
-/
theorem nlam_inv {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n⁻¹ ∈ NLam Λ F := by
  obtain ⟨hA, hF, hO⟩ := id hn
  obtain ⟨hiso, -⟩ := id hA
  simp only [NLam, Set.mem_setOf_eq]
  refine ⟨autLam_inv hA, ?_, ?_⟩
  · intro j x hx
    have hy : n.symm x ∈ Xflag F (j + 1) :=
      symm_mem_of_maps n _ (nlam_maps_Xflag hn j) x hx
    have h1 := hF j _ hy
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2
  · intro x hx
    have hy : n.symm x ∈ orth S (Xsp F) := by
      rw [mem_orth_iff] at hx ⊢
      intro u hu
      have hnu : n u ∈ Xsp F := nlam_maps_X hn u hu
      rw [← isom_app hiso u (n.symm x), LinearEquiv.apply_symm_apply]
      exact hx (n u) hnu
    have h1 := hO _ hy
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2

/- English proof (translation)
Take `⟨hnA, hnF, hnO⟩` from `id hn`. Take `⟨hmA, hmF, hmO⟩` from `id hm`. Simplify using `only [NLam, Set.mem_setOf_eq]`. Use `⟨autLam_mul hnA hmA, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx show n (m x) - x ∈ Xflag F j`.

Establish `e : n (m x) - x = (n (m x) - m x) + (m x - x)` using `by abel`. Rewrite using `[e]`. Conclude with `add_mem (hnF j _ (nlam_maps_Xflag hm j x hx)) (hmF j x hx)`. Introduce `x hx show n (m x) - x ∈ Xsp F`. Establish `e : n (m x) - x = n (m x - x) + (n x - x)` using `by rw [map_sub]; abel`.

Rewrite using `[e]`. Conclude with `add_mem (nlam_maps_X hn _ (hmO x hx)) (hnO x hx)`.
-/
theorem nlam_mul {F : LFlag S r T} {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) :
    n * m ∈ NLam Λ F := by
  obtain ⟨hnA, hnF, hnO⟩ := id hn
  obtain ⟨hmA, hmF, hmO⟩ := id hm
  simp only [NLam, Set.mem_setOf_eq]
  refine ⟨autLam_mul hnA hmA, ?_, ?_⟩
  · intro j x hx
    show n (m x) - x ∈ Xflag F j
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact add_mem (hnF j _ (nlam_maps_Xflag hm j x hx)) (hmF j x hx)
  · intro x hx
    show n (m x) - x ∈ Xsp F
    have e : n (m x) - x = n (m x - x) + (n x - x) := by rw [map_sub]; abel
    rw [e]
    exact add_mem (nlam_maps_X hn _ (hmO x hx)) (hnO x hx)

/- English proof (translation)
Establish `h` using `hfr i.castSucc`. Simplify using `only [frame, FlagG.fvec, Fin.snoc_castSucc] at h`. Conclude with `h`.
-/
theorem e_of_frame {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V} (hfr : ∀ a, frame F₂ a = g (frame F₁ a))
    (i : Fin r) : F₂.fl.e i = g (F₁.fl.e i) := by
  have h := hfr i.castSucc
  simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at h
  exact h

/- English proof (translation)
Establish `he : F₂.fl.e = (g : S.V →ₗ[E] S.V) ∘ F₁.fl.e` using `funext fun i => e_of_frame hfr i`. Simplify using `only [Xflag, FlagG.Xa]`. Rewrite using `[Submodule.map_span, ← Set.image_comp, he]`.
-/
theorem Xflag_transport {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (j : ℕ) :
    Xflag F₂ j = (Xflag F₁ j).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = (g : S.V →ₗ[E] S.V) ∘ F₁.fl.e := funext fun i => e_of_frame hfr i
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span, ← Set.image_comp, he]

/- English proof (translation)
Establish `he : F₂.fl.e = (g : S.V →ₗ[E] S.V) ∘ F₁.fl.e` using `funext fun i => e_of_frame hfr i`. Simplify using `only [Xsp, FlagG.X]`. Rewrite using `[Submodule.map_span, ← Set.range_comp, he]`.
-/
theorem Xsp_transport {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) :
    Xsp F₂ = (Xsp F₁).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = (g : S.V →ₗ[E] S.V) ∘ F₁.fl.e := funext fun i => e_of_frame hfr i
  simp only [Xsp, FlagG.X]
  rw [Submodule.map_span, ← Set.range_comp, he]

/- English proof (translation)
Rewrite using `[Xflag_transport hfr j, Submodule.mem_map_equiv]`.
-/
theorem Xflag_mem_transport {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (j : ℕ) (v : S.V) :
    v ∈ Xflag F₂ j ↔ g.symm v ∈ Xflag F₁ j := by
  rw [Xflag_transport hfr j, Submodule.mem_map_equiv]

/- English proof (translation)
Rewrite using `[Xsp_transport hfr, Submodule.mem_map_equiv]`.
-/
theorem Xsp_mem_transport {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (v : S.V) :
    v ∈ Xsp F₂ ↔ g.symm v ∈ Xsp F₁ := by
  rw [Xsp_transport hfr, Submodule.mem_map_equiv]

/- English proof (translation)
Rewrite using `[mem_orth_iff, mem_orth_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Rewrite using `[← isom_app hg w (g.symm v), LinearEquiv.apply_symm_apply]`. Apply `h` to reduce the goal to its premises.

Rewrite using `[Xsp_mem_transport hfr, LinearEquiv.symm_apply_apply]`. Conclude with `hw`. Introduce `h x hx`. Establish `hx'` using `(Xsp_mem_transport hfr x).mp hx`. Establish `h1` using `h _ hx'`.

Rewrite `h1` using `[← isom_app hg (g.symm x) (g.symm v), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h1`.
-/
theorem orth_mem_transport {F₁ F₂ : LFlag S r T} {g : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (v : S.V) :
    v ∈ orth S (Xsp F₂) ↔ g.symm v ∈ orth S (Xsp F₁) := by
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro h w hw
    rw [← isom_app hg w (g.symm v), LinearEquiv.apply_symm_apply]
    apply h
    rw [Xsp_mem_transport hfr, LinearEquiv.symm_apply_apply]
    exact hw
  · intro h x hx
    have hx' := (Xsp_mem_transport hfr x).mp hx
    have h1 := h _ hx'
    rw [← isom_app hg (g.symm x) (g.symm v), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at h1
    exact h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Establish `hgw : g w ∈ A₂` using `by rw [hA, LinearEquiv.symm_apply_apply]; exact hw`. Establish `h1` using `h _ hgw`. Rewrite `h1` using `[hB]`.

Establish `e : (g⁻¹ * x * g) w - w = g.symm (x (g w) - g w)` using `by show g.symm (x (g w)) - w = g.symm (x (g w) - g w)`. Rewrite using `[map_sub, LinearEquiv.symm_apply_apply]`. Rewrite using `[e]`. Conclude with `h1`. Introduce `h v hv`.

Establish `h1` using `h _ ((hA v).mp hv)`. Rewrite using `[hB]`. Establish `e : (g⁻¹ * x * g) (g.symm v) - g.symm v = g.symm (x v - v)` using `by show g.symm (x (g (g.symm v))) - g.symm v = g.symm (x v - v)`. Rewrite using `[LinearEquiv.apply_symm_apply, map_sub]`. Rewrite `h1` using `[e]`.

Conclude with `h1`.
-/
theorem conj_cond (g x : S.V ≃ₗ[E] S.V) (A₁ B₁ A₂ B₂ : Submodule E S.V)
    (hA : ∀ v, v ∈ A₂ ↔ g.symm v ∈ A₁) (hB : ∀ v, v ∈ B₂ ↔ g.symm v ∈ B₁) :
    (∀ v ∈ A₂, x v - v ∈ B₂) ↔ (∀ w ∈ A₁, (g⁻¹ * x * g) w - w ∈ B₁) := by
  constructor
  · intro h w hw
    have hgw : g w ∈ A₂ := by rw [hA, LinearEquiv.symm_apply_apply]; exact hw
    have h1 := h _ hgw
    rw [hB] at h1
    have e : (g⁻¹ * x * g) w - w = g.symm (x (g w) - g w) := by
      show g.symm (x (g w)) - w = g.symm (x (g w) - g w)
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    exact h1
  · intro h v hv
    have h1 := h _ ((hA v).mp hv)
    rw [hB]
    have e : (g⁻¹ * x * g) (g.symm v) - g.symm v = g.symm (x v - v) := by
      show g.symm (x (g (g.symm v))) - g.symm v = g.symm (x v - v)
      rw [LinearEquiv.apply_symm_apply, map_sub]
    rw [e] at h1
    exact h1

end Gen

/- English proof (translation)
Introduce `E _ _ _ S r T Λ F n m hn hm`. Conclude with `⟨nlam_mul hn hm, nlam_inv hn⟩`.
-/
theorem nLamGroup_holds : NLamGroup := by
  intro E _ _ _ S r T Λ F n m hn hm
  exact ⟨nlam_mul hn hm, nlam_inv hn⟩

/- English proof (translation)
Introduce `E _ _ _ S r T Λ F₁ F₂ g hg hfr x`. Take `⟨hgi, -⟩` from `id hg`. Establish `hA : IsAutLam S Λ x ↔ IsAutLam S Λ (g⁻¹ * x * g)`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `autLam_mul (autLam_mul (autLam_inv hg) hx) hg`. Introduce `hx`. Establish `e : x = g * (g⁻¹ * x * g) * g⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `autLam_mul (autLam_mul hg hx) (autLam_inv hg)`.

Simplify using `only [NLam, Set.mem_setOf_eq]`. Use `and_congr hA (and_congr ?_ ?_)` and prove the remaining obligations. Apply `forall_congr'` to reduce the goal to its premises. Introduce `j`. Conclude with `conj_cond g x _ _ _ _ (Xflag_mem_transport hfr (j + 1)) (Xflag_mem_transport hfr j)`.

Conclude with `conj_cond g x _ _ _ _ (orth_mem_transport hfr hgi) (Xsp_mem_transport hfr)`.
-/
theorem nLamConj_holds : NLamConj := by
  intro E _ _ _ S r T Λ F₁ F₂ g hg hfr x
  obtain ⟨hgi, -⟩ := id hg
  have hA : IsAutLam S Λ x ↔ IsAutLam S Λ (g⁻¹ * x * g) := by
    constructor
    · intro hx
      exact autLam_mul (autLam_mul (autLam_inv hg) hx) hg
    · intro hx
      have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [e]
      exact autLam_mul (autLam_mul hg hx) (autLam_inv hg)
  simp only [NLam, Set.mem_setOf_eq]
  refine and_congr hA (and_congr ?_ ?_)
  · apply forall_congr'
    intro j
    exact conj_cond g x _ _ _ _ (Xflag_mem_transport hfr (j + 1)) (Xflag_mem_transport hfr j)
  · exact conj_cond g x _ _ _ _ (orth_mem_transport hfr hgi) (Xsp_mem_transport hfr)

/- English proof (translation)
Introduce `E _ _ _ S r T T' Λ F`. Establish `hC` using `nLamConj_holds`. Unfold `NLamConj at hC`. Use `⟨fun F₁ => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h₁ h₂ => ?_⟩` and prove the remaining obligations. Unfold `DCRel`.

Conclude with `⟨1, one_mem_NLam (Λ := Λ) F, 1, one_mem_NLam (Λ := Λ) F₁, fun a => rfl, rfl⟩`. Take `⟨n, hn, m, hm, hfr, hz⟩` from `h`. Take `⟨hnA, -, -⟩` from `id hn`. Take `⟨hmA, -, -⟩` from `id hm`. Establish `hg : IsAutLam S Λ (n * m)` using `autLam_mul hnA hmA`.

Establish `hfr' : ∀ a, frame F₂ a = (n * m) (frame F₁ a)` using `fun a => hfr a`. Establish `hm' : n * m⁻¹ * n⁻¹ ∈ NLam Λ F₂`. Rewrite using `[hC E S r T' Λ F₁ F₂ (n * m) hg hfr' (n * m⁻¹ * n⁻¹)]`. Establish `e : (n * m)⁻¹ * (n * m⁻¹ * n⁻¹) * (n * m) = m⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `nlam_inv hm`. Unfold `DCRel`. Use `⟨n⁻¹, nlam_inv hn, n * m⁻¹ * n⁻¹, hm', fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfr a] show frame F₁ a = n.symm (n (m.symm (n.symm (n (m (frame F₁ a))))))`. Simplify using `only [LinearEquiv.symm_apply_apply]`.

Rewrite using `[hz] show F₁.zt = n.symm (n (m.symm (n.symm (n (m F₁.zt)))))`. Simplify using `only [LinearEquiv.symm_apply_apply]`. Take `⟨n₁, hn₁, m₁, hm₁, hfr₁, hz₁⟩` from `h₁`. Take `⟨n₂, hn₂, m₂, hm₂, hfr₂, hz₂⟩` from `h₂`. Take `⟨hnA, -, -⟩` from `id hn₁`.

Take `⟨hmA, -, -⟩` from `id hm₁`. Establish `hg : IsAutLam S Λ (n₁ * m₁)` using `autLam_mul hnA hmA`. Establish `hfr' : ∀ a, frame F₂ a = (n₁ * m₁) (frame F₁ a)` using `fun a => hfr₁ a`. Establish `hm'' : (n₁ * m₁)⁻¹ * m₂ * (n₁ * m₁) ∈ NLam Λ F₁` using `(hC E S r T' Λ F₁ F₂ (n₁ * m₁) hg hfr' m₂).mp hm₂`. Unfold `DCRel`.

Use `⟨n₂ * n₁, nlam_mul hn₂ hn₁, m₁ * ((n₁ * m₁)⁻¹ * m₂ * (n₁ * m₁)), nlam_mul hm₁ hm'', fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfr₂ a, hfr₁ a] show n₂ (m₂ (n₁ (m₁ (frame F₁ a)))) = n₂ (n₁ (m₁ (m₁.symm (n₁.symm (m₂ (n₁ (m₁ (frame F₁ a))))))))`. Simplify using `only [LinearEquiv.apply_symm_apply]`. Rewrite using `[hz₂, hz₁] show n₂ (m₂ (n₁ (m₁ F₁.zt))) = n₂ (n₁ (m₁ (m₁.symm (n₁.symm (m₂ (n₁ (m₁ F₁.zt)))))))`. Simplify using `only [LinearEquiv.apply_symm_apply]`.
-/
theorem dCRelEquivAll_holds : DCRelEquivAll := by
  intro E _ _ _ S r T T' Λ F
  have hC := nLamConj_holds
  unfold NLamConj at hC
  refine ⟨fun F₁ => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h₁ h₂ => ?_⟩
  · unfold DCRel
    exact ⟨1, one_mem_NLam (Λ := Λ) F, 1, one_mem_NLam (Λ := Λ) F₁, fun a => rfl, rfl⟩
  · obtain ⟨n, hn, m, hm, hfr, hz⟩ := h
    obtain ⟨hnA, -, -⟩ := id hn
    obtain ⟨hmA, -, -⟩ := id hm
    have hg : IsAutLam S Λ (n * m) := autLam_mul hnA hmA
    have hfr' : ∀ a, frame F₂ a = (n * m) (frame F₁ a) := fun a => hfr a
    have hm' : n * m⁻¹ * n⁻¹ ∈ NLam Λ F₂ := by
      rw [hC E S r T' Λ F₁ F₂ (n * m) hg hfr' (n * m⁻¹ * n⁻¹)]
      have e : (n * m)⁻¹ * (n * m⁻¹ * n⁻¹) * (n * m) = m⁻¹ := by group
      rw [e]
      exact nlam_inv hm
    unfold DCRel
    refine ⟨n⁻¹, nlam_inv hn, n * m⁻¹ * n⁻¹, hm', fun a => ?_, ?_⟩
    · rw [hfr a]
      show frame F₁ a = n.symm (n (m.symm (n.symm (n (m (frame F₁ a))))))
      simp only [LinearEquiv.symm_apply_apply]
    · rw [hz]
      show F₁.zt = n.symm (n (m.symm (n.symm (n (m F₁.zt)))))
      simp only [LinearEquiv.symm_apply_apply]
  · obtain ⟨n₁, hn₁, m₁, hm₁, hfr₁, hz₁⟩ := h₁
    obtain ⟨n₂, hn₂, m₂, hm₂, hfr₂, hz₂⟩ := h₂
    obtain ⟨hnA, -, -⟩ := id hn₁
    obtain ⟨hmA, -, -⟩ := id hm₁
    have hg : IsAutLam S Λ (n₁ * m₁) := autLam_mul hnA hmA
    have hfr' : ∀ a, frame F₂ a = (n₁ * m₁) (frame F₁ a) := fun a => hfr₁ a
    have hm'' : (n₁ * m₁)⁻¹ * m₂ * (n₁ * m₁) ∈ NLam Λ F₁ :=
      (hC E S r T' Λ F₁ F₂ (n₁ * m₁) hg hfr' m₂).mp hm₂
    unfold DCRel
    refine ⟨n₂ * n₁, nlam_mul hn₂ hn₁, m₁ * ((n₁ * m₁)⁻¹ * m₂ * (n₁ * m₁)), nlam_mul hm₁ hm'',
      fun a => ?_, ?_⟩
    · rw [hfr₂ a, hfr₁ a]
      show n₂ (m₂ (n₁ (m₁ (frame F₁ a)))) =
        n₂ (n₁ (m₁ (m₁.symm (n₁.symm (m₂ (n₁ (m₁ (frame F₁ a))))))))
      simp only [LinearEquiv.apply_symm_apply]
    · rw [hz₂, hz₁]
      show n₂ (m₂ (n₁ (m₁ F₁.zt))) = n₂ (n₁ (m₁ (m₁.symm (n₁.symm (m₂ (n₁ (m₁ F₁.zt)))))))
      simp only [LinearEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `E _ _ _ S r T T' Λ F P`. Establish `hC` using `dCRelEquivAll_holds`. Unfold `DCRelEquivAll at hC`. Establish `hEq` using `hC E S r T T' Λ F`. Establish `hR : Equivalence (Rel Λ F P)` using `⟨fun x => hEq.refl x.1, fun h => hEq.symm h, fun h₁ h₂ => hEq.trans h₁ h₂⟩`.

Unfold `EqIff`. Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(Equivalence.eqvGen_iff hR).mp (Quot.eqvGen_exact h)`.

Introduce `h`. Conclude with `Quot.sound h`.
-/
theorem eqIffAll_holds : EqIffAll := by
  intro E _ _ _ S r T T' Λ F P
  have hC := dCRelEquivAll_holds
  unfold DCRelEquivAll at hC
  have hEq := hC E S r T T' Λ F
  have hR : Equivalence (Rel Λ F P) :=
    ⟨fun x => hEq.refl x.1, fun h => hEq.symm h, fun h₁ h₂ => hEq.trans h₁ h₂⟩
  unfold EqIff
  intro x y
  constructor
  · intro h
    exact (Equivalence.eqvGen_iff hR).mp (Quot.eqvGen_exact h)
  · intro h
    exact Quot.sound h

end PI.DCRelEquiv.UnitaryGroupMassFormula
