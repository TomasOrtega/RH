import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

/- English proof (translation)
Introduce `J _ _ F c hc j σ ι _ _ p x hx`. Use `haveI := Fintype.ofFinite σ`. Use `haveI := Fintype.ofFinite ι`. Establish `hc'` using `isColimitOfPreserves (forget _) hc`. Use `choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)`.

Take `⟨K, hK⟩` from `IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))`. Take `⟨h⟩` from `hK (Finset.mem_insert_self j _)`. Establish `hm : ∀ s, Nonempty (jx s ⟶ K)` using `fun s => hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))`. Set `u : σ → F.obj K` to `fun s => (F.map (hm s).some).hom (x' s)`. Establish `hu : ∀ s, (c.ι.app K).hom (u s) = x s`.

Introduce `s`. Establish `h2` using `congr(($(c.w (hm s).some)).hom (x' s))`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2`. Rewrite using `[h2]`. Conclude with `hx' s`.

Establish `hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0`. Introduce `i`. Rewrite using `[MvPolynomial.eval₂_comp_left]`. Establish `e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom`. Rewrite using `[← CommRingCat.hom_comp, c.w h]`.

Establish `e2 : ⇑(c.ι.app K).hom ∘ u = x` using `funext hu`. Rewrite using `[e1, e2]`. Conclude with `hx i`. Establish `one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0`. Introduce `i`.

Establish `h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0`. Rewrite using `[hz i, map_zero]`. Take `⟨k₀, f₀, e⟩` from `(Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)`. Use `⟨k₀, f₀, fun k f => ?_⟩` and prove the remaining obligations. Establish `e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0` using `by simpa using e`.

Rewrite using `[Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]`. Establish `all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩`.

Consider the case `insert a S _ ih`. Take `⟨k₀, f₀, hh⟩` from `eventually_and (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0) (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0) (one a) ih`. Use `⟨k₀, f₀, fun k f i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `(hh k f).1`.

Conclude with `(hh k f).2 i hi`. Take `⟨k₀, f₀, h0⟩` from `all Finset.univ`. Use `⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩` and prove the remaining obligations. Use `h0 k f i (Finset.mem_univ i)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp]`.

Rewrite using `[Category.assoc]`. Conclude with `this`.
-/
theorem poly_eventually_solvable :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  classical
  intro J _ _ F c hc j σ ι _ _ p x hx
  haveI := Fintype.ofFinite σ
  haveI := Fintype.ofFinite ι
  have hc' := isColimitOfPreserves (forget _) hc

  choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self j _)
  have hm : ∀ s, Nonempty (jx s ⟶ K) := fun s =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))
  let u : σ → F.obj K := fun s => (F.map (hm s).some).hom (x' s)
  have hu : ∀ s, (c.ι.app K).hom (u s) = x s := by
    intro s
    have h2 := congr(($(c.w (hm s).some)).hom (x' s))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact hx' s

  have hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = x := funext hu
    rw [e1, e2]; exact hx i

  have one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    have h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0 := by
      rw [hz i, map_zero]
    obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)
    refine ⟨k₀, f₀, fun k f => ?_⟩
    have e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by simpa using e
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

  have all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a S _ ih =>
      obtain ⟨k₀, f₀, hh⟩ := eventually_and
        (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0)
        (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0)
        (one a) ih
      refine ⟨k₀, f₀, fun k f i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hh k f).1
      · exact (hh k f).2 i hi
  obtain ⟨k₀, f₀, h0⟩ := all Finset.univ
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩
  have := h0 k f i (Finset.mem_univ i)
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

end GlobalTheory.TorsorColim
