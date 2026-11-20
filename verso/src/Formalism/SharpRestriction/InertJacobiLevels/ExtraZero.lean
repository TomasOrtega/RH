import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain

/- English proof (translation)
Introduce `x`. Rewrite using `[Subsingleton.elim x 0]`. Conclude with `⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩`.
-/
theorem rrDef_of_subsingleton (D : D7) [Subsingleton D.div.RR.V] : DV.RRDef D := by
  intro x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

/- English proof (translation)
Introduce `_` and use `Subsingleton.elim _ _`.
-/
theorem nprimeDef_of_subsingleton (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V] :
    DV.NprimeDef D L := fun _ => Subsingleton.elim _ _

/- English proof (translation)
Introduce `x _` and use `⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [Subsingleton.elim ((1 : 𝓞 K) • x) 0]; exact Submodule.zero_mem _⟩`.
-/
theorem locLe_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : DV.LocLe w k A B :=
  fun x _ => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [Subsingleton.elim ((1 : 𝓞 K) • x) 0]; exact Submodule.zero_mem _⟩

/- English proof (translation)
Set `_ : w.asIdeal.IsPrime` to `w.isPrime`. Unfold `DV.lenLoc`. Rewrite using `[Module.length_eq_zero_iff]`. Establish `h1 : Subsingleton (↥B ⧸ A.comap B.subtype)`. Establish `: Subsingleton ↥B` using `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`.

Use `infer_instance`. Use `infer_instance`.
-/
theorem lenLoc_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.lenLoc w A B = 0 := by
  let _ : w.asIdeal.IsPrime := w.isPrime
  unfold DV.lenLoc
  rw [Module.length_eq_zero_iff]
  have h1 : Subsingleton (↥B ⧸ A.comap B.subtype) := by
    have : Subsingleton ↥B := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  infer_instance

/- English proof (translation)
Use `⟨fun u w _ => locLe_of_subsingleton _ _ _ _, fun u w _ _ => ⟨locLe_of_subsingleton _ _ _ _, locLe_of_subsingleton _ _ _ _⟩, fun u w l h => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[lenLoc_of_subsingleton]`. Establish `: l = 0` using `by exact_mod_cast h.symm`. Rewrite using `[this, hl]`. Simplify using the standard rewrite rules.
-/
theorem nuDef_of_subsingleton (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V]
    (hl : ∀ u w, L.lenMN u w = 0) : DV.NuDef D L := by
  refine ⟨fun u w _ => locLe_of_subsingleton _ _ _ _, fun u w _ _ =>
    ⟨locLe_of_subsingleton _ _ _ _, locLe_of_subsingleton _ _ _ _⟩, fun u w l h => ?_⟩
  rw [lenLoc_of_subsingleton] at h
  have : l = 0 := by exact_mod_cast h.symm
  rw [this, hl]
  simp

/- English proof (translation)
Establish `h1` using `h.2.2 u w 0 (by rw [lenLoc_of_subsingleton]; rfl)`. Establish `h2 : L.lenMN u w = 0 ∨ D.what₂.places.ramIdx w = 0` using `by simpa using h1.symm`. Break down `h2 with h3 | h3` into its components or cases. Rewrite using `[h3]`. Simplify using the standard rewrite rules.

Conclude with `absurd h3 (hr w)`.
-/
theorem lenMN_zero_of_nuDef (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V] (h : DV.NuDef D L)
    (hr : ∀ w, D.what₂.places.ramIdx w ≠ 0) (u : D.what₂.Word) (w : D.what₂.places.Pl) : (L.lenMN u w : ℝ) = 0 := by
  have h1 := h.2.2 u w 0 (by rw [lenLoc_of_subsingleton]; rfl)
  have h2 : L.lenMN u w = 0 ∨ D.what₂.places.ramIdx w = 0 := by simpa using h1.symm
  rcases h2 with h3 | h3
  · rw [h3]; simp
  · exact absurd h3 (hr w)

def lieOfSubsingleton (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [Subsingleton V] [Subsingleton W] : V ≃ₗᵢ[ℂ] W :=
  ⟨LinearEquiv.ofSubsingleton V W, fun x => by
    rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero]⟩

set_option synthInstance.maxHeartbeats 200000 in

def rowSideZero (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    [Subsingleton EE] : RowSide D EE where
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => lieOfSubsingleton _ _
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => 0
  Mtilde := fun _ => zeroOLat _
  cen := fun _ => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  eOp := fun _ => 0
  eOp_idem := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  eOp_sa := fun _ _ _ => by simp
  eOp_tie := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  RR := zeroHLat D.what₂.LL
  RR_frames := (zeroHLat_good D.what₂.LL).1
  jEE := 0
  jEE_basis := ⟨by
    have : IsEmpty (zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jEE_norm := fun x => (normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

/- English proof (translation)
Introduce `x`. Establish `hx : x = 0` using `Subsingleton.elim (α := Fin 0 → D.what₂.LL) x 0`. Rewrite using `[hx]`. Conclude with `⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩`.
-/
theorem rowSideZero_RRDef (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] [Subsingleton EE] : (rowSideZero D EE).RRDef := by
  intro x
  have hx : x = 0 := Subsingleton.elim (α := Fin 0 → D.what₂.LL) x 0
  rw [hx]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

def trivialSide (D : D7) [Subsingleton D.what₂.EE0] : BaseLevelRowSide D := ⟨rowSideZero D D.what₂.EE0⟩

/- English proof (translation)
The claim follows from `rowSideZero_RRDef D _`.
-/
theorem trivialSide_rrDef_of_subsingleton (D : D7) [Subsingleton D.what₂.EE0] : (trivialSide D).s.RRDef := rowSideZero_RRDef D _

end Formalism.MainNotions.Inhab

end
