import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IdemNilZero

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
  {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) (hef : e * f = e)
include hZ hx hχ he hf hef

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hw`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`. Simplify using `only [LinearMap.mulLeft_apply] at hn ⊢`. Rewrite using `[tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]`.
-/
theorem tef_nil {w : Matrix (Fin N) (Fin N) k} (hw : w ∈ Tef (Z := Z) e f) (hn : IsNilpotent w) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  simp only [LinearMap.mulLeft_apply] at hn ⊢
  rw [tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]

/- English proof (translation)
Establish `hinj : Function.Injective ((LinearMap.mulLeft k e).comp (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f))))`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨y, hy⟩ h0`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0`.

Establish `hfz` using `tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hfz`. Establish `h` using `LinearMap.finrank_range_of_inj hinj`. Rewrite `h` using `[LinearMap.range_comp, Submodule.range_subtype]`.

Conclude with `h`.
-/
theorem tef_finrank : finrank k (Tef (Z := Z) e f) = finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) := by
  have hinj : Function.Injective ((LinearMap.mulLeft k e).comp
      (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f)))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ h0
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0
    have hfz := tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)
    apply Subtype.ext
    simpa using hfz
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Rewrite using `[Submodule.mem_bot]`. Conclude with `tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)`.
-/
theorem tef_inf : Tef (Z := Z) e f ⊓ Nx D x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  exact tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)

/- English proof (translation)
Introduce `w hw`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hw`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`. Take `⟨s, hs, n, hn, rfl⟩` from `Submodule.mem_sup.1 (z_le D hZ hx hχ hz)`. Simplify using `only [LinearMap.mulLeft_apply]`.

Establish `hfS : f ∈ Sx D x` using `pz_mem_S D hZ hx hχ hf`. Establish `hfC : f ∈ Cx Z x` using `z_le_cx hf.1`. Establish `heC : e ∈ Cx Z x` using `sx_le D he.1`. Establish `hs' : s ∈ Sx D x` using `(Subalgebra.mem_toSubmodule _).1 hs`. Rewrite using `[mul_add, mul_add]`.

Use `Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn`.
-/
theorem tef_le : Tef (Z := Z) e f ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 (z_le D hZ hx hχ hz)
  simp only [LinearMap.mulLeft_apply]
  have hfS : f ∈ Sx D x := pz_mem_S D hZ hx hχ hf
  have hfC : f ∈ Cx Z x := z_le_cx hf.1
  have heC : e ∈ Cx Z x := sx_le D he.1
  have hs' : s ∈ Sx D x := (Subalgebra.mem_toSubmodule _).1 hs
  rw [mul_add, mul_add]
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_
  rw [← mul_assoc]
  exact nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn

/- English proof (translation)
Rewrite using `[← tef_finrank D hZ hx hχ he hf hef]`. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)`. Rewrite `h1` using `[tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero]`. Establish `h2 : Tef (Z` using `Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right`. Establish `h3` using `Submodule.finrank_mono h2`.

Establish `h4` using `Submodule.finrank_add_le_finrank_add_finrank ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)`. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_le : finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) ≤
    finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) := by
  rw [← tef_finrank D hZ hx hχ he hf hef]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  omega

/- English proof (translation)
Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)`. Rewrite `h1` using `[tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef]`. Establish `h2 : Tef (Z` using `Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right`. Establish `h4` using `Submodule.finrank_add_le_finrank_add_finrank ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)`. Establish `h5` using `Submodule.eq_of_le_of_finrank_le h2 (by omega)`.

Rewrite using `[h5]`. Conclude with `le_sup_left`.
-/
theorem dim_eq_le (hd : finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) ≤
    finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ≤ Tef (Z := Z) e f ⊔ Nx D x := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  have h5 := Submodule.eq_of_le_of_finrank_le h2 (by omega)
  rw [h5]
  exact le_sup_left

end

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

/- English proof (translation)
Establish `hfin` using `pi_fin hZ`. Establish `hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x`. Introduce `s hs`. Establish `hsum : s = ∑ f ∈ hfin.toFinset, f * s`. Rewrite using `[← Finset.sum_mul, pi_sum hZ, one_mul]`.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ (fun f hf => ?_)` and prove the remaining obligations. Rewrite `hf` using `[Set.Finite.mem_toFinset]`. Take `⟨hfS, hd⟩` from `h f hf`. Establish `hle` using `dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd`.

Establish `hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f)` using `Submodule.mem_map.2 ⟨s, hs, rfl⟩`. Establish `hT : Tef (Z` using `Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by`. Introduce `w hw`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hw`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`.

Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Simplify using `only [LinearMap.mulLeft_apply]`. Conclude with `(Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))`. Conclude with `(sup_le hT le_sup_right) (hle hmem)`. Establish `hxm : x ∈ Z.toSubmodule ⊔ Nx D x` using `(sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)`.

Take `⟨c, hc, n, hn, hcn⟩` from `Submodule.mem_sup.1 hxm`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcn, add_sub_cancel_left]`. Conclude with `nx_nil D hZ hx hχ n hn`.
-/
theorem zn_of_eq (h : ∀ f ∈ primIdem Z, f ∈ primIdem (Sx D x) ∧
      finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k f)) ≤ finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hfin := pi_fin hZ
  have hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x := by
    intro s hs
    have hsum : s = ∑ f ∈ hfin.toFinset, f * s := by
      rw [← Finset.sum_mul, pi_sum hZ, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ (fun f hf => ?_)
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfS, hd⟩ := h f hf
    have hle := dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd
    have hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f) :=
      Submodule.mem_map.2 ⟨s, hs, rfl⟩
    have hT : Tef (Z := Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      apply Submodule.mem_sup_left
      simp only [LinearMap.mulLeft_apply]
      exact (Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))
    exact (sup_le hT le_sup_right) (hle hmem)
  have hxm : x ∈ Z.toSubmodule ⊔ Nx D x :=
    (sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)
  obtain ⟨c, hc, n, hn, hcn⟩ := Submodule.mem_sup.1 hxm
  refine ⟨c, hc, ?_⟩
  rw [← hcn, add_sub_cancel_left]
  exact nx_nil D hZ hx hχ n hn

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
