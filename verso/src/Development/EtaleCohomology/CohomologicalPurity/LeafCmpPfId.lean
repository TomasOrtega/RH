import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPf

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Set `J` to `F₀.I.map ψ`. Set `π : C →+* C ⧸ J` to `Ideal.Quotient.mk J`. Set `ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J` to `Ideal.Quotient.lift F₀.I (π.comp ψ) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))`. Establish `hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ` using `RingHom.ext fun a => rfl`. Establish `hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w = (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι`.

Rewrite using `[Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc, ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]`. Set `t` to `F.cart.lift _ _ hw`. Establish `ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) = Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)` using `F.cart.lift_fst _ _ _`. Set `τ : F.B ⧸ F.I →+* C ⧸ J` to `(Spec.preimage t).hom`. Establish `h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) = Spec.map (CommRingCat.ofHom (π.comp φ))`.

Rewrite using `[spec_comp_ofHom, spec_comp_ofHom, ← ht]`. Use `congr 1`. Conclude with `Spec.map_preimage t`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `a ha`. Rewrite using `[Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]`. Express the relevant statement in the definitionally equal form `(π.comp φ) a = 0`. Rewrite using `[← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]`.
-/
theorem le_map_of {d : ℕ} {P : SP d} (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C)
    (e : Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w) : F.I.map φ ≤ F₀.I.map ψ := by
  let J := F₀.I.map ψ
  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  let ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J := Ideal.Quotient.lift F₀.I (π.comp ψ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))
  have hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ := RingHom.ext fun a => rfl
  have hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w =
      (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι := by
    rw [Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc,
      ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]
  let t := F.cart.lift _ _ hw
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) =
      Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) := F.cart.lift_fst _ _ _
  let τ : F.B ⧸ F.I →+* C ⧸ J := (Spec.preimage t).hom
  have h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) =
      Spec.map (CommRingCat.ofHom (π.comp φ)) := by
    rw [spec_comp_ofHom, spec_comp_ofHom, ← ht]
    congr 1
    exact Spec.map_preimage t
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (π.comp φ) a = 0
  rw [← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/- English proof (translation)
Introduce `_ _ F F₀ C _ φ ψ e` and use `le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)`.
-/
theorem LeafCmpId_pf : LeafCmpId := fun _ _ F F₀ C _ φ ψ e =>
  le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)

end LateralTheory.CohomologicalPurity.Cl
