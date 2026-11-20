import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

/- English proof (translation)
Introduce `p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst`. Establish `hc : IsUnit (c : Γ(Y, ⊤))`. Use `(hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)` as an intermediate fact. Rewrite `this` using `[← Nat.cast_pow, map_natCast, ← he]`. Conclude with `this`.

Take `⟨hfin, het, hsurj⟩` from `isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq`. Use `haveI : Surjective ψ.left := hsurj`. Use `haveI : Flat ψ.left := inferInstance`. Use `haveI : QuasiCompact ψ.left := inferInstance`. Use `haveI : IsMonHom ψ := hq.1`.

Establish `: Epi ψ` using `GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ`. Establish `: Epi (ψ ⊗ₘ ψ)` using `GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ`. Establish `hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ` using `fun a => by haveI := o.act.hom a`. Use `GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_` and prove the remaining obligations. Establish `h1 : (x₁ / x₂) ≫ ψ = 1` using `by rw [GrpObj.div_comp, h, div_self']`.

Establish `h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1` using `hst W W.hom (Category.comp_id _) _ h1 a`. Rewrite `h2` using `[GrpObj.div_comp, div_eq_one]`. Then use the resulting hypothesis. Use `choose t ht using hd`. Use `⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ }, fun a => (ht a).symm⟩` and prove the remaining obligations. Use `haveI := o.act.hom a`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]`. Rewrite using `[← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht, ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]`. Rewrite using `[← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]`. Rewrite using `[← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]`.

Rewrite using `[← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc, Category.assoc, IsMonHom.mul_hom]`.
-/
theorem exists_oAct_desc : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  obtain ⟨hfin, het, hsurj⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq
  haveI : Surjective ψ.left := hsurj
  haveI : Flat ψ.left := inferInstance
  haveI : QuasiCompact ψ.left := inferInstance
  haveI : IsMonHom ψ := hq.1
  have : Epi ψ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ
  have : Epi (ψ ⊗ₘ ψ) := GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ
  have hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ := fun a => by
    haveI := o.act.hom a
    refine GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_
    have h1 : (x₁ / x₂) ≫ ψ = 1 := by rw [GrpObj.div_comp, h, div_self']
    have h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1 := hst W W.hom (Category.comp_id _) _ h1 a
    rwa [GrpObj.div_comp, div_eq_one] at h2
  choose t ht using hd
  refine ⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ },
    fun a => (ht a).symm⟩
  · haveI := o.act.hom a
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
    · rw [← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht,
        ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]
  · rw [← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]
  · rw [← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]
  · rw [← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc,
      Category.assoc, IsMonHom.mul_hom]

end GlobalTheory.UPel.HT.ES
