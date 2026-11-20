import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Establish `hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q`. Introduce `L _ p q`. Set `p' : PrimeSpectrum L` to `p`. Set `q' : PrimeSpectrum L` to `q`. Conclude with `(PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')`.

Take `⟨W, hW, hbW, -⟩` from `exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))`. Use `haveI := hW.isOpenImmersion_fromSpec`. Establish `hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W → Set.range e ⊆ Set.range hW.fromSpec`. Introduce `Y e z hz he`. Introduce and unpack `_ ⟨z', rfl⟩`.

Rewrite using `[hW.range_fromSpec, hz z']`. Conclude with `he`. Establish `hyW` using `hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)`. Establish `hsW` using `hrange s b (fun z' => hpt K z' b) hbW`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)`.

Take `⟨σ, hσ⟩` from `Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)`. Take `⟨α, hα⟩` from `Spec.map_surjective (hW.fromSpec ≫ h)`. Establish `hσβ : α ≫ σ = CommRingCat.ofHom β` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])`. Establish `hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β)` using `Spec.map_injective (by`.

Rewrite using `[Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])`. Establish `hpts : (Spec.map ψ) a = (Spec.map σ) b`. Apply `(Scheme.Hom.isOpenEmbedding hW.fromSpec).injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a, ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, hab]`. Establish `hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0`.

Introduce `x hx`. Set `a' : PrimeSpectrum Ω` to `a`. Set `b' : PrimeSpectrum K` to `b`. Establish `ha : a'.asIdeal = ⊥` using `Ideal.eq_bot_of_prime _`. Establish `hb : b'.asIdeal = ⊥` using `Ideal.eq_bot_of_prime _`.

Establish `e` using `congrArg PrimeSpectrum.asIdeal hpts`. Establish `hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b)`. Rewrite using `[Spec.map_apply]`. Express the relevant statement in the definitionally equal form `σ.hom x ∈ b'.asIdeal`. Rewrite using `[hb, Ideal.mem_bot]`.

Conclude with `hx`. Rewrite `hmem` using `[← e, Spec.map_apply]`. Express the relevant statement in the definitionally equal form `ψ.hom x ∈ a'.asIdeal at hmem`. Rewrite `hmem` using `[ha, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hψσ : ψ = σ ≫ CommRingCat.ofHom k`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Take `⟨r, u, hu, hxu⟩` from `hβ (σ.hom x)`. Establish `hσα : ∀ z, σ.hom (α.hom z) = β z` using `fun z => by`.

Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]`. Establish `hψα : ∀ z, ψ.hom (α.hom z) = k (β z)` using `fun z => by`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Establish `h0 : ψ.hom (x * α.hom u - α.hom r) = 0` using `hker _ (by`. Rewrite using `[map_sub, map_mul, hσα, hσα, hxu, sub_self])`.

Rewrite `h0` using `[map_sub, map_mul, hψα, hψα, sub_eq_zero]`. Establish `hku : k (β u) ≠ 0` using `(map_ne_zero k).mpr hu`. Apply `mul_right_cancel₀ hku` to reduce the goal to its premises. Rewrite using `[h0, ← map_mul, hxu]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]`.
-/
private theorem eq_specMap_comp_of_apply_eq {X : Scheme.{0}} {B K Ω : Type} [CommRing B] [Field K]
    [Field Ω] (h : X ⟶ Spec (CommRingCat.of B)) (β : B →+* K)
    (hβ : ∀ x : K, ∃ r u : B, β u ≠ 0 ∧ x * β u = β r)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ h = Spec.map (CommRingCat.ofHom β))
    (k : K →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ X)
    (hy : y ≫ h = Spec.map (CommRingCat.ofHom (k.comp β)))
    (a : Spec (CommRingCat.of Ω)) (b : Spec (CommRingCat.of K)) (hab : y a = s b) :
    y = Spec.map (CommRingCat.ofHom k) ≫ s := by
  have hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q := by
    intro L _ p q
    let p' : PrimeSpectrum L := p
    let q' : PrimeSpectrum L := q
    exact (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans
      (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))
  haveI := hW.isOpenImmersion_fromSpec
  have hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W →
      Set.range e ⊆ Set.range hW.fromSpec := by
    intro Y e z hz he
    rintro _ ⟨z', rfl⟩
    rw [hW.range_fromSpec, hz z']
    exact he
  have hyW := hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)
  have hsW := hrange s b (fun z' => hpt K z' b) hbW
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)
  obtain ⟨α, hα⟩ := Spec.map_surjective (hW.fromSpec ≫ h)
  have hσβ : α ≫ σ = CommRingCat.ofHom β := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])
  have hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β) := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])
  have hpts : (Spec.map ψ) a = (Spec.map σ) b := by
    apply (Scheme.Hom.isOpenEmbedding hW.fromSpec).injective
    rw [← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a,
      ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hab]
  have hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0 := by
    intro x hx
    let a' : PrimeSpectrum Ω := a
    let b' : PrimeSpectrum K := b
    have ha : a'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hb : b'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have e := congrArg PrimeSpectrum.asIdeal hpts
    have hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b) := by
      rw [Spec.map_apply]
      change σ.hom x ∈ b'.asIdeal
      rw [hb, Ideal.mem_bot]
      exact hx
    rw [← e, Spec.map_apply] at hmem
    change ψ.hom x ∈ a'.asIdeal at hmem
    rwa [ha, Ideal.mem_bot] at hmem
  have hψσ : ψ = σ ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    ext x
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    obtain ⟨r, u, hu, hxu⟩ := hβ (σ.hom x)
    have hσα : ∀ z, σ.hom (α.hom z) = β z := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]
    have hψα : ∀ z, ψ.hom (α.hom z) = k (β z) := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom,
        RingHom.comp_apply]
    have h0 : ψ.hom (x * α.hom u - α.hom r) = 0 := hker _ (by
      rw [map_sub, map_mul, hσα, hσα, hxu, sub_self])
    rw [map_sub, map_mul, hψα, hψα, sub_eq_zero] at h0
    have hku : k (β u) ≠ 0 := (map_ne_zero k).mpr hu
    apply mul_right_cancel₀ hku
    rw [h0, ← map_mul, hxu]
  calc y = IsOpenImmersion.lift hW.fromSpec y hyW ≫ hW.fromSpec :=
        (IsOpenImmersion.lift_fac _ _ _).symm
    _ = Spec.map ψ ≫ hW.fromSpec := by rw [hψ]
    _ = Spec.map (CommRingCat.ofHom k) ≫ s := by
        rw [hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]

/- English proof (translation)
Introduce `R _ _ T _ Γ`. Consider the cases of `Γ`. Name the introduced variables `pt _ pt_onto _`. Simplify using `only`. Introduce `Ω _ k y hy`.

Set `a0 : Spec (CommRingCat.of Ω)` to `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum Ω)`. Take `⟨t, x, hx⟩` from `pt_onto (y a0) (by`. Rewrite using `[← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]`. Express the relevant statement in the definitionally equal form `Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥`. Conclude with `Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))`.

Use `⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left (Over.w (pt t)) k y hy a0 x hx.symm⟩` and prove the remaining obligations. Introduce `z`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors R) z`. Conclude with `⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩`.
-/
theorem QFGroup.exists_eq_comp_pt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left),
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) →
    ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  intro R _ _ T _ Γ
  cases Γ
  rename_i pt _ pt_onto _
  dsimp only
  intro Ω _ k y hy
  let a0 : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum Ω)
  obtain ⟨t, x, hx⟩ := pt_onto (y a0) (by
    rw [← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]
    change Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥
    exact Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))
  refine ⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left
    (Over.w (pt t)) k y hy a0 x hx.symm⟩
  intro z
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) z
  exact ⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩

end GlobalTheory.CompanionTheory.Ar.BT
