import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

/- English proof (translation)
Use `open Pointwise in`. Rewrite using `[ReciprocityTheory.Gal.mem_Dec]`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `key` using `h (s⁻¹ • x)`.

Establish `e : s (s⁻¹ • x) = x` using `ReciprocityTheory.Gal.mul_inv_apply x`. Rewrite `key` using `[e]`. Conclude with `key.symm`.
-/
private theorem mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {s : G F Ω}
    (h : ∀ x, s x ∈ A ↔ x ∈ A) : s ∈ Dec (F := F) A := by
  open Pointwise in
  rw [ReciprocityTheory.Gal.mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key := h (s⁻¹ • x)
  have e : s (s⁻¹ • x) = x := ReciprocityTheory.Gal.mul_inv_apply x
  rw [e] at key
  exact key.symm

end UpperTheory.V.Keep

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T hD ho r h w hw A hA`. Establish `hl : A.valuation (l : Ω) < 1`. Establish `h'` using `(hA ((l : ℕ) : 𝓞 T.L)).2 hw`. Simplify using `using h'`. Take `⟨κ, hκ, hne⟩` from `h A hl`.

Set `ρ : ↥(Dec (F` to `T.L) A) →* ↥(Dec (F := T.F) A) := ((resLe T.F_le).comp (Dec (F := T.L) A).subtype).codRestrict _ fun s => UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x`. Establish `hρ : Function.Surjective ρ`. Introduce `s`. Establish `hd : resQ T.F s.1 ∈ Dec (F` using `ℚ) A := UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x`. Establish `hK : resQ T.F s.1 ∈ T.K.fixingSubgroup` using `ho.split l hD.l_mem A hl hd`.

Establish `hF : resQ T.F s.1 ∈ T.F.fixingSubgroup` using `fun x => s.1.commutes x`. Establish `hLf : resQ T.F s.1 ∈ T.L.fixingSubgroup`. Rewrite using `[T.hL, IntermediateField.fixingSubgroup_sup]`. Conclude with `⟨hF, hK⟩`. Set `t : G T.L Ω` to `AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) fun x => hLf x`.

Use `⟨⟨t, UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩` and prove the remaining obligations. Use `⟨fun i => (κ i).comp ρ, ?_, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hκ.flag`. Conclude with `⟨g, fun s => hg (ρ s)⟩`. Take `⟨t, rfl⟩` from `hρ s`.

Conclude with `DFunLike.congr_fun e t`.
-/
theorem UpperTheory.V.Keep.unlL :
    UpperTheory.V.Keep.UnlL := by
  intro Ω _ _ _ l _ c D T hD ho r h w hw A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have h' := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    simpa using h'
  obtain ⟨κ, hκ, hne⟩ := h A hl
  let ρ : ↥(Dec (F := T.L) A) →* ↥(Dec (F := T.F) A) :=
    ((resLe T.F_le).comp (Dec (F := T.L) A).subtype).codRestrict _ fun s =>
      UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
  have hρ : Function.Surjective ρ := by
    intro s
    have hd : resQ T.F s.1 ∈ Dec (F := ℚ) A := UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
    have hK : resQ T.F s.1 ∈ T.K.fixingSubgroup := ho.split l hD.l_mem A hl hd
    have hF : resQ T.F s.1 ∈ T.F.fixingSubgroup := fun x => s.1.commutes x
    have hLf : resQ T.F s.1 ∈ T.L.fixingSubgroup := by
      rw [T.hL, IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, hK⟩
    let t : G T.L Ω := AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) fun x => hLf x
    refine ⟨⟨t, UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩
  refine ⟨fun i => (κ i).comp ρ, ?_, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩
  · obtain ⟨g, hg⟩ := hκ.flag
    exact ⟨g, fun s => hg (ρ s)⟩
  · obtain ⟨t, rfl⟩ := hρ s
    exact DFunLike.congr_fun e t
