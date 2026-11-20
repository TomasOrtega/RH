import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `E _ _ _ a C hC hneat`. Use `set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef`. Establish `hDC : D ≤ C.comap GlobalTheory.EllU.finPart` using `sup_le (fun c hc => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart c ∈ C`. Rewrite using `[GlobalTheory.EllU.finPart_of_finU (hC hc)]`.

Conclude with `hc)`. Use the proof step `(fun x hx => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart x ∈ C`. Rewrite using `[GlobalTheory.EllU.finPart_of_infU hx]`. Conclude with `C.one_mem)`.

Set `f : D →* C` to `(GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)`. Establish `hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1`. Introduce `g γ hγ d h`. Establish `hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C` using `hDC d.2`. Establish `e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a))`.

Rewrite using `[h]`. Use `group`. Establish `h1` using `hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e`. Conclude with `Subtype.ext h1`. Take `⟨ℓ, h1, h2⟩` from `UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp`.

Establish `hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g`. Introduce `x hx g`. Establish `e : f ⟨x, le_sup_right (a` using `C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)`. Use `h2 g ⟨x, le_sup_right (a := C) hx⟩` as an intermediate fact. Simplify using `only [e, mul_one] at this`.

Conclude with `this`. Establish `hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c`. Introduce `c g`. Establish `e : f ⟨c, le_sup_left (b` using `infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))`. Use `h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩` as an intermediate fact.

Simplify using `only [e] at this`. Conclude with `this`. Conclude with `⟨ℓ, ⟨h1, hC', hinf⟩⟩`.
-/
theorem UpperTheory.Gal.Wt.ellC_of :
    UpperTheory.Gal.Wt.EllC := by
  intro E _ _ _ a C hC hneat
  set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  have hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1 := by
    intro g γ hγ d h
    have hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C := hDC d.2
    have e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a)) := by
      rw [h]; group
    have h1 := hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e
    exact Subtype.ext h1
  obtain ⟨ℓ, h1, h2⟩ := UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp
  have hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g := by
    intro x hx g
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [e, mul_one] at this
    exact this
  have hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c := by
    intro c g
    have e : f ⟨c, le_sup_left (b := infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩
    simp only [e] at this
    exact this
  exact ⟨ℓ, ⟨h1, hC', hinf⟩⟩
