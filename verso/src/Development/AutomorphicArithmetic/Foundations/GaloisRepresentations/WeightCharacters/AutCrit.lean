import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `E _ _ _ a C hLev φ hL hC hI S hS hSub`. Take `⟨N, hNo, hN1, hNC⟩` from `hLev.isOpen`. Use `set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn`. Establish `hWo : IsOpen Wn` using `hNo.preimage GlobalTheory.EllU.continuous_finPart`. Establish `hW1 : (1 : UA E a) ∈ Wn`.

Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart 1 ∈ N`. Rewrite using `[map_one]`. Conclude with `hN1`. Establish `hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w))`. Introduce `g w hw`.

Establish `hkC : GlobalTheory.EllU.finPart w ∈ C` using `hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩`. Establish `hx` using `GlobalTheory.EllU.inv_finPart_mul_mem w`. Establish `hcm` using `GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx`. Establish `e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w`. Rewrite using `[mul_assoc, ← hcm]`.

Use `group`. Rewrite using `[e, hC _ hkC]`. Use `⟨?_, hL, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Establish `hc : Continuous fun y : UA E a => g⁻¹ * y` using `continuous_const.mul continuous_id`.

Establish `hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y), GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a)` using `Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _`. Establish `h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g` using `((hI g).comp hX).continuousAt`. Use `h0.congr ?_` and prove the remaining obligations. Establish `hm : Wn ∈ nhds (g⁻¹ * g)`. Rewrite using `[inv_mul_cancel]`.

Conclude with `hWo.mem_nhds hW1`. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy`. Use `hkey g _ hy` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.

Use `GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) _ ?_` and prove the remaining obligations. Establish `ho : IsOpen ((Subtype.val : finU E a → UA E a) ⁻¹' Wn)` using `hWo.preimage continuous_subtype_val`. Use `Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_` and prove the remaining obligations. Establish `hk' : (k : UA E a) ∈ C`. Use `hNC ⟨?_, k.2⟩` and prove the remaining obligations.

Establish `: GlobalTheory.EllU.finPart (k : UA E a) ∈ N` using `hk`. Rewrite `this` using `[GlobalTheory.EllU.finPart_of_finU k.2]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `g`. Conclude with `hC _ hk' g`. Use `haveI := hS`.

Use `Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hSub k k.2`.
-/
theorem UpperTheory.Gal.Wt.autCrit_of :
    UpperTheory.Gal.Wt.AutCrit := by
  intro E _ _ _ a C hLev φ hL hC hI S hS hSub
  obtain ⟨N, hNo, hN1, hNC⟩ := hLev.isOpen
  set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn
  have hWo : IsOpen Wn := hNo.preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E a) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ N
    rw [map_one]; exact hN1
  have hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w)) := by
    intro g w hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩
    have hx := GlobalTheory.EllU.inv_finPart_mul_mem w
    have hcm := GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx
    have e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w := by
      rw [mul_assoc, ← hcm]; group
    rw [e, hC _ hkC]
  refine ⟨?_, hL, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    have hc : Continuous fun y : UA E a => g⁻¹ * y := continuous_const.mul continuous_id
    have hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y),
        GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a) :=
      Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _
    have h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g :=
      ((hI g).comp hX).continuousAt
    refine h0.congr ?_
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    have := hkey g _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) _ ?_
    have ho : IsOpen ((Subtype.val : finU E a → UA E a) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    have hk' : (k : UA E a) ∈ C := by
      refine hNC ⟨?_, k.2⟩
      have : GlobalTheory.EllU.finPart (k : UA E a) ∈ N := hk
      rwa [GlobalTheory.EllU.finPart_of_finU k.2] at this
    funext g
    exact hC _ hk' g
  · haveI := hS
    refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hSub k k.2
