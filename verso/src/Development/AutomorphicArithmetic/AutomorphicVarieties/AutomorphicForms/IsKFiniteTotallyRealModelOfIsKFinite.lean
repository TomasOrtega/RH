import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

/- English proof (translation)
Introduce `E _ _ _ a φ hopen hfin`. Set `Kf` to `AdelicGLn.integralFiniteGL E a`. Set `V : Subgroup Kf` to `{ carrier := {v | TR.finRep E a v.1 φ = φ} one_mem' := by show TR.finRep E a 1 φ = φ`. Rewrite using `[map_one]`. Both sides reduce to the same expression.

Use the proof step `mul_mem' := fun {v w} hv hw => by`. Establish `hv' : TR.finRep E a v.1 φ = φ` using `hv`. Establish `hw' : TR.finRep E a w.1 φ = φ` using `hw`. Use `show TR.finRep E a (v.1 * w.1) φ = φ`. Rewrite using `[map_mul, Module.End.mul_apply, hw', hv']`.

Use the proof step `inv_mem' := fun {v} hv => by`. Establish `hv' : TR.finRep E a v.1 φ = φ` using `hv`. Use `show TR.finRep E a (v.1⁻¹) φ = φ`. Use `conv_lhs => rw [← hv']`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Use `rfl }`. Establish `hV : IsOpen (V : Set Kf)` using `hopen.preimage continuous_subtype_val`. Use `haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL E a)`. Use `haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV`. Unfold `IsKFinite`.

Use `Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V, ((Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)).map (TR.finRep E a q.out.1)).map (TR.Sm E a).subtype) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Set `kf : Kf` to `⟨finPart k.1, finPart_mem_integralFiniteGL k.2⟩`. Take `⟨y, hy⟩` from `(grpEq E a).surjective (archPart k.1)`. Establish `hyu : y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E)` using `(UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a y).1 (hy ▸ archPart_mem_archCompact k.2)`.

Establish `hu : Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a) = y` using `Units.ext rfl`. Take `⟨v, hv⟩` from `QuotientGroup.mk_out_eq_mul V kf`. Establish `hv2 : TR.finRep E a v.1.1 φ = φ` using `v.2`. Establish `hk : TR.infGL E a y * finGL E a kf.1 = k.1`. Rewrite using `[← infEmb_grpEq, hy, ← finEmb_eq]`.

Conclude with `infEmb_archPart_mul_finEmb_finPart k.1`. Use `Submodule.mem_iSup_of_mem (QuotientGroup.mk kf) ⟨_, ⟨_, Submodule.subset_span ⟨⟨y.val, hyu⟩, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Use function extensionality and compare the values at `g`. Use `show φ.1 (g * finGL E a (kf.1 * v.1.1) * TR.infGL E a (Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a))) = φ.1 (g * k.1)`.

Establish `h3 : φ.1 (g * k.1 * finGL E a v.1.1) = φ.1 (g * k.1)` using `congrFun (congrArg Subtype.val hv2) (g * k.1)`. Rewrite using `[hu, ← h3, ← hk, mul_assoc g, ← TR.infGL_comm, map_mul]`. Simplify using `only [mul_assoc]`.
-/
theorem UpperTheory.isKFinite_totallyRealModel_of_isKFinite :
    UpperTheory.V.Fb.KFinTo := by
  intro E _ _ _ a φ hopen hfin
  let Kf := AdelicGLn.integralFiniteGL E a
  let V : Subgroup Kf :=
    { carrier := {v | TR.finRep E a v.1 φ = φ}
      one_mem' := by
        show TR.finRep E a 1 φ = φ
        rw [map_one]; rfl
      mul_mem' := fun {v w} hv hw => by
        have hv' : TR.finRep E a v.1 φ = φ := hv
        have hw' : TR.finRep E a w.1 φ = φ := hw
        show TR.finRep E a (v.1 * w.1) φ = φ
        rw [map_mul, Module.End.mul_apply, hw', hv']
      inv_mem' := fun {v} hv => by
        have hv' : TR.finRep E a v.1 φ = φ := hv
        show TR.finRep E a (v.1⁻¹) φ = φ
        conv_lhs => rw [← hv']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hV : IsOpen (V : Set Kf) := hopen.preimage continuous_subtype_val
  haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL E a)
  haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  unfold IsKFinite
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V,
    ((Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)).map (TR.finRep E a q.out.1)).map
      (TR.Sm E a).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  let kf : Kf := ⟨finPart k.1, finPart_mem_integralFiniteGL k.2⟩
  obtain ⟨y, hy⟩ := (grpEq E a).surjective (archPart k.1)
  have hyu : y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E) :=
    (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a y).1 (hy ▸ archPart_mem_archCompact k.2)
  have hu : Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a) = y := Units.ext rfl
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
  have hv2 : TR.finRep E a v.1.1 φ = φ := v.2
  have hk : TR.infGL E a y * finGL E a kf.1 = k.1 := by
    rw [← infEmb_grpEq, hy, ← finEmb_eq]
    exact infEmb_archPart_mul_finEmb_finPart k.1
  refine Submodule.mem_iSup_of_mem (QuotientGroup.mk kf)
    ⟨_, ⟨_, Submodule.subset_span ⟨⟨y.val, hyu⟩, rfl⟩, rfl⟩, ?_⟩
  rw [hv]
  funext g
  show φ.1 (g * finGL E a (kf.1 * v.1.1) * TR.infGL E a (Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a))) = φ.1 (g * k.1)
  have h3 : φ.1 (g * k.1 * finGL E a v.1.1) = φ.1 (g * k.1) := congrFun (congrArg Subtype.val hv2) (g * k.1)
  rw [hu, ← h3, ← hk, mul_assoc g, ← TR.infGL_comm, map_mul]
  simp only [mul_assoc]
