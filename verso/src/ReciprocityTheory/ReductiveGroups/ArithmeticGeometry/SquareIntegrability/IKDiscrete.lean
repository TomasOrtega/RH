import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

def IK {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℤ (IR I) :=
  I.comap ((IR I).subtype.toAddMonoidHom.toIntLinearMap)

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_IK {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x : IR I} :
    x ∈ IK I ↔ (x : Vsp dim) ∈ I := Iff.rfl

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem IK_discrete (hI : IsSplit P I) : DiscreteTopology (IK I) := by
  let f : IK I → X.L := fun x => ⟨((x : IR I) : Vsp X.dim), hI.le (mem_IK.1 x.2)⟩
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  exact DiscreteTopology.of_continuous_injective hc hinj

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem IK_span : Submodule.span ℝ (IK I : Set (IR I)) = ⊤ := by
  apply Submodule.map_injective_of_injective (IR I).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  show _ = Submodule.span ℝ (I : Set (Vsp X.dim))
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_IK.1 hz
  · intro hy
    exact ⟨⟨y, Submodule.subset_span hy⟩, mem_IK.2 hy, rfl⟩

/- English proof (translation)
Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem IK_lattice (hI : IsSplit P I) : ∃ (_ : DiscreteTopology (IK I)) (_ : IsZLattice ℝ (IK I)),
    Module.finrank ℤ (IK I) = Module.finrank ℝ (IR I) := by
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  exact ⟨inferInstance, inferInstance, ZLattice.rank ℝ (IK I)⟩

def Ib (hI : IsSplit P I) : Module.Basis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I) :=
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  (Module.Basis.ofZLatticeBasis ℝ (IK I) (Module.Free.chooseBasis ℤ (IK I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem Ib_span (hI : IsSplit P I) : Submodule.span ℤ (Set.range (Ib hI)) = IK I := by
  unfold Ib
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Ib_mem (hI : IsSplit P I) (i : Fin (Module.finrank ℝ (IR I))) :
    ((Ib hI i : IR I) : Vsp X.dim) ∈ I := by
  have h : Ib hI i ∈ IK I := by
    rw [← Ib_span hI]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact mem_IK.1 h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Ib_det_ne (hI : IsSplit P I) : (Col.ob (IR I)).toBasis.det (Ib hI) ≠ 0 := ((Module.Basis.is_basis_iff_det _).1 ⟨(Ib hI).linearIndependent, (Ib hI).span_eq⟩).ne_zero

def zmG (I : Submodule ℤ (Vsp X.dim)) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) : ℂ :=
  s (fun _ => v) * Complex.exp (-(Real.pi / 2) * Col.S (IR I) v)

def zmBox (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

def zmC (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (v : Vsp X.dim) : ℂ :=
  ∫ t in zmBox (Module.finrank ℝ (IR I)),
    Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) *
      zmG I s (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim))

def zmB (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ :=
  fun t => zmC hI s 0 (Col.jj (IR I) t)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
