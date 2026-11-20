import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfDelta

noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def nu : P.ResidueField ⊗[B] Ω[B⁄A] →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A] :=
  LinearMap.baseChange P.ResidueField ((KaehlerDifferential.map A A B (B ⧸ I)).restrictScalars B)

/- English proof (translation)
Apply `LinearMap.lTensor_surjective` to reduce the goal to its premises. Conclude with `KaehlerDifferential.map_surjective_of_surjective A A B (B ⧸ I) Ideal.Quotient.mk_surjective`.
-/
theorem nu_surjective : Function.Surjective (nu (A := A) I P) := by
  apply LinearMap.lTensor_surjective
  exact KaehlerDifferential.map_surjective_of_surjective A A B (B ⧸ I) Ideal.Quotient.mk_surjective

/- English proof (translation)
Simplify using `[nu]`.
-/
theorem nu_D (x : B) : nu (A := A) I P ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B x) =
    (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A (B ⧸ I) (Ideal.Quotient.mk I x) := by
  simp [nu]

def LeafResDimQ : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    e ≤ Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A])

/- English proof (translation)
Introduce `d e A B _ _ _ I hB hBI P _ hIP`. Establish `: Nontrivial B` using `⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (Ideal.eq_top_of_isUnit_mem P (zero_mem P) (by rw [h]; exact isUnit_one))⟩`. Use `hB.isStandardSmooth` as an intermediate fact. Establish `: Module.Free B Ω[B⁄A]` using `inferInstance`. Establish `hr` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B) (e + d)`.

Establish `hf : Module.finrank B Ω[B⁄A] = e + d` using `Module.finrank_eq_of_rank_eq hr`. Establish `: Module.Finite B Ω[B⁄A]` using `inferInstance`. Establish `hV : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄A]) = e + d`. Rewrite using `[Module.finrank_baseChange, hf]`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker (nu (A := A) I P)`.

Rewrite `hrn` using `[LinearMap.range_eq_top.mpr (nu_surjective (A := A) I P), finrank_top, hV]`. Establish `hq` using `hQ d e A B I hB hBI P hIP`. Establish `hS : Submodule.span P.ResidueField (Set.range fun x : I => (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) ≤ LinearMap.ker (nu (A` using `A) I P) := by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Simplify using `[nu_D, Ideal.Quotient.eq_zero_iff_mem.mpr x.2]`. Conclude with `⟨inferInstance, (Submodule.finrank_mono hS).trans (by omega)⟩`.
-/
theorem LeafResSpanD_of (hQ : LeafResDimQ) : LeafResSpanD := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have : Nontrivial B := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (Ideal.eq_top_of_isUnit_mem P (zero_mem P)
    (by rw [h]; exact isUnit_one))⟩
  have := hB.isStandardSmooth
  have : Module.Free B Ω[B⁄A] := inferInstance
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B) (e + d)
  have hf : Module.finrank B Ω[B⁄A] = e + d := Module.finrank_eq_of_rank_eq hr
  have : Module.Finite B Ω[B⁄A] := inferInstance
  have hV : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄A]) = e + d := by
    rw [Module.finrank_baseChange, hf]
  have hrn := LinearMap.finrank_range_add_finrank_ker (nu (A := A) I P)
  rw [LinearMap.range_eq_top.mpr (nu_surjective (A := A) I P), finrank_top, hV] at hrn
  have hq := hQ d e A B I hB hBI P hIP
  have hS : Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) ≤ LinearMap.ker (nu (A := A) I P) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    simp [nu_D, Ideal.Quotient.eq_zero_iff_mem.mpr x.2]
  exact ⟨inferInstance, (Submodule.finrank_mono hS).trans (by omega)⟩

end LateralTheory.E.LeafCoordsPointResPf
