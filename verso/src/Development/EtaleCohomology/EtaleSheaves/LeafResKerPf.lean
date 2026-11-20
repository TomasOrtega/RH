import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfY

noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

/- English proof (translation)
Introduce `d e A B _ _ _ I _ _ P _ hIP`. Use `set K := P.ResidueField`. Use `set C := B ⧸ I`. Use `set S : Submodule K (K ⊗[B] Ω[B⁄A]) := Submodule.span K (Set.range fun x : I => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))`. Set `g : Ω[B⁄A] →ₗ[B] Ω[C⁄A]` to `(KaehlerDifferential.map A A B C).restrictScalars B`.

Establish `hI : ∀ a ∈ I, (Algebra.ofId B K) a = 0` using `fun a ha => by`. Simplify using `only [Algebra.ofId_apply]`. Conclude with `(Ideal.algebraMap_residueField_eq_zero).mpr (hIP ha)`. Set `φ : C →ₗ[B] K` to `(Ideal.Quotient.liftₐ I (Algebra.ofId B K) hI).toLinearMap`. Establish `hφ1 : φ 1 = 1` using `by simp [φ]`.

Establish `h2 : ∀ ω : Ω[B⁄A], g ω = 0 → (1 : K) ⊗ₜ[B] ω ∈ S`. Introduce `ω hω`. Establish `hm : KaehlerDifferential.mapBaseChange A B C ((1 : C) ⊗ₜ[B] ω) = 0`. Rewrite using `[KaehlerDifferential.mapBaseChange_tmul, one_smul]`. Conclude with `hω`.

Take `⟨y, hy⟩` from `(KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A B C Ideal.Quotient.mk_surjective ((1 : C) ⊗ₜ[B] ω)).mp hm`. Take `⟨x, rfl⟩` from `Ideal.toCotangent_surjective _ y`. Rewrite `hy` using `[KaehlerDifferential.kerCotangentToTensor_toCotangent]`. Establish `hx : (x : B) ∈ I`. Use `x.2` as an intermediate fact.

Rewrite `this` using `[RingHom.mem_ker]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`. Use `congrArg (LinearMap.rTensor (Ω[B⁄A]) φ) hy` as an intermediate fact. Simplify using `only [LinearMap.rTensor_tmul, hφ1] at this`. Rewrite using `[← this]`.

Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`. Establish `hex` using `lTensor_exact K (LinearMap.exact_subtype_ker_map g) (KaehlerDifferential.map_surjective_of_surjective A A B C Ideal.Quotient.mk_surjective)`. Introduce `z hz`. Rewrite `hz` using `[LinearMap.mem_ker]`. Establish `hz' : LinearMap.lTensor K g z = 0`.

Rewrite using `[← hz, nu]`. Both sides reduce to the same expression. Take `⟨w, rfl⟩` from `(hex z).mp hz'`. Use `clear hz hz'`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul k n`. Rewrite using `[LinearMap.lTensor_tmul]`. Establish `: k ⊗ₜ[B] ((LinearMap.ker g).subtype n) = k • ((1 : K) ⊗ₜ[B] (n : Ω[B⁄A]))`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `S.smul_mem k (h2 n n.2)`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `S.add_mem ha hb`.
-/
theorem LeafResKer_of : LeafResKer := by
  intro d e A B _ _ _ I _ _ P _ hIP
  set K := P.ResidueField
  set C := B ⧸ I
  set S : Submodule K (K ⊗[B] Ω[B⁄A]) := Submodule.span K (Set.range fun x : I =>
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))
  let g : Ω[B⁄A] →ₗ[B] Ω[C⁄A] := (KaehlerDifferential.map A A B C).restrictScalars B
  have hI : ∀ a ∈ I, (Algebra.ofId B K) a = 0 := fun a ha => by
    simp only [Algebra.ofId_apply]
    exact (Ideal.algebraMap_residueField_eq_zero).mpr (hIP ha)
  let φ : C →ₗ[B] K := (Ideal.Quotient.liftₐ I (Algebra.ofId B K) hI).toLinearMap
  have hφ1 : φ 1 = 1 := by simp [φ]

  have h2 : ∀ ω : Ω[B⁄A], g ω = 0 → (1 : K) ⊗ₜ[B] ω ∈ S := by
    intro ω hω
    have hm : KaehlerDifferential.mapBaseChange A B C ((1 : C) ⊗ₜ[B] ω) = 0 := by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]; exact hω
    obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A B C
      Ideal.Quotient.mk_surjective ((1 : C) ⊗ₜ[B] ω)).mp hm
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
    have hx : (x : B) ∈ I := by
      have := x.2; rw [RingHom.mem_ker] at this; exact Ideal.Quotient.eq_zero_iff_mem.mp this
    have := congrArg (LinearMap.rTensor (Ω[B⁄A]) φ) hy
    simp only [LinearMap.rTensor_tmul, hφ1] at this
    rw [← this]
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  have hex := lTensor_exact K (LinearMap.exact_subtype_ker_map g)
    (KaehlerDifferential.map_surjective_of_surjective A A B C Ideal.Quotient.mk_surjective)
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hz' : LinearMap.lTensor K g z = 0 := by
    rw [← hz, nu]; rfl
  obtain ⟨w, rfl⟩ := (hex z).mp hz'
  clear hz hz'
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul k n =>
    rw [LinearMap.lTensor_tmul]
    have : k ⊗ₜ[B] ((LinearMap.ker g).subtype n) = k • ((1 : K) ⊗ₜ[B] (n : Ω[B⁄A])) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [this]
    exact S.smul_mem k (h2 n n.2)
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb

end LateralTheory.E.LeafCoordsPointResPf
