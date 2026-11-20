import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU Filter Topology
open GlobalTheory.LocalGlobalChar (eps ev_ind tendsto_eps_tens)

section KFinite

variable {G : Type} [Group G] {K : Subgroup G}

/- English proof (translation)
Take `⟨W, hf, hW⟩` from `isKFinite_iff.1 h`. Take `⟨W', hf', hW'⟩` from `isKFinite_iff.1 h'`. Conclude with `isKFinite_iff.2 ⟨W * W', Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hf).mul (Module.Finite.iff_fg.1 hf')), fun k hk => Submodule.mul_mem_mul (hW k hk) (hW' k hk)⟩`.
-/
theorem IsKFinite.mul {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K fun g => Φ g * Ψ g := by
  obtain ⟨W, hf, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', hf', hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W * W', Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hf).mul (Module.Finite.iff_fg.1 hf')),
    fun k hk => Submodule.mul_mem_mul (hW k hk) (hW' k hk)⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact .of_invariant fun _ _ _ => rfl`. Consider the case `insert i S hi ih`. Simplify using `only [Finset.prod_insert hi]`. Conclude with `(h i (Finset.mem_insert_self i S)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem IsKFinite.prod {ι : Type} (S : Finset ι) {Φ : ι → G → ℂ} (h : ∀ i ∈ S, IsKFinite K (Φ i)) :
    IsKFinite K fun g => ∏ i ∈ S, Φ i g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact .of_invariant fun _ _ _ => rfl
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i S)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end KFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ideles

def cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) : (AF F ⊗[F] E)ˣ :=
  (∏ w, ideleAtInf F E w (unitInf F E w x)) * ∏ v ∈ S, ideleAt F E v (unitFin F E v x)

omit [NumberField E] in
/- English proof (translation)
Simplify using `only [cutIdele, map_inv, Finset.prod_inv_distrib, mul_inv]`.
-/
theorem cutIdele_inv (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    cutIdele S x⁻¹ = (cutIdele S x)⁻¹ := by
  simp only [cutIdele, map_inv, Finset.prod_inv_distrib, mul_inv]

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[cutIdele, map_mul, map_prod, map_prod, Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem unitInf_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) (w : InfinitePlace F) :
    unitInf F E w (cutIdele S x) = unitInf F E w x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]
  simp

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[cutIdele, map_mul, map_prod, map_prod, Finset.prod_eq_single v (fun u _ hu => unitFin_ideleAt_ne hu.symm _) (fun h => absurd hv h)]`. Simplify using the standard rewrite rules.
-/
theorem unitFin_cutIdele_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : unitFin F E v (cutIdele S x) = unitFin F E v x := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_single v (fun u _ hu => unitFin_ideleAt_ne hu.symm _) (fun h => absurd hv h)]
  simp

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[cutIdele, map_mul, map_prod, map_prod, Finset.prod_eq_one (s := S) (fun u hu => unitFin_ideleAt_ne (ne_of_mem_of_not_mem hu hv).symm _)]`. Simplify using the standard rewrite rules.
-/
theorem unitFin_cutIdele_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AF F ⊗[F] E)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : unitFin F E v (cutIdele S x) = 1 := by
  rw [cutIdele, map_mul, map_prod, map_prod,
    Finset.prod_eq_one (s := S) (fun u hu => unitFin_ideleAt_ne (ne_of_mem_of_not_mem hu hv).symm _)]
  simp

/- English proof (translation)
Use `adele_ext (fun w => ?_) fun v => ?_` and prove the remaining obligations. Establish `h : compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) = 1` using `rfl`. Rewrite using `[map_add, map_mul, map_sub, h, map_one, one_mul, sub_add_cancel]`. Conclude with `congrArg Units.val (unitInf_cutIdele S x w)`. Establish `h : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.LocalGlobalChar.ind S) ⊗ₜ[F] (1 : E)` using `rfl`.

Rewrite using `[map_add, map_mul, map_sub, h, map_one, ev_ind]`. Use `split_ifs with hv`. Rewrite using `[← Algebra.TensorProduct.one_def, one_mul, sub_add_cancel]`. Conclude with `congrArg Units.val (unitFin_cutIdele_of_mem x hv)`. Rewrite using `[TensorProduct.zero_tmul, zero_mul, zero_add]`.

Conclude with `congrArg Units.val (unitFin_cutIdele_of_notMem x hv)`.
-/
theorem val_cutIdele (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AF F ⊗[F] E)ˣ) :
    (cutIdele S x).1 = algebraMap (AF F) (AF F ⊗[F] E) (eps S) * (x.1 - 1) + 1 := by
  refine adele_ext (fun w => ?_) fun v => ?_
  · have h : compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) = 1 := rfl
    rw [map_add, map_mul, map_sub, h, map_one, one_mul, sub_add_cancel]
    exact congrArg Units.val (unitInf_cutIdele S x w)
  · have h : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eps S)) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.LocalGlobalChar.ind S) ⊗ₜ[F] (1 : E) := rfl
    rw [map_add, map_mul, map_sub, h, map_one, ev_ind]
    split_ifs with hv
    · rw [← Algebra.TensorProduct.one_def, one_mul, sub_add_cancel]
      exact congrArg Units.val (unitFin_cutIdele_of_mem x hv)
    · rw [TensorProduct.zero_tmul, zero_mul, zero_add]
      exact congrArg Units.val (unitFin_cutIdele_of_notMem x hv)

/- English proof (translation)
Use `isTopologicalRing_tens (F := F) (E := E) (R := AF F)` as an intermediate fact. Establish `h : ∀ y : (AF F ⊗[F] E)ˣ, Tendsto (fun S => (cutIdele S y).1) atTop (𝓝 y.1)` using `fun y => by`. Use `(tendsto_eps_tens (y.1 - 1)).add_const 1` as an intermediate fact. Rewrite `this` using `[show y.1 - 1 + 1 = y.1 by ring]`. Simplify `this` using `only [val_cutIdele]`.

Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `(h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)` and prove the remaining obligations. Simplify `h x⁻¹` using `only [cutIdele_inv]`.
-/
theorem tendsto_cutIdele (x : (AF F ⊗[F] E)ˣ) : Tendsto (fun S => cutIdele S x) atTop (𝓝 x) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : ∀ y : (AF F ⊗[F] E)ˣ, Tendsto (fun S => (cutIdele S y).1) atTop (𝓝 y.1) := fun y => by
    have := (tendsto_eps_tens (y.1 - 1)).add_const 1
    rw [show y.1 - 1 + 1 = y.1 by ring] at this
    simpa only [val_cutIdele] using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  simpa only [cutIdele_inv] using h x⁻¹

end Ideles

variable {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)} {μ : (AF F ⊗[F] E)ˣ →* Circle} {s : ℂ}
  {Φi : ∀ w, GArch σ Q w → ℂ} {Φf : ∀ v, GLoc σ Q v → ℂ}

end GlobalTheory.Doubling

end
