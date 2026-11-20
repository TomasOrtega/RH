import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicLimit

section Basis

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `[Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]`.

Consider the case `add x y hx hy`. Simplify using `only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R'] (α : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis R' (Module.finBasis F E)).repr (Algebra.TensorProduct.map α (AlgHom.id F E) z) k =
      α ((Algebra.TensorProduct.basis R (Module.finBasis F E)).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

end Basis

section Fin

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 F))` to `{v | y v ∈ v.adicCompletionIntegers F ∧ g v ∈ v.adicCompletionIntegers F}`. Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `y.2.and g.2`. Set `P` to `RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)`.

Set `f' : Finset (HeightOneSpectrum (𝓞 F)) → P` to `fun T => ⟨fun v => f T v, by`. Rewrite using `[Filter.eventually_principal]`. Introduce `w hw`. Use `show f T w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))`. Distinguish the cases in `h : w ∈ T`.

Rewrite using `[hin T w h]`. Conclude with `hw.1`. Rewrite using `[hout T w h]`. Conclude with `hw.2⟩`. Set `y' : P` to `⟨fun v => y v, by rw [Filter.eventually_principal]; exact fun w hw => hw.1⟩`.

Establish `hf : Tendsto f' atTop (𝓝 y')`. Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]`. Introduce `v`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT`.

Establish `: v ∈ T` using `hT (Finset.mem_singleton_self v)`. Express the relevant statement in the definitionally equal form `y v = f T v`. Rewrite using `[hin T v this]`. Conclude with `((RestrictedProduct.continuous_inclusion hle).tendsto y').comp hf`.
-/
theorem tendsto_finAdele (f : Finset (HeightOneSpectrum (𝓞 F)) → FiniteAdeleRing (𝓞 F) F)
    (y g : FiniteAdeleRing (𝓞 F) F) (hin : ∀ T, ∀ v ∈ T, f T v = y v) (hout : ∀ T, ∀ v, v ∉ T → f T v = g v) :
    Tendsto f atTop (𝓝 y) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | y v ∈ v.adicCompletionIntegers F ∧ g v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact y.2.and g.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f' : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => f T v, by
    rw [Filter.eventually_principal]
    intro w hw
    show f T w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))
    by_cases h : w ∈ T
    · rw [hin T w h]; exact hw.1
    · rw [hout T w h]; exact hw.2⟩
  let y' : P := ⟨fun v => y v, by rw [Filter.eventually_principal]; exact fun w hw => hw.1⟩
  have hf : Tendsto f' atTop (𝓝 y') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change y v = f T v
    rw [hin T v this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto y').comp hf

end Fin

section Entry

variable {D : D7}

set_option maxHeartbeats 800000 in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) k = _`. Rewrite using `[repr_map]`.
-/
theorem repr_infPart (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (infPart D z) k =
      fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k) := by
  change (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) k = _
  rw [repr_map]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z)) k = _`. Rewrite using `[repr_map, repr_map]`.
-/
theorem repr_compAt (w : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (compAt D w z) k =
      evalV D.host.F w (sndA D.host.F
        ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k)) := by
  change (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z)) k = _
  rw [repr_map, repr_map]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Use `set Bs := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E) with hBs`. Establish `hc : ∀ k, Tendsto (fun T => Bs.repr (a T) k) atTop (𝓝 (Bs.repr b k))`. Introduce `k`. Establish `h1 : ∀ T, (Bs.repr (a T) k).1 = (Bs.repr b k).1` using `fun T => by`.

Establish `h` using `congrArg (fun z => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k) (hinf T)`. Simplify using `only [repr_infPart] at h`. Conclude with `h`. Establish `h2 : Tendsto (fun T => (Bs.repr (a T) k).2) atTop (𝓝 (Bs.repr b k).2)`. Use `tendsto_finAdele _ _ (Bs.repr c k).2 (fun T w hw => ?_) (fun T w hw => ?_)` and prove the remaining obligations.

Establish `h` using `congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr z k) (hin T w hw)`. Simplify using `only [repr_compAt] at h`. Conclude with `h`. Establish `h` using `congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr z k) (hout T w hw)`. Simplify using `only [repr_compAt] at h`.

Conclude with `h`. Establish `h3` using `(tendsto_const_nhds (x := (Bs.repr b k).1)).prodMk_nhds h2`. Use `h3.congr fun T => ?_` and prove the remaining obligations. Conclude with `Prod.ext (h1 T).symm rfl`. Use `tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank D.host.F D.host.E))) (fun k _ => (hc k).smul_const (Bs k))` as an intermediate fact.

Simplify `this` using `only [Bs.sum_repr]`.
-/
theorem tendsto_entry (a : Finset (Pl D) → AE D) (b c : AE D) (hinf : ∀ T, infPart D (a T) = infPart D b)
    (hin : ∀ T, ∀ w ∈ T, compAt D w (a T) = compAt D w b)
    (hout : ∀ T w, w ∉ T → compAt D w (a T) = compAt D w c) : Tendsto a atTop (𝓝 b) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  set Bs := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E) with hBs
  have hc : ∀ k, Tendsto (fun T => Bs.repr (a T) k) atTop (𝓝 (Bs.repr b k)) := by
    intro k
    have h1 : ∀ T, (Bs.repr (a T) k).1 = (Bs.repr b k).1 := fun T => by
      have h := congrArg (fun z => (Algebra.TensorProduct.basis (Ainf D.host.F)
        (Module.finBasis D.host.F D.host.E)).repr z k) (hinf T)
      simp only [repr_infPart] at h
      exact h
    have h2 : Tendsto (fun T => (Bs.repr (a T) k).2) atTop (𝓝 (Bs.repr b k).2) := by
      refine tendsto_finAdele _ _ (Bs.repr c k).2 (fun T w hw => ?_) (fun T w hw => ?_)
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hin T w hw)
        simp only [repr_compAt] at h
        exact h
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hout T w hw)
        simp only [repr_compAt] at h
        exact h
    have h3 := (tendsto_const_nhds (x := (Bs.repr b k).1)).prodMk_nhds h2
    refine h3.congr fun T => ?_
    exact Prod.ext (h1 T).symm rfl
  have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank D.host.F D.host.E)))
    (fun k _ => (hc k).smul_const (Bs k))
  simpa only [Bs.sum_repr] using this

/- English proof (translation)
Establish `hM : φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = φ.mapMatrix (v : Matrix (Fin n) (Fin n) A)` using `Matrix.ext fun i j => h i j`. Establish `e1 : φ.mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `e2 : φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) * φ.mapMatrix ((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Rewrite `e2` using `[← hM]`. Establish `e` using `left_inv_eq_right_inv e1 e2`. Introduce `i j`. Conclude with `congrArg (fun M => M i j) e`.
-/
theorem map_inv_entries {A R : Type} [CommRing A] [Ring R] {n : ℕ} (φ : A →+* R) (u v : GL (Fin n) A)
    (h : ∀ i j, φ ((u : Matrix (Fin n) (Fin n) A) i j) = φ ((v : Matrix (Fin n) (Fin n) A) i j)) :
    ∀ i j, φ (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) =
      φ (((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := by
  have hM : φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) :=
    Matrix.ext fun i j => h i j
  have e1 : φ.mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) * φ.mapMatrix ((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hM] at e2
  have e := left_inv_eq_right_inv e1 e2
  intro i j
  exact congrArg (fun M => M i j) e

end Entry

set_option maxHeartbeats 800000 in

/- English proof (translation)
Set `u : Finset (Pl D) → GL (Fin S.rank) (AE D)` to `fun T => matHom S (x T)`. Apply the tactic sequence `have hv : Tendsto (fun T => (u T).val) atTop (𝓝 (matHom S κ).val) := tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_entry (fun T => mt S (x T) i j) (mt S κ i j) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) (fun T => h1 T i j) (fun T w hw => h2 T w hw i j) (f …`. Establish `hi : Tendsto (fun T => ((u T)⁻¹).val) atTop (𝓝 ((matHom S κ)⁻¹).val)`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `refine tendsto_entry _ _ ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) (fun T => map_inv_entries (infPart D) (u T) (matHom S κ) (h1 T) i j) (fun T w hw => map_inv_entries (compAt D w) (u T) (matHom S κ) (h2 T w hw) i j) (fun T w hw => ?_)`.

Establish `h` using `map_inv_entries (compAt D w) (u T) 1 (fun i j => by rw [Units.val_one]; exact h3 T w hw i j) i j`. Simplify using `using h`. Establish `key : Tendsto u atTop (𝓝 (matHom S κ))`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Conclude with `hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hi)`.

Conclude with `tendsto_subtype_rng.2 key`.
-/
theorem tendsto_of_agree (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S)
    (h1 : ∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j))
    (h2 : ∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j))
    (h3 : ∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) :
    Filter.Tendsto x Filter.atTop (nhds κ) := by
  let u : Finset (Pl D) → GL (Fin S.rank) (AE D) := fun T => matHom S (x T)
  have hv : Tendsto (fun T => (u T).val) atTop
      (𝓝 (matHom S κ).val) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_entry (fun T => mt S (x T) i j) (mt S κ i j) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
        (fun T => h1 T i j) (fun T w hw => h2 T w hw i j) (fun T w hw => h3 T w hw i j)
  have hi : Tendsto (fun T => ((u T)⁻¹).val) atTop
      (𝓝 ((matHom S κ)⁻¹).val) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_entry _ _ ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
      (fun T => map_inv_entries (infPart D) (u T) (matHom S κ) (h1 T) i j)
      (fun T w hw => map_inv_entries (compAt D w) (u T) (matHom S κ) (h2 T w hw) i j)
      (fun T w hw => ?_)
    have h := map_inv_entries (compAt D w) (u T) 1 (fun i j => by rw [Units.val_one]; exact h3 T w hw i j) i j
    simpa using h
  have key : Tendsto u atTop (𝓝 (matHom S κ)) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hi)
  exact tendsto_subtype_rng.2 key

end GlobalTheory.AdelicLimit
