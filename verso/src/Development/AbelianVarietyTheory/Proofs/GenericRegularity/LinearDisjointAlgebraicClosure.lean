import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

noncomputable section

namespace GlobalTheory.GeomConn

section Algebra

open scoped TensorProduct IntermediateField
open Topology Filter

/- English proof (translation)
Establish `: Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra` using `(algebraicClosure.isAlgebraic K L).isIntegral`. Use `Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_` and prove the remaining obligations. Establish `halg : B.IsAlgebraic` using `fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)`. Set `M : IntermediateField K L` to `halg.toIntermediateField`. Use `haveI : FiniteDimensional K M := ‹Module.Finite K B›`.

Express the relevant statement in the definitionally equal form `M.LinearDisjoint Ω`. Take `⟨θ, hθ⟩` from `Field.exists_primitive_element K M`. Establish `hi : IsIntegral K (θ : L)` using `(Algebra.IsIntegral.isIntegral (R := K) θ).map M.val`. Establish `e : K⟮(θ : L)⟯ = M`. Use `congrArg (IntermediateField.lift (F := M)) hθ` as an intermediate fact.

Simplify using `using this`. Rewrite using `[← e]`. Use `IntermediateField.LinearDisjoint.of_basis_left (IntermediateField.adjoin.powerBasis hi).basis ?_` and prove the remaining obligations. Establish `hd` using `GlobalTheory.GeomIrr.natDegree_minpoly_eq (L := K) (F := Ω) (fun x hx => h x hx.isAlgebraic) hi`. Establish `hl` using `linearIndependent_pow (K := Ω) (θ : L)`.

Rewrite `hl` using `[hd]`. Establish `he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) = fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[he]`.

Conclude with `hl`.
-/
theorem linearDisjoint_algebraicClosure {K Ω L : Type} [Field K] [CharZero K] [Field Ω] [Field L] [Algebra K Ω]
    [Algebra Ω L] [Algebra K L] [IsScalarTower K Ω L]
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) : (algebraicClosure K L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra := (algebraicClosure.isAlgebraic K L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)
  let M : IntermediateField K L := halg.toIntermediateField
  haveI : FiniteDimensional K M := ‹Module.Finite K B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K M
  have hi : IsIntegral K (θ : L) := (Algebra.IsIntegral.isIntegral (R := K) θ).map M.val
  have e : K⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := GlobalTheory.GeomIrr.natDegree_minpoly_eq (L := K) (F := Ω) (fun x hx => h x hx.isAlgebraic) hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

/- English proof (translation)
Set `N` to `algebraicClosure K (AlgebraicClosure Ω)`. Use `haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain`. Use `haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K`. Set `φ` to `Algebra.TensorProduct.map (AlgHom.id K N) j`. Establish `hφ : Function.Injective φ` using `Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj`.

Use `haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ`. Conclude with `GlobalTheory.GeomComp.isDomain_tensor_of_closure K N A F`.
-/
theorem isDomain_tensor {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (F : Type) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] A) := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let φ := Algebra.TensorProduct.map (AlgHom.id K N) j
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj
  haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ
  exact GlobalTheory.GeomComp.isDomain_tensor_of_closure K N A F

/- English proof (translation)
Establish `hc` using `isConnected_basicOpen_complexPoints_of_dense (exists_isConnected_principalOpen noetherNormalization_primitive (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface exists_mvPolynomial_of_poly_bound_off_hypersurface)) (principalOpen_dense_complexPoi …`. Establish `hf : Continuous fun (x : ℂ ⊗[K] A → ℂ) (a : A) => x (1 ⊗ₜ a)` using `continuous_pi fun a => continuous_apply _`. Use `hc.isPreconnected.image _ hf.continuousOn using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨φ, rfl⟩`. Use `⟨_, ⟨Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) φ fun _ _ => Commute.all _ _, rfl, by simp⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Introduce and unpack `⟨_, ⟨φ, rfl, -⟩, rfl⟩`.

Conclude with `⟨(φ.restrictScalars K).comp Algebra.TensorProduct.includeRight, rfl⟩`.
-/
theorem isPreconnected_points {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [Algebra K ℂ] [IsDomain (ℂ ⊗[K] A)] :
    IsPreconnected {x : A → ℂ | ∃ φ : A →ₐ[K] ℂ, ⇑φ = x} := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) (ℂ ⊗[K] A) 1 one_ne_zero
  have hf : Continuous fun (x : ℂ ⊗[K] A → ℂ) (a : A) => x (1 ⊗ₜ a) :=
    continuous_pi fun a => continuous_apply _
  convert hc.isPreconnected.image _ hf.continuousOn using 1
  ext x
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨_, ⟨Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) φ fun _ _ => Commute.all _ _, rfl, by simp⟩, ?_⟩
    funext a
    simp
  · rintro ⟨_, ⟨φ, rfl, -⟩, rfl⟩
    exact ⟨(φ.restrictScalars K).comp Algebra.TensorProduct.includeRight, rfl⟩

/- English proof (translation)
Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `haveI := isDomain_tensor j hj h ℂ`. Use `isPreconnected_points (K := K) (A := A) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨ρ, hρ, rfl⟩`. Conclude with `⟨{ ρ with commutes' := fun a => RingHom.congr_fun hρ a }, rfl⟩`. Introduce and unpack `⟨φ, rfl⟩`. Conclude with `⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a, rfl⟩`.
-/
theorem isPreconnected_points_over {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A]
    [Algebra K Ω] [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (σ : K →+* ℂ) :
    IsPreconnected {g : A → ℂ | ∃ ρ : A →+* ℂ, ρ.comp (algebraMap K A) = σ ∧ ⇑ρ = g} := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := isDomain_tensor j hj h ℂ
  convert isPreconnected_points (K := K) (A := A) using 1
  ext g
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨{ ρ with commutes' := fun a => RingHom.congr_fun hρ a }, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a, rfl⟩

end Algebra

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def ReadOn (U : Formalism.L2.PjFree.Unf Xo c σ r) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A)
    (f : A → ℂ) (k : U.Comp) : Prop :=
  ∃ (ψ : A →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ),
    (∀ a, Formalism.L2.PjFree.toC (ψ a) = f a) ∧ FrMap ψ yA z ∧ FrBor t (U.un k x) z

/- English proof (translation)
Take `⟨ψ, z, x, t, hψ, hz, ht⟩` from `h`. Take `⟨ψ', z', x', t', hψ', hz', ht'⟩` from `h'`. Take `rfl : ψ = ψ'` from `AlgHom.ext fun a => (hψ a).trans (hψ' a).symm`. Take `rfl : z = z'` from `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ yA).1 _ _ hz hz'`. Take `⟨-, hmul, hinv, -⟩` from `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)`.

Take `⟨ga, -, b, -, e⟩` from `(hU.2.2.2.1 k k' x x').1 ⟨_, hmul _ _ _ _ _ ht (hinv _ _ _ ht')⟩`. Conclude with `(congrArg Sigma.fst e).symm`.
-/
theorem ReadOn.unique {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A]
    [Algebra c.F A] {yA : FrPt Xo c A} {f : A → ℂ} {k k' : U.Comp} (h : ReadOn U yA f k) (h' : ReadOn U yA f k') :
    k = k' := by
  obtain ⟨ψ, z, x, t, hψ, hz, ht⟩ := h
  obtain ⟨ψ', z', x', t', hψ', hz', ht'⟩ := h'
  obtain rfl : ψ = ψ' := AlgHom.ext fun a => (hψ a).trans (hψ' a).symm
  obtain rfl : z = z' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ yA).1 _ _ hz hz'
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨ga, -, b, -, e⟩ := (hU.2.2.2.1 k k' x x').1 ⟨_, hmul _ _ _ _ _ ht (hinv _ _ _ ht')⟩
  exact (congrArg Sigma.fst e).symm

/- English proof (translation)
Take `⟨hL, -, -, -⟩` from `evLaws_genFr_atlas E H Dw l Xo c`. Take `⟨ψ₀, z₀, x₀, t₀, hf, hz₀, hb₀⟩` from `h`. Set `φ₀ : A →+* ℂ` to `ψ₀.toRingHom`. Take `rfl : ⇑φ₀ = f` from `funext hf`. Establish `hφ₀ : φ₀.comp (algebraMap c.F A) = σ` using `RingHom.ext fun a => ψ₀.commutes a`.

Take `⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩` from `GlobalTheory.SmoothPointFamily.exists_holomorphic_family c.F A σ φ₀ hφ₀`. Set `ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)` to `fun b => if hb : b ∈ B then { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b hb).1 a } else ψ₀`. Establish `hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a`. Introduce `b hb a`. Simplify using `only [ψ', dif_pos hb]`.

Both sides reduce to the same expression. Use `choose z hz using fun b => hL.bc _ _ (ψ' b) yA`. Take `⟨h1, h2⟩` from `hnear φ₀ hφ₀ (fun a _ => by simpa using hε)`. Establish `e₀ : ψ' (fun i => φ₀ (s i)) = ψ₀` using `AlgHom.ext fun a => by`. Use `hψ' _ h1 a` as an intermediate fact.

Rewrite `this` using `[h2]`. Conclude with `this`. Establish `hz₀' : z₀ = z fun i => φ₀ (s i)` using `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ₀ yA).1 _ _ hz₀ (e₀ ▸ hz _)`. Take `⟨B₁, hB₁, hb₁, hloc⟩` from `GlobalTheory.CompModel.exists_open_same_model U hσ hU yA ψ' z hB (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) h1 (hz₀' ▸ hb₀)`. Establish `e₁ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, (fun i => g (s i)) ∈ B₁` using `(continuous_pi fun i => continuous_apply (s i)).continuousAt.eventually (hB₁.mem_nhds hb₁)`.

Establish `e₂ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, ∀ a ∈ S, ‖g a - φ₀ a‖ < ε` using `(eventually_all_finset S).2 fun a _ => (((continuous_apply a).sub continuous_const).norm.continuousAt (x := ⇑φ₀)).eventually_lt continuousAt_const (by simpa using hε)`. Use `filter_upwards [e₁, e₂] with g hg₁ hg₂`. Introduce and unpack `⟨ρ, hρ, rfl⟩`. Take `⟨h3, h4⟩` from `hnear ρ hρ hg₂`. Take `⟨x, t, ht⟩` from `hloc _ hg₁`.

Conclude with `⟨ψ' _, z _, x, t, fun a => by rw [hψ' _ h3, h4], hz _, ht⟩`.
-/
theorem ReadOn.eventually {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] {yA : FrPt Xo c A}
    {f : A → ℂ} {k : U.Comp} (h : ReadOn U yA f k) :
    ∀ᶠ g in 𝓝 f, (∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = g) → ReadOn U yA g k := by
  classical
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨ψ₀, z₀, x₀, t₀, hf, hz₀, hb₀⟩ := h
  let φ₀ : A →+* ℂ := ψ₀.toRingHom
  obtain rfl : ⇑φ₀ = f := funext hf
  have hφ₀ : φ₀.comp (algebraMap c.F A) = σ := RingHom.ext fun a => ψ₀.commutes a
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family c.F A σ φ₀ hφ₀
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if hb : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b hb).1 a }
    else ψ₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => hL.bc _ _ (ψ' b) yA
  obtain ⟨h1, h2⟩ := hnear φ₀ hφ₀ (fun a _ => by simpa using hε)
  have e₀ : ψ' (fun i => φ₀ (s i)) = ψ₀ := AlgHom.ext fun a => by
    have := hψ' _ h1 a
    rw [h2] at this
    exact this
  have hz₀' : z₀ = z fun i => φ₀ (s i) :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) ψ₀ yA).1 _ _ hz₀ (e₀ ▸ hz _)
  obtain ⟨B₁, hB₁, hb₁, hloc⟩ := GlobalTheory.CompModel.exists_open_same_model U hσ hU yA ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) h1 (hz₀' ▸ hb₀)
  have e₁ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, (fun i => g (s i)) ∈ B₁ :=
    (continuous_pi fun i => continuous_apply (s i)).continuousAt.eventually (hB₁.mem_nhds hb₁)
  have e₂ : ∀ᶠ g : A → ℂ in 𝓝 ⇑φ₀, ∀ a ∈ S, ‖g a - φ₀ a‖ < ε :=
    (eventually_all_finset S).2 fun a _ =>
      (((continuous_apply a).sub continuous_const).norm.continuousAt (x := ⇑φ₀)).eventually_lt
        continuousAt_const (by simpa using hε)
  filter_upwards [e₁, e₂] with g hg₁ hg₂
  rintro ⟨ρ, hρ, rfl⟩
  obtain ⟨h3, h4⟩ := hnear ρ hρ hg₂
  obtain ⟨x, t, ht⟩ := hloc _ hg₁
  exact ⟨ψ' _, z _, x, t, fun a => by rw [hψ' _ h3, h4], hz _, ht⟩

/- English proof (translation)
Take `⟨hL, -, -, -⟩` from `evLaws_genFr_atlas E H Dw l Xo c`. Establish `hmem : ∀ {f k}, ReadOn U yA f k → ∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = f`. Introduce and unpack `f k ⟨ψ, -, -, -, hψ, -⟩`. Conclude with `⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a, funext hψ⟩`. Establish `key` using `hc.induction₂' (fun f g => ∀ k, ReadOn U yA f k → ReadOn U yA g k) (by`.

Introduce and unpack `_ ⟨ρ, hρ, rfl⟩`. Set `ψ : A →ₐ[c.F] CAt σ` to `{ (show A →+* CAt σ from ρ) with commutes' := fun a => RingHom.congr_fun hρ a }`. Take `⟨z, hz⟩` from `hL.bc _ _ ψ yA`. Take `⟨k₀, x, t, ht⟩` from `hU.2.2.1 z`. Establish `h₀ : ReadOn U yA ρ k₀` using `⟨ψ, z, x, t, fun _ => rfl, hz, ht⟩`.

Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (h₀.eventually hσ hU), self_mem_nhdsWithin] with g hg hgs`. Conclude with `⟨fun k hk => h₀.unique hU hk ▸ hg hgs, fun k hk => (hg hgs).unique hU hk ▸ h₀⟩)`. Use the proof step `(fun _ _ _ _ _ _ h₁ h₂ k hk => h₂ k (h₁ k hk)) (hmem h) (hmem h')`. Conclude with `(key k h).unique hU h'`.
-/
theorem ReadOn.eq_of_isPreconnected {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {A : Type} [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] {yA : FrPt Xo c A}
    (hc : IsPreconnected {g : A → ℂ | ∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = g})
    {f f' : A → ℂ} {k k' : U.Comp} (h : ReadOn U yA f k) (h' : ReadOn U yA f' k') : k = k' := by
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have hmem : ∀ {f k}, ReadOn U yA f k → ∃ ρ : A →+* ℂ, ρ.comp (algebraMap c.F A) = σ ∧ ⇑ρ = f := by
    rintro f k ⟨ψ, -, -, -, hψ, -⟩
    exact ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a, funext hψ⟩
  have key := hc.induction₂' (fun f g => ∀ k, ReadOn U yA f k → ReadOn U yA g k) (by
    rintro _ ⟨ρ, hρ, rfl⟩
    let ψ : A →ₐ[c.F] CAt σ := { (show A →+* CAt σ from ρ) with commutes' := fun a => RingHom.congr_fun hρ a }
    obtain ⟨z, hz⟩ := hL.bc _ _ ψ yA
    obtain ⟨k₀, x, t, ht⟩ := hU.2.2.1 z
    have h₀ : ReadOn U yA ρ k₀ := ⟨ψ, z, x, t, fun _ => rfl, hz, ht⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (h₀.eventually hσ hU), self_mem_nhdsWithin] with g hg hgs
    exact ⟨fun k hk => h₀.unique hU hk ▸ hg hgs, fun k hk => (hg hgs).unique hU hk ▸ h₀⟩)
    (fun _ _ _ _ _ _ h₁ h₂ k hk => h₂ k (h₁ k hk)) (hmem h) (hmem h')
  exact (key k h).unique hU h'

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU hac h Z k k' x x' hk hk'`. Take `⟨hL, -, -, hA⟩` from `evLaws_genFr_atlas E H Dw l Xo c`. Take `⟨-, hmul, hinv, -⟩` from `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)`. Take `⟨C, ψ, z, t, hz, ht⟩` from `hA h (Om Z) (genFr h Z)`. Use `haveI := C.sm`.

Establish `hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') → ∃ f, ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k`. Introduce and unpack `k x ⟨φ, y', t', hy', ht'⟩`. Take `⟨w, hw⟩` from `hL.bc _ _ φ z`. Conclude with `⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw, hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩`. Take `⟨f, hf⟩` from `hread k x hk`.

Take `⟨f', hf'⟩` from `hread k' x' hk'`. Use `ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'` and prove the remaining obligations. Conclude with `isPreconnected_points_over C.R.val Subtype.val_injective (hac C.Z) σ`.
-/
theorem comp_eq_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') → (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hac h Z k k' x x' hk hk'
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
  haveI := C.sm
  have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
      ∃ f, ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
    rintro k x ⟨φ, y', t', hy', ht'⟩
    obtain ⟨w, hw⟩ := hL.bc _ _ φ z
    exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
      hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
  obtain ⟨f, hf⟩ := hread k x hk
  obtain ⟨f', hf'⟩ := hread k' x' hk'
  refine ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
  exact isPreconnected_points_over C.R.val Subtype.val_injective (hac C.Z) σ

end GlobalTheory.GeomConn
