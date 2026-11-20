import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankSchwartzBruhatLeAleph0Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterNontrivialAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFiniteAdelicIrreducibleStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology
open GlobalTheory.FinHeis

open scoped Classical Matrix

namespace GlobalTheory.ArchFactorFin

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
The claim follows from `GlobalTheory.T.heisenberg_preserves_schwartz_bruhat`.
-/
theorem heisFin_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (a b : κ → Af F), ∀ g ∈ SB (κ → Af F), heisFin F ψ a b g ∈ SB (κ → Af F) := GlobalTheory.T.heisenberg_preserves_schwartz_bruhat
/- English proof (translation)
The claim follows from `GlobalTheory.T.rank_schwartz_bruhat_le_aleph0`.
-/
theorem rank_SB_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], Module.rank ℂ (SB (κ → Af F)) ≤ Cardinal.aleph0 := GlobalTheory.T.rank_schwartz_bruhat_le_aleph0
/- English proof (translation)
The claim follows from `GlobalTheory.T.standard_character_nontrivial_at_finite_place`.
-/
theorem psiLoc_nontrivial : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1 := GlobalTheory.T.standard_character_nontrivial_at_finite_place
/- English proof (translation)
The claim follows from `GlobalTheory.T.heisenberg_finite_adelic_irreducible`.
-/
theorem heisFin_irreducible : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1) → ∀ N : Submodule ℂ ((κ → Af F) → ℂ), N ≤ SB (κ → Af F) → (∀ (a b : κ → Af F), ∀ g ∈ N, heisFin F ψ a b g ∈ N) → N = ⊥ ∨ N = SB (κ → Af F) := GlobalTheory.T.heisenberg_finite_adelic_irreducible

/- English proof (translation)
Simplify using `[pureA, pt]`.
-/
theorem pureA_pt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F)
    (z : κ → Af F) : pureA F f g (pt F y z) = f y * g z := by
  simp [pureA, pt]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [pt, RingEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem pt_eta (x : κ → AF F) :
    pt F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) (fun i => (x i).2) = x := by
  funext i; simp only [pt, RingEquiv.symm_apply_apply]; rfl

/- English proof (translation)
Simplify using `only [dotProduct, finA, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x i).1 * 0 = 0`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `(x i).2 * b i = (x i).2 * b i`. Both sides reduce to the same expression.
-/
theorem dot_finA (x : κ → AF F) (b : κ → Af F) :
    (x ⬝ᵥ fun i => finA F (b i)) = finA F ((fun i => (x i).2) ⬝ᵥ b) := by
  simp only [dotProduct, finA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · change (x i).1 * 0 = 0; simp
  · change (x i).2 * b i = (x i).2 * b i; rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(pt F y z i).1 + 0 = _`. Simplify using `[pt]`. Express the relevant statement in the definitionally equal form `(pt F y z i).2 + a i = _`.

Simplify using `[pt]`.
-/
theorem pt_add (y : κ → mixedEmbedding.mixedSpace F) (z a : κ → Af F) :
    (pt F y z + fun i => finA F (a i)) = pt F y (z + a) := by
  funext i; refine Prod.ext ?_ ?_
  · change (pt F y z i).1 + 0 = _; simp [pt]
  · change (pt F y z i).2 + a i = _; simp [pt]

/- English proof (translation)
Simplify using `only [heisA, heisFin, dot_finA, pt_add]`. Both sides reduce to the same expression.
-/
theorem heisA_pt (ψ : AddChar (AF F) ℂ) (a b : κ → Af F) (Φ : (κ → AF F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F)
    (z : κ → Af F) : heisA F ψ a b Φ (pt F y z) = heisFin F ψ a b (fun z => Φ (pt F y z)) z := by
  simp only [heisA, heisFin, dot_finA, pt_add]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `conv_lhs => rw [← pt_eta x]`. Use `conv_rhs => rw [← pt_eta x]`. Rewrite using `[heisA_pt, pureA_pt]`. Simplify using `only [heisFin, pureA_pt]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pureA_heisFin (ψ : AddChar (AF F) ℂ) (a b : κ → Af F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → Af F) → ℂ) : pureA F f (heisFin F ψ a b g) = heisA F ψ a b (pureA F f g) := by
  funext x
  conv_lhs => rw [← pt_eta x]
  conv_rhs => rw [← pt_eta x]
  rw [heisA_pt, pureA_pt]
  simp only [heisFin, pureA_pt]
  ring

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Establish `: (fun z => pureA F f g (pt F y z)) = f y • g` using `by funext z; simp [pureA_pt]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hg`. Consider the case `zero => exact (SB _).zero_mem`. Consider the case `add Φ Ψ _ _ h1 h2 => exact (SB _).add_mem h1 h2`. Consider the case `smul c Φ _ h => exact (SB _).smul_mem c h`.
-/
theorem slice_mem_SB {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    (fun z => Φ (pt F y z)) ∈ SB (κ → Af F) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have : (fun z => pureA F f g (pt F y z)) = f y • g := by funext z; simp [pureA_pt]
    rw [this]; exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add Φ Ψ _ _ h1 h2 => exact (SB _).add_mem h1 h2
  | smul c Φ _ h => exact (SB _).smul_mem c h

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Conclude with `⟨g z • f, fun y => by simp [pureA_pt, mul_comm]⟩`. Consider the case `zero => exact ⟨0, fun y => rfl⟩`.

Consider the case `add Φ Ψ _ _ h1 h2`. Take `⟨s, hs⟩` from `h1`. Take `⟨t, ht⟩` from `h2`. Conclude with `⟨s + t, fun y => by simp [hs, ht]⟩`. Consider the case `smul c Φ _ h`.

Take `⟨s, hs⟩` from `h`. Conclude with `⟨c • s, fun y => by simp [hs]⟩`.
-/
theorem slice_schwartz {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (z : κ → Af F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ y, Φ (pt F y z) = s y := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨g z • f, fun y => by simp [pureA_pt, mul_comm]⟩
  | zero => exact ⟨0, fun y => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s, hs⟩ := h1; obtain ⟨t, ht⟩ := h2
    exact ⟨s + t, fun y => by simp [hs, ht]⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun y => by simp [hs]⟩

def heisFinL (ψ : AddChar (AF F) ℂ) (a b : κ → Af F) : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) where
  toFun := heisFin F ψ a b
  map_add' g g' := by funext z; simp [heisFin, mul_add]
  map_smul' c g := by funext z; simp [heisFin]; ring

def pureL (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun := pureA F f
  map_add' g g' := by funext x; simp [pureA, mul_add]
  map_smul' c g := by funext x; simp [pureA]; ring

/- English proof (translation)
Establish `hmem : ∀ g ∈ SB (κ → Af F), pureA F f g ∈ schA F κ` using `fun g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Set `V` to `SB (κ → Af F)`. Set `ρ : (κ → Af F) × (κ → Af F) → Module.End ℂ V` to `fun p => (heisFinL ψ p.1 p.2).restrict (fun g hg => heisFin_mem_SB F κ ψ hψ.1 p.1 p.2 g hg)`. Set `τ : (κ → mixedEmbedding.mixedSpace F) → Module.End ℂ V` to `fun y => { toFun := fun g => ⟨fun z => T (pureA F f g.1) (pt F y z), slice_mem_SB (hpres _ (hmem _ g.2)) y⟩ map_add' := fun g g' => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `z`. Simplify using `only [Submodule.coe_add, Pi.add_apply]`. Rewrite using `[show pureA F f (g.1 + g'.1) = pureL f g.1 + pureL f g'.1 from (pureL f).map_add _ _, map_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c g => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]`. Rewrite using `[show pureA F f (c • g.1) = c • pureL f g.1 from (pureL f).map_smul _ _, map_smul]`. Use `rfl }`.

Establish `hscal : ∀ y, ∃ c : ℂ, τ y = c • 1`. Introduce `y`. Use `GlobalTheory.dixmier_commutant_scalar _ V ρ (rank_SB_le F κ) ?_ (τ y) ?_` and prove the remaining obligations. Introduce `N hN`. Establish `h` using `heisFin_irreducible F κ ψ hψ.1 (psiLoc_nontrivial F ψ hψ) (N.map V.subtype) (by`.

Introduce and unpack `_ ⟨g, -, rfl⟩; exact g.2) (by`. Introduce and unpack `a b _ ⟨g, hg, rfl⟩`. Conclude with `⟨ρ (a, b) g, hN (a, b) g hg, rfl⟩)`. Break down `h with h | h` into its components or cases. Use `left`.

Conclude with `Submodule.map_injective_of_injective V.injective_subtype (by rw [h, Submodule.map_bot])`. Use `right`. Use `Submodule.map_injective_of_injective V.injective_subtype ?_` and prove the remaining obligations. Rewrite using `[h, Submodule.map_subtype_top]`. Introduce `p`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Use `show T (pureA F f (heisFin F ψ p.1 p.2 g.1)) (pt F y z) = heisFin F ψ p.1 p.2 (fun z => T (pureA F f g.1) (pt F y z)) z`.

Rewrite using `[pureA_heisFin, hcomm _ _ _ (hmem _ g.2), heisA_pt]`. Use `choose c hc using hscal`. Establish `key : ∀ g ∈ SB (κ → Af F), ∀ y z, T (pureA F f g) (pt F y z) = c y * g z`. Introduce `g hg y z`. Use `congrArg (fun φ : V => (φ : (κ → Af F) → ℂ) z) (LinearMap.congr_fun (hc y) ⟨g, hg⟩)` as an intermediate fact.

Simplify `this` using `[τ]`. Distinguish the cases in `h0 : ∃ g0 ∈ SB (κ → Af F), ∃ z0, g0 z0 ≠ 0`. Take `⟨g0, hg0, z0, hz0⟩` from `h0`. Take `⟨s, hs⟩` from `slice_schwartz (hpres _ (hmem _ hg0)) z0`. Use `⟨(g0 z0)⁻¹ • s, fun g hg => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Rewrite using `[← pt_eta x, key g hg, pureA_pt]`. Establish `h1` using `key g0 hg0 (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) z0`. Rewrite `h1` using `[hs]`. Simplify using `only [SchwartzMap.smul_apply, smul_eq_mul, h1]`.

Clear the denominators using the available nonvanishing facts. Use `push_neg at h0`. Use `⟨f, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hg0 : g = 0` using `funext fun z => h0 g hg z`. Substitute `hg0` using the available equality.

Establish `: pureA F f (0 : (κ → Af F) → ℂ) = 0` using `by funext x; simp [pureA]`. Rewrite using `[this, map_zero]`.
-/
theorem exists_arch_factor_of_comm (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hcomm : ∀ (a b : κ → Af F), ∀ Φ ∈ schA F κ, T (heisA F ψ a b Φ) = heisA F ψ a b (T Φ))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    ∃ u : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ g ∈ SB (κ → Af F), T (pureA F f g) = pureA F u g := by
  have hmem : ∀ g ∈ SB (κ → Af F), pureA F f g ∈ schA F κ := fun g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩
  let V := SB (κ → Af F)
  let ρ : (κ → Af F) × (κ → Af F) → Module.End ℂ V := fun p =>
    (heisFinL ψ p.1 p.2).restrict (fun g hg => heisFin_mem_SB F κ ψ hψ.1 p.1 p.2 g hg)
  let τ : (κ → mixedEmbedding.mixedSpace F) → Module.End ℂ V := fun y =>
    { toFun := fun g => ⟨fun z => T (pureA F f g.1) (pt F y z), slice_mem_SB (hpres _ (hmem _ g.2)) y⟩
      map_add' := fun g g' => by
        apply Subtype.ext; funext z
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [show pureA F f (g.1 + g'.1) = pureL f g.1 + pureL f g'.1 from (pureL f).map_add _ _, map_add]; rfl
      map_smul' := fun c g => by
        apply Subtype.ext; funext z
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        rw [show pureA F f (c • g.1) = c • pureL f g.1 from (pureL f).map_smul _ _, map_smul]; rfl }
  have hscal : ∀ y, ∃ c : ℂ, τ y = c • 1 := by
    intro y
    refine GlobalTheory.dixmier_commutant_scalar _ V ρ (rank_SB_le F κ) ?_ (τ y) ?_
    · intro N hN
      have h := heisFin_irreducible F κ ψ hψ.1 (psiLoc_nontrivial F ψ hψ) (N.map V.subtype) (by
          rintro _ ⟨g, -, rfl⟩; exact g.2) (by
          rintro a b _ ⟨g, hg, rfl⟩
          exact ⟨ρ (a, b) g, hN (a, b) g hg, rfl⟩)
      rcases h with h | h
      · left
        exact Submodule.map_injective_of_injective V.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        refine Submodule.map_injective_of_injective V.injective_subtype ?_
        rw [h, Submodule.map_subtype_top]
    · intro p
      apply LinearMap.ext; intro g
      apply Subtype.ext; funext z
      show T (pureA F f (heisFin F ψ p.1 p.2 g.1)) (pt F y z) = heisFin F ψ p.1 p.2 (fun z => T (pureA F f g.1) (pt F y z)) z
      rw [pureA_heisFin, hcomm _ _ _ (hmem _ g.2), heisA_pt]
  choose c hc using hscal
  have key : ∀ g ∈ SB (κ → Af F), ∀ y z, T (pureA F f g) (pt F y z) = c y * g z := by
    intro g hg y z
    have := congrArg (fun φ : V => (φ : (κ → Af F) → ℂ) z) (LinearMap.congr_fun (hc y) ⟨g, hg⟩)
    simpa [τ] using this
  by_cases h0 : ∃ g0 ∈ SB (κ → Af F), ∃ z0, g0 z0 ≠ 0
  · obtain ⟨g0, hg0, z0, hz0⟩ := h0
    obtain ⟨s, hs⟩ := slice_schwartz (hpres _ (hmem _ hg0)) z0
    refine ⟨(g0 z0)⁻¹ • s, fun g hg => ?_⟩
    funext x
    rw [← pt_eta x, key g hg, pureA_pt]
    have h1 := key g0 hg0 (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) z0
    rw [hs] at h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul, h1]
    field_simp
  · push_neg at h0
    refine ⟨f, fun g hg => ?_⟩
    have hg0 : g = 0 := funext fun z => h0 g hg z
    subst hg0
    have : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by funext x; simp [pureA]
    rw [this, map_zero]

/- English proof (translation)
Introduce `h`. Use `AddChar.map_add_eq_mul ψ x (-x)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul]`. Conclude with `one_ne_zero this`.
-/
theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hs` using `hM.triple.weil'.1.1.toIsSplitting`. Use `set d := G.M'.co`. Use `set w := d.e.symm ((fun i => finA F (x i)), fun i => finA F (y i)) with hw`. Establish `hew : d.e w = ((fun i => finA F (x i)), fun i => finA F (y i))` using `d.e.apply_symm_apply _`. Establish `hef : finA F 1 • w = w`.

Apply `d.e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, hew]`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf F) * 0 = 0`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : Af F) * x i = x i`. Simplify using the standard rewrite rules. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf F) * 0 = 0`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : Af F) * y i = y i`. Simplify using the standard rewrite rules. Establish `hev : evI F (finA F 1) = 0`. Express the relevant statement in the definitionally equal form `InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0`.

Conclude with `map_zero _`. Establish `hfix : actB (cA σ) h w = w`. Establish `h0 : finA F 1 • (mat h - 1) = 0` using `hh _ hev`. Use `show w * (mat h)ᵀ = w`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.transpose_add, Matrix.mul_add, Matrix.transpose_one, Matrix.mul_one, Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul]`. Use `_ = w := by rw [h0, Matrix.transpose_zero, Matrix.mul_zero, zero_add, hef]`. Establish `himpl` using `hs.impl h w Φ hΦ`. Rewrite `himpl` using `[hfix]`. Establish `hrho : ∀ Ψ, d.rho B.ψ w Ψ = B.ψ (⅟(2 : AF F) * ((fun i => finA F (x i)) ⬝ᵥ fun i => finA F (y i))) • heisA F B.ψ x y Ψ`.

Introduce `Ψ`. Use function extensionality and compare the values at `z`. Simplify using `only [Darboux.rho, hew, schr, heisA, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `himpl` using `[hrho, hrho]`.

Simplify using `only [MonoidHom.comp_apply, MonoidHom.inr_apply, map_smul] at himpl`. Conclude with `smul_right_injective _ (addChar_ne_zero _ _) himpl`.
-/
theorem comm_heisA {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf)
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F)) (x y : Fin a' × Fin (a + a') → Af F)
    {Φ : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) :
    om' (1, h) (heisA F B.ψ x y Φ) = heisA F B.ψ x y (om' (1, h) Φ) := by
  have hs := hM.triple.weil'.1.1.toIsSplitting
  set d := G.M'.co
  set w := d.e.symm ((fun i => finA F (x i)), fun i => finA F (y i)) with hw
  have hew : d.e w = ((fun i => finA F (x i)), fun i => finA F (y i)) := d.e.apply_symm_apply _
  have hef : finA F 1 • w = w := by
    apply d.e.injective
    rw [map_smul, hew]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) * 0 = 0; simp
      · change (1 : Af F) * x i = x i; simp
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) * 0 = 0; simp
      · change (1 : Af F) * y i = y i; simp
  have hev : evI F (finA F 1) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0; exact map_zero _
  have hfix : actB (cA σ) h w = w := by
    have h0 : finA F 1 • (mat h - 1) = 0 := hh _ hev
    show w * (mat h)ᵀ = w
    calc w * (mat h)ᵀ = (finA F 1 • w) * (mat h - 1 + 1)ᵀ := by rw [hef, sub_add_cancel]
      _ = w * (finA F 1 • (mat h - 1))ᵀ + finA F 1 • w := by
        rw [Matrix.transpose_add, Matrix.mul_add, Matrix.transpose_one, Matrix.mul_one, Matrix.smul_mul,
          Matrix.transpose_smul, Matrix.mul_smul]
      _ = w := by rw [h0, Matrix.transpose_zero, Matrix.mul_zero, zero_add, hef]
  have himpl := hs.impl h w Φ hΦ
  rw [hfix] at himpl
  have hrho : ∀ Ψ, d.rho B.ψ w Ψ =
      B.ψ (⅟(2 : AF F) * ((fun i => finA F (x i)) ⬝ᵥ fun i => finA F (y i))) • heisA F B.ψ x y Ψ := by
    intro Ψ; funext z
    simp only [Darboux.rho, hew, schr, heisA, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hrho, hrho] at himpl
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, map_smul] at himpl
  exact smul_right_injective _ (addChar_ne_zero _ _) himpl

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM h hh f`. Conclude with `exists_arch_factor_of_comm B.ψ hM.triple.base.std (om' (1, h)) (fun Φ hΦ => hM.triple.weil'.1.1.toIsSplitting.pres h Φ hΦ) (fun x y Φ hΦ => comm_heisA hM hh x y hΦ) f`.
-/
theorem arch_factor : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ h ∈ UAt σ G.W (evI F),
    ∀ f : SInf F (Fin a' × Fin (a + a')), ∃ u : SInf F (Fin a' × Fin (a + a')),
      ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, h) (pureA F f g) = pureA F u g := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM h hh f
  exact exists_arch_factor_of_comm B.ψ hM.triple.base.std (om' (1, h)) (fun Φ hΦ => hM.triple.weil'.1.1.toIsSplitting.pres h Φ hΦ)
    (fun x y Φ hΦ => comm_heisA hM hh x y hΦ) f

end GlobalTheory.ArchFactorFin

end
