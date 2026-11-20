import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisMapOfLiftBaseChangeSurjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolForm

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Take `⟨J, hJ⟩` from `GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero (⇑(Module.finBasis K V).dualBasis) (Module.finBasis K V).dualBasis.span_eq z hz`. Conclude with `hJ (h _)`.
-/
theorem wedge_two_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V)
    (h : ∀ f : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨J, hJ⟩ := GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
    (⇑(Module.finBasis K V).dualBasis) (Module.finBasis K V).dualBasis.span_eq z hz
  exact hJ (h _)

/- English proof (translation)
Rewrite using `[exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairingDual_ιMulti_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 2 → Module.Dual K V) (u v : V) :
    exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) (exteriorPower.ιMulti K 2 ![u, v]) =
      f 0 u * f 1 v - f 0 v * f 1 u := by
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp
  ring

/- English proof (translation)
Establish `e : (![v, u] ∘ Equiv.swap (0 : Fin 2) 1) = ![u, v]`. Apply the tactic sequence `ext i; fin_cases i <;> rfl`. Rewrite using `[← e, AlternatingMap.map_swap _ _ (by decide)]`.
-/
theorem ιMulti_two_swap {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] (u v : V) :
    exteriorPower.ιMulti K 2 ![u, v] = -exteriorPower.ιMulti K 2 ![v, u] := by
  have e : (![v, u] ∘ Equiv.swap (0 : Fin 2) 1) = ![u, v] := by
    ext i; fin_cases i <;> rfl
  rw [← e, AlternatingMap.map_swap _ _ (by decide)]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `H K _ A _ g hA hg L hL ψ hψ`. Take `⟨hFree, hHodge, -, -, hDual⟩` from `H`. Take `⟨-, hfin, -, -, e, he⟩` from `hFree K A g hA hg`. Take `⟨-, ⟨N, hN⟩, -⟩` from `hHodge K A g hA hg`. Establish `hiso` using `(hDual K A g hA hg L hL ψ hψ).1`.

Take `⟨n, a, b, hch, rfl⟩` from `hψ`. Set `pF` to `Submodule.projectionOnto (PrimitiveSubmodule A) N hN`. Set `pN` to `Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm`. Establish `hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c` using `Submodule.projection_add_projection_eq_self hN`. Establish `hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0` using `fun c hc ↦ (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc`.

Establish `hvan : ∀ x y : Module.Dual K (primDR A), ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0`. Introduce `x y`. Establish `hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A` using `fun z ↦ (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]`. Use `hiso _ (hmem x) _ (hmem y)` as an intermediate fact. Rewrite `this` using `[wedgeForm_apply]`.

Simplify using `using this`. Establish `h0 : ∑ k, exteriorPower.ιMulti K 2 ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0` using `by haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin`. Apply `wedge_two_eq_zero` to reduce the goal to its premises. Introduce `f`. Rewrite using `[map_sum]`.

Simplify using `only [pairingDual_ιMulti_two]`. Conclude with `hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)`. Establish `hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)), Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K)))` using `fun c ↦ by`. Establish `hc` using `c.2`. Express the relevant statement in the definitionally equal form `((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc`.

Rewrite `hc` using `[hodgeFiltration_eq_range]`. Conclude with `hc`. Use `choose form hform using hform`. Establish `hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)), cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u` using `fun u v ↦ by`. Rewrite using `[← he, ← he, ← map_neg, ιMulti_two_swap]`.

Establish `key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)), cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) = cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂`. Introduce `a₁ a₂ b₁ b₂`. Simplify using `only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply]`. Rewrite using `[hanti a₁ b₂]`. Normalize the expressions using the abelian group laws.

Establish `hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0`. Rewrite using `[← map_zero e, ← h0, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ ↦ (he _ _).symm`. Take `⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)), ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k)))` from `⟨_, rfl⟩`. Take `⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A, c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A))` from `⟨_, rfl⟩`.

Establish `hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1` using `fun k ↦ by`. Rewrite using `[hωdef, Sum.elim_inl, hform]`. Establish `hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1` using `fun k ↦ by`. Rewrite using `[hωdef, Sum.elim_inr, hform]`. Establish `hcl : ∀ k, c (Sum.inl k) = a k` using `fun k ↦ by rw [hcdef, Sum.elim_inl]`.

Establish `hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A)` using `fun k ↦ by rw [hcdef, Sum.elim_inr]`. Establish `hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A` using `fun k ↦ by`. Break down `k with k | k` into its components or cases. Rewrite using `[hωl]`. Conclude with `Subtype.property _`.

Rewrite using `[hωr]`. Conclude with `Subtype.property _`. Establish `hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) = ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1`. Establish `e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 = cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 ( …` using `fun k ↦ by`. Establish `ha` using `congrArg Subtype.val (hsplit (a k))`.

Establish `hb` using `congrArg Subtype.val (hsplit (b k))`. Rewrite `ha`, `hb` using `[Submodule.coe_add]`. Rewrite using `[← ha, ← hb]`. Conclude with `key _ _ _ _`. Rewrite using `[Fintype.sum_sum_type]`.

Simplify using `only [hcl, hcr, hωl, hωr, Submodule.coe_neg]`. Rewrite using `[Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ, add_zero]`. Use `⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩` and prove the remaining obligations. Introduce `f hf x`. Rewrite `hf` using `[Fil, Submodule.mem_dualAnnihilator]`.

Establish `hfF : ∀ c : PrimitiveSubmodule A, f c = 0` using `fun c ↦ hf _ c.2`. Establish `hfa : ∀ k, f (a k) = f (pN (a k))` using `fun k ↦ by conv_lhs => rw [← hsplit (a k)]`. Rewrite using `[map_add, hfF, zero_add]`. Establish `hfb : ∀ k, f (b k) = f (pN (b k))` using `fun k ↦ by conv_lhs => rw [← hsplit (b k)]`. Rewrite using `[map_add, hfF, zero_add]`.

Establish `hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k))` using `fun k ↦ by conv_lhs => rw [← hsplit (a k)]`. Rewrite using `[map_add]`. Establish `hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k))` using `fun k ↦ by conv_lhs => rw [← hsplit (b k)]`. Rewrite using `[map_add]`. Establish `hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k))` using `fun k ↦ congrArg x (Subtype.ext (hωl k))`.

Establish `hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k))` using `fun k ↦ congrArg x (Subtype.ext (hωr k))`. Establish `hv` using `hvan f x`. Rewrite using `[wedgeForm_apply, Fintype.sum_sum_type]`. Simplify using `only [hxl, hxr, hcl, hcr, map_neg]`. Simplify using `only [hfa, hfb, hxa, hxb]`.

Rewrite using `[← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chern_eq_sum_cup_form : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  intro H K _ A _ g hA hg L hL ψ hψ
  obtain ⟨hFree, hHodge, -, -, hDual⟩ := H
  obtain ⟨-, hfin, -, -, e, he⟩ := hFree K A g hA hg
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hHodge K A g hA hg
  have hiso := (hDual K A g hA hg L hL ψ hψ).1
  obtain ⟨n, a, b, hch, rfl⟩ := hψ
  let pF := Submodule.projectionOnto (PrimitiveSubmodule A) N hN
  let pN := Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm
  have hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c :=
    Submodule.projection_add_projection_eq_self hN
  have hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0 := fun c hc ↦
    (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc

  have hvan : ∀ x y : Module.Dual K (primDR A),
      ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0 := by
    intro x y
    have hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A := fun z ↦
      (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]
    have := hiso _ (hmem x) _ (hmem y)
    rw [wedgeForm_apply] at this
    simpa using this
  have h0 : ∑ k, exteriorPower.ιMulti K 2
      ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0 := by
    haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin
    apply wedge_two_eq_zero
    intro f
    rw [map_sum]
    simp only [pairingDual_ιMulti_two]
    exact hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)

  have hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)),
      Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := fun c ↦ by
    have hc := c.2
    change ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    exact hc
  choose form hform using hform
  have hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u := fun u v ↦ by
    rw [← he, ← he, ← map_neg, ιMulti_two_swap]
  have key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂ := by
    intro a₁ a₂ b₁ b₂
    simp only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply]
    rw [hanti a₁ b₂]
    abel
  have hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0 := by
    rw [← map_zero e, ← h0, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (he _ _).symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)),
      ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A,
      c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A)) := ⟨_, rfl⟩
  have hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inl, hform]
  have hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inr, hform]
  have hcl : ∀ k, c (Sum.inl k) = a k := fun k ↦ by rw [hcdef, Sum.elim_inl]
  have hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A) := fun k ↦ by rw [hcdef, Sum.elim_inr]
  have hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A := fun k ↦ by
    rcases k with k | k
    · rw [hωl]; exact Subtype.property _
    · rw [hωr]; exact Subtype.property _
  have hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) =
      ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 := by
    have e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 :=
      fun k ↦ by
      have ha := congrArg Subtype.val (hsplit (a k))
      have hb := congrArg Subtype.val (hsplit (b k))
      rw [Submodule.coe_add] at ha hb
      rw [← ha, ← hb]
      exact key _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [hcl, hcr, hωl, hωr, Submodule.coe_neg]
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ,
      add_zero]
  refine ⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩
  intro f hf x
  rw [Fil, Submodule.mem_dualAnnihilator] at hf
  have hfF : ∀ c : PrimitiveSubmodule A, f c = 0 := fun c ↦ hf _ c.2
  have hfa : ∀ k, f (a k) = f (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add, hfF, zero_add]
  have hfb : ∀ k, f (b k) = f (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add, hfF, zero_add]
  have hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add]
  have hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add]
  have hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k)) := fun k ↦
    congrArg x (Subtype.ext (hωl k))
  have hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k)) := fun k ↦
    congrArg x (Subtype.ext (hωr k))
  have hv := hvan f x
  rw [wedgeForm_apply, Fintype.sum_sum_type]
  simp only [hxl, hxr, hcl, hcr, map_neg]
  simp only [hfa, hfb, hxa, hxb]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.PolForm
