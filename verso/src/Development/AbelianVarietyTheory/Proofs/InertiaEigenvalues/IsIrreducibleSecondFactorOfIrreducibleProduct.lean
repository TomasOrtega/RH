import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

open Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.ProdIrr

/- English proof (translation)
Take `⟨N, hN, hNS⟩` from `(mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))`. Take `⟨K, hKo, hKN⟩` from `hG N (by simpa using hN)`. Establish `hfix : ∀ p : P, (p : G) ∈ K → σ p u = u` using `fun p hp => hNS (hKN _ hp)`. Establish `wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u`. Introduce `p p' c c' hc hc' h`.

Establish `hm : ((p'⁻¹ * p : P) : G) ∈ K`. Establish `: ((p'⁻¹ * p : P) : G) = c' * c⁻¹`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]`. Rewrite using `[this]`.

Conclude with `mul_mem hc' (inv_mem hc)`. Establish `h2` using `hfix _ hm`. Rewrite `h2` using `[map_mul, Module.End.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Use `_ = σ p' u := by rw [h2]`. Set `F : G → W` to `fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0`. Establish `hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u`. Introduce `p c hc`. Establish `h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c'` using `⟨p, c, hc, rfl⟩`.

Simplify using `only [F, dif_pos h]`. Take `⟨c', hc', e⟩` from `h.choose_spec`. Conclude with `wd _ _ _ _ hc' hc e.symm`. Establish `hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0` using `fun g h => by`. Simplify using `only [F, dif_neg h]`.

Establish `hmem : F ∈ indSpace P σ`. Introduce `h g`. Distinguish the cases in `hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c`. Take `⟨p, c, hc, rfl⟩` from `hg`. Rewrite using `[← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul, Module.End.mul_apply]`.

Establish `: ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c`. Introduce and unpack `⟨p, c, hc, e⟩`. Conclude with `hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩`. Rewrite using `[hF0 _ hg, hF0 _ this, map_zero]`. Use `⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩, ?_, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x show F (x * c) = F x`. Distinguish the cases in `hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'`. Take `⟨p, c', hc', rfl⟩` from `hx`. Rewrite using `[mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']`.

Establish `: ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c'`. Introduce and unpack `⟨p, c', hc', e⟩`. Conclude with `hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩`. Rewrite using `[hF0 _ hx, hF0 _ this]`. Use `show F 1 = u`.

Use `hF 1 1 K.one_mem` as an intermediate fact. Simplify using `using this`. Introduce `g show F g = 0 ∨ ∃ p, F g = σ p u`. Distinguish the cases in `hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c`. Take `⟨p, c, hc, rfl⟩` from `hg`.

Conclude with `Or.inr ⟨p, hF _ _ hc⟩`. Conclude with `Or.inl (hF0 _ hg)`.
-/
theorem exists_mem_ind_apply_one {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (hG : ∀ N ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g ∈ K, g ∈ N)
    (P : Subgroup G) (σ : Representation ℂ P W) (hσ : IsSmooth σ) (u : W) :
    ∃ f : smoothPart (ind P σ), f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ p, f.1.1 g = σ p u := by
  classical
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))
  obtain ⟨K, hKo, hKN⟩ := hG N (by simpa using hN)
  have hfix : ∀ p : P, (p : G) ∈ K → σ p u = u := fun p hp => hNS (hKN _ hp)
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩,
    ?_, ?_⟩
  · apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  · show F 1 = u
    have := hF 1 1 K.one_mem
    simpa using this
  · intro g
    show F g = 0 ∨ ∃ p, F g = σ p u
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg; exact Or.inr ⟨p, hF _ _ hc⟩
    · exact Or.inl (hF0 _ hg)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_def, leviProj_apply]`. Conclude with `(Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _`. Establish `: (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) = fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k)`.

Use function extensionality and compare the values at `p`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Simplify using `only [leviProj_apply]`. Conclude with `((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _`.
-/
theorem continuous_leviProj (e : (Σ a, m a) ≃ n) : Continuous (leviProj k e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, leviProj_apply]
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have : (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) =
        fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k) := by
      funext p; rw [map_inv]; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [leviProj_apply]
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _

/- English proof (translation)
Introduce `N hN`. Take `⟨γ, hγ, h⟩` from `GlobalTheory.CentralExponent.exists_cong_subset hN`. Conclude with `⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩`.
-/
theorem exists_openSubgroup_GL :
    ∀ N ∈ 𝓝 (1 : GL n k), ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ ∀ g ∈ K, g ∈ N := by
  intro N hN
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset hN
  exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩

/- English proof (translation)
Take `⟨f, h1, h2⟩` from `exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _ (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u`. Conclude with `⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩`.
-/
theorem exists_indSp_apply_one {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (hρ : IsSmooth ρ) (u : W) :
    ∃ f : IndSp e ρ, f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ l : Levi k m, ∃ c : ℂ, f.1.1 g = c • ρ l u := by
  obtain ⟨f, h1, h2⟩ := exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u
  exact ⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩

end Local

end GlobalTheory.SmGL.ProdIrr

namespace GlobalTheory.SmGL.ProdIrr

/- English proof (translation)
Introduce `k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩`. Establish `hI : (prod₂ σ₀ τ).IsIrreducible` using `(MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi`. Take `⟨hV, -⟩` from `(isIrreducible_iff σ₀).1 hσi`. Take `⟨hX, hIirr⟩` from `(isIrreducible_iff _).1 hI`. Take `⟨x₀, hx₀⟩` from `exists_ne (0 : V)`.

Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)`. Set `L : V ⊗[ℂ] W →ₗ[ℂ] W` to `(TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ`.

Establish `hL : ∀ x w, L (x ⊗ₜ w) = φ x • w` using `fun x w => by simp [L]`. Set `ρ'` to `(extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom`. Establish `hρ' : IsSmooth ρ'` using `isSmooth_comp (isSmooth_extTensor hσs hτs) _ (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from (continuous_apply false).prodMk (continuous_apply true))`. Establish `hW : Nontrivial W`. Assume the negation of the conclusion as `hW`.

Rewrite `hW` using `[not_nontrivial_iff_subsingleton]`. Establish `h0 : ∀ z : V ⊗[ℂ] W, z = 0` using `fun z => z.induction_on rfl (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]) (fun a b ha hb => by rw [ha, hb, add_zero])`. Take `⟨f₁, f₂, hne⟩` from `hX`. Conclude with `hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))`. Rewrite using `[isIrreducible_iff]`.

Use `⟨hW, fun S hS => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hS0 : S = ⊥`. Conclude with `Or.inl hS0`. Use `right`. Take `⟨s, hsS, hs0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS0`.

Set `R : Submodule ℂ (V ⊗[ℂ] W)` to `LinearMap.range (LinearMap.lTensor V S.subtype)`. Establish `hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R`. Introduce and unpack `l _ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x w`. Conclude with `⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`.

Establish `hLR : ∀ y ∈ R, L y ∈ S`. Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x w => rw [LinearMap.lTensor_tmul, hL]`.

Conclude with `S.smul_mem _ w.2`. Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `add_mem ha hb`. Set `Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ')` to `{ carrier := {f | ∀ g, f.1.1 g ∈ R} add_mem' := fun ha hb g => add_mem (ha g) (hb g) zero_mem' := fun g => zero_mem R smul_mem' := fun c f hf g => R.smul_mem c (hf g) }`. Establish `hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y` using `fun g f hf x => hf (x * g)`.

Establish `hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u`. Introduce `u hu`. Take `⟨f, h1, h2⟩` from `exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u`. Use `⟨f, fun g => ?_, h1⟩` and prove the remaining obligations. Break down `h2 g with h | ⟨l, c, h⟩` into its components or cases.

Rewrite using `[h]`. Conclude with `zero_mem R`. Rewrite using `[h]`. Conclude with `R.smul_mem c (hR l u hu)`. Establish `hYtop : Y = ⊤`.

Use `(hIirr Y hYs).resolve_left fun hY => ?_` and prove the remaining obligations. Take `⟨f, hf, h1⟩` from `hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩`. Rewrite `hf` using `[hY, Submodule.mem_bot]`. Establish `: L (x₀ ⊗ₜ s) = 0` using `by rw [← h1, hf]; rfl`. Rewrite `this` using `[hL]`.

Conclude with `smul_ne_zero hφ hs0 this`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Take `⟨f, h1, -⟩` from `exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)`. Establish `hf : f ∈ Y` using `hYtop ▸ Submodule.mem_top`. Establish `h2` using `hLR _ (h1 ▸ hf 1)`.

Rewrite `h2` using `[hL]`. Conclude with `(S.smul_mem_iff hφ).1 h2`.
-/
theorem isIrreducible_of_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  intro k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩
  classical
  have hI : (prod₂ σ₀ τ).IsIrreducible := (MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi
  obtain ⟨hV, -⟩ := (isIrreducible_iff σ₀).1 hσi
  obtain ⟨hX, hIirr⟩ := (isIrreducible_iff _).1 hI
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
  let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
  have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
  let ρ' := (extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hσs hτs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have h0 : ∀ z : V ⊗[ℂ] W, z = 0 := fun z => z.induction_on rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))
  rw [isIrreducible_iff]
  refine ⟨hW, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
  have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
    rintro l _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
      exact ⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
        ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
    | add a b ha hb =>
      rw [map_add, map_add]; exact add_mem ha hb
  have hLR : ∀ y ∈ R, L y ∈ S := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
    { carrier := {f | ∀ g, f.1.1 g ∈ R}
      add_mem' := fun ha hb g => add_mem (ha g) (hb g)
      zero_mem' := fun g => zero_mem R
      smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
  have hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y := fun g f hf x => hf (x * g)
  have hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u := by
    intro u hu
    obtain ⟨f, h1, h2⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
    refine ⟨f, fun g => ?_, h1⟩
    rcases h2 g with h | ⟨l, c, h⟩
    · rw [h]; exact zero_mem R
    · rw [h]; exact R.smul_mem c (hR l u hu)
  have hYtop : Y = ⊤ := by
    refine (hIirr Y hYs).resolve_left fun hY => ?_
    obtain ⟨f, hf, h1⟩ := hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩
    rw [hY, Submodule.mem_bot] at hf
    have : L (x₀ ⊗ₜ s) = 0 := by rw [← h1, hf]; rfl
    rw [hL] at this
    exact smul_ne_zero hφ hs0 this
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, h1, -⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)
  have hf : f ∈ Y := hYtop ▸ Submodule.mem_top
  have h2 := hLR _ (h1 ▸ hf 1)
  rw [hL] at h2
  exact (S.smul_mem_iff hφ).1 h2

end GlobalTheory.SmGL.ProdIrr
