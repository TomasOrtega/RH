import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsionStatement
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.AdicEqZeroOfMemAll
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.Bcompl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.GaloisActionAdicClose
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MemAOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Topology

namespace UpperTheory.Kd.K4.CocycleShiftCongruenceModPower

section Shapiro

variable {R G V U A : Type*} [Ring R] [Group G] [AddCommGroup V] [Module R V] [CommGroup U] [Fintype U]
  [CommGroup A] [DecidableEq A]

private def sh (g : G → V →ₗ[R] V) (c : G →* U) (rep : U → G) (z : G → V) (s : G) (y : U) : V :=
  g (rep y) (z ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)))

/- English proof (translation)
Simplify using `only [map_mul, map_inv, hr]`. Simplify using `[mul_comm, mul_left_comm]`.
-/
private theorem sh_arg (c : G →* U) (rep : U → G) (hr : ∀ y, c (rep y) = y) (s : G) (y : U) :
    c ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)) = 1 := by
  simp only [map_mul, map_inv, hr]
  simp [mul_comm, mul_left_comm]

/- English proof (translation)
Establish `hσ` using `sh_arg c rep hr s y`. Establish `hτ` using `sh_arg c rep hr t (y * (c s)⁻¹)`. Establish `h` using `hP (rep y) _ (H _ _ hσ hτ)`. Establish `e1 : (rep y)⁻¹ * (s * t) * rep (y * (c (s * t))⁻¹) = ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)) * ((rep (y * (c s)⁻¹))⁻¹ * t * rep (y * (c s)⁻¹ * (c t)⁻¹))`. Establish `: y * (c (s * t))⁻¹ = y * (c s)⁻¹ * (c t)⁻¹`.

Rewrite using `[map_mul, mul_inv, mul_assoc]`. Rewrite using `[this]`. Use `group`. Establish `e2 : ∀ v, g (rep y) (g ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)) v) = g s (g (rep (y * (c s)⁻¹)) v)`. Introduce `v`.

Rewrite using `[← hg, ← hg]`. Use `congr 2`. Use `group`. Simplify using `only [sh]`. Rewrite using `[e1]`.

Rewrite `h` using `[map_sub, map_add, e2]`. Conclude with `h`.
-/
private theorem sh_coc (g : G → V →ₗ[R] V) (hg : ∀ s t v, g (s * t) v = g s (g t v)) (c : G →* U) (rep : U → G)
    (hr : ∀ y, c (rep y) = y) (P : AddSubgroup V) (hP : ∀ s, ∀ v ∈ P, g s v ∈ P) (z : G → V)
    (H : ∀ σ τ, c σ = 1 → c τ = 1 → z (σ * τ) - (z σ + g σ (z τ)) ∈ P) (s t : G) (y : U) :
    sh g c rep z (s * t) y - (sh g c rep z s y + g s (sh g c rep z t (y * (c s)⁻¹))) ∈ P := by
  have hσ := sh_arg c rep hr s y
  have hτ := sh_arg c rep hr t (y * (c s)⁻¹)
  have h := hP (rep y) _ (H _ _ hσ hτ)
  have e1 : (rep y)⁻¹ * (s * t) * rep (y * (c (s * t))⁻¹) =
      ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)) * ((rep (y * (c s)⁻¹))⁻¹ * t * rep (y * (c s)⁻¹ * (c t)⁻¹)) := by
    have : y * (c (s * t))⁻¹ = y * (c s)⁻¹ * (c t)⁻¹ := by
      rw [map_mul, mul_inv, mul_assoc]
    rw [this]; group
  have e2 : ∀ v, g (rep y) (g ((rep y)⁻¹ * s * rep (y * (c s)⁻¹)) v) = g s (g (rep (y * (c s)⁻¹)) v) := by
    intro v
    rw [← hg, ← hg]
    congr 2
    group
  simp only [sh]
  rw [e1]
  rw [map_sub, map_add, e2] at h
  exact h

/- English proof (translation)
Establish `e : GlobalTheory.KA.push red (sh g c rep z) t (x * κ s) = ∑ y ∈ Finset.univ.filter (fun y => red y = x), sh g c rep z t (y * (c s)⁻¹)`. Unfold `GlobalTheory.KA.push`. Use `symm`. Use `Finset.sum_equiv (Equiv.mulRight (c s)⁻¹) ?_ ?_` and prove the remaining obligations. Introduce `y`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight, map_mul, hκ]`. Conclude with `⟨fun h => by rw [h], fun h => mul_right_cancel h⟩`. Introduce `y _`. Both sides reduce to the same expression. Rewrite using `[e, map_sum]`.

Simplify using `only [GlobalTheory.KA.push]`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Conclude with `AddSubgroup.sum_mem _ fun y _ => sh_coc g hg c rep hr P hP z H s t y`.
-/
private theorem push_coc (g : G → V →ₗ[R] V) (hg : ∀ s t v, g (s * t) v = g s (g t v)) (c : G →* U) (rep : U → G)
    (hr : ∀ y, c (rep y) = y) (P : AddSubgroup V) (hP : ∀ s, ∀ v ∈ P, g s v ∈ P) (z : G → V)
    (H : ∀ σ τ, c σ = 1 → c τ = 1 → z (σ * τ) - (z σ + g σ (z τ)) ∈ P)
    (red : U →* A) (κ : G → A) (hκ : ∀ s, red (c s)⁻¹ = κ s) (s t : G) (x : A) :
    GlobalTheory.KA.push red (sh g c rep z) (s * t) x -
      (GlobalTheory.KA.push red (sh g c rep z) s x + g s (GlobalTheory.KA.push red (sh g c rep z) t (x * κ s))) ∈ P := by
  have e : GlobalTheory.KA.push red (sh g c rep z) t (x * κ s) =
      ∑ y ∈ Finset.univ.filter (fun y => red y = x), sh g c rep z t (y * (c s)⁻¹) := by
    unfold GlobalTheory.KA.push
    symm
    refine Finset.sum_equiv (Equiv.mulRight (c s)⁻¹) ?_ ?_
    · intro y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight, map_mul, hκ]
      exact ⟨fun h => by rw [h], fun h => mul_right_cancel h⟩
    · intro y _
      rfl
  rw [e, map_sum]
  simp only [GlobalTheory.KA.push]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact AddSubgroup.sum_mem _ fun y _ => sh_coc g hg c rep hr P hP z H s t y

end Shapiro

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Set `L` to `IntermediateField.adjoin ℚ (E : Set Ω)`. Use `haveI : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Establish `hU` using `L.fixingSubgroup_isOpen`. Establish `h1 : (1 : Ω ≃ₐ[ℚ] Ω) ∈ (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω))` using `one_mem L.fixingSubgroup`.

Establish `hc : Continuous fun t : Ω ≃ₐ[ℚ] Ω => s⁻¹ * t` using `continuous_const.mul continuous_id`. Establish `h0 : (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) ∈ 𝓝 (s⁻¹ * s)`. Rewrite using `[inv_mul_cancel]`. Conclude with `hU.mem_nhds h1`. Establish `h2 : ∀ᶠ t in 𝓝 s, s⁻¹ * t ∈ (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω))` using `hc.continuousAt h0`.

Use `filter_upwards [h2] with t ht a ha`. Establish `h` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht a (IntermediateField.subset_adjoin ℚ _ ha)`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem ev_agree {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (E : Finset Ω) (s : Ω ≃ₐ[ℚ] Ω) :
    ∀ᶠ t in 𝓝 s, ∀ a ∈ E, t a = s a := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let L := IntermediateField.adjoin ℚ (E : Set Ω)
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hU := L.fixingSubgroup_isOpen
  have h1 : (1 : Ω ≃ₐ[ℚ] Ω) ∈ (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) := one_mem L.fixingSubgroup
  have hc : Continuous fun t : Ω ≃ₐ[ℚ] Ω => s⁻¹ * t := continuous_const.mul continuous_id
  have h0 : (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) ∈ 𝓝 (s⁻¹ * s) := by
    rw [inv_mul_cancel]
    exact hU.mem_nhds h1
  have h2 : ∀ᶠ t in 𝓝 s, s⁻¹ * t ∈ (L.fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) := hc.continuousAt h0
  filter_upwards [h2] with t ht a ha
  have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 ht a (IntermediateField.subset_adjoin ℚ _ ha)
  calc t a = (s * (s⁻¹ * t)) a := by rw [mul_inv_cancel_left]
    _ = s ((s⁻¹ * t) a) := rfl
    _ = s a := by rw [h]

section Loc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {R V A : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [DecidableEq A]

/- English proof (translation)
Use `filter_upwards [ev_agree (Polynomial.nthRootsFinset M (1 : Ω)) s] with t ht`. Establish `h1 : s⁻¹ * t ∈ fixMu Ω M`. Rewrite using `[mem_fixMu_iff]`. Introduce `a ha`. Establish `: t a = s a` using `ht a ((Polynomial.mem_nthRootsFinset (NeZero.pos M) _).2 ha)`.

Express the relevant statement in the definitionally equal form `s⁻¹ (t a) = a`. Rewrite using `[this]`. Conclude with `s.symm_apply_apply a`. Establish `h2` using `(hf _).1 h1`. Establish `h3 : cycM M t = cycM M s * cycM M (s⁻¹ * t)` using `by rw [← hc, mul_inv_cancel_left]`.

Rewrite using `[h3, h2, mul_one]`.
-/
private theorem cyc_ev (M : ℕ) [NeZero M] (hc : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t)
    (hf : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1) (s : Ω ≃ₐ[ℚ] Ω) :
    ∀ᶠ t in 𝓝 s, cycM M t = cycM M s := by
  filter_upwards [ev_agree (Polynomial.nthRootsFinset M (1 : Ω)) s] with t ht
  have h1 : s⁻¹ * t ∈ fixMu Ω M := by
    rw [mem_fixMu_iff]
    intro a ha
    have : t a = s a := ht a ((Polynomial.mem_nthRootsFinset (NeZero.pos M) _).2 ha)
    change s⁻¹ (t a) = a
    rw [this]
    exact s.symm_apply_apply a
  have h2 := (hf _).1 h1
  have h3 : cycM M t = cycM M s * cycM M (s⁻¹ * t) := by rw [← hc, mul_inv_cancel_left]
  rw [h3, h2, mul_one]

private noncomputable def cH (M : ℕ) (hc : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t) : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ :=
  MonoidHom.mk' (cycM M) hc

/- English proof (translation)
Use `filter_upwards [ev_agree (T.image (repM M (y * (cycM M s)⁻¹) : Ω ≃ₐ[ℚ] Ω)) s, cyc_ev M hc hf s] with s' h1 h2`. Establish `e : (cH M hc) s' = (cH M hc) s` using `h2`. Establish `m1` using `(hf _).2 (sh_arg (cH M hc) (repM M) hr s' y)`. Establish `m2` using `(hf _).2 (sh_arg (cH M hc) (repM M) hr s y)`. Simplify using `only [sh]`.

Rewrite using `[← map_sub]`. Apply `hP` to reduce the goal to its premises. Rewrite `m1`, the goal using `[e]`. Use `H _ m1 _ m2 fun a ha => ?_` and prove the remaining obligations. Establish `h3` using `h1 _ (Finset.mem_image_of_mem _ ha)`.

Express the relevant statement in the definitionally equal form `(repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ (s' (repM M (y * (cycM M s)⁻¹) a)) = (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ (s (repM M (y * (cycM M s)⁻¹) a))`. Rewrite using `[h3]`.
-/
private theorem sh_loc (g : (Ω ≃ₐ[ℚ] Ω) → V →ₗ[R] V) (M : ℕ) [NeZero M] [Fintype (ZMod M)ˣ]
    (hc : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t)
    (hr : ∀ y : (ZMod M)ˣ, cycM M (repM M y : Ω ≃ₐ[ℚ] Ω) = y)
    (hf : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1) (P : AddSubgroup V) (hP : ∀ s, ∀ v ∈ P, g s v ∈ P)
    (z : (Ω ≃ₐ[ℚ] Ω) → V) (T : Finset Ω)
    (H : ∀ σ ∈ fixMu Ω M, ∀ τ ∈ fixMu Ω M, (∀ a ∈ T, σ a = τ a) → z σ - z τ ∈ P) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) :
    ∀ᶠ s' in 𝓝 s, sh g (cH M hc) (repM M) z s' y - sh g (cH M hc) (repM M) z s y ∈ P := by
  classical
  filter_upwards [ev_agree (T.image (repM M (y * (cycM M s)⁻¹) : Ω ≃ₐ[ℚ] Ω)) s, cyc_ev M hc hf s] with s' h1 h2
  have e : (cH M hc) s' = (cH M hc) s := h2
  have m1 := (hf _).2 (sh_arg (cH M hc) (repM M) hr s' y)
  have m2 := (hf _).2 (sh_arg (cH M hc) (repM M) hr s y)
  simp only [sh]
  rw [← map_sub]
  apply hP
  rw [e] at m1 ⊢
  refine H _ m1 _ m2 fun a ha => ?_
  have h3 := h1 _ (Finset.mem_image_of_mem _ ha)
  change (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ (s' (repM M (y * (cycM M s)⁻¹) a)) = (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ (s (repM M (y * (cycM M s)⁻¹) a))
  rw [h3]

/- English proof (translation)
Establish `h` using `(Filter.eventually_all_finset (Finset.univ.filter (fun y => red y = x))).2 fun y _ => sh_loc g M hc hr hf P hP z T H s y`. Use `filter_upwards [h] with s' hs'`. Simplify using `only [GlobalTheory.KA.push]`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `AddSubgroup.sum_mem _ hs'`.
-/
private theorem push_loc (g : (Ω ≃ₐ[ℚ] Ω) → V →ₗ[R] V) (M : ℕ) [NeZero M] [Fintype (ZMod M)ˣ]
    (hc : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t)
    (hr : ∀ y : (ZMod M)ˣ, cycM M (repM M y : Ω ≃ₐ[ℚ] Ω) = y)
    (hf : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1) (P : AddSubgroup V) (hP : ∀ s, ∀ v ∈ P, g s v ∈ P)
    (z : (Ω ≃ₐ[ℚ] Ω) → V) (T : Finset Ω)
    (H : ∀ σ ∈ fixMu Ω M, ∀ τ ∈ fixMu Ω M, (∀ a ∈ T, σ a = τ a) → z σ - z τ ∈ P) (red : (ZMod M)ˣ → A)
    (s : Ω ≃ₐ[ℚ] Ω) (x : A) :
    ∀ᶠ s' in 𝓝 s, GlobalTheory.KA.push red (sh g (cH M hc) (repM M) z) s' x - GlobalTheory.KA.push red (sh g (cH M hc) (repM M) z) s x ∈ P := by
  have h := (Filter.eventually_all_finset (Finset.univ.filter (fun y => red y = x))).2
    fun y _ => sh_loc g M hc hr hf P hP z T H s y
  filter_upwards [h] with s' hs'
  simp only [GlobalTheory.KA.push]
  rw [← Finset.sum_sub_distrib]
  exact AddSubgroup.sum_mem _ hs'

end Loc

section Good

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
  (N w c j : ℕ)

private def Gd (n : ℕ) (a b : X.Fn l) : Prop := ∃ b', b = (l : ℤ_[l]) ^ j • b' ∧ LiftB X l N w n c a b'

private def Pn (n : ℕ) : AddSubgroup (X.Fn l) where
  carrier := {x | ∃ d ∈ X.B N l w, x = (l : ℤ_[l]) ^ n • d}
  add_mem' := by
    rintro _ _ ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
    exact ⟨d + e, add_mem hd he, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, zero_mem _, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨-d, neg_mem hd, (smul_neg _ _).symm⟩

variable {X l N w c j}

/- English proof (translation)
Take `⟨b', rfl, h⟩` from `h`. Conclude with `Submodule.smul_mem _ _ h.1`.
-/
private theorem Gd.mem {n : ℕ} {a b : X.Fn l} (h : Gd X l N w c j n a b) : b ∈ X.B N l w := by
  obtain ⟨b', rfl, h⟩ := h
  exact Submodule.smul_mem _ _ h.1

/- English proof (translation)
Introduce `u` and use `h.2 u`.
-/
private theorem cg_of {n : ℕ} {a b : X.Fn l} (h : LiftB X l N w n c a b) : CgF X l n b ((l : ℤ_[l]) ^ c • a) := fun u => h.2 u

/- English proof (translation)
Use `⟨0, (smul_zero _).symm, zero_mem _, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `(hA Ω ε X l n).1.refl (0 : X.Fn l)`. Simplify using `using h u`.
-/
private theorem Gd.zero (hA : SApi) (n : ℕ) : Gd X l N w c j n 0 0 := by
  refine ⟨0, (smul_zero _).symm, zero_mem _, fun u => ?_⟩
  have h := (hA Ω ε X l n).1.refl (0 : X.Fn l)
  simpa using h u

/- English proof (translation)
Take `⟨b₁, rfl, h₁⟩` from `h`. Take `⟨b₂, rfl, h₂⟩` from `h'`. Use `⟨b₁ + b₂, (smul_add _ _ _).symm, add_mem h₁.1 h₂.1, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `((hA Ω ε X l n).2.1 _ _ _ _ (cg_of h₁) (cg_of h₂)).1`. Rewrite `h` using `[← smul_add]`.

Conclude with `h u`.
-/
private theorem Gd.add (hA : SApi) {n : ℕ} {a a' b b' : X.Fn l} (h : Gd X l N w c j n a b) (h' : Gd X l N w c j n a' b') :
    Gd X l N w c j n (a + a') (b + b') := by
  obtain ⟨b₁, rfl, h₁⟩ := h
  obtain ⟨b₂, rfl, h₂⟩ := h'
  refine ⟨b₁ + b₂, (smul_add _ _ _).symm, add_mem h₁.1 h₂.1, fun u => ?_⟩
  have h := ((hA Ω ε X l n).2.1 _ _ _ _ (cg_of h₁) (cg_of h₂)).1
  rw [← smul_add] at h
  exact h u

/- English proof (translation)
Take `⟨b₁, rfl, h₁⟩` from `h`. Take `⟨b₂, rfl, h₂⟩` from `h'`. Use `⟨b₁ - b₂, (smul_sub _ _ _).symm, sub_mem h₁.1 h₂.1, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `((hA Ω ε X l n).2.1 _ _ _ _ (cg_of h₁) (cg_of h₂)).2`. Rewrite `h` using `[← smul_sub]`.

Conclude with `h u`.
-/
private theorem Gd.sub (hA : SApi) {n : ℕ} {a a' b b' : X.Fn l} (h : Gd X l N w c j n a b) (h' : Gd X l N w c j n a' b') :
    Gd X l N w c j n (a - a') (b - b') := by
  obtain ⟨b₁, rfl, h₁⟩ := h
  obtain ⟨b₂, rfl, h₂⟩ := h'
  refine ⟨b₁ - b₂, (smul_sub _ _ _).symm, sub_mem h₁.1 h₂.1, fun u => ?_⟩
  have h := ((hA Ω ε X l n).2.1 _ _ _ _ (cg_of h₁) (cg_of h₂)).2
  rw [← smul_sub] at h
  exact h u

/- English proof (translation)
Take `⟨b₁, rfl, h₁⟩` from `h`. Use `⟨X.galB l s b₁, map_smul _ _ _, (hS Ω ε X l N w hN b₁ h₁.1).1 s, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `(hA Ω ε X l n).2.2.2.2.2.2.1 s _ _ (cg_of h₁)`. Rewrite `h` using `[map_smul]`. Conclude with `h u`.
-/
private theorem Gd.gal (hA : SApi) (hS : SBStab) (hN : 0 < N) {n : ℕ} {a b : X.Fn l} (s : Ω ≃ₐ[ℚ] Ω)
    (h : Gd X l N w c j n a b) : Gd X l N w c j n (X.galB l s a) (X.galB l s b) := by
  obtain ⟨b₁, rfl, h₁⟩ := h
  refine ⟨X.galB l s b₁, map_smul _ _ _, (hS Ω ε X l N w hN b₁ h₁.1).1 s, fun u => ?_⟩
  have h := (hA Ω ε X l n).2.2.2.2.2.2.1 s _ _ (cg_of h₁)
  rw [map_smul] at h
  exact h u

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using Gd.zero hA n`. Consider the case `insert i S hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Conclude with `Gd.add hA (h i (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
private theorem Gd.sum (hA : SApi) {n : ℕ} {ι : Type*} (S : Finset ι) (a b : ι → X.Fn l)
    (h : ∀ i ∈ S, Gd X l N w c j n (a i) (b i)) : Gd X l N w c j n (∑ i ∈ S, a i) (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Gd.zero hA n
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact Gd.add hA (h i (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
The claim follows from `Gd.sum hA _ _ _ fun y _ => h y`.
-/
private theorem Gd.push (hA : SApi) {n : ℕ} {Γ : Type*} [Group Γ] {C C' : Type*} [Fintype C'] [DecidableEq C] (π : C' → C)
    (a b : Γ → C' → X.Fn l) (s : Γ) (x : C) (h : ∀ y, Gd X l N w c j n (a s y) (b s y)) :
    Gd X l N w c j n (GlobalTheory.KA.push π a s x) (GlobalTheory.KA.push π b s x) :=
  Gd.sum hA _ _ _ fun y _ => h y

/- English proof (translation)
Take `⟨b₁, rfl, h₁⟩` from `h`. Conclude with `⟨b₁, rfl, h₁.1, fun u => (hA Ω ε X l n).2.2.2.2.2.2.2.1 _ _ (cg_of h₁) u⟩`.
-/
private theorem Gd.mono (hA : SApi) {n : ℕ} {a b : X.Fn l} (h : Gd X l N w c j (n + 1) a b) : Gd X l N w c j n a b := by
  obtain ⟨b₁, rfl, h₁⟩ := h
  exact ⟨b₁, rfl, h₁.1, fun u => (hA Ω ε X l n).2.2.2.2.2.2.2.1 _ _ (cg_of h₁) u⟩

/- English proof (translation)
Use `⟨h.mem, fun u => ?_⟩` and prove the remaining obligations. Take `⟨b₁, rfl, h₁⟩` from `h`. Establish `h` using `(hA Ω ε X l n).2.2.1 ((l : ℤ_[l]) ^ j) _ _ (cg_of h₁)`. Rewrite `h` using `[smul_smul, ← pow_add, add_comm j c]`. Conclude with `h u`.
-/
private theorem Gd.lift (hA : SApi) {n : ℕ} {a b : X.Fn l} (h : Gd X l N w c j n a b) : LiftB X l N w n (c + j) a b := by
  refine ⟨h.mem, fun u => ?_⟩
  obtain ⟨b₁, rfl, h₁⟩ := h
  have h := (hA Ω ε X l n).2.2.1 ((l : ℤ_[l]) ^ j) _ _ (cg_of h₁)
  rw [smul_smul, ← pow_add, add_comm j c] at h
  exact h u

/- English proof (translation)
Take `⟨b₁, rfl, h₁⟩` from `h`. Take `⟨b₂, rfl, h₂⟩` from `h'`. Take `⟨hE, hadd, hsm, -⟩` from `hA Ω ε X l n`. Establish `e1` using `(hadd _ _ _ _ (cg_of h₁) (cg_of h₂)).2`. Establish `e2` using `(hadd _ _ _ _ (hsm ((l : ℤ_[l]) ^ c) _ _ hc) (hE.refl ((l : ℤ_[l]) ^ c • a'))).2`.

Rewrite `e2` using `[sub_self]`. Take `⟨d, hd, e⟩` from `hpur n (b₁ - b₂) (sub_mem h₁.1 h₂.1) (hE.trans e1 e2)`. Take `⟨i, rfl⟩ : ∃ i, j = i + cP` from `⟨j - cP, by omega⟩`. Use `⟨(l : ℤ_[l]) ^ i • d, Submodule.smul_mem _ _ hd, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub, pow_add, mul_smul, e, smul_comm]`.
-/
private theorem Gd.diff (hA : SApi) {cP : ℕ} (hj : cP ≤ j)
    (hpur : ∀ (n : ℕ), ∀ b ∈ X.B N l w, CgF X l n b 0 → ∃ b' ∈ X.B N l w, ((l : ℤ_[l]) ^ cP) • b = ((l : ℤ_[l]) ^ n) • b')
    {n : ℕ} {a a' b b' : X.Fn l} (h : Gd X l N w c j n a b) (h' : Gd X l N w c j n a' b') (hc : CgF X l n a a') :
    ∃ d ∈ X.B N l w, b - b' = (l : ℤ_[l]) ^ n • d := by
  obtain ⟨b₁, rfl, h₁⟩ := h
  obtain ⟨b₂, rfl, h₂⟩ := h'
  obtain ⟨hE, hadd, hsm, -⟩ := hA Ω ε X l n
  have e1 := (hadd _ _ _ _ (cg_of h₁) (cg_of h₂)).2
  have e2 := (hadd _ _ _ _ (hsm ((l : ℤ_[l]) ^ c) _ _ hc) (hE.refl ((l : ℤ_[l]) ^ c • a'))).2
  rw [sub_self] at e2
  obtain ⟨d, hd, e⟩ := hpur n (b₁ - b₂) (sub_mem h₁.1 h₂.1) (hE.trans e1 e2)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + cP := ⟨j - cP, by omega⟩
  refine ⟨(l : ℤ_[l]) ^ i • d, Submodule.smul_mem _ _ hd, ?_⟩
  rw [← smul_sub, pow_add, mul_smul, e, smul_comm]

/- English proof (translation)
Substitute `hcl` using the available equality. Take `⟨b₀, hb₀, hc⟩` from `hC`. Establish `hex : ∀ y, ∃ b, Gd X l N w (cL X l N w) j n (b₀ y) b` using `fun y => by`. Take `⟨-, -, b', h⟩` from `hb₀ y`. Conclude with `⟨_, b', rfl, h⟩`.

Use `choose b hb using hex`. Conclude with `⟨b, fun y => (hb y).mem, fun s y => Gd.diff hA hj hpur (h' s y) (Gd.add hA (h₀ s y) (Gd.sub hA (Gd.gal hA hS hN s (hb _)) (hb y))) (hc s y)⟩`.
-/
private theorem coh_step (hA : SApi) (hS : SBStab) (hN : 0 < N) {cP : ℕ} (hj : cP ≤ j)
    (hpur : ∀ (n : ℕ), ∀ b ∈ X.B N l w, CgF X l n b 0 → ∃ b' ∈ X.B N l w, ((l : ℤ_[l]) ^ cP) • b = ((l : ℤ_[l]) ^ n) • b')
    (hcl : c = cL X l N w) {n : ℕ} {C : Type} [Mul C] (κ : (Ω ≃ₐ[ℚ] Ω) → C) {Z' Z₀ F' F₀ : (Ω ≃ₐ[ℚ] Ω) → C → X.Fn l}
    (h' : ∀ s y, Gd X l N w c j n (Z' s y) (F' s y)) (h₀ : ∀ s y, Gd X l N w c j n (Z₀ s y) (F₀ s y))
    (hC : CohB X l N w n κ Z' Z₀) :
    ∃ b : C → X.Fn l, (∀ y, b y ∈ X.B N l w) ∧ ∀ s y, ∃ d ∈ X.B N l w,
      F' s y - (F₀ s y + (X.galB l s (b (y * κ s)) - b y)) = (l : ℤ_[l]) ^ n • d := by
  subst hcl
  obtain ⟨b₀, hb₀, hc⟩ := hC
  have hex : ∀ y, ∃ b, Gd X l N w (cL X l N w) j n (b₀ y) b := fun y => by
    obtain ⟨-, -, b', h⟩ := hb₀ y
    exact ⟨_, b', rfl, h⟩
  choose b hb using hex
  exact ⟨b, fun y => (hb y).mem, fun s y =>
    Gd.diff hA hj hpur (h' s y) (Gd.add hA (h₀ s y) (Gd.sub hA (Gd.gal hA hS hN s (hb _)) (hb y))) (hc s y)⟩

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (x : X.Khat l), (l : ℤ_[l]) ^ k • x = 0 → x = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x hx`. Simplify using `using hx`.

Consider the case `succ k ih`. Introduce `x hx`. Use `ih x (GlobalTheory.T.kummerCompletion_no_prime_torsion X l _ ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `hx`.

Use function extensionality and compare the values at `u`. Establish `h1` using `congrFun h u`. Simplify using `only [Pi.smul_apply] at h1`. Rewrite `h1` using `[← sub_eq_zero, ← smul_sub]`. Conclude with `sub_eq_zero.1 (key k _ h1)`.
-/
private theorem tf {k : ℕ} {f g : X.Fn l} (h : (l : ℤ_[l]) ^ k • f = (l : ℤ_[l]) ^ k • g) : f = g := by
  have key : ∀ (k : ℕ) (x : X.Khat l), (l : ℤ_[l]) ^ k • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      refine ih x (GlobalTheory.T.kummerCompletion_no_prime_torsion X l _ ?_)
      rw [smul_smul, ← pow_succ']
      exact hx
  funext u
  have h1 := congrFun h u
  simp only [Pi.smul_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (key k _ h1)

end Good

end UpperTheory.Kd.K4.CocycleShiftCongruenceModPower

open UpperTheory.Kd.K4.CocycleShiftCongruenceModPower in
/- English proof (translation)
Introduce `hA hI hS hD Ω _ _ _ ε X l _ N w hN`. Take `⟨cP, hpur⟩` from `pur ε X l N w`. Use `⟨cL X l N w + cP, ?_⟩` and prove the remaining obligations. Introduce `c₀ hc₀ A _ _ _ π κ M _ red t z Z hπ hπκ hredκ hZ hT hCπ hCn`. Take `⟨j, rfl⟩ : ∃ j, c₀ = cL X l N w + j` from `⟨c₀ - cL X l N w, by omega⟩`.

Establish `hj : cP ≤ j` using `by omega`. Establish `h8` using `(hD Ω ε X N hN).2.2.2.2.2.2.2`. Establish `hmul : ∀ (M : ℕ) [NeZero M] (s t : Ω ≃ₐ[ℚ] Ω), cycM M (s * t) = cycM M s * cycM M t` using `fun M _ s t => (h8 M s).2.1 t`. Establish `hrep : ∀ (M : ℕ) [NeZero M] (y : (ZMod M)ˣ), cycM M (repM M y : Ω ≃ₐ[ℚ] Ω) = y` using `fun M _ y => (h8 M 1).2.2.1 y`. Establish `hfix : ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω), s ∈ fixMu Ω M ↔ cycM M s = 1` using `fun M _ s => (h8 M s).2.2.2.1`.

Establish `gmul : ∀ (s t : Ω ≃ₐ[ℚ] Ω) (v : X.Fn l), X.galB l (s * t) v = X.galB l s (X.galB l t v)` using `(hA Ω ε X l 0).2.2.2.2.2.2.2.2.2.1`. Establish `gone : ∀ v : X.Fn l, X.galB l 1 v = v` using `(hA Ω ε X l 0).2.2.2.2.2.2.2.2.2.2`. Establish `hstab : ∀ s, ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w` using `fun s b hb => (hS Ω ε X l N w hN b hb).1 s`. Establish `hPg : ∀ (n : ℕ) s, ∀ v ∈ Pn X l N w n, X.galB l s v ∈ Pn X l N w n`. Introduce and unpack `n s _ ⟨d, hd, rfl⟩`.

Conclude with `⟨X.galB l s d, hstab s d hd, map_smul _ _ _⟩`. Establish `hex : ∀ n r σ, ∃ b, σ ∈ fixMu Ω (M n r) → Gd X l N w (cL X l N w) j n (z n r σ) b`. Introduce `n r σ`. Distinguish the cases in `hσ : σ ∈ fixMu Ω (M n r)`. Take `⟨-, -, b', hb'⟩` from `(hT n r).inv σ hσ`.

Conclude with `⟨_, fun _ => ⟨b', rfl, hb'⟩⟩`. Conclude with `⟨0, fun h => absurd h hσ⟩`. Use `choose bB hbB using hex`. Establish `shE : ∀ n r (f : (Ω ≃ₐ[ℚ] Ω) → X.Fn l), sh (X.galB l) (cH (M n r) (hmul (M n r))) (repM (M n r)) f = shB X l (M n r) f` using `fun _ _ _ => rfl`. Set `F : ∀ r : ℕ, ℕ → (Ω ≃ₐ[ℚ] Ω) → A r → X.Fn l` to `fun r n s y => GlobalTheory.KA.push (red n r) (shB X l (M n r) (bB n r)) s (y * t n r)`.

Establish `hFG : ∀ r n s y, Gd X l N w (cL X l N w) j n (Z n r s y) (F r n s y)`. Introduce `r n s y`. Rewrite using `[hZ]`. Use `Gd.push hA _ _ _ _ _ fun y' => Gd.gal hA hS hN _ (hbB n r _ ?_)` and prove the remaining obligations. Conclude with `(hfix _ _).2 (sh_arg (cH (M n r) (hmul (M n r))) (repM (M n r)) (hrep (M n r)) s y')`.

Establish `hcoc : ∀ r n s s' x, F r n (s * s') x - (F r n s x + X.galB l s (F r n s' (x * κ r s))) ∈ Pn X l N w n`. Introduce `r n s s' x`. Establish `H : ∀ σ τ, (cH (M n r) (hmul (M n r))) σ = 1 → (cH (M n r) (hmul (M n r))) τ = 1 → bB n r (σ * τ) - (bB n r σ + X.galB l σ (bB n r τ)) ∈ Pn X l N w n`. Introduce `σ τ h₁ h₂`. Establish `m₁` using `(hfix _ _).2 h₁`.

Establish `m₂` using `(hfix _ _).2 h₂`. Conclude with `Gd.diff hA hj hpur (hbB n r _ (mul_mem m₁ m₂)) (Gd.add hA (hbB n r σ m₁) (Gd.gal hA hS hN σ (hbB n r τ m₂))) ((hT n r).coc σ m₁ τ m₂)`. Establish `h` using `push_coc (X.galB l) gmul (cH (M n r) (hmul (M n r))) (repM (M n r)) (hrep (M n r)) (Pn X l N w n) (hPg n) (bB n r) H (red n r) (κ r) (hredκ n r) s s' (x * t n r)`. Rewrite `h` using `[shE]`. Establish `e : x * κ r s * t n r = x * t n r * κ r s` using `mul_right_comm _ _ _`.

Simplify using `only [F]`. Rewrite using `[e]`. Conclude with `h`. Establish `hloc : ∀ r n s x, ∀ᶠ s' in 𝓝 s, F r n s' x - F r n s x ∈ Pn X l N w n`. Introduce `r n s x`.

Take `⟨T, hT'⟩` from `(hT n r).loc`. Establish `H : ∀ σ ∈ fixMu Ω (M n r), ∀ τ ∈ fixMu Ω (M n r), (∀ a ∈ T, σ a = τ a) → bB n r σ - bB n r τ ∈ Pn X l N w n` using `fun σ m₁ τ m₂ h => Gd.diff hA hj hpur (hbB n r σ m₁) (hbB n r τ m₂) (hT' σ m₁ τ m₂ h)`. Establish `h` using `push_loc (X.galB l) (M n r) (hmul (M n r)) (hrep (M n r)) (hfix (M n r)) (Pn X l N w n) (hPg n) (bB n r) T H (red n r) s (x * t n r)`. Rewrite `h` using `[shE]`. Conclude with `h`.

Use `haveI hcompl : IsAdicComplete (idl l) (X.B N l w) := bcompl ε X l N w`. Set `σB : (Ω ≃ₐ[ℚ] Ω) →* Module.End ℤ_[l] (X.B N l w)` to `{ toFun := fun s => (X.galB l s).restrict (hstab s) map_one' := by`. Use extensionality with `b : 2`. Conclude with `gone b.1`. Use the proof step `map_mul' := fun s s' => by`.

Use extensionality with `b : 2`. Conclude with `gmul s s' b.1 }`. Set `Fs : ∀ r : ℕ, ℕ → (Ω ≃ₐ[ℚ] Ω) → A r → X.B N l w` to `fun r n s y => ⟨F r n s y, (hFG r n s y).mem⟩`. Establish `hκl : ∀ r, IsLocallyConstant (κ r)` using `fun r => (IsLocallyConstant.iff_eventually_eq _).2 fun s => by filter_upwards [cyc_ev (M 0 r) (hmul (M 0 r)) (hfix (M 0 r)) s] with s' h`. Rewrite using `[← hredκ 0 r s', ← hredκ 0 r s, h]`.

Establish `hσc : ∀ (n : ℕ) b s, ∀ᶠ s' in 𝓝 s, ∃ d, σB s' b - σB s b = (l : ℤ_[l]) ^ n • d`. Introduce `n b s`. Take `⟨E0, hE⟩` from `galc ε X l N w b.1 b.2 (n + cP)`. Use `filter_upwards [ev_agree E0 s] with s' hs'`. Establish `hu : ∀ a ∈ E0, (s⁻¹ * s') a = a` using `fun a ha => by`.

Express the relevant statement in the definitionally equal form `s⁻¹ (s' a) = a`. Rewrite using `[hs' a ha]`. Conclude with `s.symm_apply_apply a`. Establish `hcg` using `hE _ hu`. Take `⟨hEq, hadd, -⟩` from `hA Ω ε X l (n + cP)`.

Establish `hcg0` using `(hadd _ _ _ _ hcg (hEq.refl b.1)).2`. Rewrite `hcg0` using `[sub_self]`. Take `⟨d, hd, e⟩` from `hpur (n + cP) _ (sub_mem (hstab _ _ b.2) b.2) hcg0`. Establish `e2 : X.galB l (s⁻¹ * s') b.1 - b.1 = (l : ℤ_[l]) ^ n • d`. Use `tf (k := cP) ?_` and prove the remaining obligations.

Rewrite using `[e, smul_smul, pow_add, mul_comm]`. Use `⟨⟨X.galB l s d, hstab s d hd⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X.galB l s' b.1 - X.galB l s b.1 = (l : ℤ_[l]) ^ n • X.galB l s d`. Rewrite using `[← map_smul, ← e2, map_sub, ← gmul, mul_inv_cancel_left]`. Establish `h1 : ∀ r n s x, ∀ᶠ s' in 𝓝 s, ∃ d, Fs r n s' x - Fs r n s x = (l : ℤ_[l]) ^ n • d`.

Introduce `r n s x`. Use `filter_upwards [hloc r n s x] with s' h`. Take `⟨d, hd, e⟩` from `h`. Conclude with `⟨⟨d, hd⟩, Subtype.ext e⟩`. Establish `h2 : ∀ r n s s' x, ∃ d, Fs r n (s * s') x - (Fs r n s x + σB s (Fs r n s' (x * κ r s))) = (l : ℤ_[l]) ^ n • d`.

Introduce `r n s s' x`. Take `⟨d, hd, e⟩` from `hcoc r n s s' x`. Conclude with `⟨⟨d, hd⟩, Subtype.ext e⟩`. Establish `h3 : ∀ r n, ∃ b : A r → X.B N l w, ∀ s x, ∃ d, Fs r (n + 1) s x - (Fs r n s x + (σB s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d`. Introduce `r n`.

Take `⟨b, hbm, hb⟩` from `coh_step hA hS hN hj hpur rfl (κ r) (fun s y => (hFG r (n + 1) s y).mono hA) (fun s y => hFG r n s y) (hCn n r)`. Use `⟨fun y => ⟨b y, hbm y⟩, fun s x => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, e⟩` from `hb s x`. Conclude with `⟨⟨d, hd⟩, Subtype.ext e⟩`. Establish `h4 : ∀ r n, ∃ b : A r → X.B N l w, ∀ s x, ∃ d, GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x - (Fs r n s x + (σB s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d`.

Introduce `r n`. Take `⟨b, hbm, hb⟩` from `coh_step hA hS hN hj hpur rfl (κ r) (F' := GlobalTheory.KA.push (π r) (F (r + 1) n)) (fun s y => Gd.push hA _ _ _ _ _ fun y' => hFG (r + 1) n s y') (fun s y => hFG r n s y) (hCπ n r)`. Use `⟨fun y => ⟨b y, hbm y⟩, fun s x => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, e⟩` from `hb s x`. Use `⟨⟨d, hd⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `ec : ((GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x : X.B N l w) : X.Fn l) = GlobalTheory.KA.push (π r) (F (r + 1) n) s x`. Simplify using `only [GlobalTheory.KA.push]`. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Express the relevant statement in the definitionally equal form `((GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x : X.B N l w) : X.Fn l) - (F r n s x + (X.galB l s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d`. Rewrite using `[ec]`.

Conclude with `e`. Take `⟨Y, hY1, hY2, hY3, hY4⟩` from `ml3 l (X.B N l w) (Ω ≃ₐ[ℚ] Ω) A π κ σB Fs hπ hπκ hκl hσc h1 h2 h3 h4`. Use `⟨fun r s y => (Y r s y : X.Fn l), fun r s y => (Y r s y).2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r s s' y`. Conclude with `congrArg Subtype.val (hY1 r s s' y)`.

Introduce `r n s y filter_upwards [hY2 r n s y] with s' h`. Take `⟨d, e⟩` from `h`. Conclude with `⟨d.1, d.2, congrArg Subtype.val e⟩`. Introduce `r`. Use function extensionality and compare the values at `s y`.

Establish `h` using `congrArg Subtype.val (congrFun (congrFun (hY3 r) s) y)`. Simplify using `only [GlobalTheory.KA.push] at h ⊢`. Rewrite using `[h, AddSubmonoidClass.coe_finset_sum]`. Introduce `r n`. Take `⟨b, hb⟩` from `hY4 r n`.

Use `⟨bB n r, fun σ hσ => (hbB n r σ hσ).lift hA, fun y => (b y : X.Fn l), fun y => (b y).2, fun s y => ?_⟩` and prove the remaining obligations. Take `⟨d, e⟩` from `hb s y`. Conclude with `⟨d.1, d.2, congrArg Subtype.val e⟩`.
-/
theorem UpperTheory.Kd.K4.mlB :
    SApi → SInvApi → SBStab → SSlD → ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), 0 < N → ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ →
      ∀ (A : ℕ → Type) [∀ r, CommGroup (A r)] [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] (π : ∀ r, A (r + 1) →* A r)
        (κ : ∀ r, (Ω ≃ₐ[ℚ] Ω) →* A r) (M : ℕ → ℕ → ℕ) [∀ n r, NeZero (M n r)] (red : ∀ n r, (ZMod (M n r))ˣ →* A r) (t : ∀ (_ r : ℕ), A r)
        (z : ℕ → ℕ → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (Z : ∀ (_ r : ℕ), (Ω ≃ₐ[ℚ] Ω) → A r → X.Fn l),
      (∀ r, Function.Surjective (π r)) → (∀ r s, π r (κ (r + 1) s) = κ r s) → (∀ n r s, red n r (cycM (M n r) s)⁻¹ = κ r s) →
      (∀ n r s y, Z n r s y = GlobalTheory.KA.push (red n r) (shB X l (M n r) (z n r)) s (y * t n r)) →
      (∀ n r, TopCoc X l N w n (M n r) (z n r)) →
      (∀ n r, CohB X l N w n (κ r) (GlobalTheory.KA.push (π r) (Z n (r + 1))) (Z n r)) → (∀ n r, CohB X l N w n (κ r) (Z (n + 1) r) (Z n r)) →
      ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → A r → X.Fn l, (∀ r s y, Y r s y ∈ X.B N l w) ∧
        (∀ r s s' y, Y r (s * s') y = Y r s y + X.galB l s (Y r s' (y * κ r s))) ∧
        (∀ r (n : ℕ) s y, ∀ᶠ s' in 𝓝 s, ∃ d ∈ X.B N l w, Y r s' y - Y r s y = (l : ℤ_[l]) ^ n • d) ∧
        (∀ r, Y r = GlobalTheory.KA.push (π r) (Y (r + 1))) ∧
        ∀ r n, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (M n r), LiftB X l N w n c₀ (z n r σ) (bB σ)) ∧
          ∃ b : A r → X.Fn l, (∀ y, b y ∈ X.B N l w) ∧ ∀ s y, ∃ d ∈ X.B N l w,
            Y r s y - (GlobalTheory.KA.push (red n r) (shB X l (M n r) bB) s (y * t n r) + (X.galB l s (b (y * κ r s)) - b y)) = (l : ℤ_[l]) ^ n • d := by

  intro hA hI hS hD Ω _ _ _ ε X l _ N w hN
  obtain ⟨cP, hpur⟩ := pur ε X l N w
  refine ⟨cL X l N w + cP, ?_⟩
  intro c₀ hc₀ A _ _ _ π κ M _ red t z Z hπ hπκ hredκ hZ hT hCπ hCn
  obtain ⟨j, rfl⟩ : ∃ j, c₀ = cL X l N w + j := ⟨c₀ - cL X l N w, by omega⟩
  have hj : cP ≤ j := by omega
  have h8 := (hD Ω ε X N hN).2.2.2.2.2.2.2
  have hmul : ∀ (M : ℕ) [NeZero M] (s t : Ω ≃ₐ[ℚ] Ω), cycM M (s * t) = cycM M s * cycM M t :=
    fun M _ s t => (h8 M s).2.1 t
  have hrep : ∀ (M : ℕ) [NeZero M] (y : (ZMod M)ˣ), cycM M (repM M y : Ω ≃ₐ[ℚ] Ω) = y :=
    fun M _ y => (h8 M 1).2.2.1 y
  have hfix : ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω), s ∈ fixMu Ω M ↔ cycM M s = 1 :=
    fun M _ s => (h8 M s).2.2.2.1
  have gmul : ∀ (s t : Ω ≃ₐ[ℚ] Ω) (v : X.Fn l), X.galB l (s * t) v = X.galB l s (X.galB l t v) :=
    (hA Ω ε X l 0).2.2.2.2.2.2.2.2.2.1
  have gone : ∀ v : X.Fn l, X.galB l 1 v = v := (hA Ω ε X l 0).2.2.2.2.2.2.2.2.2.2
  have hstab : ∀ s, ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := fun s b hb => (hS Ω ε X l N w hN b hb).1 s
  have hPg : ∀ (n : ℕ) s, ∀ v ∈ Pn X l N w n, X.galB l s v ∈ Pn X l N w n := by
    rintro n s _ ⟨d, hd, rfl⟩
    exact ⟨X.galB l s d, hstab s d hd, map_smul _ _ _⟩
  have hex : ∀ n r σ, ∃ b, σ ∈ fixMu Ω (M n r) → Gd X l N w (cL X l N w) j n (z n r σ) b := by
    intro n r σ
    by_cases hσ : σ ∈ fixMu Ω (M n r)
    · obtain ⟨-, -, b', hb'⟩ := (hT n r).inv σ hσ
      exact ⟨_, fun _ => ⟨b', rfl, hb'⟩⟩
    · exact ⟨0, fun h => absurd h hσ⟩
  choose bB hbB using hex
  have shE : ∀ n r (f : (Ω ≃ₐ[ℚ] Ω) → X.Fn l),
      sh (X.galB l) (cH (M n r) (hmul (M n r))) (repM (M n r)) f = shB X l (M n r) f := fun _ _ _ => rfl
  let F : ∀ r : ℕ, ℕ → (Ω ≃ₐ[ℚ] Ω) → A r → X.Fn l := fun r n s y =>
    GlobalTheory.KA.push (red n r) (shB X l (M n r) (bB n r)) s (y * t n r)
  have hFG : ∀ r n s y, Gd X l N w (cL X l N w) j n (Z n r s y) (F r n s y) := by
    intro r n s y
    rw [hZ]
    refine Gd.push hA _ _ _ _ _ fun y' => Gd.gal hA hS hN _ (hbB n r _ ?_)
    exact (hfix _ _).2 (sh_arg (cH (M n r) (hmul (M n r))) (repM (M n r)) (hrep (M n r)) s y')
  have hcoc : ∀ r n s s' x, F r n (s * s') x - (F r n s x + X.galB l s (F r n s' (x * κ r s))) ∈ Pn X l N w n := by
    intro r n s s' x
    have H : ∀ σ τ, (cH (M n r) (hmul (M n r))) σ = 1 → (cH (M n r) (hmul (M n r))) τ = 1 →
        bB n r (σ * τ) - (bB n r σ + X.galB l σ (bB n r τ)) ∈ Pn X l N w n := by
      intro σ τ h₁ h₂
      have m₁ := (hfix _ _).2 h₁
      have m₂ := (hfix _ _).2 h₂
      exact Gd.diff hA hj hpur (hbB n r _ (mul_mem m₁ m₂))
        (Gd.add hA (hbB n r σ m₁) (Gd.gal hA hS hN σ (hbB n r τ m₂))) ((hT n r).coc σ m₁ τ m₂)
    have h := push_coc (X.galB l) gmul (cH (M n r) (hmul (M n r))) (repM (M n r)) (hrep (M n r))
      (Pn X l N w n) (hPg n) (bB n r) H (red n r) (κ r) (hredκ n r) s s' (x * t n r)
    rw [shE] at h
    have e : x * κ r s * t n r = x * t n r * κ r s := mul_right_comm _ _ _
    simp only [F]
    rw [e]
    exact h
  have hloc : ∀ r n s x, ∀ᶠ s' in 𝓝 s, F r n s' x - F r n s x ∈ Pn X l N w n := by
    intro r n s x
    obtain ⟨T, hT'⟩ := (hT n r).loc
    have H : ∀ σ ∈ fixMu Ω (M n r), ∀ τ ∈ fixMu Ω (M n r), (∀ a ∈ T, σ a = τ a) →
        bB n r σ - bB n r τ ∈ Pn X l N w n := fun σ m₁ τ m₂ h =>
      Gd.diff hA hj hpur (hbB n r σ m₁) (hbB n r τ m₂) (hT' σ m₁ τ m₂ h)
    have h := push_loc (X.galB l) (M n r) (hmul (M n r)) (hrep (M n r)) (hfix (M n r)) (Pn X l N w n) (hPg n)
      (bB n r) T H (red n r) s (x * t n r)
    rw [shE] at h
    exact h
  haveI hcompl : IsAdicComplete (idl l) (X.B N l w) := bcompl ε X l N w
  let σB : (Ω ≃ₐ[ℚ] Ω) →* Module.End ℤ_[l] (X.B N l w) :=
    { toFun := fun s => (X.galB l s).restrict (hstab s)
      map_one' := by
        ext b : 2
        exact gone b.1
      map_mul' := fun s s' => by
        ext b : 2
        exact gmul s s' b.1 }
  let Fs : ∀ r : ℕ, ℕ → (Ω ≃ₐ[ℚ] Ω) → A r → X.B N l w := fun r n s y => ⟨F r n s y, (hFG r n s y).mem⟩
  have hκl : ∀ r, IsLocallyConstant (κ r) := fun r =>
    (IsLocallyConstant.iff_eventually_eq _).2 fun s => by
      filter_upwards [cyc_ev (M 0 r) (hmul (M 0 r)) (hfix (M 0 r)) s] with s' h
      rw [← hredκ 0 r s', ← hredκ 0 r s, h]
  have hσc : ∀ (n : ℕ) b s, ∀ᶠ s' in 𝓝 s, ∃ d, σB s' b - σB s b = (l : ℤ_[l]) ^ n • d := by
    intro n b s
    obtain ⟨E0, hE⟩ := galc ε X l N w b.1 b.2 (n + cP)
    filter_upwards [ev_agree E0 s] with s' hs'
    have hu : ∀ a ∈ E0, (s⁻¹ * s') a = a := fun a ha => by
      change s⁻¹ (s' a) = a
      rw [hs' a ha]
      exact s.symm_apply_apply a
    have hcg := hE _ hu
    obtain ⟨hEq, hadd, -⟩ := hA Ω ε X l (n + cP)
    have hcg0 := (hadd _ _ _ _ hcg (hEq.refl b.1)).2
    rw [sub_self] at hcg0
    obtain ⟨d, hd, e⟩ := hpur (n + cP) _ (sub_mem (hstab _ _ b.2) b.2) hcg0
    have e2 : X.galB l (s⁻¹ * s') b.1 - b.1 = (l : ℤ_[l]) ^ n • d := by
      refine tf (k := cP) ?_
      rw [e, smul_smul, pow_add, mul_comm]
    refine ⟨⟨X.galB l s d, hstab s d hd⟩, Subtype.ext ?_⟩
    change X.galB l s' b.1 - X.galB l s b.1 = (l : ℤ_[l]) ^ n • X.galB l s d
    rw [← map_smul, ← e2, map_sub, ← gmul, mul_inv_cancel_left]
  have h1 : ∀ r n s x, ∀ᶠ s' in 𝓝 s, ∃ d, Fs r n s' x - Fs r n s x = (l : ℤ_[l]) ^ n • d := by
    intro r n s x
    filter_upwards [hloc r n s x] with s' h
    obtain ⟨d, hd, e⟩ := h
    exact ⟨⟨d, hd⟩, Subtype.ext e⟩
  have h2 : ∀ r n s s' x, ∃ d, Fs r n (s * s') x - (Fs r n s x + σB s (Fs r n s' (x * κ r s))) = (l : ℤ_[l]) ^ n • d := by
    intro r n s s' x
    obtain ⟨d, hd, e⟩ := hcoc r n s s' x
    exact ⟨⟨d, hd⟩, Subtype.ext e⟩
  have h3 : ∀ r n, ∃ b : A r → X.B N l w, ∀ s x, ∃ d,
      Fs r (n + 1) s x - (Fs r n s x + (σB s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d := by
    intro r n
    obtain ⟨b, hbm, hb⟩ := coh_step hA hS hN hj hpur rfl (κ r) (fun s y => (hFG r (n + 1) s y).mono hA)
      (fun s y => hFG r n s y) (hCn n r)
    refine ⟨fun y => ⟨b y, hbm y⟩, fun s x => ?_⟩
    obtain ⟨d, hd, e⟩ := hb s x
    exact ⟨⟨d, hd⟩, Subtype.ext e⟩
  have h4 : ∀ r n, ∃ b : A r → X.B N l w, ∀ s x, ∃ d,
      GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x - (Fs r n s x + (σB s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d := by
    intro r n
    obtain ⟨b, hbm, hb⟩ := coh_step hA hS hN hj hpur rfl (κ r)
      (F' := GlobalTheory.KA.push (π r) (F (r + 1) n)) (fun s y => Gd.push hA _ _ _ _ _ fun y' => hFG (r + 1) n s y')
      (fun s y => hFG r n s y) (hCπ n r)
    refine ⟨fun y => ⟨b y, hbm y⟩, fun s x => ?_⟩
    obtain ⟨d, hd, e⟩ := hb s x
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    have ec : ((GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x : X.B N l w) : X.Fn l) = GlobalTheory.KA.push (π r) (F (r + 1) n) s x := by
      simp only [GlobalTheory.KA.push]
      rw [AddSubmonoidClass.coe_finset_sum]
    change ((GlobalTheory.KA.push (π r) (Fs (r + 1) n) s x : X.B N l w) : X.Fn l) -
      (F r n s x + (X.galB l s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d
    rw [ec]
    exact e
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := ml3 l (X.B N l w) (Ω ≃ₐ[ℚ] Ω) A π κ σB Fs hπ hπκ hκl hσc h1 h2 h3 h4
  refine ⟨fun r s y => (Y r s y : X.Fn l), fun r s y => (Y r s y).2, ?_, ?_, ?_, ?_⟩
  · intro r s s' y
    exact congrArg Subtype.val (hY1 r s s' y)
  · intro r n s y
    filter_upwards [hY2 r n s y] with s' h
    obtain ⟨d, e⟩ := h
    exact ⟨d.1, d.2, congrArg Subtype.val e⟩
  · intro r
    funext s y
    have h := congrArg Subtype.val (congrFun (congrFun (hY3 r) s) y)
    simp only [GlobalTheory.KA.push] at h ⊢
    rw [h, AddSubmonoidClass.coe_finset_sum]
  · intro r n
    obtain ⟨b, hb⟩ := hY4 r n
    refine ⟨bB n r, fun σ hσ => (hbB n r σ hσ).lift hA, fun y => (b y : X.Fn l), fun y => (b y).2, fun s y => ?_⟩
    obtain ⟨d, e⟩ := hb s y
    exact ⟨d.1, d.2, congrArg Subtype.val e⟩
