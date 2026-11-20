import Mathlib
import Formalism.LocalToGlobal.Columns.BrpAevalScaleMonomial
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv

open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Loc

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem localization_comap (p : Ideal (𝓞 K)) [p.IsPrime] (U : Submodule K V) (N : Submodule (𝓞 K) V) :
    localization₂ p (N.comap (U.subtype.restrictScalars (𝓞 K))) = (localization₂ p N).comap (U.subtype.restrictScalars (𝓞 K)) := by
  ext x
  simp only [localization₂, locS, Submodule.mem_comap, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.restrictScalars_apply, Submodule.subtype_apply]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem localization_map₃ (p : Ideal (𝓞 K)) [p.IsPrime] (f : V →ₗ[K] V') (A : Submodule (𝓞 K) V) :
    localization₂ p (A.map (f.restrictScalars (𝓞 K))) = (localization₂ p A).map (f.restrictScalars (𝓞 K)) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by exact_mod_cast h0
      rw [this]; exact p.zero_mem
    refine ⟨((s : K)⁻¹) • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul]
      rw [show (algebraMap (𝓞 K) K s) * (s : K)⁻¹ = 1 from mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · simp only [LinearMap.restrictScalars_apply, map_smul]
      simp only [LinearMap.restrictScalars_apply] at hax
      rw [hax, ← algebraMap_smul K s x, smul_smul]
      rw [show (s : K)⁻¹ * (algebraMap (𝓞 K) K s) = 1 from inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    simp only [LinearMap.restrictScalars_apply]
    rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]

end Loc

section LocDel

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem brp_act_inv_mem (lam : DomWeight n) (B : GL (Fin n) K) (y : Pol K Unit n)
    (hy : actP (oneW lam) (fun _ => B) y ∈ VV K (oneW lam)) : y ∈ VV K (oneW lam) := by
  have h := polyAction_mem_VV (oneW lam) (fun _ => B⁻¹) hy
  have e : actP (oneW lam) (fun _ => B⁻¹) (actP (oneW lam) (fun _ => B) y) = y := by
    have := congrArg (fun φ : Module.End K (Pol K Unit n) => φ y) ((rhoP (oneW lam)).map_mul (fun _ => B⁻¹) (fun _ => B))
    simp only [rhoP, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply] at this
    rw [← this]
    have h1 : ((fun _ : Unit => B⁻¹) * fun _ => B) = 1 := by funext; simp
    rw [h1]
    have := congrArg (fun φ : Module.End K (Pol K Unit n) => φ y) (rhoP (oneW lam)).map_one
    simpa [rhoP] using this
  rwa [e] at h

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem localization_delK_eq_map (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M)
    (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) (hB : IsBasisAt w M B) :
    localization₂ w.asIdeal (delK (oneW lam) fun _ => M) =
      (localization₂ w.asIdeal (stdDelL K lam)).map ((rhoK (oneW lam) (fun _ => B)).restrictScalars (𝓞 K)) := by
  have h := (nabDelLoc K Unit n (oneW lam) (fun _ => M) (fun _ => hM) w (fun _ => B) (fun _ => hB)).2
  unfold delK stdDelL
  rw [localization_comap, localization_comap, h]
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyV : y ∈ VV K (oneW lam) := brp_act_inv_mem K lam B y (by rw [hyx]; exact x.2)
    refine ⟨⟨y, hyV⟩, hy, ?_⟩
    apply Subtype.ext
    exact hyx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1, hz, rfl⟩

def brpRhoEquiv (lam : DomWeight n) (B : GL (Fin n) K) : VV K (oneW lam) ≃ₗ[K] VV K (oneW lam) :=
  LinearEquiv.ofLinear (rhoK (oneW lam) (fun _ => B)) (rhoK (oneW lam) (fun _ => B⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B) * fun _ => B⁻¹) = 1 := by funext; simp
      rw [this, map_one]; rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B⁻¹) * fun _ => B) = 1 := by funext; simp
      rw [this, map_one]; rfl)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem brp_lidx_delK (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M)
    (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) (hB : IsBasisAt w M B) :
    lidx w.asIdeal (stdDelL K lam) (delK (oneW lam) fun _ => M) = vAdd w (chiW K lam B) := by
  have : FiniteDimensional K (VV K (oneW lam)) := Module.Finite.of_basis (bVV K (oneW lam))
  rw [bridge_lidx_det_holds K (VV K (oneW lam)) w (stdDelL K lam) (delK (oneW lam) fun _ => M) (brpRhoEquiv K lam B)
    (stdDelL_isLattice K lam) ?_]
  · rfl
  · rw [localization_map₃, localization_delK_eq_map K lam M hM w B hB]
    rfl

def brpMatEquiv (B : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (B : Matrix (Fin n) (Fin n) K)) (Matrix.mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.mulVecLin_mul]; simp)
    (by rw [← Matrix.mulVecLin_mul]; simp)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem brp_lidx_colLat (M : Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K)
    (hB : IsBasisAt w M B) :
    lidx w.asIdeal (colLat (1 : GL (Fin n) K)) M = vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
  rw [bridge_lidx_det_holds K (Fin n → K) w (colLat 1) M (brpMatEquiv K B) (brz_colLat_one_lattice K) ?_]
  · show vAdd w (LinearMap.det (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))) = _
    rw [LinearMap.det_toLin']
  · rw [hB, lc_colLat_eq_gLat B]
    rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brp_vAdd_pow (w : HeightOneSpectrum (𝓞 K)) (x : K) (m : ℕ) : vAdd w (x ^ m) = m * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brp_vAdd_zpow (w : HeightOneSpectrum (𝓞 K)) (x : K) (m : ℤ) : vAdd w (x ^ m) = m * vAdd w x := by
  unfold vAdd
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem brp_vAdd_chiW (lam : DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) :
    (n : ℤ) * vAdd w (chiW K lam B) = (wsum lam * (dimW K lam : ℤ)) * vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
  have := congrArg (vAdd w) (chiW_pow K lam B)
  rwa [brp_vAdd_pow, brp_vAdd_zpow] at this

end LocDel

section Sum

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem brp_finsum_comb {α : Type} (c : α → ℝ) (x0 x1 x2 : α → ℤ) (k : ℤ) (m : ℕ)
    (h0 : (Function.support x0).Finite) (h2 : (Function.support x2).Finite)
    (h : ∀ p, (m : ℤ) * x1 p = m * x0 p + k * x2 p) :
    (m : ℝ) * ∑ᶠ p, c p * (x1 p : ℝ) = (m : ℝ) * ∑ᶠ p, c p * (x0 p : ℝ) + (k : ℝ) * ∑ᶠ p, c p * (x2 p : ℝ) := by
  have f0 : (Function.support fun p => c p * (x0 p : ℝ)).Finite :=
    h0.subset fun p hp => by
      simp only [Function.mem_support] at hp ⊢
      intro h'; apply hp; rw [h']; simp
  have f2 : (Function.support fun p => c p * (x2 p : ℝ)).Finite :=
    h2.subset fun p hp => by
      simp only [Function.mem_support] at hp ⊢
      intro h'; apply hp; rw [h']; simp
  rw [mul_finsum, mul_finsum, mul_finsum, ← finsum_add_distrib (f0.subset (Function.support_mul_subset_right _ _))
    (f2.subset (Function.support_mul_subset_right _ _))]
  refine finsum_congr fun p => ?_
  have hp : (((m : ℤ) * x1 p : ℤ) : ℝ) = ((m : ℤ) * x0 p + k * x2 p : ℤ) := congrArg (fun z : ℤ => (z : ℝ)) (h p)
  push_cast at hp
  linear_combination c p * hp

end Sum

section Weyl

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

/- English proof (translation)
Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem brp_alg (I F0 F1 F k D n : ℝ) (hD : 0 < D) (hn : 0 < n) (h : n * F1 = n * F0 + (k * D) * F) :
    -(I + 2 * F1) / D = k * (-(0 + 2 * F) / n) + -(I + 2 * F0) / D := by
  have key : F1 = F0 + k * D * F / n := by
    field_simp
    linarith
  rw [key]
  field_simp
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem brp_span_lattice {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {j : ℕ}
    (e : Fin j → V) (hsp : Submodule.span K (Set.range e) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower]
  exact hsp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem brp_colLat_one_span (n : ℕ) :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K)) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem brp_lcvInf_std (n : ℕ) :
    Formalism.LFunctionChainParameters.LLcv.lcvInf (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 0 := by
  unfold Formalism.LFunctionChainParameters.LLcv.lcvInf
  have : ∀ v, gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 1 := by
    intro v
    ext a c
    simp only [gramPl, Matrix.of_apply, majAt, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = c
      · subst h; simp
      · simp [Pi.single_apply, Matrix.one_apply, h, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem weylFunct : WeylFunct K := by
  intro n lam M hM
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hM1 : M = colLat (1 : GL (Fin 0) K) := by
      ext x
      rw [Subsingleton.elim x 0]
      simp only [Submodule.zero_mem]
    rw [hM1, weylH_std]
    simp
  classical
  have : Nontrivial (Fin n → K) := Pi.nontrivial_at ⟨0, hn⟩
  have hs := formH_spec (bVV K (oneW lam)) (stdPair K lam) (stdPair_pos K lam) (stdDelL K lam)
  have hX : ∀ v, IsUnit ((stdDelH K lam).X v).det := hs.1
  have hΔ0 := stdDelL_isLattice K lam
  have hΔ1 : Submodule.IsLattice K (delK (oneW lam) fun _ => M) :=
    (nabDelLattice K Unit n (oneW lam) (fun _ => M) (fun _ => hM)).2
  have : FiniteDimensional K (VV K (oneW lam)) := Module.Finite.of_basis (bVV K (oneW lam))
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (stdDelL_ne_bot K lam)
  have : Nontrivial (VV K (oneW lam)) := nontrivial_of_ne x0 0 hx00
  obtain ⟨j, e, he, -, hsp⟩ := Formalism.LFunctionChainParameters.LLcv.covolume_exists K (VV K (oneW lam)) (stdDelL K lam)
  have hspT : Submodule.span K (Set.range e) = ⊤ := hsp ▸ hΔ0.span_eq_top
  obtain ⟨hrk0, hj, -, hfin0, hmu0⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (VV K (oneW lam)) _ (bVV K (oneW lam))
    (stdDelH K lam).X hX j e (stdDelL K lam) he hΔ0.fg (stdDelL_ne_bot K lam) hsp
  obtain ⟨hrk1, -, -, hfin1, hmu1⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (VV K (oneW lam)) _ (bVV K (oneW lam))
    (stdDelH K lam).X hX j e (delK (oneW lam) fun _ => M) he hΔ1.fg (isLattice_ne_bot hΔ1)
    (by rw [hΔ1.span_eq_top, hspT])
  set es : Fin n → (Fin n → K) := fun i => Pi.single i 1 with hesdef
  have hesb : es = ⇑(Pi.basisFun K (Fin n)) := by funext i; simp [hesdef]
  have hes : LinearIndependent K es := by rw [hesb]; exact (Pi.basisFun K (Fin n)).linearIndependent
  have hspS : Submodule.span K (Set.range es) = ⊤ := by rw [hesb]; exact (Pi.basisFun K (Fin n)).span_eq
  obtain ⟨hrk2, -, -, hfin2, hmu2⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) (Pi.basisFun K (Fin n))
    (fun _ => 1) (fun _ => by simp) n es M hes hM.fg (isLattice_ne_bot hM) (by rw [hM.span_eq_top, hspS])
  have hterm : ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal},
      (n : ℤ) * (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) (delK (oneW lam) fun _ => M)) =
        n * (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) (stdDelL K lam)) +
          (wsum lam * (dimW K lam : ℤ)) * (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range es)) M) := by
    intro p
    have := p.2.isPrime
    let w : HeightOneSpectrum (𝓞 K) :=
      ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
    obtain ⟨B, hB⟩ := basisAtEx K n M hM w
    have hadd := Formalism.DivisionValues.idxLcv_lidx_add (K := K) p.1 (Submodule.span (𝓞 K) (Set.range e)) (stdDelL K lam)
      (delK (oneW lam) fun _ => M) (brp_span_lattice K e hspT) hΔ0 hΔ1
    have h1 : lidx p.1 (stdDelL K lam) (delK (oneW lam) fun _ => M) = vAdd w (chiW K lam B) :=
      brp_lidx_delK K lam M hM w B hB
    have h2 : lidx p.1 (Submodule.span (𝓞 K) (Set.range es)) M = vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
      rw [← brp_colLat_one_span]
      exact brp_lidx_colLat K M w B hB
    have h3 := brp_vAdd_chiW K lam w B
    show (n : ℤ) * lidx p.1 _ _ = n * lidx p.1 _ _ + _ * lidx p.1 _ _
    rw [hadd, h1, h2]
    linear_combination h3
  have hF := brp_finsum_comb (fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
      Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) _ _ _ _ n hfin0 hfin2 hterm
  have hjD : (j : ℝ) = (dimW K lam : ℝ) := by
    rw [← hrk0]
    unfold rkK dimW
    rw [hΔ0.span_eq_top, finrank_top]
  have hmuW : (weylH K lam M).mu = muDef (bVV K (oneW lam)) (stdDelH K lam).X (delK (oneW lam) fun _ => M) := rfl
  have hmuS : (stdDelH K lam).mu = muDef (bVV K (oneW lam)) (stdDelH K lam).X (stdDelL K lam) := rfl
  rw [hmuW, hmuS, brp_latK_mu K M hM.fg]
  show _ = _ * muDef (Pi.basisFun K (Fin n)) (fun _ => 1) M + _
  rw [hmu0, hmu1, hmu2, hrk0, hrk1, hrk2]
  unfold Formalism.LFunctionChainParameters.LLcv.lcv Formalism.LFunctionChainParameters.LLcv.lcvFin
  rw [brp_lcvInf_std]
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [hjD] at hjpos ⊢
  simp only [wsum] at hF
  push_cast at hF ⊢
  exact brp_alg _ _ _ _ _ _ _ hjpos hnpos hF

end Weyl

end Formalism.L2.Col
