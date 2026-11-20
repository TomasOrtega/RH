import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

section Jumps

variable {T : LocLat G Qp LL O}

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem pfLvJumps_act (g : G) (z : T.V ⊗[Qp] B) :
    actVdR PD T.ρ g (ιV PD (LL := LL) (V := T.V) z) = ιV PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVdR, actVB, ιV, PD.ι_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.
-/
theorem pfLvJumps_mul (c : K₀) (z : T.V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c) (ιV PD (LL := LL) (V := T.V) z) =
      ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [mulVdR, mulVB, ιV, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities.
-/
theorem pfLvJumps_dcrisL (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (z : T.V ⊗[Qp] B)
    (hz : z ∈ DcrisL PD T.ρ τ₀) : ιV PD (LL := LL) (V := T.V) z ∈ DdRE PD T.ρ τ := by
  rw [DcrisL, Submodule.mem_inf] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz1
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz2
  rw [DdRE, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro g
    rw [pfLvJumps_act, hz1 g]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro c
    obtain ⟨c', rfl⟩ := hK c
    have hτc : τ (algebraMap K₀ K c') = τ₀ c' := by
      rw [← hτ]
      rfl
    rw [pfLvJumps_mul, hz2 c', map_smul, hτc]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem pfLvJumps_fil (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (a : ℤ)
    (h : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a) :
    FilCris PD T.ρ a ⊓ DcrisL PD T.ρ τ₀ = FilCris PD T.ρ (a + 1) ⊓ DcrisL PD T.ρ τ₀ := by
  have key : ∀ b b' : ℤ, FildR PD T.ρ τ b ≤ FildR PD T.ρ τ b' →
      FilCris PD T.ρ b ⊓ DcrisL PD T.ρ τ₀ ≤ FilCris PD T.ρ b' ⊓ DcrisL PD T.ρ τ₀ := by
    intro b b' hbb x hx
    rw [Submodule.mem_inf, FilCris, Submodule.mem_inf, Submodule.mem_comap] at hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hd : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ b :=
      (Submodule.mem_inf).2 ⟨pfLvJumps_dcrisL hK τ₀ τ hτ x hx3, hx2⟩
    have hd' := ((Submodule.mem_inf).1 (hbb hd)).2
    exact (Submodule.mem_inf).2 ⟨(Submodule.mem_inf).2 ⟨hx1, hd'⟩, hx3⟩
  exact le_antisymm (key a (a + 1) h.ge) (key (a + 1) a h.le)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem pfLvJumps_filD (c : ZMod n) (s : ℕ) (u : ℤ)
    (h : FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) =
      FilCris PD T.ρ (u + 1) ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))) :
    FilD W T c s u = FilD W T c s (u + 1) := by
  unfold FilD FilLev
  rw [h]

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem pfLvJumps_over (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀ := by
  let e : K₀ ≃ₐ[Qp] K :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) ⟨(algebraMap K₀ K).injective, hK⟩
  refine ⟨τ₀.comp e.symm.toAlgHom, ?_⟩
  ext c
  exact congrArg τ₀ (e.symm_apply_apply c)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pfLvJumps_win (hK : Function.Surjective (algebraMap K₀ K)) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T W.emb G₀ Sz η ty) (c : ZMod n) (s : ℕ) (u : ℤ)
    (hu : FilD W T c s u ≠ FilD W T c s (u + 1)) : u ∈ (ty (c - (s : ZMod n))).win G₀ Sz η := by
  obtain ⟨τ, hτ⟩ := pfLvJumps_over hK (W.emb (c - (s : ZMod n)))
  refine hJ (c - (s : ZMod n)) τ hτ u ?_
  intro h
  exact hu (pfLvJumps_filD c s u (pfLvJumps_fil hK _ τ hτ u h))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Split into cases according to the possible forms of the given data. Treat this case separately.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem jumps_holds (hK : Function.Surjective (algebraMap K₀ K)) (c : ZMod n) (ell : ℕ)
    (G₀ Sz η : ℕ) (ty : ZMod n → LT) (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s) (FilD W T c s) := by
  intro s _
  have hw := pfLvJumps_win hK G₀ Sz η ty hJ c s
  change Formalism.ExponentWindows.G.Jumps (kdOf ty (c - (s : ZMod n))) G₀ Sz η (bbOf ty (c - (s : ZMod n))) (FilD W T c s)
  cases h : ty (c - (s : ZMod n)) with
  | thin =>
    simp only [kdOf, h, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | up b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | down b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jumps_holds_quot (hK : Function.Surjective (algebraMap K₀ K))
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (c : ZMod n) (ell : ℕ) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T₁ W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s)
      (FilD W T₂ c s) :=
  jumps_holds hK c ell G₀ Sz η ty fun i τ hτ a ha => hJ i τ hτ a (hQuot T₁ T₂ F hc₁ hc₂ hon τ a ha)

end Jumps

end Formalism.MainNotions.N.Ln03.Pf
