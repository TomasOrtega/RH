import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace Formalism.MainNotions.N.K.Norm

section ConjM

variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

def IsConjM (M M' : Γ → Matrix n n K) : Prop :=
  ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ ∀ g, P * M g = M' g * P

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, by simp, by simp, fun g => by simp⟩`.
-/
theorem IsConjM.refl (M : Γ → Matrix n n K) : IsConjM M M :=
  ⟨1, 1, by simp, by simp, fun g => by simp⟩

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `h`. Use `⟨Q, P, h2, h1, fun g => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsConjM.symm {M M' : Γ → Matrix n n K} (h : IsConjM M M') : IsConjM M' M := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨Q, P, h2, h1, fun g => ?_⟩
  calc Q * M' g = Q * M' g * (P * Q) := by rw [h1, Matrix.mul_one]
    _ = Q * (M' g * P) * Q := by simp only [Matrix.mul_assoc]
    _ = Q * (P * M g) * Q := by rw [h3]
    _ = M g * Q := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `h`. Conclude with `⟨P, Q, h1, h2, fun g => h3 (f g)⟩`.
-/
theorem IsConjM.comp {M M' : Γ → Matrix n n K} (h : IsConjM M M') {Γ' : Type} (f : Γ' → Γ) :
    IsConjM (fun g => M (f g)) (fun g => M' (f g)) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => h3 (f g)⟩

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `h`. Use `⟨P.map f, Q.map f, ?_, ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ f.map_zero f.map_one]`. Rewrite using `[← Matrix.map_mul, h2, Matrix.map_one _ f.map_zero f.map_one]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h3]`.
-/
theorem IsConjM.map {M M' : Γ → Matrix n n K} (h : IsConjM M M') {S : Type} [CommRing S] (f : K →+* S) :
    IsConjM (fun g => (M g).map f) (fun g => (M' g).map f) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨P.map f, Q.map f, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.map_mul, h1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, h3]

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `h`. Conclude with `⟨P, Q, h1, h2, fun g => by rw [Matrix.mul_smul, Matrix.smul_mul, h3]⟩`.
-/
theorem IsConjM.smul {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K) :
    IsConjM (fun g => c g • M g) (fun g => c g • M' g) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [Matrix.mul_smul, Matrix.smul_mul, h3]⟩

/- English proof (translation)
Take `⟨Q, P, h2, h1, h3⟩` from `h.symm`. Use `⟨Q.transpose, P.transpose, ?_, ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.transpose_mul, h1, Matrix.transpose_one]`. Rewrite using `[← Matrix.transpose_mul, h2, Matrix.transpose_one]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, h3]`.
-/
theorem IsConjM.dual [Group Γ] {M M' : Γ → Matrix n n K} (h : IsConjM M M') :
    IsConjM (fun g => (M g⁻¹).transpose) (fun g => (M' g⁻¹).transpose) := by
  obtain ⟨Q, P, h2, h1, h3⟩ := h.symm
  refine ⟨Q.transpose, P.transpose, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h3]

end ConjM

section MatRep

variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}

/- English proof (translation)
Simplify using `[matRep, Matrix.toLinAlgEquiv'_apply]`.
-/
theorem matRep_apply (M : Γ →* Matrix (Fin k) (Fin k) K) (g : Γ) (v : Fin k → K) :
    matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

def matEquiv (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) :
    (Fin k → K) ≃ₗ[K] (Fin k → K) where
  toLinearMap := Matrix.toLin' P
  invFun v := Q.mulVec v
  left_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  right_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matEquiv_apply (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) (v : Fin k → K) :
    matEquiv P Q h1 h2 v = P.mulVec v := rfl

/- English proof (translation)
Take `⟨P, Q, h1, h2, h3⟩` from `h`. Use `⟨matEquiv P Q h1 h2, fun g v => ?_⟩` and prove the remaining obligations. Rewrite using `[matEquiv_apply, matEquiv_apply, matRep_apply, matRep_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]`.
-/
theorem exists_equiv_of_conj {M M' : Γ →* Matrix (Fin k) (Fin k) K} (h : IsConjM ⇑M ⇑M') :
    ∃ e : (Fin k → K) ≃ₗ[K] (Fin k → K), ∀ g v, e (matRep M g v) = matRep M' g (e v) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨matEquiv P Q h1 h2, fun g v => ?_⟩
  rw [matEquiv_apply, matEquiv_apply, matRep_apply, matRep_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]

end MatRep

section Inv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

/- English proof (translation)
Set `E : V ⊗[Qp] B ≃ₗ[LL] V' ⊗[Qp] B` to `AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)`. Establish `hE : ∀ g x, E (actVB PD ρ g x) = actVB PD ρ' g (E x)`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [E, actVB, he]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`. Establish `hD : Dcris PD ρ = (Dcris PD ρ').comap (E : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B)`. Use extensionality with `x`. Simplify using `only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx g`. Rewrite using `[LinearEquiv.coe_coe, ← hE, hx g]`. Introduce `hx g`. Apply `E.injective` to reduce the goal to its premises.

Rewrite using `[hE]`. Conclude with `hx g`. Unfold `IsCrys at h ⊢`. Rewrite using `[← e.finrank_eq, ← h, hD]`. Conclude with `(E.ofSubmodule' (Dcris PD ρ')).finrank_eq.symm`.
-/
theorem isCrys_congr (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  let E : V ⊗[Qp] B ≃ₗ[LL] V' ⊗[Qp] B := AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)
  have hE : ∀ g x, E (actVB PD ρ g x) = actVB PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVB, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : Dcris PD ρ = (Dcris PD ρ').comap (E : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B) := by
    ext x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (Dcris PD ρ')).finrank_eq.symm

omit he in
/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`.
-/
theorem filV_map_tmul (a : ℤ) (y : V ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp)) :
    AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype y) =
      AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL] V') ((PD.Fil a).restrictScalars Qp).subtype
        (AlgebraTensorModule.congr e (LinearEquiv.refl Qp _) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit he in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem congr_symm_tmul (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp BdR)
      (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Use `set E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) with hEd`. Establish `hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x)`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [E, actVdR, he]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`. Establish `hM : ∀ c x, E (mulVdR (K` using `K) (BdR := BdR) (V := V) (LL := LL) c x) = mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c (E x) := by`. Introduce `c x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [E, mulVdR]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`. Establish `hF : x ∈ FilV PD (LL` using `LL) (V := V) a ↔ E x ∈ FilV PD (LL := LL) (V := V') a := by`. Simplify using `only [FilV, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨_, (filV_map_tmul PD e a y).symm⟩`. Introduce and unpack `⟨y, hy⟩`. Use `⟨AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp _) y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← filV_map_tmul PD e.symm a y, hy, hEd, congr_symm_tmul]`. Simplify using `only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]`. Use `and_congr (and_congr ⟨fun h g => ?_, fun h g => E.injective ?_⟩ ⟨fun h c => ?_, fun h c => E.injective ?_⟩) hF` and prove the remaining obligations. Rewrite using `[← hE, h g]`. Rewrite using `[hE]`.

Conclude with `h g`. Rewrite using `[← hM, h c, map_smul]`. Rewrite using `[hM, map_smul]`. Conclude with `h c`.
-/
theorem mem_fildR_iff (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) x ∈ FildR PD ρ' τ a := by
  set E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) with hEd
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hM : ∀ c x, E (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c (E x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, mulVdR]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hF : x ∈ FilV PD (LL := LL) (V := V) a ↔ E x ∈ FilV PD (LL := LL) (V := V') a := by
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (filV_map_tmul PD e a y).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp _) y, ?_⟩
      rw [← filV_map_tmul PD e.symm a y, hy, hEd, congr_symm_tmul]
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
  refine and_congr (and_congr ⟨fun h g => ?_, fun h g => E.injective ?_⟩ ⟨fun h c => ?_, fun h c => E.injective ?_⟩) hF
  · rw [← hE, h g]
  · rw [hE]; exact h g
  · rw [← hM, h c, map_smul]
  · rw [hM, map_smul]; exact h c

/- English proof (translation)
Use extensionality with `x`. Conclude with `mem_fildR_iff PD e he τ a x`.
-/
theorem fildR_eq_comap (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FildR PD ρ' τ a).comap
      (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
  ext x
  exact mem_fildR_iff PD e he τ a x

/- English proof (translation)
Unfold `IsJumpV`. Rewrite using `[fildR_eq_comap PD e he, fildR_eq_comap PD e he]`. Conclude with `not_congr (Submodule.comap_injective_of_surjective (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).surjective).eq_iff`.
-/
theorem isJumpV_congr (τ : K →ₐ[Qp] LL) (a : ℤ) : IsJumpV PD ρ τ a ↔ IsJumpV PD ρ' τ a := by
  unfold IsJumpV
  rw [fildR_eq_comap PD e he, fildR_eq_comap PD e he]
  exact not_congr (Submodule.comap_injective_of_surjective
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).surjective).eq_iff

/- English proof (translation)
Unfold `multV`. Rewrite using `[fildR_eq_comap PD e he, fildR_eq_comap PD e he, ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ a)).finrank_eq, ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ (a + 1))).finrank_eq]`.
-/
theorem multV_congr (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  unfold multV
  rw [fildR_eq_comap PD e he, fildR_eq_comap PD e he,
    ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ a)).finrank_eq,
    ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ (a + 1))).finrank_eq]

end Inv

section Sums

variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}

/- English proof (translation)
Use `choose P Q h1 h2 h3 using fun x => (hc x).symm`. Take `⟨m, xs, j, hj, hjg⟩` from `h`. Use `⟨m, xs, LinearMap.pi (fun a => (Matrix.toLin' (P (xs a))) ∘ₗ (LinearMap.proj a ∘ₗ j)), ?_, fun g v => ?_⟩` and prove the remaining obligations. Introduce `v w hvw`. Apply `hj` to reduce the goal to its premises.

Use function extensionality and compare the values at `a`. Establish `h0` using `congrArg (Matrix.mulVec (Q (xs a))) (congrFun hvw a)`. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h0`. Conclude with `h0`. Use function extensionality and compare the values at `a`.

Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]`. Rewrite using `[hjg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]`.
-/
theorem isSubOfSums_of_conj (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubOfSums ρ Ms') : IsSubOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, j, hj, hjg⟩ := h
  refine ⟨m, xs, LinearMap.pi (fun a => (Matrix.toLin' (P (xs a))) ∘ₗ (LinearMap.proj a ∘ₗ j)), ?_, fun g v => ?_⟩
  · intro v w hvw
    apply hj
    funext a
    have h0 := congrArg (Matrix.mulVec (Q (xs a))) (congrFun hvw a)
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h0
    exact h0
  · funext a
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]
    rw [hjg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]

/- English proof (translation)
Use `choose P Q h1 h2 h3 using fun x => (hc x).symm`. Take `⟨m, xs, U, q, hU, hq, hqg⟩` from `h`. Set `Φ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL)` to `LinearMap.pi fun a => Matrix.toLin' (P (xs a)) ∘ₗ LinearMap.proj a`. Set `Ψ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL)` to `LinearMap.pi fun a => Matrix.toLin' (Q (xs a)) ∘ₗ LinearMap.proj a`. Establish `hΦ : ∀ u a, Φ u a = (P (xs a)).mulVec (u a)` using `fun _ _ => rfl`.

Establish `hΨ : ∀ u a, Ψ u a = (Q (xs a)).mulVec (u a)` using `fun _ _ => rfl`. Establish `hΨΦ : ∀ u, Ψ (Φ u) = u`. Introduce `u`. Use function extensionality and compare the values at `a`. Rewrite using `[hΨ, hΦ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`.

Establish `hcomm : ∀ g u, (fun a => (Ms (xs a) g).mulVec (Φ u a)) = Φ (fun a => (Ms' (xs a) g).mulVec (u a))`. Introduce `g u`. Use function extensionality and compare the values at `a`. Rewrite using `[hΦ, hΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]`. Use `⟨m, xs, U.map Φ, q ∘ₗ Ψ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Conclude with `⟨_, hU g u hu, (hcomm g u).symm⟩`. Introduce `v`. Take `⟨u, hu, rfl⟩` from `hq v`. Conclude with `⟨Φ u, ⟨u, hu, rfl⟩, by rw [LinearMap.comp_apply, hΨΦ]⟩`.

Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hcomm, hΨΦ, hΨΦ]`. Conclude with `hqg g u hu`.
-/
theorem isSubquotOfSums_of_conj (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubquotOfSums ρ Ms') : IsSubquotOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, U, q, hU, hq, hqg⟩ := h
  let Φ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (P (xs a)) ∘ₗ LinearMap.proj a
  let Ψ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (Q (xs a)) ∘ₗ LinearMap.proj a
  have hΦ : ∀ u a, Φ u a = (P (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨ : ∀ u a, Ψ u a = (Q (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨΦ : ∀ u, Ψ (Φ u) = u := by
    intro u
    funext a
    rw [hΨ, hΦ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hcomm : ∀ g u, (fun a => (Ms (xs a) g).mulVec (Φ u a)) = Φ (fun a => (Ms' (xs a) g).mulVec (u a)) := by
    intro g u
    funext a
    rw [hΦ, hΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
  refine ⟨m, xs, U.map Φ, q ∘ₗ Ψ, ?_, ?_, ?_⟩
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hU g u hu, (hcomm g u).symm⟩
  · intro v
    obtain ⟨u, hu, rfl⟩ := hq v
    exact ⟨Φ u, ⟨u, hu, rfl⟩, by rw [LinearMap.comp_apply, hΨΦ]⟩
  · rintro g _ ⟨u, hu, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcomm, hΨΦ, hΨΦ]
    exact hqg g u hu

end Sums

section SS

variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

/- English proof (translation)
Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h (W.comap (e : V →ₗ[Kf] V')) (fun g v hv => by`. Simplify using `only [Submodule.mem_comap, LinearEquiv.coe_coe, he] at hv ⊢`. Conclude with `hW g _ hv)`. Use `⟨W'.map (e : V →ₗ[Kf] V'), ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Conclude with `⟨ρ g v, hW' g v hv, he g v⟩`. Establish `h1 : IsCompl ((W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V')) (W'.map (e : V →ₗ[Kf] V'))` using `(Submodule.orderIsoMapComap e).isCompl_iff.1 hc`. Establish `h2 : (W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V') = W` using `Submodule.map_comap_eq_of_surjective e.surjective W`. Rewrite `h1` using `[h2]`.

Conclude with `h1`.
-/
theorem isSS_congr (h : IsSS ρ) : IsSS ρ' := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h (W.comap (e : V →ₗ[Kf] V')) (fun g v hv => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, he] at hv ⊢
    exact hW g _ hv)
  refine ⟨W'.map (e : V →ₗ[Kf] V'), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hW' g v hv, he g v⟩
  · have h1 : IsCompl ((W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V')) (W'.map (e : V →ₗ[Kf] V')) :=
      (Submodule.orderIsoMapComap e).isCompl_iff.1 hc
    have h2 : (W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V') = W :=
      Submodule.map_comap_eq_of_surjective e.surjective W
    rw [h2] at h1
    exact h1

end SS

section Abs

variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

/- English proof (translation)
Take `⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩` from `h`. Set `Vs' : ι → Submodule Kf V'` to `fun j => (Vs j).map (e : V →ₗ[Kf] V')`. Establish `hs' : ∀ j, Stable ρ' (Vs' j)`. Introduce and unpack `j g _ ⟨v, hv, rfl⟩`. Conclude with `⟨ρ g v, hs j g v hv, he g v⟩`.

Set `ej : ∀ j, Vs j ≃ₗ[Kf] Vs' j` to `fun j => e.submoduleMap (Vs j)`. Establish `hej : ∀ j g (v : Vs j), ej j ((ρ g).restrict (hs j g) v) = (ρ' g).restrict (hs' j g) (ej j v)`. Introduce `j g v`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `he g v`.

Use `⟨ι, hι, hd, Vs', hs', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hint`, the goal using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Take `⟨hind, htop⟩` from `hint`. Use `⟨hind.map_orderIso (Submodule.orderIsoMapComap e), ?_⟩` and prove the remaining obligations. Use `show ⨆ j, (Vs j).map (e : V →ₗ[Kf] V') = ⊤`.

Rewrite using `[← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]`. Introduce `j hj`. Apply `hne j` to reduce the goal to its premises. Establish `h1` using `congrArg (Submodule.comap (e : V →ₗ[Kf] V')) hj`. Rewrite `h1` using `[Submodule.comap_map_eq_of_injective e.injective, Submodule.comap_bot, LinearEquiv.ker]`. Then use the resulting hypothesis.

Introduce `j`. Set `c : Module.End Kf (Vs j) ≃ₗ[Kf] Module.End Kf (Vs' j)` to `LinearEquiv.conj (ej j)`. Establish `hc : ∀ g, c ((ρ g).restrict (hs j g)) = (ρ' g).restrict (hs' j g)`. Introduce `g`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[LinearEquiv.conj_apply]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hej, LinearEquiv.apply_symm_apply]`. Establish `hr : Set.range (fun g => (ρ' g).restrict (hs' j g)) = (c : Module.End Kf (Vs j) →ₗ[Kf] Module.End Kf (Vs' j)) '' Set.range (fun g => (ρ g).restrict (hs j g))`.

Use extensionality with `f`. Simplify using `only [Set.mem_range, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨_, ⟨g, rfl⟩, hc g⟩`.

Introduce and unpack `⟨_, ⟨g, rfl⟩, rfl⟩`. Conclude with `⟨g, (hc g).symm⟩`. Rewrite using `[hr, ← Submodule.map_span, hspan j, Submodule.map_top, LinearEquiv.range]`. Introduce `j j' hjj f hf`. Apply `hdist j j' hjj (((ej j).trans f).trans (ej j').symm)` to reduce the goal to its premises.

Introduce `g v`. Simplify using `only [LinearEquiv.trans_apply]`. Rewrite using `[hej, hf]`. Use `conv_lhs => rw [← LinearEquiv.apply_symm_apply (ej j') (f (ej j v)), ← hej, LinearEquiv.symm_apply_apply]`.
-/
theorem absIrrDistinct_congr (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  let Vs' : ι → Submodule Kf V' := fun j => (Vs j).map (e : V →ₗ[Kf] V')
  have hs' : ∀ j, Stable ρ' (Vs' j) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, he g v⟩
  let ej : ∀ j, Vs j ≃ₗ[Kf] Vs' j := fun j => e.submoduleMap (Vs j)
  have hej : ∀ j g (v : Vs j), ej j ((ρ g).restrict (hs j g) v) = (ρ' g).restrict (hs' j g) (ej j v) := by
    intro j g v
    apply Subtype.ext
    exact he g v
  refine ⟨ι, hι, hd, Vs', hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    obtain ⟨hind, htop⟩ := hint
    refine ⟨hind.map_orderIso (Submodule.orderIsoMapComap e), ?_⟩
    show ⨆ j, (Vs j).map (e : V →ₗ[Kf] V') = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    apply hne j
    have h1 := congrArg (Submodule.comap (e : V →ₗ[Kf] V')) hj
    rwa [Submodule.comap_map_eq_of_injective e.injective, Submodule.comap_bot, LinearEquiv.ker] at h1
  · intro j
    let c : Module.End Kf (Vs j) ≃ₗ[Kf] Module.End Kf (Vs' j) := LinearEquiv.conj (ej j)
    have hc : ∀ g, c ((ρ g).restrict (hs j g)) = (ρ' g).restrict (hs' j g) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [LinearEquiv.conj_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hej, LinearEquiv.apply_symm_apply]
    have hr : Set.range (fun g => (ρ' g).restrict (hs' j g)) =
        (c : Module.End Kf (Vs j) →ₗ[Kf] Module.End Kf (Vs' j)) '' Set.range (fun g => (ρ g).restrict (hs j g)) := by
      ext f
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, hc g⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, (hc g).symm⟩
    rw [hr, ← Submodule.map_span, hspan j, Submodule.map_top, LinearEquiv.range]
  · intro j j' hjj f hf
    apply hdist j j' hjj (((ej j).trans f).trans (ej j').symm)
    intro g v
    simp only [LinearEquiv.trans_apply]
    rw [hej, hf]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (ej j') (f (ej j v)), ← hej, LinearEquiv.symm_apply_apply]

end Abs

end Formalism.MainNotions.N.K.Norm
