import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SplitJ

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩ i j`. Use `⟨⟨(h : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `⟨((h⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩`.

Introduce `h choose A hA using fun i j => (h i j).1 choose B hB using fun i j => (h i j).2`. Establish `eA : (Matrix.of A).map f = (g : Matrix (Fin 2) (Fin 2) S)` using `by ext i j; exact hA i j`. Establish `eB : (Matrix.of B).map f = ((g⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)` using `by ext i j; exact hB i j`. Establish `inj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) R => M.map f)` using `Matrix.map_injective hf`. Use `⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.mul_inv]`. Simplify using `only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.inv_mul]`. Conclude with `Units.ext eA`.
-/
private lemma mem_range_iff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (g : GL (Fin 2) S) : g ∈ (Matrix.GeneralLinearGroup.map f).range ↔
      ∀ i j, (g : Matrix (Fin 2) (Fin 2) S) i j ∈ f.range ∧ ((g⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) i j ∈ f.range := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    refine ⟨⟨(h : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩, ?_⟩
    rw [← map_inv]
    exact ⟨((h⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩
  · intro h
    choose A hA using fun i j => (h i j).1
    choose B hB using fun i j => (h i j).2
    have eA : (Matrix.of A).map f = (g : Matrix (Fin 2) (Fin 2) S) := by ext i j; exact hA i j
    have eB : (Matrix.of B).map f = ((g⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by ext i j; exact hB i j
    have inj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) R => M.map f) := Matrix.map_injective hf
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, ?_⟩
    · simp only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.mul_inv]
    · simp only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.inv_mul]
    · exact Units.ext eA

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _`. Rewrite using `[inv_inv, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff]`. Both sides reduce to the same expression.
-/
private lemma mem_DX {K : Type} [Field K] {Δ : K} (g : GL (Fin 2) (Lsq K Δ)) :
    g ∈ DX Δ ↔ !![0, 1; -1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star = (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  change Matrix.GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _
  rw [inv_inv, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg QuadraticAlgebra.im h` as an intermediate fact. Simplify using `only [QuadraticAlgebra.im_star] at this`. Establish `h0 : x.im = 0`.

Establish `: 2 * x.im = 0` using `by linear_combination -this`. Conclude with `(mul_eq_zero.1 this).resolve_left h2`. Apply the tactic sequence `exact ⟨x.re, by ext <;> simp [h0]⟩`. Introduce and unpack `⟨y, rfl⟩`. Apply the tactic sequence `ext <;> simp`.
-/
private lemma star_fix {K : Type} [Field K] {Δ : K} (h2 : (2 : K) ≠ 0) (x : Lsq K Δ) :
    star x = x ↔ x ∈ (algebraMap K (Lsq K Δ)).range := by
  constructor
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.im_star] at this
    have h0 : x.im = 0 := by
      have : 2 * x.im = 0 := by linear_combination -this
      exact (mul_eq_zero.1 this).resolve_left h2
    exact ⟨x.re, by ext <;> simp [h0]⟩
  · rintro ⟨y, rfl⟩
    ext <;> simp

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap K (Lsq K Δ))` using `(algebraMap K (Lsq K Δ)).injective`. Establish `key : ∀ g : GL (Fin 2) (Lsq K Δ), g ∈ DX Δ ↔ ∀ i j, ((P * g * P⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j ∈ (algebraMap K (Lsq K Δ)).range`. Introduce `g`. Rewrite using `[mem_DX, hP, ← Matrix.ext_iff]`. Simplify using `only [← star_fix h2, Units.val_mul, Matrix.map_apply]`.

Set `ψ : GL (Fin 2) K →* GL (Fin 2) (Lsq K Δ)` to `(MulAut.conj P⁻¹).toMonoidHom.comp (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))`. Establish `hψ : ∀ h, P * ψ h * P⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)) h`. Introduce `h`. Express the relevant statement in the definitionally equal form `P * (P⁻¹ * _ * P⁻¹⁻¹) * P⁻¹ = _`. Use `group`.

Establish `hmem : ∀ h, ψ h ∈ DX Δ`. Introduce `h`. Rewrite using `[key, hψ]`. Conclude with `fun i j => ⟨(h : Matrix (Fin 2) (Fin 2) K) i j, rfl⟩`. Establish `hbij : Function.Bijective (ψ.codRestrict (DX Δ) hmem)`.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `e : ψ a = ψ b` using `congrArg Subtype.val hab`. Establish `e'` using `hψ a`. Rewrite `e'` using `[e, hψ, Units.ext_iff]`.

Conclude with `(Units.ext (Matrix.map_injective hinj e')).symm`. Introduce `g`. Take `⟨h, hh⟩` from `(mem_range_iff _ hinj (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)).2 fun i j => ⟨(key _).1 g.2 i j, by`. Establish `e : (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)⁻¹ = P * (g : GL (Fin 2) (Lsq K Δ))⁻¹ * P⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `(key _).1 (inv_mem g.2) i j⟩`. Use `⟨h, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e` using `hψ h`. Rewrite `e` using `[hh]`. Conclude with `mul_left_cancel (mul_right_cancel e)`.

Use `⟨(MulEquiv.ofBijective _ hbij).symm, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← hψ]`. Use `congrArg Subtype.val ((MulEquiv.ofBijective _ hbij).apply_symm_apply g)` as an intermediate fact. Conclude with `congrArg (fun x => P * x * P⁻¹) this`.
-/
private lemma exists_phi {K : Type} [Field K] {Δ : K} (h2 : (2 : K) ≠ 0) (P : GL (Fin 2) (Lsq K Δ))
    (hP : ∀ X : Matrix (Fin 2) (Fin 2) (Lsq K Δ), !![0, 1; -1, 0] * X.map star = X * !![0, 1; -1, 0] ↔
        ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))).map star = (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))) :
    ∃ φ : DX Δ ≃* GL (Fin 2) K, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)) (φ g) = P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹ := by
  have hinj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
  have key : ∀ g : GL (Fin 2) (Lsq K Δ), g ∈ DX Δ ↔
      ∀ i j, ((P * g * P⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j ∈ (algebraMap K (Lsq K Δ)).range := by
    intro g
    rw [mem_DX, hP, ← Matrix.ext_iff]
    simp only [← star_fix h2, Units.val_mul, Matrix.map_apply]
  let ψ : GL (Fin 2) K →* GL (Fin 2) (Lsq K Δ) :=
    (MulAut.conj P⁻¹).toMonoidHom.comp (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))
  have hψ : ∀ h, P * ψ h * P⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)) h := by
    intro h
    change P * (P⁻¹ * _ * P⁻¹⁻¹) * P⁻¹ = _
    group
  have hmem : ∀ h, ψ h ∈ DX Δ := by
    intro h
    rw [key, hψ]
    exact fun i j => ⟨(h : Matrix (Fin 2) (Fin 2) K) i j, rfl⟩
  have hbij : Function.Bijective (ψ.codRestrict (DX Δ) hmem) := by
    constructor
    · intro a b hab
      have e : ψ a = ψ b := congrArg Subtype.val hab
      have e' := hψ a
      rw [e, hψ, Units.ext_iff] at e'
      exact (Units.ext (Matrix.map_injective hinj e')).symm
    · intro g
      obtain ⟨h, hh⟩ := (mem_range_iff _ hinj (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)).2 fun i j => ⟨(key _).1 g.2 i j, by
        have e : (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)⁻¹ = P * (g : GL (Fin 2) (Lsq K Δ))⁻¹ * P⁻¹ := by group
        rw [e]
        exact (key _).1 (inv_mem g.2) i j⟩
      refine ⟨h, Subtype.ext ?_⟩
      have e := hψ h
      rw [hh] at e
      exact mul_left_cancel (mul_right_cancel e)
  refine ⟨(MulEquiv.ofBijective _ hbij).symm, fun g => ?_⟩
  rw [← hψ]
  have := congrArg Subtype.val ((MulEquiv.ofBijective _ hbij).apply_symm_apply g)
  exact congrArg (fun x => P * x * P⁻¹) this

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ hl`. Use `haveI := hl.frac`. Establish `h2 : (2 : K) ≠ 0`. Use `(hl.two.map (algebraMap O K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Take `⟨P, hPi, hP⟩` from `UpperTheory.V.Z.Sym.Loc.splitJ O K Δ hl`. Take `⟨φ, hφ⟩` from `exists_phi h2 P hP`. Establish `hinj : Function.Injective (algebraMap K (Lsq K Δ))` using `(algebraMap K (Lsq K Δ)).injective`. Establish `minj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) K => M.map (algebraMap K (Lsq K Δ)))` using `Matrix.map_injective hinj`. Establish `hm : ∀ g, (φ g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) = (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt g * (P⁻¹ : GL (Fin 2) (Lsq K Δ))` using `fun g => congrArg Units.val (hφ g)`.

Establish `hdet : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).det = (mt g).det`. Introduce `g`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_units_conj]`. Establish `htr : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).trace = (mt g).trace`. Introduce `g`.

Rewrite using `[← Matrix.trace_units_conj P, ← hm]`. Simplify using `[Matrix.trace_fin_two]`. Use `⟨φ, fun g => ?_, fun z g => ?_, hdet, fun τ γ j hγ hj => ?_⟩` and prove the remaining obligations. Set `H` to `(Matrix.GeneralLinearGroup.map (n := Fin 2) ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range`. Establish `hr : ∀ x : Lsq K Δ, x ∈ ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).range ↔ IsIntegral O x` using `fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩`.

Establish `hH : ∀ x : GL (Fin 2) (Lsq K Δ), x ∈ H ↔ ∀ i j, IsIntegral O ((x : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) ∧ IsIntegral O (((x⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j)`. Introduce `x`. Rewrite using `[mem_range_iff _ Subtype.val_injective]`. Simplify using `only [hr]`. Establish `hPH : P ∈ H` using `(hH P).2 hPi`.

Establish `hr' : ∀ x : K, IsIntegral O (algebraMap K (Lsq K Δ) x) ↔ x ∈ (algebraMap O K).range`. Introduce `x`. Rewrite using `[isIntegral_algebraMap_iff hinj, IsIntegrallyClosed.isIntegral_iff]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `φ g ∈ (Matrix.GeneralLinearGroup.map (algebraMap O K)).range ↔ (g : GL (Fin 2) (Lsq K Δ)) ∈ H`.

Rewrite using `[← H.mul_mem_cancel_left hPH, ← H.mul_mem_cancel_right (inv_mem hPH), ← hφ, hH, mem_range_iff _ (IsFractionRing.injective O K), ← map_inv (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))]`. Simplify using `only [← hr']`. Both sides reduce to the same expression. Rewrite using `[Units.ext_iff, ← minj.eq_iff] beta_reduce`. Rewrite using `[hm, Units.mul_inv_eq_iff_eq_mul]`.

Establish `e : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z)`. Use extensionality with `i j : 1`. Apply the tactic sequence `by_cases h : i = j <;> simp [h]`. Rewrite using `[e, (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq, Units.mul_right_inj]`. Both sides reduce to the same expression.

Establish `hd : (φ γ : Matrix (Fin 2) (Fin 2) K).det = 1` using `hinj (by rw [hdet, hγ.1, map_one])`. Establish `ht : (φ γ : Matrix (Fin 2) (Fin 2) K).trace = τ` using `hinj (by rw [htr, hγ.2])`. Establish `hu : (φ γ : Matrix (Fin 2) (Fin 2) K) * (φ γ : Matrix (Fin 2) (Fin 2) K) = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) + τ • (φ γ : Matrix (Fin 2) (Fin 2) K)`. Rewrite `hd` using `[Matrix.det_fin_two]`. Rewrite `ht` using `[Matrix.trace_fin_two]`.

Rewrite using `[← ht]`. Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination -hd`. Establish `hω : QuadraticAlgebra.lift ⟨_, hu⟩ (ω : Etau K τ) = (φ γ : Matrix (Fin 2) (Fin 2) K)`. Express the relevant statement in the definitionally equal form `(ω : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (ω : Etau K τ).im • _ = _`.

Simplify using the standard rewrite rules. Use `⟨QuadraticAlgebra.lift ⟨_, hu⟩, hω, by rw [hω, ht], fun z => Units.ext (minj ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ((z : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (z : Etau K τ).im • (φ γ : Matrix (Fin 2) (Fin 2) K)).map _`. Use `beta_reduce`. Rewrite using `[hm, hj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, ← hm, mul_one, Units.mul_inv]`.

Use extensionality with `a b : 1`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply]`. Apply the tactic sequence `by_cases h : a = b <;> simp [h, Algebra.smul_def]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.dIso :
    UpperTheory.V.Z.Sym.Loc.DIso := by
  intro O K _ _ _ _ _ Δ hl
  haveI := hl.frac
  have h2 : (2 : K) ≠ 0 := by
    have := (hl.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨P, hPi, hP⟩ := UpperTheory.V.Z.Sym.Loc.splitJ O K Δ hl
  obtain ⟨φ, hφ⟩ := exists_phi h2 P hP
  have hinj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
  have minj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) K => M.map (algebraMap K (Lsq K Δ))) :=
    Matrix.map_injective hinj
  have hm : ∀ g, (φ g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) =
      (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt g * (P⁻¹ : GL (Fin 2) (Lsq K Δ)) := fun g => congrArg Units.val (hφ g)
  have hdet : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).det = (mt g).det := by
    intro g
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_units_conj]
  have htr : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).trace = (mt g).trace := by
    intro g
    rw [← Matrix.trace_units_conj P, ← hm]
    simp [Matrix.trace_fin_two]
  refine ⟨φ, fun g => ?_, fun z g => ?_, hdet, fun τ γ j hγ hj => ?_⟩
  · let H := (Matrix.GeneralLinearGroup.map (n := Fin 2)
      ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range
    have hr : ∀ x : Lsq K Δ, x ∈ ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).range ↔
        IsIntegral O x := fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have hH : ∀ x : GL (Fin 2) (Lsq K Δ), x ∈ H ↔ ∀ i j, IsIntegral O ((x : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) ∧
        IsIntegral O (((x⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) := by
      intro x
      rw [mem_range_iff _ Subtype.val_injective]
      simp only [hr]
    have hPH : P ∈ H := (hH P).2 hPi
    have hr' : ∀ x : K, IsIntegral O (algebraMap K (Lsq K Δ) x) ↔ x ∈ (algebraMap O K).range := by
      intro x
      rw [isIntegral_algebraMap_iff hinj, IsIntegrallyClosed.isIntegral_iff]
      rfl
    change φ g ∈ (Matrix.GeneralLinearGroup.map (algebraMap O K)).range ↔ (g : GL (Fin 2) (Lsq K Δ)) ∈ H
    rw [← H.mul_mem_cancel_left hPH, ← H.mul_mem_cancel_right (inv_mem hPH), ← hφ, hH,
      mem_range_iff _ (IsFractionRing.injective O K), ← map_inv (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))]
    simp only [← hr']
    rfl
  · rw [Units.ext_iff, ← minj.eq_iff]
    beta_reduce
    rw [hm, Units.mul_inv_eq_iff_eq_mul]
    have e : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) =
        Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := by
      ext i j : 1
      by_cases h : i = j <;> simp [h]
    rw [e, (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq, Units.mul_right_inj]
    rfl
  · have hd : (φ γ : Matrix (Fin 2) (Fin 2) K).det = 1 := hinj (by rw [hdet, hγ.1, map_one])
    have ht : (φ γ : Matrix (Fin 2) (Fin 2) K).trace = τ := hinj (by rw [htr, hγ.2])
    have hu : (φ γ : Matrix (Fin 2) (Fin 2) K) * (φ γ : Matrix (Fin 2) (Fin 2) K) =
        (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) + τ • (φ γ : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.det_fin_two] at hd
      rw [Matrix.trace_fin_two] at ht
      rw [← ht]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination -hd
    have hω : QuadraticAlgebra.lift ⟨_, hu⟩ (ω : Etau K τ) = (φ γ : Matrix (Fin 2) (Fin 2) K) := by
      change (ω : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (ω : Etau K τ).im • _ = _
      simp
    refine ⟨QuadraticAlgebra.lift ⟨_, hu⟩, hω, by rw [hω, ht], fun z => Units.ext (minj ?_)⟩
    change _ = ((z : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (z : Etau K τ).im • (φ γ : Matrix (Fin 2) (Fin 2) K)).map _
    beta_reduce
    rw [hm, hj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, ← hm,
      mul_one, Units.mul_inv]
    ext a b : 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply]
    by_cases h : a = b <;> simp [h, Algebra.smul_def]
