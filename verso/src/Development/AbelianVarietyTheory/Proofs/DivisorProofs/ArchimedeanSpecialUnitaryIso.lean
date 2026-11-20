import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.InfUnitarySU

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Simplify using `[hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct, star_sum]`.
-/
theorem star_mulVec_map (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    star (M *ᵥ w) = M.map star *ᵥ star w := by
  ext i
  simp [mulVec, dotProduct, star_sum]

/- English proof (translation)
Rewrite using `[dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]`.
-/
theorem mulVec_dot (M : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

/- English proof (translation)
Rewrite using `[hermC_eq_dot, star_mulVec_map, mulVec_dot]`. Simplify using `only [mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map star) *ᵥ star w) := by
  rw [hermC_eq_dot, star_mulVec_map, mulVec_dot]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_of_dot (N N' : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ u w : Fin r → ℂ, u ⬝ᵥ (N *ᵥ star w) = u ⬝ᵥ (N' *ᵥ star w)) : N = N' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa using this

/- English proof (translation)
Simplify using `[Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc]`.
-/
theorem transpose_form (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    Mᵀ * G.map τ * M.map star = (Mᴴ * Gᵀ.map τ * M)ᵀ := by
  simp [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc]

/- English proof (translation)
Establish `hG : (Gᵀ.map τ)ᵀ = G.map τ` using `by simp [Matrix.transpose_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : Mᵀ * G.map τ * M.map star = G.map τ` using `eq_of_dot _ _ fun u w => by rw [← hermC_mulVec, h, hermC_eq_dot]`. Rewrite `key` using `[transpose_form, ← hG]`.

Conclude with `Matrix.transpose_injective key`. Introduce `h u w`. Rewrite using `[hermC_mulVec, transpose_form, h, hG, hermC_eq_dot]`.
-/
theorem hermC_invariant_iff (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) ↔ Mᴴ * Gᵀ.map τ * M = Gᵀ.map τ := by
  have hG : (Gᵀ.map τ)ᵀ = G.map τ := by simp [Matrix.transpose_map]
  constructor
  · intro h
    have key : Mᵀ * G.map τ * M.map star = G.map τ :=
      eq_of_dot _ _ fun u w => by rw [← hermC_mulVec, h, hermC_eq_dot]
    rw [transpose_form, ← hG] at key
    exact Matrix.transpose_injective key
  · intro h u w
    rw [hermC_mulVec, transpose_form, h, hG, hermC_eq_dot]

end Forms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]

/- English proof (translation)
Establish `hinj : ∀ x y : Ainf F ⊗[F] E, (∀ ρ, θ ρ x = θ ρ y) → x = y` using `fun x y h => Φ.injective (funext fun ρ => by rw [hΦ, hΦ, h])`. Establish `hminj : ∀ X Y : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E), (∀ ρ, X.map (θ ρ) = Y.map (θ ρ)) → X = Y` using `fun X Y h => Matrix.ext fun i j => hinj _ _ fun ρ => congrFun (congrFun (h ρ) i) j`. Establish `hlift : ∀ (x : Ψ → ℂ) ρ, θ ρ (Φ.symm x) = x ρ` using `fun x ρ => by rw [← hΦ, Φ.apply_symm_apply]`. Establish `hcont : ∀ ρ, Continuous (θ ρ)` using `fun ρ => by`. Establish `e : (θ ρ : Ainf F ⊗[F] E → ℂ) = fun z => Φ z ρ` using `funext fun z => (hΦ z ρ).symm`.

Rewrite using `[e]`. Conclude with `(continuous_apply ρ).comp Φ.continuous`. Establish `hform : ∀ ρ (X : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)), (Formalism.UG.cT (sigR (Ainf F) σ) X * JR (Ainf F) Gᵀ * X).map (θ ρ) = (X.map (θ ρ))ᴴ * Gᵀ.map ρ.1 * X.map (θ ρ)` using `fun ρ X => by`. Rewrite using `[GlobalTheory.Member.Arch.form_map _ (θ ρ) (GlobalTheory.Mem.VolExists.infEmb_sigR hσ (hθ ρ)), GlobalTheory.Mem.VolExists.JR_map Gᵀ (hθ ρ)]`. Establish `hJ : ∀ ρ, (JR (Ainf F) Gᵀ).map (θ ρ) = Gᵀ.map ρ.1` using `fun ρ => GlobalTheory.Mem.VolExists.JR_map Gᵀ (hθ ρ)`.

Set `K` to `((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ Gᵀ).subtype).ker : Subgroup (HA (Ainf F) σ Gᵀ))`. Set `mat : K → GL (Fin r) (Ainf F ⊗[F] E)` to `fun g => HA.mat (Ainf F) σ Gᵀ g.1`. Establish `hmatU : ∀ g : K, Formalism.UG.cT (sigR (Ainf F) σ) (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) * JR (Ainf F) Gᵀ * (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) = JR (Ainf F) Gᵀ` using `fun g => (g.1 : HR (Ainf F) σ Gᵀ).2`. Establish `hmatD : ∀ g : K, (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).det = 1` using `fun g => by`. Establish `h` using `g.2`.

Rewrite `h` using `[MonoidHom.mem_ker, Units.ext_iff]`. Conclude with `h.trans Units.val_one`. Set `fw : K → Ψ → GL (Fin r) ℂ` to `fun g ρ => Units.map ((θ ρ).mapMatrix (m := Fin r)).toMonoidHom (mat g)`. Establish `hfw : ∀ g ρ, ((fw g ρ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ)` using `fun g ρ => rfl`. Establish `hfwm : ∀ g, fw g ∈ realSU Ψ G` using `fun g ρ => by`.

Use `⟨?_, (hermC_invariant_iff ρ.1 G _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[hfw, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hmatD, map_one]`. Rewrite using `[hfw, ← hform, hmatU, hJ]`. Set `lm : (Ψ → Matrix (Fin r) (Fin r) ℂ) → Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)` to `fun t i j => Φ.symm fun ρ => t ρ i j`. Establish `hlm : ∀ t ρ, (lm t).map (θ ρ) = t ρ` using `fun t ρ => Matrix.ext fun i j => hlift _ ρ`.

Set `ts : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ` to `fun t ρ => ((t.1 ρ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)`. Set `tsi : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ` to `fun t ρ => (((t.1 ρ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)`. Establish `hmap1 : ∀ ρ, (1 : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ) = 1` using `fun ρ => Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h1 : ∀ t, lm (ts t) * lm (tsi t) = 1` using `fun t => hminj _ _ fun ρ => by`. Rewrite using `[Matrix.map_mul, hlm, hlm, hmap1]`.

Conclude with `(t.1 ρ).mul_inv`. Establish `h2 : ∀ t, lm (tsi t) * lm (ts t) = 1` using `fun t => hminj _ _ fun ρ => by`. Rewrite using `[Matrix.map_mul, hlm, hlm, hmap1]`. Conclude with `(t.1 ρ).inv_mul`. Set `U : realSU Ψ G → GL (Fin r) (Ainf F ⊗[F] E)` to `fun t => ⟨lm (ts t), lm (tsi t), h1 t, h2 t⟩`.

Establish `hUm : ∀ t, U t ∈ HR (Ainf F) σ Gᵀ` using `fun t => hminj _ _ fun ρ => by show (Formalism.UG.cT (sigR (Ainf F) σ) (lm (ts t)) * JR (Ainf F) Gᵀ * lm (ts t)).map (θ ρ) = _`. Rewrite using `[hform, hJ, hlm]`. Conclude with `(hermC_invariant_iff ρ.1 G _).1 (t.2 ρ).2`. Establish `hUd : ∀ t, (lm (ts t)).det = 1` using `fun t => hinj _ _ fun ρ => by`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hlm, map_one]`.

Conclude with `(t.2 ρ).1`. Set `bw : realSU Ψ G → K` to `fun t => ⟨(⟨U t, hUm t⟩ : HR (Ainf F) σ Gᵀ), by`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff]`. Conclude with `hUd t⟩`. Establish `hbw : ∀ t, mat (bw t) = U t` using `fun t => rfl`.

Establish `hm : Continuous fun g : K => (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E))` using `Units.continuous_val.comp ((continuous_subtype_val (p := (· ∈ HR (Ainf F) σ Gᵀ))).comp continuous_subtype_val)`. Establish `hmi : Continuous fun g : K => (((mat g)⁻¹ : GL (Fin r) (Ainf F ⊗[F] E)) : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E))` using `Units.continuous_coe_inv.comp ((continuous_subtype_val (p := (· ∈ HR (Ainf F) σ Gᵀ))).comp continuous_subtype_val)`. Establish `hts : ∀ ρ, Continuous fun t : realSU Ψ G => ts t ρ` using `fun ρ => Units.continuous_val.comp ((continuous_apply ρ).comp continuous_subtype_val)`. Establish `htsi : ∀ ρ, Continuous fun t : realSU Ψ G => tsi t ρ` using `fun ρ => Units.continuous_coe_inv.comp ((continuous_apply ρ).comp continuous_subtype_val)`. Establish `hlmc : ∀ s : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ ρ, Continuous fun t => s t ρ) → Continuous fun t => lm (s t)` using `fun s hs => continuous_pi fun i => continuous_pi fun j => Φ.continuous_symm.comp (continuous_pi fun ρ => (hs ρ).matrix_elem i j)`.

Establish `hU : Continuous U` using `Units.continuous_iff.2 ⟨hlmc ts hts, hlmc tsi htsi⟩`. Use `⟨{ toFun := fun g => ⟨fw g, hfwm g⟩ invFun := bw left_inv := fun g => ?_ right_inv := fun t => ?_ map_mul' := fun g h => ?_ continuous_toFun := ?_ continuous_invFun := ?_ }, fun g ρ => rfl⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `hminj _ _ fun ρ => (hlm _ ρ).trans (hfw g ρ)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `ρ`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hlm (ts t) ρ`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `ρ`. Apply `Units.ext` to reduce the goal to its premises. Use `show (((mat g * mat h : GL (Fin r) (Ainf F ⊗[F] E)) : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E))).map (θ ρ) = (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ) * (mat h : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ)`. Rewrite using `[Units.val_mul, Matrix.map_mul]`.

Use `Continuous.subtype_mk (continuous_pi fun ρ => Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `hm.matrix_map (hcont ρ)`. Conclude with `hmi.matrix_map (hcont ρ)`. Conclude with `Continuous.subtype_mk (Continuous.subtype_mk hU hUm) _`.
-/
theorem exists_equiv_of_isCMExt {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf F ⊗[F] E →+* ℂ)) (hθ : ∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ))
    (Φ : (Ainf F ⊗[F] E) ≃ₜ (Ψ → ℂ)) (hΦ : ∀ z ρ, Φ z ρ = θ ρ z) :
    ∃ f : ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ Gᵀ).subtype).ker : Subgroup (HA (Ainf F) σ Gᵀ))
        ≃ₜ* realSU Ψ G,
      ∀ g ρ, ((f g : Ψ → GL (Fin r) ℂ) ρ : Matrix (Fin r) (Fin r) ℂ) =
        ((HA.mat (Ainf F) σ Gᵀ g.1 : GL (Fin r) (Ainf F ⊗[F] E)) : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map
          (θ ρ) := by
  classical
  have hinj : ∀ x y : Ainf F ⊗[F] E, (∀ ρ, θ ρ x = θ ρ y) → x = y := fun x y h =>
    Φ.injective (funext fun ρ => by rw [hΦ, hΦ, h])
  have hminj : ∀ X Y : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E), (∀ ρ, X.map (θ ρ) = Y.map (θ ρ)) → X = Y :=
    fun X Y h => Matrix.ext fun i j => hinj _ _ fun ρ => congrFun (congrFun (h ρ) i) j
  have hlift : ∀ (x : Ψ → ℂ) ρ, θ ρ (Φ.symm x) = x ρ := fun x ρ => by rw [← hΦ, Φ.apply_symm_apply]
  have hcont : ∀ ρ, Continuous (θ ρ) := fun ρ => by
    have e : (θ ρ : Ainf F ⊗[F] E → ℂ) = fun z => Φ z ρ := funext fun z => (hΦ z ρ).symm
    rw [e]
    exact (continuous_apply ρ).comp Φ.continuous
  have hform : ∀ ρ (X : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)),
      (Formalism.UG.cT (sigR (Ainf F) σ) X * JR (Ainf F) Gᵀ * X).map (θ ρ) =
        (X.map (θ ρ))ᴴ * Gᵀ.map ρ.1 * X.map (θ ρ) := fun ρ X => by
    rw [GlobalTheory.Member.Arch.form_map _ (θ ρ) (GlobalTheory.Mem.VolExists.infEmb_sigR hσ (hθ ρ)),
      GlobalTheory.Mem.VolExists.JR_map Gᵀ (hθ ρ)]
  have hJ : ∀ ρ, (JR (Ainf F) Gᵀ).map (θ ρ) = Gᵀ.map ρ.1 := fun ρ => GlobalTheory.Mem.VolExists.JR_map Gᵀ (hθ ρ)

  let K := ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ Gᵀ).subtype).ker : Subgroup (HA (Ainf F) σ Gᵀ))
  let mat : K → GL (Fin r) (Ainf F ⊗[F] E) := fun g => HA.mat (Ainf F) σ Gᵀ g.1
  have hmatU : ∀ g : K, Formalism.UG.cT (sigR (Ainf F) σ) (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) * JR (Ainf F) Gᵀ *
      (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) = JR (Ainf F) Gᵀ := fun g => (g.1 : HR (Ainf F) σ Gᵀ).2
  have hmatD : ∀ g : K, (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).det = 1 := fun g => by
    have h := g.2
    rw [MonoidHom.mem_ker, Units.ext_iff] at h
    exact h.trans Units.val_one

  let fw : K → Ψ → GL (Fin r) ℂ := fun g ρ => Units.map ((θ ρ).mapMatrix (m := Fin r)).toMonoidHom (mat g)
  have hfw : ∀ g ρ, ((fw g ρ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ) :=
    fun g ρ => rfl
  have hfwm : ∀ g, fw g ∈ realSU Ψ G := fun g ρ => by
    refine ⟨?_, (hermC_invariant_iff ρ.1 G _).2 ?_⟩
    · rw [hfw, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hmatD, map_one]
    · rw [hfw, ← hform, hmatU, hJ]

  let lm : (Ψ → Matrix (Fin r) (Fin r) ℂ) → Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) :=
    fun t i j => Φ.symm fun ρ => t ρ i j
  have hlm : ∀ t ρ, (lm t).map (θ ρ) = t ρ := fun t ρ => Matrix.ext fun i j => hlift _ ρ
  let ts : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ := fun t ρ => ((t.1 ρ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  let tsi : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ :=
    fun t ρ => (((t.1 ρ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  have hmap1 : ∀ ρ, (1 : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ) = 1 := fun ρ =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : ∀ t, lm (ts t) * lm (tsi t) = 1 := fun t => hminj _ _ fun ρ => by
    rw [Matrix.map_mul, hlm, hlm, hmap1]
    exact (t.1 ρ).mul_inv
  have h2 : ∀ t, lm (tsi t) * lm (ts t) = 1 := fun t => hminj _ _ fun ρ => by
    rw [Matrix.map_mul, hlm, hlm, hmap1]
    exact (t.1 ρ).inv_mul
  let U : realSU Ψ G → GL (Fin r) (Ainf F ⊗[F] E) := fun t => ⟨lm (ts t), lm (tsi t), h1 t, h2 t⟩
  have hUm : ∀ t, U t ∈ HR (Ainf F) σ Gᵀ := fun t => hminj _ _ fun ρ => by
    show (Formalism.UG.cT (sigR (Ainf F) σ) (lm (ts t)) * JR (Ainf F) Gᵀ * lm (ts t)).map (θ ρ) = _
    rw [hform, hJ, hlm]
    exact (hermC_invariant_iff ρ.1 G _).1 (t.2 ρ).2
  have hUd : ∀ t, (lm (ts t)).det = 1 := fun t => hinj _ _ fun ρ => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hlm, map_one]
    exact (t.2 ρ).1
  let bw : realSU Ψ G → K := fun t => ⟨(⟨U t, hUm t⟩ : HR (Ainf F) σ Gᵀ), by
    rw [MonoidHom.mem_ker, Units.ext_iff]
    exact hUd t⟩
  have hbw : ∀ t, mat (bw t) = U t := fun t => rfl
  have hm : Continuous fun g : K => (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) :=
    Units.continuous_val.comp ((continuous_subtype_val (p := (· ∈ HR (Ainf F) σ Gᵀ))).comp continuous_subtype_val)
  have hmi : Continuous fun g : K => (((mat g)⁻¹ : GL (Fin r) (Ainf F ⊗[F] E)) : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)) :=
    Units.continuous_coe_inv.comp ((continuous_subtype_val (p := (· ∈ HR (Ainf F) σ Gᵀ))).comp continuous_subtype_val)
  have hts : ∀ ρ, Continuous fun t : realSU Ψ G => ts t ρ := fun ρ =>
    Units.continuous_val.comp ((continuous_apply ρ).comp continuous_subtype_val)
  have htsi : ∀ ρ, Continuous fun t : realSU Ψ G => tsi t ρ := fun ρ =>
    Units.continuous_coe_inv.comp ((continuous_apply ρ).comp continuous_subtype_val)
  have hlmc : ∀ s : realSU Ψ G → Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ ρ, Continuous fun t => s t ρ) →
      Continuous fun t => lm (s t) := fun s hs =>
    continuous_pi fun i => continuous_pi fun j => Φ.continuous_symm.comp
      (continuous_pi fun ρ => (hs ρ).matrix_elem i j)
  have hU : Continuous U := Units.continuous_iff.2 ⟨hlmc ts hts, hlmc tsi htsi⟩
  refine ⟨{ toFun := fun g => ⟨fw g, hfwm g⟩
            invFun := bw
            left_inv := fun g => ?_
            right_inv := fun t => ?_
            map_mul' := fun g h => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g ρ => rfl⟩
  · apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hminj _ _ fun ρ => (hlm _ ρ).trans (hfw g ρ)
  · apply Subtype.ext
    funext ρ
    apply Units.ext
    exact hlm (ts t) ρ
  · apply Subtype.ext
    funext ρ
    apply Units.ext
    show (((mat g * mat h : GL (Fin r) (Ainf F ⊗[F] E)) : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E))).map (θ ρ) =
      (mat g : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ) * (mat h : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E)).map (θ ρ)
    rw [Units.val_mul, Matrix.map_mul]
  · refine Continuous.subtype_mk (continuous_pi fun ρ => Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact hm.matrix_map (hcont ρ)
    · exact hmi.matrix_map (hcont ρ)
  · exact Continuous.subtype_mk (Continuous.subtype_mk hU hUm) _

end Main

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩`.
-/
theorem isCMExt_maxReal' (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

/- English proof (translation)
Introduce `E _ _ _ r G Ψ θ hθ Φ hΦ`. Conclude with `exists_equiv_of_isCMExt (isCMExt_maxReal' E) r G Ψ θ hθ Φ hΦ`.
-/
theorem infSU_equiv_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∀ Φ : (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) ≃ₜ (Ψ → ℂ), (∀ z ρ, Φ z ρ = θ ρ z) →
    ∃ f : ((Matrix.GeneralLinearGroup.det.comp
        (HR (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ).subtype).ker :
          Subgroup (HA (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ)) ≃ₜ* realSU Ψ G,
      ∀ g ρ, ((f g : Ψ → GL (Fin r) ℂ) ρ : Matrix (Fin r) (Fin r) ℂ) =
        ((HA.mat (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ g.1 :
          GL (Fin r) (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
            Matrix (Fin r) (Fin r) (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).map (θ ρ) := by
  intro E _ _ _ r G Ψ θ hθ Φ hΦ
  exact exists_equiv_of_isCMExt (isCMExt_maxReal' E) r G Ψ θ hθ Φ hΦ

end GlobalTheory.InfUnitarySU
