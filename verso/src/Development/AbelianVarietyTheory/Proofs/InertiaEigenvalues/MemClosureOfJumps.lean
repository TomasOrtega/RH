import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadicStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.HodgeTateCochar

/- English proof (translation)
Introduce `l _ P AI hT K LL K'' m r₁ hLL hK Pm k heig f hf t ht`. Use `letI act : MulSemiringAction ↥(GK K'') ℂ_[l] := { smul := fun g x => Per.σC (g : GQ l) x one_smul := fun x => GlobalTheory.RingBasics.σC_one x mul_smul := fun g h x => GlobalTheory.RingBasics.σC_mul (g : GQ l) (h : GQ l) x smul_zero := fun g => map_zero (Per.σC (g : GQ l)) smul_a …`. Set `χ : ↥(GK K'') →* ℂ_[l]ˣ` to `((Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom).comp (P.χQ.comp (GK K'').subtype))⁻¹`. Establish `hχ : ∀ (g : ↥(GK K'')) (n : ℤ), ((χ g ^ n : ℂ_[l]ˣ) : ℂ_[l]) = ((((P.χQ (g : GQ l)) ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])`. Introduce `g n`.

Establish `e : χ g ^ n = Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom (P.χQ (g : GQ l) ^ (-n))`. Rewrite using `[map_zpow]`. Simplify using `[χ, zpow_neg, inv_zpow']`. Rewrite using `[e]`. Both sides reduce to the same expression.

Set `φ : ↥LL.1 →+* ℂ_[l]` to `(UniformSpace.Completion.coeRingHom).comp (algebraMap ↥LL.1 (Om l))`. Set `ρ : ↥(GK K'') →* Matrix.GeneralLinearGroup (Fin m) ℂ_[l]` to `(mapRep φ r₁).comp (Subgroup.inclusion (GK_le hK))`. Establish `hρ : ∀ (γ : ↥(GK K'')) i j, (ρ γ : Matrix (Fin m) (Fin m) ℂ_[l]) i j = ((((r₁ (Subgroup.inclusion (GK_le hK) γ) : Matrix (Fin m) (Fin m) ↥LL.1) i j : ↥LL.1) : Om l) : ℂ_[l])` using `fun _ _ _ => rfl`. Establish `key` using `GlobalTheory.T.vanish_at_hodgeTate_cocharacter (C := ℂ_[l]) (Γ := ↥(GK K'')) (n := Fin m) χ ?_ ρ ?_ Pm k ?_ f ?_ (Units.mk0 t ht)`. Simplify `key` using `[Units.val_zpow_eq_zpow_val]`.

Introduce `n hn x H`. Use `GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (-n) (neg_ne_zero.mpr hn) x fun g => ?_` and prove the remaining obligations. Conclude with `(H g).trans (by rw [hχ])`. Introduce `g γ i j`. Express the relevant statement in the definitionally equal form `Per.σC (g : GQ l) _ = _`.

Rewrite using `[hρ, GlobalTheory.RingBasics.σC_coe]`. Use `congr 1`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (hLL (r₁ _ i j).2)`. Introduce `g`. Establish `h1` using `heig (Subgroup.inclusion (GK_le hK) g) g.2`.

Express the relevant statement in the definitionally equal form `(ρ g : Matrix (Fin m) (Fin m) ℂ_[l]) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = _`. Simplify using `only [hχ]`. Conclude with `h1`. Introduce `γ`. Conclude with `hf _ γ.2`.
-/
theorem poly_vanish : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL K'' : FinExt l) (m : ℕ) (r₁ : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    LL.1 ≤ K''.1 → K.1 ≤ K''.1 → ∀ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      (r₁ g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) *
        (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) =
      (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) *
        Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]))) →
    ∀ f : MvPolynomial (Fin m × Fin m) ℂ_[l],
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      MvPolynomial.eval (fun ij => ((((r₁ g : Matrix (Fin m) (Fin m) ↥LL.1) ij.1 ij.2 : ↥LL.1) : Om l) : ℂ_[l])) f = 0) →
    ∀ t : ℂ_[l], t ≠ 0 →
      MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) *
        ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) : Matrix (Fin m) (Fin m) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT K LL K'' m r₁ hLL hK Pm k heig f hf t ht
  letI act : MulSemiringAction ↥(GK K'') ℂ_[l] :=
    { smul := fun g x => Per.σC (g : GQ l) x
      one_smul := fun x => GlobalTheory.RingBasics.σC_one x
      mul_smul := fun g h x => GlobalTheory.RingBasics.σC_mul (g : GQ l) (h : GQ l) x
      smul_zero := fun g => map_zero (Per.σC (g : GQ l))
      smul_add := fun g x y => map_add (Per.σC (g : GQ l)) x y
      smul_one := fun g => map_one (Per.σC (g : GQ l))
      smul_mul := fun g x y => map_mul (Per.σC (g : GQ l)) x y }
  let χ : ↥(GK K'') →* ℂ_[l]ˣ :=
    ((Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom).comp (P.χQ.comp (GK K'').subtype))⁻¹
  have hχ : ∀ (g : ↥(GK K'')) (n : ℤ), ((χ g ^ n : ℂ_[l]ˣ) : ℂ_[l]) =
      ((((P.χQ (g : GQ l)) ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
    intro g n
    have e : χ g ^ n = Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom (P.χQ (g : GQ l) ^ (-n)) := by
      rw [map_zpow]
      simp [χ, zpow_neg, inv_zpow']
    rw [e]
    rfl
  let φ : ↥LL.1 →+* ℂ_[l] := (UniformSpace.Completion.coeRingHom).comp (algebraMap ↥LL.1 (Om l))
  let ρ : ↥(GK K'') →* Matrix.GeneralLinearGroup (Fin m) ℂ_[l] :=
    (mapRep φ r₁).comp (Subgroup.inclusion (GK_le hK))
  have hρ : ∀ (γ : ↥(GK K'')) i j, (ρ γ : Matrix (Fin m) (Fin m) ℂ_[l]) i j =
      ((((r₁ (Subgroup.inclusion (GK_le hK) γ) : Matrix (Fin m) (Fin m) ↥LL.1) i j : ↥LL.1) : Om l) : ℂ_[l]) :=
    fun _ _ _ => rfl
  have key := GlobalTheory.T.vanish_at_hodgeTate_cocharacter (C := ℂ_[l]) (Γ := ↥(GK K'')) (n := Fin m) χ ?_ ρ ?_ Pm k ?_ f ?_ (Units.mk0 t ht)
  · simpa [Units.val_zpow_eq_zpow_val] using key
  · intro n hn x H
    refine GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (-n) (neg_ne_zero.mpr hn) x fun g => ?_
    exact (H g).trans (by rw [hχ])
  · intro g γ i j
    change Per.σC (g : GQ l) _ = _
    rw [hρ, GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (hLL (r₁ _ i j).2)
  · intro g
    have h1 := heig (Subgroup.inclusion (GK_le hK) g) g.2
    change (ρ g : Matrix (Fin m) (Fin m) ℂ_[l]) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = _
    simp only [hχ]
    exact h1
  · intro γ
    exact hf _ γ.2

/- English proof (translation)
Introduce `l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r τ J hJ hcard`. Take `⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', -, hcnt⟩` from `hJ`. Use `haveI := Bw.Kw.2`. Use `haveI := LL'.2`. Set `τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l` to `LL'.1.val.comp τ'`.

Set `g : GQ l` to `AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)`. Establish `hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l)` using `fun x => τo.liftNormal_commutes (Om l) x`. Take `⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l)` from `⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l), LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩`. Establish `hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1` using `GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁`. Establish `hK₁LL : K₁.1 ≤ LL'.1`.

Rewrite using `[hK₁]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `hg ⟨x, hx⟩` as an intermediate fact. Simplify using `only at this`. Express the relevant statement in the definitionally equal form `g x ∈ LL'.1`.

Rewrite using `[this]`. Conclude with `(τ' ⟨x, hx⟩).2`. Set `cj : ↥(GK K₁) →* ↥(GK Bw.Kw)` to `{ toFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }`. Set `r₀ : ↥(GK Bw.Kw) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1` to `r'.comp Bw.e.symm.toMonoidHom`. Set `r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1` to `r₀.comp cj`.

Establish `hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = g * h * g⁻¹ → (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h`. Introduce `h h' hh`. Establish `: cj h' = h` using `Subtype.ext (by simp [cj, hh, mul_assoc])`. Simplify using `only [MonoidHom.comp_apply, r₁, this]`. Both sides reduce to the same expression.

Establish `hD` using `GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK`. Establish `hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL` using `↥LL'.1) (V := Fin a → ↥LL'.1) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * a := by`. Rewrite using `[← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]`. Conclude with `hdR`. Set `τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1` to `IntermediateField.inclusion hK₁LL`.

Establish `hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l)` using `fun x => rfl`. Establish `hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n` using `fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(c' : Om l) = _`. Rewrite using `[hc, hg])) n`. Establish `hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1`.

Introduce `σ x`. Establish `hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1` using `(hK _).2 (by simp)`. Set `e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1` to `((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2`. Establish `he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `g (g⁻¹ (x : Om l)) = (x : Om l)`.

Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel]`. Use the proof step `rfl)`. Rewrite using `[← he]`. Conclude with `hLL (Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩)`. Use `haveI := K₁.2`.

Set `K₀ : FinExt l` to `⟨K₁.1 ⊔ LL'.1, inferInstance⟩`. Take `⟨Pm, k, hk, heig⟩` from `GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' a r₁ hdR₁ hsplit τ₂ hτ₂ K₀ le_sup_left le_sup_right`. Use `⟨Pm, k, ?_, ?_⟩` and prove the remaining obligations. Use `Multiset.ext.mpr fun n => ?_` and prove the remaining obligations. Use `(hk n).trans ((hM n).symm.trans (hcnt n).symm)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Introduce `K' hK' f hf t ht`. Use `haveI := K'.2`. Take `⟨K₂, hK₂⟩ : ∃ K₂ : FinExt l, K₂.1 = K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l)` from `⟨⟨K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l), LinearEquiv.finiteDimensional (IntermediateField.equivMap K'.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩`. Establish `hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K₂.1` using `GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₂`.

Use `haveI := K₂.2`. Set `K'' : FinExt l` to `⟨K₂.1 ⊔ K₀.1, inferInstance⟩`. Use `poly_vanish l P AI hT K₁ LL' K'' a r₁ (le_trans le_sup_right le_sup_right) (le_trans le_sup_left le_sup_right) Pm k (fun h hh => heig h (GK_le le_sup_right hh)) f ?_ t ht` and prove the remaining obligations. Introduce `h hh`. Establish `h2 : (h : GQ l) ∈ GK K₂` using `GK_le le_sup_left hh`.

Establish `h3 : ((cj h : ↥(GK Bw.Kw)) : GQ l) ∈ GK K'` using `GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK' h2`. Establish `h4` using `hf (Bw.e.symm (cj h)) (by simpa using h3)`. Rewrite `h4` using `[← hmod]`. Conclude with `h4`.
-/
theorem mem_closure_of_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin a) (Om l)) (τ : E →+* Om l) (J : Multiset ℤ), GlobalTheory.Pst.IsJumpsAt P Bw r τ J → Multiset.card J = a → ∃ (Pm : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) (k : Fin a → ℤ), Multiset.map k Finset.univ.val = J ∧ ∀ (K' : FinExt l), Bw.Kw.1 ≤ K'.1 → ∀ f : MvPolynomial (Fin a × Fin a) ℂ_[l], (∀ g : ↥Gw, ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' → MvPolynomial.eval (fun ij => (((r g : Matrix (Fin a) (Fin a) (Om l)) ij.1 ij.2 : Om l) : ℂ_[l])) f = 0) → ∀ t : ℂ_[l], t ≠ 0 → MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin a) (Fin a) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) * ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) : Matrix (Fin a) (Fin a) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r τ J hJ hcard
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', -, hcnt⟩ := hJ
  haveI := Bw.Kw.2
  haveI := LL'.2

  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) := fun x => τo.liftNormal_commutes (Om l) x

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    have := hg ⟨x, hx⟩
    simp only at this
    change g x ∈ LL'.1
    rw [this]; exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₀ : ↥(GK Bw.Kw) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r'.comp Bw.e.symm.toMonoidHom
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r₀.comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = g * h * g⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin a → ↥LL'.1) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * a := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change g (g⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' a r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  refine ⟨Pm, k, ?_, ?_⟩
  · refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this
  intro K' hK' f hf t ht
  haveI := K'.2
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : FinExt l, K₂.1 = K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap K'.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K₂.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₂
  haveI := K₂.2
  let K'' : FinExt l := ⟨K₂.1 ⊔ K₀.1, inferInstance⟩
  refine poly_vanish l P AI hT K₁ LL' K'' a r₁ (le_trans le_sup_right le_sup_right)
    (le_trans le_sup_left le_sup_right) Pm k (fun h hh => heig h (GK_le le_sup_right hh)) f ?_ t ht
  intro h hh
  have h2 : (h : GQ l) ∈ GK K₂ := GK_le le_sup_left hh
  have h3 : ((cj h : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' := GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK' h2
  have h4 := hf (Bw.e.symm (cj h)) (by simpa using h3)
  rw [← hmod] at h4
  exact h4

end GlobalTheory.HodgeTateCochar
