import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBoundedStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLatVac

/- English proof (translation)
Establish `hv : Valued.v (2 : Fv F v) = 1`. Establish `e : (2 : Fv F v) = algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F))`. Rewrite using `[show (((2 : 𝓞 F) : F)) = 2 from map_ofNat (algebraMap (𝓞 F) F) 2, map_ofNat]`. Establish `e2 : algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) = ((algebraMap (𝓞 F) F (2 : 𝓞 F) : F) : v.adicCompletion F)` using `rfl`. Rewrite using `[e, e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_eq_one_iff_notMem]`.

Conclude with `h`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, invOf_eq_inv, map_inv₀, hv, inv_one]`.
-/
theorem two_inv_mem {F : Type} [Field F] [NumberField F] (v : Pl F) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    (⅟(2 : Fv F v)) ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) := by
      rw [show (((2 : 𝓞 F) : F)) = 2 from map_ofNat (algebraMap (𝓞 F) F) 2, map_ofNat]
    have e2 : algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) =
        ((algebraMap (𝓞 F) F (2 : 𝓞 F) : F) : v.adicCompletion F) := rfl
    rw [e, e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, invOf_eq_inv, map_inv₀, hv, inv_one]

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem hTens_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E) (e : E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (e • x) y = e * GlobalTheory.WeilM.hTens c JA JB x y := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `: r • x = (algebraMap R E r) • x` using `(algebraMap_smul E r x).symm`. Rewrite using `[this]`. Simplify using `only [GlobalTheory.WeilM.symp, hTens_smul_left]`. Rewrite using `[mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`.
-/
theorem symp_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Module.Free R E] [Module.Finite R E]
    (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (r : R)
    (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JA JB (r • x) y = r * GlobalTheory.WeilM.symp c ξ JA JB x y := by
  have : r • x = (algebraMap R E r) • x := (algebraMap_smul E r x).symm
  rw [this]
  simp only [GlobalTheory.WeilM.symp, hTens_smul_left]
  rw [mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
Introduce `γ hγ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨r, hr, hr', x, hx, y, hy, rfl⟩` from `hz`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨r, hr, hr', e • x, X.L.smul_mem e hx, y, hy, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, RingOfIntegers.coe_eq_algebraMap]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem latAtV_smul_int {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (v : Pl F) (e : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, (inclR (F := F) (AF F) (e : E)) • γ ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨r, hr, hr', x, hx, y, hy, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨r, hr, hr', e • x, X.L.smul_mem e hx, y, hy, ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.smul_def, map_mul, RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hin θ hθ γ hγ`. Establish `hst` using `GlobalTheory.LatVac.latAtV_at_stable G.V G.W v`. Establish `h2` using `two_inv_mem v (hT.base.inert v w hin).1`. Establish `hγ' : GlobalTheory.LatVac.liftV v (⅟2) • γ ∈ latAtV G.V G.W v` using `hst.2 _ h2 γ hγ`. Establish `e1 : (⅟(2 : AF F)) • γ = GlobalTheory.LatVac.liftV v (⅟2) • γ`.

Establish `h0 : ((⅟(2 : AF F)) - GlobalTheory.LatVac.liftV v (⅟2)) • γ = 0` using `hst.1 γ hγ _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, GlobalTheory.VacAny.evFin_invOf_two, sub_self])`. Rewrite `h0` using `[sub_smul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hz : -((inclR (F` using `F) (AF F) (θ : E)) • GlobalTheory.LatVac.liftV v (⅟2) • γ) ∈ latAtV G.V G.W v := neg_mem (latAtV_smul_int G.V G.W v θ _ hγ')`. Establish `key` using `(GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin _ (hst.1 _ hz)).1 hz γ hγ`. Rewrite using `[← symp_smul_left, e1]`.

Use `Eq.trans ?_ key` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← neg_smul, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.symp, hTens_smul_left]`. Put the polynomial expressions in normal form.
-/
theorem phase_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ θ : 𝓞 E, (θ : E) + σ (θ : E) = 1 → ∀ γ ∈ latAtV G.V G.W v,
      B.ψ (⅟2 * symp (cA σ) ((inclR (AF F)) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin θ hθ γ hγ
  have hst := GlobalTheory.LatVac.latAtV_at_stable G.V G.W v
  have h2 := two_inv_mem v (hT.base.inert v w hin).1
  have hγ' : GlobalTheory.LatVac.liftV v (⅟2) • γ ∈ latAtV G.V G.W v := hst.2 _ h2 γ hγ
  have e1 : (⅟(2 : AF F)) • γ = GlobalTheory.LatVac.liftV v (⅟2) • γ := by
    have h0 : ((⅟(2 : AF F)) - GlobalTheory.LatVac.liftV v (⅟2)) • γ = 0 :=
      hst.1 γ hγ _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, GlobalTheory.VacAny.evFin_invOf_two, sub_self])
    rwa [sub_smul, sub_eq_zero] at h0
  have hz : -((inclR (F := F) (AF F) (θ : E)) • GlobalTheory.LatVac.liftV v (⅟2) • γ) ∈ latAtV G.V G.W v :=
    neg_mem (latAtV_smul_int G.V G.W v θ _ hγ')
  have key := (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin _ (hst.1 _ hz)).1 hz γ hγ
  rw [← symp_smul_left, e1]
  refine Eq.trans ?_ key
  congr 1
  rw [← neg_smul, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.symp, hTens_smul_left]
  ring_nf

/- English proof (translation)
Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest κ v`. Establish `e` using `(h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ))`. Use function extensionality and compare the values at `y`. Establish `hx` using `congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))`. Establish `hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i))` using `GlobalTheory.VacAny.at_pi (fun i => GlobalTheory.LatVac.at_liftV v (y i))`.

Establish `hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0`. Use `(hR φ hφ).1 0 _ hat` as an intermediate fact. Simplify using `using this`. Simplify using `only [tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx`. Conclude with `mul_right_cancel₀ hR0 hx`.
-/
theorem acts_unique {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e := (h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ))
  funext y
  have hx := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) :=
    GlobalTheory.VacAny.at_pi (fun i => GlobalTheory.LatVac.at_liftV v (y i))
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 _ hat
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx
  exact mul_right_cancel₀ hR0 hx

/- English proof (translation)
Establish `hne : ∀ x : K, ψ₀ x ≠ 0` using `fun x h => by`. Use `AddChar.map_add_eq_mul ψ₀ x (-x)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul]`. Conclude with `one_ne_zero this`. Establish `key1 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) → ∀ t, h t ≠ 0 → ∃ l ∈ Λ, l.1 = t`.

Introduce `h hh t ht`. Apply `hrefl` to reduce the goal to its premises. Introduce `y hy`. Establish `hmem : ((0 : κ → K), y) ∈ Λ`. Rewrite using `[hdual]`.

Introduce `l hl`. Simplify using `only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv, hy l hl, inv_one]`. Use `congrFun (hh _ hmem) t` as an intermediate fact. Simplify using `only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero] at this`. Establish `h' : ψ₀ (t ⬝ᵥ y) * h t = 1 * h t` using `by rw [one_mul]; exact this`.

Conclude with `mul_right_cancel₀ ht h'`. Establish `key2 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) → ∀ l ∈ Λ, ψ₀ (⅟2 * l.1 ⬝ᵥ l.2) * h l.1 = h 0`. Introduce `h hh l hl`. Use `congrFun (hh l hl) 0` as an intermediate fact. Simplify `this` using `[GlobalTheory.WeilM.schr]`.

Establish `hg0 : g 0 ≠ 0`. Introduce `h0`. Apply `hg` to reduce the goal to its premises. Use function extensionality and compare the values at `t`. Assume the negation of the conclusion as `ht`.

Take `⟨l, hl, rfl⟩` from `key1 g hgf t ht`. Use `key2 g hgf l hl` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `ht ((mul_eq_zero.1 this).resolve_left (hne _))`. Use `⟨f 0 / g 0, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `ht : ∃ l ∈ Λ, l.1 = t`. Take `⟨l, hl, rfl⟩` from `ht`. Establish `e1` using `key2 f hf l hl`.

Establish `e2` using `key2 g hgf l hl`. Apply `mul_left_cancel₀ (hne (⅟2 * l.1 ⬝ᵥ l.2))` to reduce the goal to its premises. Rewrite using `[e1, ← mul_assoc, mul_comm _ (f 0 / g 0), mul_assoc, e2, div_mul_cancel₀ _ hg0]`. Establish `hf0 : f t = 0` using `by by_contra h; exact ht (key1 f hf t h)`. Establish `hg0' : g t = 0` using `by by_contra h; exact ht (key1 g hgf t h)`.

Rewrite using `[hf0, hg0', mul_zero]`.
-/
theorem fixed_eq_smul {K : Type} [Field K] {h2 : Invertible (2 : K)} {κ : Type} [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K)))
    (hdual : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hrefl : ∀ t : κ → K, (∀ y : κ → K, (∀ l ∈ Λ, ψ₀ (l.1 ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → ∃ l ∈ Λ, l.1 = t)
    {f g : (κ → K) → ℂ} (hg : g ≠ 0)
    (hf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l f = f) (hgf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l g = g) :
    ∃ c : ℂ, f = c • g := by
  have hne : ∀ x : K, ψ₀ x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul ψ₀ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this

  have key1 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ t, h t ≠ 0 → ∃ l ∈ Λ, l.1 = t := by
    intro h hh t ht
    apply hrefl
    intro y hy
    have hmem : ((0 : κ → K), y) ∈ Λ := by
      rw [hdual]
      intro l hl
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv, hy l hl, inv_one]
    have := congrFun (hh _ hmem) t
    simp only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero] at this
    have h' : ψ₀ (t ⬝ᵥ y) * h t = 1 * h t := by rw [one_mul]; exact this
    exact mul_right_cancel₀ ht h'

  have key2 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ l ∈ Λ, ψ₀ (⅟2 * l.1 ⬝ᵥ l.2) * h l.1 = h 0 := by
    intro h hh l hl
    have := congrFun (hh l hl) 0
    simpa [GlobalTheory.WeilM.schr] using this
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    funext t
    by_contra ht
    obtain ⟨l, hl, rfl⟩ := key1 g hgf t ht
    have := key2 g hgf l hl
    rw [h0] at this
    exact ht ((mul_eq_zero.1 this).resolve_left (hne _))
  refine ⟨f 0 / g 0, ?_⟩
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : ∃ l ∈ Λ, l.1 = t
  · obtain ⟨l, hl, rfl⟩ := ht
    have e1 := key2 f hf l hl
    have e2 := key2 g hgf l hl
    apply mul_left_cancel₀ (hne (⅟2 * l.1 ⬝ᵥ l.2))
    rw [e1, ← mul_assoc, mul_comm _ (f 0 / g 0), mul_assoc, e2, div_mul_cancel₀ _ hg0]
  · have hf0 : f t = 0 := by by_contra h; exact ht (key1 f hf t h)
    have hg0' : g t = 0 := by by_contra h; exact ht (key1 g hgf t h)
    rw [hf0, hg0', mul_zero]

/- English proof (translation)
Simplify using `only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV]`. Both sides reduce to the same expression.
-/
theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux Bf κ) (v : Pl F) (c : Fv F v) (z : W) :
    GlobalTheory.LatVac.locCo co v (GlobalTheory.LatVac.liftV v c • z) =
      (c • (GlobalTheory.LatVac.locCo co v z).1, c • (GlobalTheory.LatVac.locCo co v z).2) := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT Y _ Xm P hP hPs ρ hρ`. Take `⟨hvSB, hv0, θ, hθ, hvac⟩` from `hT.geo.hM.vac v`. Establish `hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ` using `(GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1`. Establish `hloc : ∀ γ ∈ latAtV G.V G.W v, ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ)` using `fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hAt γ hγ) φ`. Establish `hph` using `phase_one F E σ B a a' G X om om' hT v w hin θ hθ`.

Establish `hvfix : ∀ γ ∈ latAtV G.V G.W v, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) (G.M.vac v) = G.M.vac v`. Introduce `γ hγ`. Establish `h1` using `hvac γ hγ`. Rewrite `h1` using `[hph γ hγ, one_smul]`. Conclude with `acts_unique v _ hvSB (hloc γ hγ _) h1`.

Establish `hρs : ∀ u, P u → ∀ s : SB (Fin a × Fin (a + a') → Fv F v), ((ρ u s : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (Xm u)) s` using `fun u hu s => acts_unique v _ s.2 (hρ u s) (hloc _ (hP u hu) _)`. Use `⟨fun s hs u hu => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρs u hu s, hs]`. Conclude with `hvfix _ (hP u hu)`.

Use `set Λ := (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) with hΛ`. Establish `hdual : ∀ l, l ∈ Λ ↔ ∀ m ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ m.2 - m.1 ⬝ᵥ l.2) = 1` using `fun l => GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hAt (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin) l`. Establish `hsfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = s`. Introduce and unpack `l ⟨z, hz, rfl⟩`. Take `⟨u, hu, rfl⟩` from `hPs z hz`.

Use `hρs u hu s` as an intermediate fact. Rewrite `this` using `[hs u hu]`. Conclude with `this.symm`. Establish `hgfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (G.M.vac v) = G.M.vac v`. Introduce and unpack `l ⟨z, hz, rfl⟩`.

Conclude with `hvfix z hz`. Establish `hPU` using `(hT.base.inert v w hin).2.2`. Establish `hψ : ∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v`. Introduce `x`. Simplify using `only [GlobalTheory.LatVac.psiAt_apply]`.

Conclude with `hPU x`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded F E σ B a a' G X om om' hT v`. Establish `hrefl : ∀ t : Fin a × Fin (a + a') → Fv F v, (∀ y, (∀ l ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ y) = 1) → GlobalTheory.LatVac.psiAt B.ψ v (t ⬝ᵥ y) = 1) → ∃ l ∈ Λ, l.1 = t`. Introduce `t ht`. Use `GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal F v (Fin a × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ v) hψ (Λ.map (AddMonoidHom.fst _ _)) (by` as an intermediate fact.

Introduce and unpack `r hr _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩`. Use `⟨GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.LatVac.liftV v r • z), ⟨_, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 r hr z hz, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[locCo_smul]`. Use the proof step `rfl)`. Use the proof step `⟨c, hc0, by`.

Introduce and unpack `_ ⟨l, ⟨z, hz, rfl⟩, rfl⟩ k`. Conclude with `(hc z hz k).1⟩ t`. Use the proof step `(fun y hy => ht y fun l hl => hy _ ⟨l, hl, rfl⟩)`. Take `⟨l, hl, rfl⟩` from `this`. Conclude with `⟨l, hl, rfl⟩`.

Conclude with `fixed_eq_smul (GlobalTheory.LatVac.psiAt B.ψ v) Λ hdual hrefl hv0 hsfix hgfix`.
-/
theorem vac_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (AE F E)) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT Y _ Xm P hP hPs ρ hρ
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hloc : ∀ γ ∈ latAtV G.V G.W v, ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hAt γ hγ) φ
  have hph := phase_one F E σ B a a' G X om om' hT v w hin θ hθ
  have hvfix : ∀ γ ∈ latAtV G.V G.W v,
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) (G.M.vac v) = G.M.vac v := by
    intro γ hγ
    have h1 := hvac γ hγ
    rw [hph γ hγ, one_smul] at h1
    exact acts_unique v _ hvSB (hloc γ hγ _) h1
  have hρs : ∀ u, P u → ∀ s : SB (Fin a × Fin (a + a') → Fv F v),
      ((ρ u s : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) =
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (Xm u)) s :=
    fun u hu s => acts_unique v _ s.2 (hρ u s) (hloc _ (hP u hu) _)
  refine ⟨fun s hs u hu => ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    rw [hρs u hu s, hs]
    exact hvfix _ (hP u hu)
  · set Λ := (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) with hΛ
    have hdual : ∀ l, l ∈ Λ ↔ ∀ m ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ m.2 - m.1 ⬝ᵥ l.2) = 1 :=
      fun l => GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hAt
        (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin) l
    have hsfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = s := by
      rintro l ⟨z, hz, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hPs z hz
      have := hρs u hu s
      rw [hs u hu] at this
      exact this.symm
    have hgfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (G.M.vac v) = G.M.vac v := by
      rintro l ⟨z, hz, rfl⟩
      exact hvfix z hz
    have hPU := (hT.base.inert v w hin).2.2
    have hψ : ∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
        x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
      intro x
      simp only [GlobalTheory.LatVac.psiAt_apply]
      exact hPU x
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded F E σ B a a' G X om om' hT v
    have hrefl : ∀ t : Fin a × Fin (a + a') → Fv F v,
        (∀ y, (∀ l ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ y) = 1) → GlobalTheory.LatVac.psiAt B.ψ v (t ⬝ᵥ y) = 1) →
          ∃ l ∈ Λ, l.1 = t := by
      intro t ht
      have := GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal F v (Fin a × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ v) hψ (Λ.map (AddMonoidHom.fst _ _))
        (by
          rintro r hr _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩
          refine ⟨GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.LatVac.liftV v r • z),
            ⟨_, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 r hr z hz, rfl⟩, ?_⟩
          rw [locCo_smul]
          rfl)
        ⟨c, hc0, by
          rintro _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩ k
          exact (hc z hz k).1⟩ t
        (fun y hy => ht y fun l hl => hy _ ⟨l, hl, rfl⟩)
      obtain ⟨l, hl, rfl⟩ := this
      exact ⟨l, hl, rfl⟩
    exact fixed_eq_smul (GlobalTheory.LatVac.psiAt B.ψ v) Λ hdual hrefl hv0 hsfix hgfix

end GlobalTheory.InertLatVac
