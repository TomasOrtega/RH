import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAtStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertVacLagP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hs : Function.Surjective (compFin F E v)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul x e`.

Use `⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩` and prove the remaining obligations. Simplify using `[compFin, GlobalTheory.LatVac.evFin_liftV]`. Consider the case `add x y hx hy`. Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`.

Conclude with `⟨p + q, by rw [map_add, hp, hq]⟩`. Use `choose f hf using hs`. Conclude with `⟨Cy.map f, by ext i j; simp [hf]⟩`.
-/
theorem exists_map_compFin (v : Pl F) {d m : ℕ} (Cy : Matrix (Fin d) (Fin m) (Fv F v ⊗[F] E)) :
    ∃ C : Matrix (Fin d) (Fin m) (AE F E), C.map (compFin F E v) = Cy := by
  have hs : Function.Surjective (compFin F E v) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x e =>
      refine ⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩
      simp [compFin, GlobalTheory.LatVac.evFin_liftV]
    | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  choose f hf using hs
  exact ⟨Cy.map f, by ext i j; simp [hf]⟩

def lagSub {n d m : ℕ} (v : Pl F) (C : Matrix (Fin d) (Fin m) (AE F E)) : AddSubgroup (Matrix (Fin n) (Fin d) (AE F E)) where
  carrier := GlobalTheory.InertVacLag.lagAt v C
  zero_mem' := ⟨fun u _ => smul_zero u, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, z, rfl⟩ ⟨hy, z', rfl⟩
    exact ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩
  neg_mem' := by
    rintro x ⟨hx, z, rfl⟩
    exact ⟨fun u hu => by rw [smul_neg, hx u hu, neg_zero], -z, by rw [Matrix.neg_mul]⟩

/- English proof (translation)
Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v`. Establish `e` using `(h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))`. Use function extensionality and compare the values at `y`. Establish `hy` using `congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))`. Simplify using `only [tens] at hy`.

Establish `hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y` using `funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)`. Rewrite `hy` using `[hev]`. Establish `hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0`. Use `(hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v (y i))` as an intermediate fact. Simplify using `using this`.

Rewrite `hy` using `[hRx]`. Conclude with `mul_right_cancel₀ hR0 hy`.
-/
theorem acts_unique {κ : Type} [Fintype κ] (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) (h1 : Acts (evFin F v) T φ φ₁)
    (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e := (h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))
  funext y
  have hy := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens] at hy
  have hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y := funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)
  rw [hev] at hy
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v (y i))
    simpa using this
  rw [hRx] at hy
  exact mul_right_cancel₀ hR0 hy

/- English proof (translation)
Establish `hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k)`. Introduce `z hz k`. Use `⟨fun t ht => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Use `congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)` as an intermediate fact. Simplify `this.symm` using `[hz t ht]`.

Use `congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)` as an intermediate fact. Simplify `this.symm` using `[hz t ht]`. Apply `co.e.injective` to reduce the goal to its premises. Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`.

Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]`. Conclude with `congrArg _ (congrFun h1 k)`. Rewrite using `[GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]`. Conclude with `congrArg _ (congrFun h2 k)`.
-/
theorem eq_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (g u : W) (hg : At (evFin F v) g) (hu : At (evFin F v) u)
    (h : GlobalTheory.LatVac.locCo co v g = GlobalTheory.LatVac.locCo co v u) : g = u := by
  have hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) := by
    intro z hz k
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
    · have := congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
  apply co.e.injective
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]
    exact congrArg _ (congrFun h1 k)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]
    exact congrArg _ (congrFun h2 k)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _`. Take `⟨Cy, hCy⟩` from `GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin`. Take `⟨C, hC⟩` from `exists_map_compFin (E := E) v Cy`. Establish `hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C`. Unfold `GlobalTheory.InertVacLag.IsLagrAt`.

Rewrite using `[hC]`. Conclude with `hCy`. Use `set co := G.M'.co with hco`. Use `set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ`. Use `set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ`.

Establish `hgood` using `hT.base.inert v w hin`. Take `⟨hsb, hne, θ, hθ, hvac⟩` from `hT.geo.hM'.vac v`. Establish `hatL` using `(GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)`. Establish `hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) → x ∈ v.adicCompletionIntegers F` using `fun x hx => (hgood.2.2 x).1 hx`.

Establish `hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0`. Introduce and unpack `_ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩`. Establish `h0` using `GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'`. Rewrite `h0` using `[co.form]`. Establish `h1` using `congrArg (evFin F v) h0`.

Simplify `h1` using `[GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]`. Establish `hOC` using `GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v`. Establish `hdual` using `GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)`. Establish `heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F` using `F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) g g) • G.M'.vac v := fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)`. Establish `heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v`.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨_, heig0 g hg⟩`. Establish `hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v`. Introduce and unpack `γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩`. Establish `e : g = u` using `eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm`.

Substitute `e` using the available equality. Rewrite using `[heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]`. Take `⟨l, hl, hl0⟩` from `GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso hOC.1 hOC.2 hdual hsb hne heig hfix`. Use `⟨C, l, hLag, ?_, hl0⟩` and prove the remaining obligations. Introduce `u hu φ hφ φ₁ _ hA`.

Establish `e` using `acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)`. Rewrite using `[e]`. Conclude with `hl _ ⟨u, hu, rfl⟩ φ hφ`.
-/
theorem exists_lagr_inv_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (AE F E)) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _
  obtain ⟨Cy, hCy⟩ := GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin
  obtain ⟨C, hC⟩ := exists_map_compFin (E := E) v Cy
  have hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C := by
    unfold GlobalTheory.InertVacLag.IsLagrAt; rw [hC]; exact hCy
  set co := G.M'.co with hco
  set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ
  set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ
  have hgood := hT.base.inert v w hin
  obtain ⟨hsb, hne, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  have hatL := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)
  have hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) →
      x ∈ v.adicCompletionIntegers F := fun x hx => (hgood.2.2 x).1 hx
  have hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'
    rw [co.form] at h0
    have h1 := congrArg (evFin F v) h0
    simpa [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub] using h1
  have hOC := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v
  have hdual := GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL
    (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)
  have heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) g g) • G.M'.vac v :=
    fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)
  have heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, heig0 g hg⟩
  have hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v := by
    rintro γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩
    have e : g = u := eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm
    subst e
    rw [heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]
  obtain ⟨l, hl, hl0⟩ := GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso
    hOC.1 hOC.2 hdual hsb hne heig hfix
  refine ⟨C, l, hLag, ?_, hl0⟩
  intro u hu φ hφ φ₁ _ hA
  have e := acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)
  rw [e]
  exact hl _ ⟨u, hu, rfl⟩ φ hφ

end GlobalTheory.InertVacLagP

end
