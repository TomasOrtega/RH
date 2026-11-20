import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMatMapSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.DblLocal

open MeasureTheory GlobalTheory.HoweLocal GlobalTheory.LatVac

section Uniq

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type}

/- English proof (translation)
Use `letI : MeasurableSpace (κ → k) := borel _`. Use `haveI : BorelSpace (κ → k) := ⟨rfl⟩`. Use `SplitWeil.t2Space k` as an intermediate fact. Use `nonarch_pi k κ` as an intermediate fact. Establish `hz : ∀ φ ∈ SB (κ ⊕ κ → k), ∀ φ' ∈ SB (κ ⊕ κ → k), (∀ x, φ' (Sum.elim x x) = φ (Sum.elim x x)) → l φ' = l φ`.

Introduce `φ hφ φ' hφ' h`. Use `diag_invariant_comp ψ hψ hψ1 l hl 1 hφ hφ' (fun x => by simpa using h x)` as an intermediate fact. Simplify using `using this`. Set `K : Set (κ → k)` to `Set.univ.pi fun _ => (𝒪[k] : Set k)`. Establish `hKc : IsCompact K` using `isCompact_univ_pi fun _ => SplitWeil.isCompact_int k`.

Establish `hK : IsClopen K` using `⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int k⟩`. Set `e : (κ → k) → ℂ` to `K.indicator 1`. Establish `he : IsLocallyConstant e` using `(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant`. Establish `he0 : e 0 = 1` using `Set.indicator_of_mem (show (0 : κ → k) ∈ K from fun _ _ => zero_mem _) _`. Set `ext : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ)` to `{ toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) map_add' := fun f f' => by funext u; simp [add_mul] map_smul' := fun a f => by funext u; simp [mul_assoc] }`.

Establish `hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)` using `fun _ _ => rfl`. Establish `c1 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inl` using `continuous_pi fun k => continuous_apply _`. Establish `c2 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inr` using `continuous_pi fun k => continuous_apply _`. Establish `hSB : ∀ f ∈ SB (κ → k), ext f ∈ SB (κ ⊕ κ → k)`. Introduce `f hf`.

Apply the tactic sequence `have c3 : Continuous fun p : (κ → k) × (κ → k) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → k) := continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)`. Use `⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)), HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Rewrite `h` using `[hext]`. Use `hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl), ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hres : ∀ φ ∈ SB (κ ⊕ κ → k), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x)`. Introduce `φ hφ`. Rewrite using `[LinearMap.comp_apply]`. Use `hz _ (hSB _ (diag_mem_SB hφ)) _ hφ fun x => ?_` and prove the remaining obligations.

Simplify using `[hext, he0]`. Establish `hinv : ∀ f ∈ SB (κ → k), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f`. Introduce `f hf a`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Establish `e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a` using `rfl`. Establish `e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a` using `rfl`. Simplify using `[schr, hext, e1, e2]`. Take `⟨c, hc⟩` from `GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → k) μ _ hinv`.

Conclude with `⟨c, fun φ hφ => by rw [hres φ hφ, hc _ (diag_mem_SB hφ)]⟩`.
-/
theorem diag_eq_mul_integral [Invertible (2 : k)] [Fintype κ] (ψ : AddChar k ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → k, ∀ φ ∈ SB (κ ⊕ κ → k), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (μ : @Measure (κ → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ ⊕ κ → k), l φ = c * ∫ x, φ (Sum.elim x x) ∂μ := by
  classical
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have := SplitWeil.t2Space k
  have := nonarch_pi k κ
  have hz : ∀ φ ∈ SB (κ ⊕ κ → k), ∀ φ' ∈ SB (κ ⊕ κ → k), (∀ x, φ' (Sum.elim x x) = φ (Sum.elim x x)) → l φ' = l φ := by
    intro φ hφ φ' hφ' h
    have := diag_invariant_comp ψ hψ hψ1 l hl 1 hφ hφ' (fun x => by simpa using h x)
    simpa using this
  let K : Set (κ → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int k
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int k⟩
  let e : (κ → k) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → k) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → k), ext f ∈ SB (κ ⊕ κ → k) := by
    intro f hf
    have c3 : Continuous fun p : (κ → k) × (κ → k) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → k) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → k), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply]
    refine hz _ (hSB _ (diag_mem_SB hφ)) _ hφ fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → k), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → k) μ _ hinv
  exact ⟨c, fun φ hφ => by rw [hres φ hφ, hc _ (diag_mem_SB hφ)]⟩

end Uniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Lift

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem liftE_eq (v : Pl F) (y : Fv F v ⊗[F] E) : liftE v y = Supp.singleTens E v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq, Supp.singleTens_mul]`.
-/
theorem map_liftE_mul (v : Pl F) {a b c : Type} [Fintype b] (x : Matrix a b (Fv F v ⊗[F] E)) (P : Matrix b c (AE F E)) :
    x.map (liftE v) * P = (x * P.map (compFin F E v)).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq, Supp.singleTens_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, Supp.singleTens_mul, mul_comm]`.
-/
theorem mul_map_liftE (v : Pl F) {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) (x : Matrix b c (Fv F v ⊗[F] E)) :
    P * x.map (liftE v) = (P.map (compFin F E v) * x).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, Supp.singleTens_mul, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, liftE_eq, Supp.compFin_singleTens_self]`.
-/
theorem map_liftE_map (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (compFin F E v) = x := by
  ext i j
  simp only [Matrix.map_apply, liftE_eq, Supp.compFin_singleTens_self]

/- English proof (translation)
Introduce `u hu`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.map_apply, liftE_eq, Algebra.smul_def, mul_comm, Supp.singleTens_mul]`. Establish `e : compFin F E v (algebraMap (AF F) (AE F E) u) = 0` using `by show evFin F v u ⊗ₜ[F] (1 : E) = 0`. Rewrite using `[hu, TensorProduct.zero_tmul]`.

Rewrite using `[e, mul_zero, map_zero]`. Both sides reduce to the same expression.
-/
theorem at_map_liftE (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) : At (evFin F v) (x.map (liftE v)) := by
  intro u hu
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, liftE_eq, Algebra.smul_def, mul_comm, Supp.singleTens_mul]
  have e : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    show evFin F v u ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [e, mul_zero, map_zero]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Proceed by induction on `x i j using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_liftE_cA (σ : E →ₐ[F] E) (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (cA σ) = (x.map (cv σ v)).map (liftE v) := by
  ext i j
  simp only [Matrix.map_apply]
  induction x i j using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {β : Type} [Fintype β] [DecidableEq β]

def liftM (v : Pl F) (β : Type) [Fintype β] [DecidableEq β] : Matrix β β (Fv F v ⊗[F] E) →* Matrix β β (AE F E) where
  toFun h := 1 + (h - 1).map (liftE v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    have e2 : ((a - 1) * (b - 1)).map (liftE v) = (a - 1).map (liftE v) * (b - 1).map (liftE v) := by
      rw [map_liftE_mul, map_liftE_map]
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), e2]
    noncomm_ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftM_apply (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : liftM v β h = 1 + (h - 1).map (liftE v) := rfl

/- English proof (translation)
Rewrite using `[liftM_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), map_liftE_map]`. Normalize the expressions using the abelian group laws.
-/
theorem liftM_map (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : (liftM v β h).map (compFin F E v) = h := by
  rw [liftM_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), map_liftE_map]
  abel

/- English proof (translation)
Rewrite using `[liftM_apply, add_sub_cancel_left]`. Conclude with `at_map_liftE v _`.
-/
theorem liftM_at (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : At (evFin F v) (liftM v β h - 1) := by
  rw [liftM_apply, add_sub_cancel_left]
  exact at_map_liftE v _

/- English proof (translation)
Establish `e : g.map (compFin F E v) - 1 = (g - 1).map (compFin F E v)`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[liftM_apply, e, Matrix.map_map]`. Use extensionality with `i j`. Establish `hz : At (evFin F v) ((g - 1) i j)` using `fun u hu => by`.

Use `congrArg (fun M => M i j) (hg u hu)` as an intermediate fact. Simplify using `only [Matrix.smul_apply, Matrix.zero_apply] at this`. Conclude with `this`. Rewrite using `[Matrix.add_apply, Matrix.map_apply, Function.comp_apply, liftE_eq, CompIso.lift_comp v _ hz, Matrix.sub_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem liftM_comp (v : Pl F) (g : Matrix β β (AE F E)) (hg : At (evFin F v) (g - 1)) :
    liftM v β (g.map (compFin F E v)) = g := by
  have e : g.map (compFin F E v) - 1 = (g - 1).map (compFin F E v) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [liftM_apply, e, Matrix.map_map]
  ext i j
  have hz : At (evFin F v) ((g - 1) i j) := fun u hu => by
    have := congrArg (fun M => M i j) (hg u hu)
    simp only [Matrix.smul_apply, Matrix.zero_apply] at this
    exact this
  rw [Matrix.add_apply, Matrix.map_apply, Function.comp_apply, liftE_eq, CompIso.lift_comp v _ hz, Matrix.sub_apply]
  abel

/- English proof (translation)
Establish `hh : (h.1 : Matrix β β (Fv F v ⊗[F] E))ᵀ * JL * (h.1 : Matrix β β (Fv F v ⊗[F] E)).map (cv σ v) = JL` using `h.2`. Use `show (liftM v β h.1.1)ᵀ * J * (liftM v β h.1.1).map (cA σ) = J`. Take `⟨a, ha⟩ : ∃ a, (h.1 : Matrix β β (Fv F v ⊗[F] E)) = 1 + a` from `⟨h.1.1 - 1, by abel⟩`. Rewrite `hh` using `[ha]`. Rewrite using `[ha, liftM_apply, add_sub_cancel_left]`.

Rewrite `hh`, the goal using `[Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]`. Rewrite using `[map_liftE_cA, ← Matrix.transpose_map]`. Use `set c := a.map (cv σ v)`. Establish `h0 : aᵀ * JL + JL * c + aᵀ * JL * c = 0`. Rewrite `hh` using `[← sub_eq_zero]`.

Rewrite using `[← hh]`. Use `noncomm_ring`. Establish `e1 : aᵀ.map (liftE v) * J = (aᵀ * JL).map (liftE v)` using `by rw [map_liftE_mul, hJ]`. Establish `e2 : J * c.map (liftE v) = (JL * c).map (liftE v)` using `by rw [mul_map_liftE, hJ]`. Establish `e3 : aᵀ.map (liftE v) * J * c.map (liftE v) = (aᵀ * JL * c).map (liftE v)`.

Rewrite using `[e1, map_liftE_mul, map_liftE_map]`. Establish `h1 : aᵀ.map (liftE v) * J + J * c.map (liftE v) + aᵀ.map (liftE v) * J * c.map (liftE v) = 0`. Rewrite using `[e3, e1, e2, ← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), h0, Matrix.map_zero _ (map_zero _)]`. Rewrite using `[← sub_eq_zero, ← h1]`. Use `noncomm_ring`.
-/
theorem liftM_mem (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) : Units.map (liftM v β) h.1 ∈ UG (cA σ) J := by
  have hh : (h.1 : Matrix β β (Fv F v ⊗[F] E))ᵀ * JL * (h.1 : Matrix β β (Fv F v ⊗[F] E)).map (cv σ v) = JL := h.2
  show (liftM v β h.1.1)ᵀ * J * (liftM v β h.1.1).map (cA σ) = J
  obtain ⟨a, ha⟩ : ∃ a, (h.1 : Matrix β β (Fv F v ⊗[F] E)) = 1 + a := ⟨h.1.1 - 1, by abel⟩
  rw [ha] at hh
  rw [ha, liftM_apply, add_sub_cancel_left]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one] at hh ⊢
  rw [map_liftE_cA, ← Matrix.transpose_map]
  set c := a.map (cv σ v)
  have h0 : aᵀ * JL + JL * c + aᵀ * JL * c = 0 := by
    rw [← sub_eq_zero] at hh
    rw [← hh]; noncomm_ring
  have e1 : aᵀ.map (liftE v) * J = (aᵀ * JL).map (liftE v) := by rw [map_liftE_mul, hJ]
  have e2 : J * c.map (liftE v) = (JL * c).map (liftE v) := by rw [mul_map_liftE, hJ]
  have e3 : aᵀ.map (liftE v) * J * c.map (liftE v) = (aᵀ * JL * c).map (liftE v) := by
    rw [e1, map_liftE_mul, map_liftE_map]
  have h1 : aᵀ.map (liftE v) * J + J * c.map (liftE v) + aᵀ.map (liftE v) * J * c.map (liftE v) = 0 := by
    rw [e3, e1, e2, ← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), h0, Matrix.map_zero _ (map_zero _)]
  rw [← sub_eq_zero, ← h1]
  noncomm_ring

def liftU (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) : UG (cv σ v) JL →* UG (cA σ) J :=
  ((Units.map (liftM v β)).comp (UG (cv σ v) JL).subtype).codRestrict _ (liftM_mem σ v hJ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftU_val (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) :
    ((liftU σ v hJ h : GL β (AE F E)) : Matrix β β (AE F E)) = liftM v β (h : GL β (Fv F v ⊗[F] E)) := rfl

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _`. Establish `hst : Continuous (Supp.singleTens E v)` using `GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))`. Establish `hst' : Continuous (liftE (E` using `E) v) := hst.congr fun y => (liftE_eq v y).symm`.

Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `(Continuous.units_map _ (continuous_const.add ((continuous_id.sub continuous_const).matrix_map hst'))).comp continuous_subtype_val`.
-/
theorem continuous_liftU (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) : Continuous (liftU σ v hJ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hst : Continuous (Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hst' : Continuous (liftE (E := E) v) := hst.congr fun y => (liftE_eq v y).symm
  refine Continuous.subtype_mk ?_ _
  exact (Continuous.units_map _ (continuous_const.add ((continuous_id.sub continuous_const).matrix_map hst'))).comp
    continuous_subtype_val

/- English proof (translation)
Rewrite using `[liftM_apply, liftM_apply, Matrix.add_mul, Matrix.mul_add, map_liftE_mul, mul_map_liftE, Matrix.sub_mul, Matrix.mul_sub, hp, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem liftM_mul_of {ν : Type} [Fintype ν] [DecidableEq ν] (v : Pl F) (D : Matrix β ν (AE F E))
    (p : Matrix β β (Fv F v ⊗[F] E)) (t : Matrix ν ν (Fv F v ⊗[F] E))
    (hp : p * D.map (compFin F E v) = D.map (compFin F E v) * t) : liftM v β p * D = D * liftM v ν t := by
  rw [liftM_apply, liftM_apply, Matrix.add_mul, Matrix.mul_add, map_liftE_mul, mul_map_liftE, Matrix.sub_mul,
    Matrix.mul_sub, hp, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[liftM_apply, liftM_apply]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`.
-/
theorem liftM_fromBlocks (v : Pl F) (g : Matrix β β (Fv F v ⊗[F] E)) :
    liftM v (β ⊕ β) (Matrix.fromBlocks g 0 0 1) = Matrix.fromBlocks (liftM v β g) 0 0 1 := by
  rw [liftM_apply, liftM_apply]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end Lift

section Split

open scoped GlobalTheory.VacAny

variable {κ : Type} [Fintype κ]

/- English proof (translation)
Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `letI : MeasurableSpace (κ → Fv F v) := borel _`. Use `haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩`. Take `⟨r, hr, hS, h0⟩` from `GlobalTheory.LocalUnitaryL2.exists_r (κ := κ) v`.

Set `μA : Measure (κ → AF F)` to `Measure.addHaar`. Take `⟨c, hc0, hct, hc⟩` from `GlobalTheory.LocalUnitaryL2.exists_const v r hr hS μA ⟨0, h0⟩ μ`. Establish `h` using `hU μA inferInstance (tens (evFin F v) φ r) (hS φ hφ)`. Rewrite `h` using `[hA r ⟨hr, hS φ hφ⟩, hc φ₁ hφ₁, hc φ hφ]`. Conclude with `(ENNReal.mul_right_inj hc0 hct).1 h`.
-/
theorem lintegral_eq_of_acts (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ)
    {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (hA : Acts (evFin F v) T φ φ₁)
    (μ : @Measure (κ → Fv F v) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  obtain ⟨r, hr, hS, h0⟩ := GlobalTheory.LocalUnitaryL2.exists_r (κ := κ) v
  let μA : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.LocalUnitaryL2.exists_const v r hr hS μA ⟨0, h0⟩ μ
  have h := hU μA inferInstance (tens (evFin F v) φ r) (hS φ hφ)
  rw [hA r ⟨hr, hS φ hφ⟩, hc φ₁ hφ₁, hc φ hφ] at h
  exact (ENNReal.mul_right_inj hc0 hct).1 h

open scoped Classical in

/- English proof (translation)
Introduce `l _ φ hφ`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest κ v`. Set `lift : (κ → Fv F v) → (κ → AF F)` to `fun t i => liftV v (t i)`. Set `L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ` to `(R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)`. Establish `hL : L ∈ (adeleClass F).adm κ`.

Introduce `g _`. Use `⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) • ((BoundedContinuousFunction.evalCLM ℂ 0).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩` and prove the remaining obligations. Establish `e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2)`. Use function extensionality and compare the values at `t`. Establish `h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0`.

Use function extensionality and compare the values at `i`. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`. Simplify using `only [pureA, h0, Pi.smul_apply, smul_eq_mul]`. Use `show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _`.

Rewrite using `[e, map_smul]`. Simplify using `[smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]`. Use `(hc0 L hL _ (hR φ hφ).2).congr fun q => ?_` and prove the remaining obligations. Rewrite using `[hom q φ hφ R (hR φ hφ)]`. Establish `e : (fun t => tens (evFin F v) (om q φ) R (lift t)) = R 0 • om q φ`.

Use function extensionality and compare the values at `t`. Establish `hz : At (evFin F v) (lift t)` using `fun u hu => funext fun i => at_liftV v _ u hu`. Establish `hrz : R (lift t) = R 0` using `by simpa using (hR φ hφ).1 0 _ hz`. Simplify using `only [tens, lift, evFin_liftV, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[show (fun i => liftV v (t i)) = lift t from rfl, hrz, mul_comm]`.

Use `show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om q φ) R (lift t)) = _`. Rewrite using `[e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]`.
-/
theorem isContOn_of_acts (v : Pl F) {G : Type} [Group G] [TopologicalSpace G]
    (Ω : G →* Module.End ℂ ((κ → AF F) → ℂ)) (hc0 : IsContOn (adeleClass F) Ω)
    (om : G →* Module.End ℂ ((κ → Fv F v) → ℂ))
    (hom : ∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (Ω g) φ (om g φ)) : IsContOn (sbClass (Fv F v)) om := by
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let lift : (κ → Fv F v) → (κ → AF F) := fun t i => liftV v (t i)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  refine (hc0 L hL _ (hR φ hφ).2).congr fun q => ?_
  rw [hom q φ hφ R (hR φ hφ)]
  have e : (fun t => tens (evFin F v) (om q φ) R (lift t)) = R 0 • om q φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om q φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/- English proof (translation)
Establish `hex : ∀ g, ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ φ₁`. Introduce `g φ hφ`. Use `GlobalTheory.DblActs.acts_of_comm v ψ hψ _ (fun Φ hΦ => hS.pres _ Φ hΦ) (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) ?_ φ hφ` and prove the remaining obligations. Introduce `u hu x y Φ hΦ`. Use `set w := d.e.symm (x, y) with hw`.

Establish `he : d.e (u • w) = (u • x, u • y)`. Rewrite using `[LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Establish `h2` using `liftM_at v ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E)) u hu`. Establish `e2 : actB (cA σ) (liftU σ v hJ g) (u • w) = u • w`. Rewrite using `[actB, liftU_val]`.

Use `set P := liftM v β ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E))`. Establish `: (u • w) * Pᵀ - u • w = w * (u • (P - 1))ᵀ`. Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero]`. Conclude with `this`.

Establish `h3` using `hS.impl (liftU σ v hJ g) (u • w) Φ hΦ`. Simplify using `only [Darboux.rho, he, e2] at h3`. Conclude with `h3`. Take `⟨T, hT⟩` from `GlobalTheory.HoweLocal.LocOpsW.loc_hom v (om.comp (liftU σ v hJ)) (fun x Φ hΦ => hS.pres _ Φ hΦ) hex`. Take `⟨omL, homL⟩` from `GlobalTheory.HoweLocal.LocOpsW.extend_hom (SB (κ → Fv F v)) T`.

Establish `hpres : ∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v)` using `fun g φ hφ => by`. Rewrite using `[show omL g φ = _ from homL g ⟨φ, hφ⟩]`. Conclude with `(T g ⟨φ, hφ⟩).2`. Establish `hact : ∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ (omL g φ)` using `fun g φ hφ => by`. Rewrite using `[show omL g φ = _ from homL g ⟨φ, hφ⟩]`.

Conclude with `hT g ⟨φ, hφ⟩`. Use `⟨omL, hact, ⟨hpres, fun g w φ hφ => ?_, fun _ _ _ => Set.mem_univ _⟩, fun μ hμ g φ hφ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest κ v`. Establish `hrho : ∀ x, ∀ f ∈ SB (κ → Fv F v), d.rho ψ (x.map (liftE v)) (tens (evFin F v) f R) = tens (evFin F v) (co.rho (psiAt ψ v) x f) R` using `fun x f hf => by`. Rewrite using `[GlobalTheory.VacBridge.rho_acts_locCo d ψ v _ (at_map_liftE v x) f R (hR f hf), Darboux.rho, hco]`.

Establish `hm : co.rho (psiAt ψ v) w φ ∈ SB (κ → Fv F v)` using `GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ`. Establish `e : actB (cA σ) (liftU σ v hJ g) (w.map (liftE v)) = (actB (cv σ v) g w).map (liftE v)`. Rewrite using `[actB, actB, liftU_val, map_liftE_mul, Matrix.transpose_map, liftM_map]`. Use `GlobalTheory.DblSwap.eq_of_tens_ne v (hR φ hφ).1 hR0 ?_` and prove the remaining obligations. Rewrite using `[← hact g _ hm R (hR _ hm), ← hrho w φ hφ, hS.impl _ _ _ (hR φ hφ).2, e, hact g φ hφ R (hR φ hφ), hrho _ _ (hpres g φ hφ)]`.

Conclude with `lintegral_eq_of_acts v _ (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) hφ (hpres g φ hφ) (hact g φ hφ) μ hμ`. Conclude with `isContOn_of_acts v (om.comp (liftU σ v hJ)) (hS.cont.comp (continuous_liftU σ v hJ)) omL hact`.
-/
theorem exists_loc_splitting (σ : E →ₐ[F] E) (v : Pl F) {ξ : AE F E} {JA : Matrix α α (AE F E)} {J : Matrix β β (AE F E)}
    {ξL : Fv F v ⊗[F] E} {JAL : Matrix α α (Fv F v ⊗[F] E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (d : Darboux (symp (R := AF F) (cA σ) ξ JA J) κ) {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ)}
    (hS : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (co : Darboux (symp (R := Fv F v) (cv σ v) ξL JAL JL) κ) (hco : ∀ x, co.e x = locCo d v (x.map (liftE v))) :
    ∃ omL : UG (cv σ v) JL →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ (omL g φ)) ∧
      IsUSplitting (sbClass (Fv F v)) (psiAt ψ v) co (actB (cv σ v)) omL := by
  have hex : ∀ g, ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ φ₁ := by
    intro g φ hφ
    refine GlobalTheory.DblActs.acts_of_comm v ψ hψ _ (fun Φ hΦ => hS.pres _ Φ hΦ) (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) ?_ φ hφ
    intro u hu x y Φ hΦ
    set w := d.e.symm (x, y) with hw
    have he : d.e (u • w) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := liftM_at v ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E)) u hu
    have e2 : actB (cA σ) (liftU σ v hJ g) (u • w) = u • w := by
      rw [actB, liftU_val]
      set P := liftM v β ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E))
      have : (u • w) * Pᵀ - u • w = w * (u • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have h3 := hS.impl (liftU σ v hJ g) (u • w) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  obtain ⟨T, hT⟩ := GlobalTheory.HoweLocal.LocOpsW.loc_hom v (om.comp (liftU σ v hJ)) (fun x Φ hΦ => hS.pres _ Φ hΦ) hex
  obtain ⟨omL, homL⟩ := GlobalTheory.HoweLocal.LocOpsW.extend_hom (SB (κ → Fv F v)) T
  have hpres : ∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) := fun g φ hφ => by
    rw [show omL g φ = _ from homL g ⟨φ, hφ⟩]; exact (T g ⟨φ, hφ⟩).2
  have hact : ∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ (omL g φ) := fun g φ hφ => by
    rw [show omL g φ = _ from homL g ⟨φ, hφ⟩]; exact hT g ⟨φ, hφ⟩
  refine ⟨omL, hact, ⟨hpres, fun g w φ hφ => ?_, fun _ _ _ => Set.mem_univ _⟩, fun μ hμ g φ hφ => ?_, ?_⟩
  · obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
    have hrho : ∀ x, ∀ f ∈ SB (κ → Fv F v), d.rho ψ (x.map (liftE v)) (tens (evFin F v) f R) =
        tens (evFin F v) (co.rho (psiAt ψ v) x f) R := fun x f hf => by
      rw [GlobalTheory.VacBridge.rho_acts_locCo d ψ v _ (at_map_liftE v x) f R (hR f hf), Darboux.rho, hco]
    have hm : co.rho (psiAt ψ v) w φ ∈ SB (κ → Fv F v) := GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ
    have e : actB (cA σ) (liftU σ v hJ g) (w.map (liftE v)) = (actB (cv σ v) g w).map (liftE v) := by
      rw [actB, actB, liftU_val, map_liftE_mul, Matrix.transpose_map, liftM_map]
    refine GlobalTheory.DblSwap.eq_of_tens_ne v (hR φ hφ).1 hR0 ?_
    rw [← hact g _ hm R (hR _ hm), ← hrho w φ hφ, hS.impl _ _ _ (hR φ hφ).2, e, hact g φ hφ R (hR φ hφ),
      hrho _ _ (hpres g φ hφ)]
  · exact lintegral_eq_of_acts v _ (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) hφ (hpres g φ hφ) (hact g φ hφ) μ hμ
  · exact isContOn_of_acts v (om.comp (liftU σ v hJ)) (hS.cont.comp (continuous_liftU σ v hJ)) omL hact

end Split

/- English proof (translation)
Rewrite using `[dbl, dbl, Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg _), CompIso.incM_map, Matrix.map_zero _ (map_zero _)]`.
-/
theorem dbl_map (v : Pl F) {b : ℕ} (J : Matrix (Fin b) (Fin b) E) :
    (dbl (incM F J)).map (compFin F E v) = dbl (Jv v J) := by
  rw [dbl, dbl, Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg _), CompIso.incM_map, Matrix.map_zero _ (map_zero _)]

/- English proof (translation)
Rewrite using `[diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]`.
-/
theorem diag_mul {R : Type} [CommRing R] {α β : Type} [Fintype β] [DecidableEq β] (z : Matrix α β R) :
    z * (diagCols β : Matrix (β ⊕ β) β R)ᵀ = Matrix.fromCols z z := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hχ z h1]`. Use `congr 1`. Conclude with `Units.ext hz`. Establish `h` using `GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at F v (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) h2`.

Rewrite `h` using `[show Units.map (evFin F v : AF F →* Fv F v) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) = Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) zv from Units.ext ((GlobalTheory.NormAtPlace.evFin_norm_eq F E v z).trans (congrArg _ hz))]`. Conclude with `h`.
-/
theorem scalar_eq (χ : Chr F E) (v : Pl F) (χv : (Fv F v ⊗[F] E)ˣ →* Circle) (hχ : IsLocChr χ v χv) (z : (AE F E)ˣ)
    (zv : (Fv F v ⊗[F] E)ˣ) (hz : compFin F E v z = zv) (h1 : At (evFin F v) ((z : AE F E) - 1))
    (h2 : At (evFin F v) (Algebra.norm (AF F) (z : AE F E) - 1)) :
    χ z = χv zv ∧ ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) : ℝ) =
      (sbClass (Fv F v)).modu (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) zv) := by
  refine ⟨?_, ?_⟩
  · rw [← hχ z h1]
    congr 1
    exact Units.ext hz
  · have h := GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at F v (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) h2
    rw [show Units.map (evFin F v : AF F →* Fv F v) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) =
      Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) zv from
        Units.ext ((GlobalTheory.NormAtPlace.evFin_norm_eq F E v z).trans (congrArg _ hz))] at h
    exact h

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ a b JA B κ _ dA ψ χ omB hψ _ hB _ _ hW v _ inst eB heB omL homL co hco χv hχv`. Take `rfl : inst = GlobalTheory.VacAny.invTwoV v` from `Subsingleton.elim _ _`. Use `letI := GlobalTheory.VacAny.invTwoV v`. Take `⟨-, ddA, omdA, hdd, ⟨-, hS, hSieg⟩, hbox⟩` from `hW`. Establish `hD` using `GlobalTheory.DblSchr.isDblCoord_dblD (cv σ v) co`.

Use `set dd := GlobalTheory.DblSchr.dblD (cv σ v) co`. Establish `hcod : ∀ x, dd.e x = locCo ddA v (x.map (liftE v))` using `fun x => by`. Rewrite using `[← Matrix.fromCols_toCols x, hD, Matrix.fromCols_map, hco, hco]`. Apply the tactic sequence `ext (k | k) <;> simp [locCo, hdd _ _]`. Take `⟨omd, hact, hspl⟩` from `exists_loc_splitting σ v (dbl_map v B.J) ddA hψ hS dd hcod`.

Use `⟨dd, omd, hD, ⟨isLagr_diagCols _ _, hspl, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `l _ hl p t hp φ hφ`. Take `⟨r, hr, c₀, hc₀, μ, hμ, hint, -⟩` from `GlobalTheory.DiagLocal.exists_local (ι := κ) v`. Take `⟨c, hc⟩` from `diag_eq_mul_integral (psiAt ψ v) (GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) l (fun x y f hf => by`. Use `hl (co.e.symm (x, y)) f hf` as an intermediate fact.

Rewrite using `[Darboux.rho, diag_mul, hD, LinearEquiv.apply_symm_apply] at this) μ hμ` and apply the resulting hypothesis. Set `tA : GL (Fin b) (AE F E)` to `Units.map (liftM v (Fin b)) t`. Establish `hDm : (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)).map (compFin F E v) = diagCols (Fin b)`. Rewrite using `[diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hpA : ((liftU σ v (dbl_map v B.J) p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (tA : Matrix (Fin b) (Fin b) (AE F E))` using `liftM_mul_of v _ _ _ (by rw [hDm]; exact hp)`.

Take `⟨h1, h2, -⟩` from `GlobalTheory.InertLagLevi.levi_det F E σ hσ b B.J hB v _ tA (liftM_at v _) hpA`. Take `⟨s1, s2⟩` from `scalar_eq χ v χv hχv (Matrix.GeneralLinearGroup.det tA) (Matrix.GeneralLinearGroup.det t) (((compFin F E v).map_det _).trans (congrArg Matrix.det (liftM_map v _))) h1 h2`. Establish `key` using `hSieg _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by`. Rewrite using `[diag_mul, Darboux.rho, hdd z z]`. Conclude with `GlobalTheory.DiagForm.lDiag_schr ψ _ _ hΦ) _ tA hpA _ (hr φ hφ).2`.

Rewrite `key` using `[hact p φ hφ r (hr φ hφ), hint _ (hspl.pres p φ hφ), hint φ hφ, s1, s2, mul_left_comm]`. Rewrite using `[hc _ (hspl.pres p φ hφ), hc φ hφ, mul_left_cancel₀ hc₀ key, mul_left_comm]`. Introduce `g gd hg φ₁ h₁ φ₂ h₂`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest κ v`. Establish `hg1 : liftM v (Fin b) (g : GL (Fin b) (Fv F v ⊗[F] E)) = mat (eB.symm g).1`.

Use `heB.1 (eB.symm g)` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `liftM_comp v _ (eB.symm g).2`. Establish `hgA : ((liftU σ v (dbl_map v B.J) gd : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = Matrix.fromBlocks (mat (eB.symm g).1) 0 0 1`.

Rewrite using `[liftU_val, hg, ← hg1, liftM_fromBlocks]`. Establish `hrb` using `GlobalTheory.DblSwap.rest_box v (hR φ₁ h₁) (hR φ₂ h₂)`. Use `GlobalTheory.DblSwap.eq_of_tens_ne v hrb.1 (x₀ := 0) (mul_ne_zero hR0 hR0) ?_` and prove the remaining obligations. Rewrite using `[← hact gd _ (GlobalTheory.DblSwap.box_mem_SB h₁ h₂) _ hrb, GlobalTheory.DblSwap.tens_box, GlobalTheory.DblSwap.tens_box, hbox _ _ hgA _ (hR φ₁ h₁).2 _ (hR φ₂ h₂).2]`. Conclude with `congrArg (boxFun · _) ((homL g φ₁ h₁).2 R (hR φ₁ h₁))`.
-/
theorem exists_dbl_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ) (χ : Chr F E)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → JA.det ≠ 0 → B.J.det ≠ 0 →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ a → IsHecke F E χ →
    IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F B.J) dA χ omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    ∀ χv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χ v χv →
    ∃ (dd : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (dbl (GlobalTheory.HoweLocal.Jv v B.J))) (κ ⊕ κ))
      (omd : UG (GlobalTheory.HoweLocal.cv σ v) (dbl (GlobalTheory.HoweLocal.Jv v B.J)) →* Module.End ℂ ((κ ⊕ κ → Fv F v) → ℂ)),
      IsDblCoord (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA) (GlobalTheory.HoweLocal.Jv v B.J) co dd ∧
      IsUWeilSplit (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (dbl (GlobalTheory.HoweLocal.Jv v B.J)) dd χv (diagCols (Fin b)) omd ∧
      ∀ (g : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J))
        (gd : UG (GlobalTheory.HoweLocal.cv σ v) (dbl (GlobalTheory.HoweLocal.Jv v B.J))),
        ((gd : GL (Fin b ⊕ Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (Fv F v ⊗[F] E)) =
          Matrix.fromBlocks ((g : GL (Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b) (Fin b) (Fv F v ⊗[F] E)) 0 0 1 →
        ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), omd gd (boxFun φ₁ φ₂) = boxFun (omL g φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ hσ a b JA B κ _ dA ψ χ omB hψ _ hB _ _ hW v _ inst eB heB omL homL co hco χv hχv
  obtain rfl : inst = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  letI := GlobalTheory.VacAny.invTwoV v
  obtain ⟨-, ddA, omdA, hdd, ⟨-, hS, hSieg⟩, hbox⟩ := hW
  have hD := GlobalTheory.DblSchr.isDblCoord_dblD (cv σ v) co
  set dd := GlobalTheory.DblSchr.dblD (cv σ v) co
  have hcod : ∀ x, dd.e x = locCo ddA v (x.map (liftE v)) := fun x => by
    rw [← Matrix.fromCols_toCols x, hD, Matrix.fromCols_map, hco, hco]
    ext (k | k) <;> simp [locCo, hdd _ _]
  obtain ⟨omd, hact, hspl⟩ := exists_loc_splitting σ v (dbl_map v B.J) ddA hψ hS dd hcod
  refine ⟨dd, omd, hD, ⟨isLagr_diagCols _ _, hspl, ?_⟩, ?_⟩
  · intro l _ hl p t hp φ hφ
    obtain ⟨r, hr, c₀, hc₀, μ, hμ, hint, -⟩ := GlobalTheory.DiagLocal.exists_local (ι := κ) v
    obtain ⟨c, hc⟩ := diag_eq_mul_integral (psiAt ψ v) (GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) l (fun x y f hf => by
        have := hl (co.e.symm (x, y)) f hf
        rwa [Darboux.rho, diag_mul, hD, LinearEquiv.apply_symm_apply] at this) μ hμ
    let tA : GL (Fin b) (AE F E) := Units.map (liftM v (Fin b)) t
    have hDm : (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)).map (compFin F E v) = diagCols (Fin b) := by
      rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
    have hpA : ((liftU σ v (dbl_map v B.J) p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) =
        diagCols (Fin b) * (tA : Matrix (Fin b) (Fin b) (AE F E)) :=
      liftM_mul_of v _ _ _ (by rw [hDm]; exact hp)
    obtain ⟨h1, h2, -⟩ := GlobalTheory.InertLagLevi.levi_det F E σ hσ b B.J hB v _ tA (liftM_at v _) hpA
    obtain ⟨s1, s2⟩ := scalar_eq χ v χv hχv (Matrix.GeneralLinearGroup.det tA) (Matrix.GeneralLinearGroup.det t)
      (((compFin F E v).map_det _).trans (congrArg Matrix.det (liftM_map v _))) h1 h2
    have key := hSieg _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by
      rw [diag_mul, Darboux.rho, hdd z z]
      exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ hΦ) _ tA hpA _ (hr φ hφ).2
    rw [hact p φ hφ r (hr φ hφ), hint _ (hspl.pres p φ hφ), hint φ hφ, s1, s2, mul_left_comm] at key
    rw [hc _ (hspl.pres p φ hφ), hc φ hφ, mul_left_cancel₀ hc₀ key, mul_left_comm]
  · intro g gd hg φ₁ h₁ φ₂ h₂
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
    have hg1 : liftM v (Fin b) (g : GL (Fin b) (Fv F v ⊗[F] E)) = mat (eB.symm g).1 := by
      have := heB.1 (eB.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      exact liftM_comp v _ (eB.symm g).2
    have hgA : ((liftU σ v (dbl_map v B.J) gd : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
        Matrix.fromBlocks (mat (eB.symm g).1) 0 0 1 := by
      rw [liftU_val, hg, ← hg1, liftM_fromBlocks]
    have hrb := GlobalTheory.DblSwap.rest_box v (hR φ₁ h₁) (hR φ₂ h₂)
    refine GlobalTheory.DblSwap.eq_of_tens_ne v hrb.1 (x₀ := 0) (mul_ne_zero hR0 hR0) ?_
    rw [← hact gd _ (GlobalTheory.DblSwap.box_mem_SB h₁ h₂) _ hrb, GlobalTheory.DblSwap.tens_box, GlobalTheory.DblSwap.tens_box,
      hbox _ _ hgA _ (hR φ₁ h₁).2 _ (hR φ₂ h₂).2]
    exact congrArg (boxFun · _) ((homL g φ₁ h₁).2 R (hR φ₁ h₁))

end GlobalTheory.HoweLocal.DblLocal
