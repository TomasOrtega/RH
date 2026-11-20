import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

/- English proof (translation)
Establish `hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥` using `fun h => ha (by`. Establish `: a ∈ (IsLocalRing.maximalIdeal B).comap f` using `hf`. Rewrite using `[h, Ideal.mem_bot] at this)` and apply the resulting hypothesis. Establish `hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hne`. Establish `he` using `IsLocalRing.eq_maximalIdeal hm`.

Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `: x ∈ (IsLocalRing.maximalIdeal B).comap f` using `by rw [he]; exact h`. Conclude with `this hx`.
-/
theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

/- English proof (translation)
Establish `hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B` using `Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx`. Use `continuous_of_continuousAt_zero f.toAddMonoidHom ?_` and prove the remaining obligations. Introduce `s hs`. Rewrite `hs` using `[map_zero]`. Take `⟨n, hn⟩` from `(isAdic_iff.1 hB).2 s hs`.

Use `Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_)` and prove the remaining obligations. Establish `h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n)` using `Ideal.mem_map_of_mem _ hx`. Rewrite `h1` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm n h1`.
-/
theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨l, hl0, hl⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Establish `hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1)`. Introduce `Y`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Y]`.

Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Establish `key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0`. Introduce `Y`.

Establish `hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f)` using `h ▸ Submodule.mem_top`. Proceed by induction on `hY using Submodule.span_induction with`. Consider the case `mem Y hY`. Take `⟨g, rfl⟩` from `hY`. Establish `h0 : l (M g) = 0` using `hl (Submodule.subset_span ⟨g, rfl⟩)`.

Use `congrArg f ((hexp (M g)).symm.trans h0)` as an intermediate fact. Simplify `this` using `[map_sum]`. Consider the case `zero => simp`. Consider the case `add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]`. Consider the case `smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]`.

Apply `hl0` to reduce the goal to its premises. Use `LinearMap.ext fun Y => ?_` and prove the remaining obligations. Rewrite using `[hexp, LinearMap.zero_apply]`. Use `Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Establish `h1` using `key (Matrix.single p q 1)`.

Rewrite `h1` using `[Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp), Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)]`. Simplify using `only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1`. Rewrite using `[h1, mul_zero]`.
-/
theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)
      simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises. Set `d : Fin t → FractionRing A` to `fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)`. Establish `h1 : Matrix.toLin' ((mat σ g).map (toFr A)) = e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d)))`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `u`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, LinearMap.prodMap_apply]`. Use `(he g u).trans ?_` and prove the remaining obligations. Use extensionality with `c`.

Both sides reduce to the same expression. Simplify using `[Matrix.mulVec_diagonal, d]`. Establish `h2` using `congrArg (LinearMap.trace _ _) h1`. Rewrite `h2` using `[LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]`. Rewrite using `[map_add, map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]`.

Conclude with `h2`.
-/
theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2
  rw [map_add, map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

/- English proof (translation)
The claim follows from `(iotaO N A i).charZero`.
-/
theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i))`. Introduce `x y h`. Establish `hx` using `A.iotaQ_alg i x`. Rewrite `hx` using `[h, A.iotaQ_alg i y]`. Conclude with `(Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm`.

Establish `: FaithfulSMul ℤ_[N.l i] (N.O i)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i]` using `PadicInt.p_nonunit`. Use `map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

/- English proof (translation)
Use `charZero_O N₀ A₀ i₀` as an intermediate fact. Establish `hl : (N₁.l i₁).Prime` using `Fact.out`. Use `isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_` and prove the remaining obligations. Rewrite using `[map_natCast]`. Conclude with `l_mem_maximalIdeal N₁ A₁ i₁`.
-/
theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

/- English proof (translation)
The claim follows from `haveI := isLocalHom_φ a continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ`.
-/
theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

/- English proof (translation)
Use `haveI := (N₁.O_complete i₁).toIsHausdorff`. Use `haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance`. Use `congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace) ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ`. Take `⟨B₀, hB₀, hσ₀⟩` from `(a.frob w σ).1 ⟨B, hB, hσ⟩`.

Establish `e₀` using `h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀`. Establish `e₁` using `h₁.2.2 w (h hw) B σ hB hσ`. Rewrite `e₁` using `[GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map]`. Rewrite using `[AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]`.
-/
theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

/- English proof (translation)
Introduce and unpack `hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩`. Establish `hπ₀` using `(a.Z π).1 hπ`. Take `⟨ρ₀, hd₀⟩` from `hZ _ hπ₀ _ (hr₀ _)`. Use `⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩` and prove the remaining obligations. Establish `htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace`.

Introduce `g`. Establish `h` using `trace_eq hC a π _ r (hr₀ _) hr g`. Rewrite `h` using `[trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add, map_sum, Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g]`. Conclude with `add_right_cancel h`. Use `haveI := isLocalHom_φ a`.

Establish `hpos` using `pos_of_absIrrSub _ habs`. Use `haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩`. Use `absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)` and prove the remaining obligations. Establish `h` using `span_eq_top_of_trace_eq ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom) (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)`. Rewrite using `[eq_top_iff, ← h]`.

Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨a.γ g, (mat_mapRep _ _ _).symm⟩`. Express the relevant statement in the definitionally equal form `(mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)) (a.γ g)).trace = _`. Rewrite using `[mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]`.
-/
theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g
    rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add, map_sum,
      Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
