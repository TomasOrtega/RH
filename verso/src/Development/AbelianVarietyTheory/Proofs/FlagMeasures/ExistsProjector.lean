import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.WittInt

/- English proof (translation)
Establish `hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ` using `fun y => by`. Establish `hy : y ∈ Submodule.span K (Λ : Set V)` using `by rw [hspan]; trivial`. Take `⟨s, hs⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy`. Rewrite `hs` using `[Submodule.span_eq]`. Conclude with `⟨s, hs⟩`.

Establish `hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s)` using `fun s => by`. Use `isLocalizedModule_id (nonZeroDivisors O) V K` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s`. Establish `hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype` using `{ map_units := hunit surj := fun y => by`. Take `⟨s, hs⟩` from `hmul y`.

Conclude with `⟨(⟨_, hs⟩, s), rfl⟩`. Use `exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }`. Establish `hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0` using `fun s => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Establish `hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W` using `fun s v h => by`. Rewrite `h` using `[← algebraMap_smul K]`.

Conclude with `(W.smul_mem_iff (hne s)).1 h`. Establish `: Module.Finite O Λ` using `Module.Finite.iff_fg.2 hfg`. Set `Q : Submodule O Λ` to `(W.restrictScalars O).comap Λ.subtype`. Establish `: Module.Flat O (Λ ⧸ Q)`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`.

Introduce `q hq`. Take `⟨v, rfl⟩` from `Q.mkQ_surjective q`. Take `⟨c, hc⟩` from `hq`. Establish `h1 : Q.mkQ ((c : O) • v) = 0` using `by rw [map_smul]; exact hc`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hsat c v h1`. Establish `: Module.FinitePresentation O (Λ ⧸ Q)` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective O (Λ ⧸ Q)` using `Module.Flat.projective_of_finitePresentation`. Take `⟨s, hs⟩` from `Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective`.

Set `π : Λ →ₗ[O] Λ` to `LinearMap.id - s ∘ₗ Q.mkQ`. Establish `hπ : ∀ v, π v ∈ Q`. Introduce `v`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]`. Establish `h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v` using `LinearMap.congr_fun hs _`.

Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]`. Establish `hπ' : ∀ v ∈ Q, π v = v`. Introduce `v hv`. Establish `h1 : Q.mkQ v = 0` using `by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]`.

Set `g : V →ₗ[K] V` to `LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)`. Establish `hg : ∀ y : Λ, g y = π y` using `fun y => IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y`. Use `⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hg ⟨z, hz⟩]`. Conclude with `(π _).2`.

Take `⟨c, hc⟩` from `hmul z`. Use `hsat c _ ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.map_smul_of_tower]`. Use `hg ⟨_, hc⟩` as an intermediate fact. Rewrite using `[show g ((c : O) • z) = _ from this]`.

Conclude with `hπ _`. Take `⟨c, hc⟩` from `hmul z`. Establish `h1` using `hg ⟨_, hc⟩`. Rewrite `h1` using `[hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)]`. Establish `h2 : g (algebraMap O K c • z) = algebraMap O K c • z`.

Rewrite using `[algebraMap_smul]`. Conclude with `h1`. Rewrite `h2` using `[map_smul]`. Conclude with `smul_right_injective V (hne c) h2`.
-/
theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ z ∈ Λ, P z ∈ Λ) ∧ (∀ z, P z ∈ W) ∧ ∀ z ∈ W, P z = z := by
  have hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ := fun y => by
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨s, hs⟩
  have hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨s, hs⟩ := hmul y
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W := fun s v h => by
    rw [← algebraMap_smul K] at h
    exact (W.smul_mem_iff (hne s)).1 h
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := (W.restrictScalars O).comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c v h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y
  refine ⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact (π _).2
  · obtain ⟨c, hc⟩ := hmul z
    refine hsat c _ ?_
    rw [← LinearMap.map_smul_of_tower]
    have := hg ⟨_, hc⟩
    rw [show g ((c : O) • z) = _ from this]
    exact hπ _
  · obtain ⟨c, hc⟩ := hmul z
    have h1 := hg ⟨_, hc⟩
    rw [hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)] at h1
    have h2 : g (algebraMap O K c • z) = algebraMap O K c • z := by
      rw [algebraMap_smul]; exact h1
    rw [map_smul] at h2
    exact smul_right_injective V (hne c) h2

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

/- English proof (translation)
Rewrite using `[← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]`.
-/
theorem form_star {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]

/- English proof (translation)
Rewrite using `[mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]`.
-/
theorem form_adj {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    star (M *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ ((J⁻¹ * Mᴴ * J) *ᵥ y)) := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/- English proof (translation)
Apply `eq_zero_of_mulVec_eq_zero hd` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `h (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[← Pi.single_star]`.
-/
theorem form_nondeg {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (y : Fin n → E)
    (h : ∀ x : Fin n → E, star x ⬝ᵥ (J *ᵥ y) = 0) : y = 0 := by
  apply eq_zero_of_mulVec_eq_zero hd
  funext i
  have := h (Pi.single i 1)
  simpa [← Pi.single_star] using this

/- English proof (translation)
Take `⟨M, rfl⟩` from `Matrix.toLin'.surjective P`. Use `⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle, mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]`.
-/
theorem exists_adjoint {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0)
    (P : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ Q : (Fin n → E) →ₗ[E] (Fin n → E),
      (∀ x y, star (P x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ Q y)) ∧
      LinearMap.trace E _ Q = star (LinearMap.trace E _ P) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective P
  refine ⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle,
    mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]

end Form

/- English proof (translation)
Take `⟨P, hPΛ, hPW, hPid⟩` from `exists_projector Λ hΛ.fg hΛ.span_eq_top W`. Take `⟨Q, hPQ, htr⟩` from `exists_adjoint hd P`. Establish `hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y)` using `fun x y => by`. Rewrite using `[← form_star hJ, ← hPQ, form_star hJ]`. Establish `hQΛ : ∀ z ∈ Λ, Q z ∈ Λ` using `fun z hz => (hself _).2 fun y hy => by`.

Rewrite using `[← hPQ]`. Conclude with `(hself z).1 hz _ (hPΛ y hy)`. Establish `hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0` using `fun y hy => form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)`. Establish `hQW : ∀ y ∈ W, Q y = 0` using `fun y hy => hQ0 y fun x hx => hW x hx y hy`. Establish `hPP : ∀ y, P (P y) = P y` using `fun y => hPid _ (hPW y)`.

Establish `hQQ : ∀ y, Q (Q y) = Q y` using `fun y => by`. Rewrite using `[← sub_eq_zero]`. Use `form_nondeg hd _ fun x => ?_` and prove the remaining obligations. Rewrite using `[mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]`. Establish `hQPz : ∀ y, Q (P y) = 0` using `fun y => hQW _ (hPW y)`.

Set `T : (Fin n → E) →ₗ[E] (Fin n → E)` to `Q - (w : E) • (P ∘ₗ Q)`. Establish `hT : ∀ y, T y = Q y - (w : E) • P (Q y)` using `fun y => rfl`. Establish `hQT : ∀ y, Q (T y) = Q y` using `fun y => by`. Rewrite using `[hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]`. Establish `hTT : ∀ y, T (T y) = T y` using `fun y => by rw [hT (T y), hQT, hT]`.

Establish `hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y)` using `fun x hx y => by`. Rewrite using `[hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]`. Establish `hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y)))` using `fun x y => by`. Rewrite using `[hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul]`. Use `⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero, dotProduct_zero]`. Establish `h1 : LinearMap.IsProj W P` using `⟨hPW, hPid⟩`. Establish `h2 : LinearMap.IsProj (LinearMap.range T) T` using `⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩`. Establish `h3 : Q ∘ₗ P = 0` using `LinearMap.ext hQPz`.

Establish `h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q`. Simplify using `only [T]`. Rewrite using `[map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]`. Rewrite `h4` using `[h2.trace, htr, h1.trace, star_natCast]`. Conclude with `h4` after adjusting the coercions.

Introduce and unpack `_ ⟨y, rfl⟩ hy`. Establish `h0 : Q y = 0` using `hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx`. Rewrite using `[hT, h0, map_zero, smul_zero, sub_zero]`. Establish `hTz : T z ∈ Λ` using `Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))`. Establish `hu : z - T z ∈ Λ` using `Λ.sub_mem hz hTz`.

Establish `hxW : P (z - T z) ∈ W` using `hPW _`. Establish `hQu : Q (z - T z) = 0` using `by rw [map_sub, hQT, sub_self]`. Use `⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, _, ⟨b, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 ht`. Rewrite using `[star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self, sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub, mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, su …`.
-/
theorem split_of_trace (E : Type) [Field E] [NumberField E] [StarRing E] (w : 𝓞 E)
    (hw : (w : E) + star (w : E) = 1) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (hd : J.det ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hself : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (W : Submodule E (Fin n → E)) (hW : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) :
    ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧
      Module.finrank E W' = Module.finrank E W ∧
      (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧
      ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧
        ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  obtain ⟨P, hPΛ, hPW, hPid⟩ := exists_projector Λ hΛ.fg hΛ.span_eq_top W
  obtain ⟨Q, hPQ, htr⟩ := exists_adjoint hd P
  have hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y) := fun x y => by
    rw [← form_star hJ, ← hPQ, form_star hJ]
  have hQΛ : ∀ z ∈ Λ, Q z ∈ Λ := fun z hz => (hself _).2 fun y hy => by
    rw [← hPQ]; exact (hself z).1 hz _ (hPΛ y hy)
  have hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0 := fun y hy =>
    form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)
  have hQW : ∀ y ∈ W, Q y = 0 := fun y hy => hQ0 y fun x hx => hW x hx y hy
  have hPP : ∀ y, P (P y) = P y := fun y => hPid _ (hPW y)
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    rw [← sub_eq_zero]
    refine form_nondeg hd _ fun x => ?_
    rw [mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]
  have hQPz : ∀ y, Q (P y) = 0 := fun y => hQW _ (hPW y)
  let T : (Fin n → E) →ₗ[E] (Fin n → E) := Q - (w : E) • (P ∘ₗ Q)
  have hT : ∀ y, T y = Q y - (w : E) • P (Q y) := fun y => rfl
  have hQT : ∀ y, Q (T y) = Q y := fun y => by
    rw [hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]
  have hTT : ∀ y, T (T y) = T y := fun y => by rw [hT (T y), hQT, hT]
  have hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y) := fun x hx y => by
    rw [hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]
  have hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) =
      star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y))) := fun x y => by
    rw [hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub,
      dotProduct_sub, mulVec_smul, dotProduct_smul]
  refine ⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero,
      dotProduct_zero]
  · have h1 : LinearMap.IsProj W P := ⟨hPW, hPid⟩
    have h2 : LinearMap.IsProj (LinearMap.range T) T :=
      ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩
    have h3 : Q ∘ₗ P = 0 := LinearMap.ext hQPz
    have h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q := by
      simp only [T]
      rw [map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]
    rw [h2.trace, htr, h1.trace, star_natCast] at h4
    exact_mod_cast h4
  · rintro _ ⟨y, rfl⟩ hy
    have h0 : Q y = 0 := hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx
    rw [hT, h0, map_zero, smul_zero, sub_zero]
  · have hTz : T z ∈ Λ := Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))
    have hu : z - T z ∈ Λ := Λ.sub_mem hz hTz
    have hxW : P (z - T z) ∈ W := hPW _
    have hQu : Q (z - T z) = 0 := by rw [map_sub, hQT, sub_self]
    refine ⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self,
      sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub,
      mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, sub_self, sub_self]

/- English proof (translation)
Introduce `E _ _ _ hE n J hJ hd Λ hΛ hs W hW`. Take `⟨w, hw⟩` from `GlobalTheory.TraceOnto.exists_trace_one E hE`. Conclude with `split_of_trace E w hw n J hJ hd Λ hΛ hs W hW`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ W : Submodule E (Fin n → E), (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧ Module.finrank E W' = Module.finrank E W ∧ (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧ ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  intro E _ _ _ hE n J hJ hd Λ hΛ hs W hW
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one E hE
  exact split_of_trace E w hw n J hJ hd Λ hΛ hs W hW

end GlobalTheory.WittInt
