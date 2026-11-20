import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentResolvent

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Polynomial Cardinal

namespace GlobalTheory.LocGL

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub`. Consider the case `exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub`. Consider the case `(apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub ..)`.
-/
theorem exists_not_isUnit_sub [Nontrivial V] (hV : Module.rank ℂ V ≤ ℵ₀) (T : Module.End ℂ V) :
    ∃ c : ℂ, ¬ IsUnit (T - algebraMap ℂ _ c) := by
  first
  | exact @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | (apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub ..)

variable {G : Type} [Group G]

/- English proof (translation)
Use `Model.nontrivial_of_isIrreducible hi` as an intermediate fact. Take `⟨c, hc⟩` from `exists_not_isUnit_sub hV T.toLinearMap`. Set `S : π.IntertwiningMap π` to `T - c • .id π`. Break down `Representation.IsIrreducible.bijective_or_eq_zero S with h | h` into its components or cases. Conclude with `absurd ((Module.End.isUnit_iff _).2 h) hc`.

Conclude with `⟨c, fun v => sub_eq_zero.1 (congrArg (fun f : π.IntertwiningMap π => f v) h)⟩`.
-/
theorem exists_eq_smul_of_rank_le {π : Representation ℂ G V} (hi : π.IsIrreducible) (hV : Module.rank ℂ V ≤ ℵ₀)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨c, hc⟩ := exists_not_isUnit_sub hV T.toLinearMap
  let S : π.IntertwiningMap π := T - c • .id π
  rcases Representation.IsIrreducible.bijective_or_eq_zero S with h | h
  · exact absurd ((Module.End.isUnit_iff _).2 h) hc
  · exact ⟨c, fun v => sub_eq_zero.1 (congrArg (fun f : π.IntertwiningMap π => f v) h)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

/- English proof (translation)
Take `⟨D, hD, hd⟩` from `TopologicalSpace.exists_countable_dense G`. Use `(hD.image fun g => π g v).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Take `⟨x, hx, hxD⟩` from `hd.inter_open_nonempty _ ((hs v).preimage (continuous_const_mul g⁻¹)) ⟨g, by simp⟩`. Use `⟨x, hxD, ?_⟩` and prove the remaining obligations.

Establish `hx' : π (g⁻¹ * x) v = v` using `hx`. Use `show π x v = π g v`. Use `conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`.
-/
theorem countable_orbit {π : Representation ℂ G V} (hs : IsSmooth π) (v : V) : (Set.range fun g => π g v).Countable := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense G
  refine (hD.image fun g => π g v).mono ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ ((hs v).preimage (continuous_const_mul g⁻¹)) ⟨g, by simp⟩
  refine ⟨x, hxD, ?_⟩
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/- English proof (translation)
Use `Model.nontrivial_of_isIrreducible hi` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `ht : Submodule.span ℂ (Set.range fun g => π g v) = ⊤`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨f, rfl⟩` from `orbitMap_surjective hi hv w`.

Use `show π.asAlgebraHom f v ∈ _`. Proceed by induction on `f using MonoidAlgebra.induction_on with`. Consider the case `of g => exact Submodule.subset_span ⟨g, by simp⟩`. Consider the case `add a b ha hb => rw [map_add, LinearMap.add_apply]`. Conclude with `add_mem (ha trivial) (hb trivial)`.

Consider the case `smul c a ha => rw [map_smul, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (ha trivial)`. Rewrite using `[← rank_top, ← ht]`. Conclude with `(rank_span_le _).trans (le_aleph0_iff_set_countable.2 (countable_orbit hs v))`.
-/
theorem rank_le_aleph0_of_isIrreducible {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ V ≤ ℵ₀ := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ht : Submodule.span ℂ (Set.range fun g => π g v) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨f, rfl⟩ := orbitMap_surjective hi hv w
    show π.asAlgebraHom f v ∈ _
    induction f using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span ⟨g, by simp⟩
    | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem (ha trivial) (hb trivial)
    | smul c a ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (ha trivial)
  rw [← rank_top, ← ht]
  exact (rank_span_le _).trans (le_aleph0_iff_set_countable.2 (countable_orbit hs v))

/- English proof (translation)
The claim follows from `exists_eq_smul_of_rank_le hi (rank_le_aleph0_of_isIrreducible hs hi) T`.
-/
theorem exists_eq_smul_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  exists_eq_smul_of_rank_le hi (rank_le_aleph0_of_isIrreducible hs hi) T

/- English proof (translation)
Use `Model.nontrivial_of_isIrreducible hi` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Use `⟨fun a b h => smul_left_injective ℂ hv (congrArg (fun f : π.IntertwiningMap π => f v) h), fun T => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_eq_smul_of_isSmooth hs hi T`. Conclude with `⟨c, by ext w; exact (hc w).symm⟩`.
-/
theorem algebraMap_intertwiningMap_bijective_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨fun a b h => smul_left_injective ℂ hv (congrArg (fun f : π.IntertwiningMap π => f v) h), fun T => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSmooth hs hi T
  exact ⟨c, by ext w; exact (hc w).symm⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k n) in

/- English proof (translation)
Establish `: SecondCountableTopology k`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne := { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Establish `: ProperSpace k` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`. Use `infer_instance`. Establish `: SecondCountableTopology (Matrix n n k)` using `inferInstanceAs (SecondCountableTopology (n → n → k))`. Establish `: SecondCountableTopology (Matrix n n k)ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountableTopology_GL : SecondCountableTopology (GL n k) := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  have : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  have : SecondCountableTopology (Matrix n n k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
The claim follows from `haveI := secondCountableTopology_GL k n exists_eq_smul_of_isSmooth hs hi T`.
-/
theorem schur_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  haveI := secondCountableTopology_GL k n
  exists_eq_smul_of_isSmooth hs hi T

/- English proof (translation)
The claim follows from `haveI := secondCountableTopology_GL k n algebraMap_intertwiningMap_bijective_of_isSmooth hs hi`.
-/
theorem algebraMap_intertwiningMap_bijective_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) :=
  haveI := secondCountableTopology_GL k n
  algebraMap_intertwiningMap_bijective_of_isSmooth hs hi

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `Units.continuous_map (f := (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom) ?_` and prove the remaining obligations. Conclude with `(continuous_pi fun _ => continuous_id).matrix_diagonal`.
-/
theorem continuous_glScalar : Continuous (GeneralLinearGroup.scalar n : kˣ → GL n k) := by
  refine Units.continuous_map (f := (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom) ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `: (ω.ker : Set kˣ) = GeneralLinearGroup.scalar n ⁻¹' {g | π g v = v}`. Use extensionality with `z`. Use `show ω z = 1 ↔ π (GeneralLinearGroup.scalar n z) v = v`. Rewrite using `[h]`.

Conclude with `⟨fun e => by simp [e], fun e => Units.ext (smul_left_injective ℂ hv (e.trans (one_smul _ _).symm))⟩`. Use `show IsOpen (ω.ker : Set kˣ)`. Rewrite using `[this]`. Conclude with `(hs v).preimage continuous_glScalar`.
-/
theorem isSmoothChar_of_hasCentralChar [Nontrivial V] {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : IsSmoothChar ω := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (ω.ker : Set kˣ) = GeneralLinearGroup.scalar n ⁻¹' {g | π g v = v} := by
    ext z
    show ω z = 1 ↔ π (GeneralLinearGroup.scalar n z) v = v
    rw [h]
    exact ⟨fun e => by simp [e], fun e => Units.ext (smul_left_injective ℂ hv (e.trans (one_smul _ _).symm))⟩
  show IsOpen (ω.ker : Set kˣ)
  rw [this]
  exact (hs v).preimage continuous_glScalar

/- English proof (translation)
Use `Model.nontrivial_of_isIrreducible hi` as an intermediate fact. Take `⟨w₀, hw₀⟩` from `exists_ne (0 : V)`. Establish `key : ∀ z : kˣ, ∃ c : ℂ, ∀ w, π (GeneralLinearGroup.scalar n z) w = c • w` using `fun z => schur_GL hs hi ⟨π (GeneralLinearGroup.scalar n z), fun g => by`. Rewrite using `[← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]⟩`. Use `choose c hc using key`.

Establish `: ∃ ω, HasCentralChar π ω`. Use `⟨MonoidHom.toHomUnits ⟨⟨c, smul_left_injective ℂ hw₀ ?_⟩, fun x y => smul_left_injective ℂ hw₀ ?_⟩, hc⟩` and prove the remaining obligations. Simplify using `[← hc]`. Simplify using `only [← hc, mul_smul, map_mul, Module.End.mul_apply]`. Take `⟨ω, hω⟩` from `this`.

Conclude with `⟨ω, isSmoothChar_of_hasCentralChar hs hω, hω⟩`.
-/
theorem exists_smooth_hasCentralChar {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  have key : ∀ z : kˣ, ∃ c : ℂ, ∀ w, π (GeneralLinearGroup.scalar n z) w = c • w := fun z =>
    schur_GL hs hi ⟨π (GeneralLinearGroup.scalar n z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]⟩
  choose c hc using key
  have : ∃ ω, HasCentralChar π ω := by
    refine ⟨MonoidHom.toHomUnits ⟨⟨c, smul_left_injective ℂ hw₀ ?_⟩, fun x y => smul_left_injective ℂ hw₀ ?_⟩, hc⟩
    · simp [← hc]
    · simp only [← hc, mul_smul, map_mul, Module.End.mul_apply]
  obtain ⟨ω, hω⟩ := this
  exact ⟨ω, isSmoothChar_of_hasCentralChar hs hω, hω⟩

section CentralChar

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Conclude with `MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv ((h z v).symm.trans (h' z v)))`.
-/
theorem centralChar_unique [Nontrivial V] {π : Representation ℂ (GL n R) V} {ω ω' : Rˣ →* ℂˣ}
    (h : HasCentralChar π ω) (h' : HasCentralChar π ω') : ω = ω' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv ((h z v).symm.trans (h' z v)))

/- English proof (translation)
Introduce `z w` and use `by obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w show σ _ (φ.toIntertwiningMap v) = _ • φ.toIntertwiningMap v rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]`.
-/
theorem hasCentralChar_of_equiv {π : Representation ℂ (GL n R) V} {σ : Representation ℂ (GL n R) W} (φ : π.Equiv σ)
    {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := fun z w => by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ _ (φ.toIntertwiningMap v) = _ • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

/- English proof (translation)
Introduce `z v` and use `by have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by ext; simp [GeneralLinearGroup.scalar] rw [twist_apply, h, detChar_apply, this, smul_smul, mul_comm] simp`.
-/
theorem hasCentralChar_twist {π : Representation ℂ (GL n R) V} {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω)
    (χ : Rˣ →* ℂˣ) : HasCentralChar (twist π (detChar n χ)) (ω * χ ^ Fintype.card n) := fun z v => by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  rw [twist_apply, h, detChar_apply, this, smul_smul, mul_comm]
  simp

end CentralChar

namespace IrrGL

/- English proof (translation)
Use `Model.nontrivial_of_isIrreducible x.2.rep.irr` as an intermediate fact. Take `⟨ω, -, hω⟩` from `exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr`. Take `⟨φ⟩` from `IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h)`. Establish `h1` using `centralChar_unique (V := x.2.rep.V) (hasCentralChar_of_equiv φ (hasCentralChar_twist hω χ)) (hasCentralChar_twist hω ψ)`. Simplify using `using h1`.
-/
theorem pow_eq_of_tw_eq {x : IrrGL k} {χ ψ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} {hψ : IsSmoothChar ψ}
    (h : x.tw χ hχ = x.tw ψ hψ) : χ ^ x.1 = ψ ^ x.1 := by
  have := Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h)
  have h1 := centralChar_unique (V := x.2.rep.V) (hasCentralChar_of_equiv φ (hasCentralChar_twist hω χ)) (hasCentralChar_twist hω ψ)
  simpa using h1

/- English proof (translation)
Use `⟨fun h => ?_, fun h => by rw [h]⟩` and prove the remaining obligations. Establish `h1` using `pow_eq_of_tw_eq h`. Establish `h2 : ∀ (s : ℂ) (m : ℕ), absPow k s ^ m = absPow k (m * s)` using `fun s m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih => rw [pow_succ, ih, ← absPow_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2, h2]`.

Establish `h3 : absPow k ((x.1 * (s - t) : ℝ) : ℂ) = 1`. Rewrite using `[show ((x.1 * (s - t) : ℝ) : ℂ) = x.1 * s + -(x.1 * t) by push_cast; ring, absPow_add, absPow_neg, h1, mul_inv_cancel]`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 (absPow_ofReal_eq_one.1 h3)).resolve_left (Nat.cast_ne_zero.2 hx.ne'))`.
-/
theorem nu_ofReal_inj {x : IrrGL k} (hx : 0 < x.1) {s t : ℝ} : x.nu s = x.nu t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := pow_eq_of_tw_eq h
  have h2 : ∀ (s : ℂ) (m : ℕ), absPow k s ^ m = absPow k (m * s) := fun s m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← absPow_add]; congr 1; push_cast; ring
  rw [h2, h2] at h1
  have h3 : absPow k ((x.1 * (s - t) : ℝ) : ℂ) = 1 := by
    rw [show ((x.1 * (s - t) : ℝ) : ℂ) = x.1 * s + -(x.1 * t) by push_cast; ring, absPow_add, absPow_neg, h1,
      mul_inv_cancel]
  exact sub_eq_zero.1 ((mul_eq_zero.1 (absPow_ofReal_eq_one.1 h3)).resolve_left (Nat.cast_ne_zero.2 hx.ne'))

/- English proof (translation)
Simplify using `using nu_ofReal_inj hx (s := a) (t := b)`.
-/
theorem nu_intCast_inj {x : IrrGL k} (hx : 0 < x.1) {a b : ℤ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

/- English proof (translation)
Simplify using `using nu_ofReal_inj hx (s := a) (t := b)`.
-/
theorem nu_natCast_inj {x : IrrGL k} (hx : 0 < x.1) {a b : ℕ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

/- English proof (translation)
Simplify using `using nu_ofReal_inj hx (s := s) (t := 0)`.
-/
theorem nu_ofReal_eq_self {x : IrrGL k} (hx : 0 < x.1) {s : ℝ} : x.nu s = x ↔ s = 0 := by
  simpa using nu_ofReal_inj hx (s := s) (t := 0)

end IrrGL

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `_ _ h` and use `Fin.ext ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 h)`.
-/
theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun _ _ h =>
  Fin.ext ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 h)

/- English proof (translation)
The claim follows from `Finset.univ.nodup.map Δ.term_injective`.
-/
theorem nodup_ms (Δ : Segment k) : Δ.ms.Nodup := Finset.univ.nodup.map Δ.term_injective

/- English proof (translation)
Introduce `Δ Δ' h` and use `by have key : ∀ D : Segment k, D.first ∈ D.carrier := fun D => mem_carrier.2 ⟨0, D.len_pos, by simp⟩ obtain ⟨a, -, ha⟩ := mem_carrier.1 (h ▸ key Δ) obtain ⟨b, -, hb⟩ := mem_carrier.1 (h.symm ▸ key Δ') have h0 : b + a = 0 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by rw [Nat.ca …`.
-/
theorem carrier_injective : Function.Injective (carrier : Segment k → Set (IrrGL k)) := fun Δ Δ' h => by
  have key : ∀ D : Segment k, D.first ∈ D.carrier := fun D => mem_carrier.2 ⟨0, D.len_pos, by simp⟩
  obtain ⟨a, -, ha⟩ := mem_carrier.1 (h ▸ key Δ)
  obtain ⟨b, -, hb⟩ := mem_carrier.1 (h.symm ▸ key Δ')
  have h0 : b + a = 0 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by
    rw [Nat.cast_add, ← IrrGL.nu_nu, hb, ha, Nat.cast_zero, IrrGL.nu_zero])
  obtain rfl : b = 0 := by omega
  refine ext_first (by simpa using hb) ?_
  rw [← card_ms, ← card_ms, (Multiset.Nodup.ext Δ.nodup_ms Δ'.nodup_ms).2 fun x => by rw [mem_ms, mem_ms, h]]

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ _ _ hs hi => ⟨algebraMap_intertwiningMap_bijective_GL hs hi, exists_smooth_hasCentralChar hs hi⟩, fun _ hx _ _ => IrrGL.nu_ofReal_inj hx, fun Δ => ⟨Δ.term_injective, Δ.nodup_ms⟩, Segment.carrier_injective⟩`.
-/
theorem schur_and_segments (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
      IsSmooth π → π.IsIrreducible → Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) ∧
        ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω) ∧
    (∀ x : IrrGL k, 0 < x.1 → ∀ s t : ℝ, x.nu s = x.nu t ↔ s = t) ∧
    (∀ Δ : Segment k, Function.Injective Δ.term ∧ Δ.ms.Nodup) ∧
    Function.Injective (Segment.carrier : Segment k → Set (IrrGL k)) :=
  ⟨fun _ _ _ _ _ _ _ hs hi => ⟨algebraMap_intertwiningMap_bijective_GL hs hi, exists_smooth_hasCentralChar hs hi⟩,
    fun _ hx _ _ => IrrGL.nu_ofReal_inj hx, fun Δ => ⟨Δ.term_injective, Δ.nodup_ms⟩, Segment.carrier_injective⟩

end GlobalTheory.LocGL
