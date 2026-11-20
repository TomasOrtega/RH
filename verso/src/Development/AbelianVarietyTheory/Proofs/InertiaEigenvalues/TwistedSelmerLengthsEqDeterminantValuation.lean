import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthKerMatActKmodEqAddValDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RestrictionH1MemBlochKato
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.SelDetLength

section Transport

variable {Λ O G M : Type} [CommRing Λ] [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module Λ M]
  [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M] [ContinuousConstSMul O M]
  (ρ : Representation Λ G M) (ρ' : Representation O G M) (h : ∀ g m, ρ g m = ρ' g m)

def trZ : ↥(Z1 ρ) ≃+ ↥(Z1 ρ') where
  toFun z := ⟨z.1, z.2.1, fun g g' => by rw [← h]; exact z.2.2 g g'⟩
  invFun z := ⟨z.1, z.2.1, fun g g' => by rw [h]; exact z.2.2 g g'⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def trH : H1 ρ ≃+ H1 ρ' :=
  QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup
    (trZ ρ ρ' h) (by
      ext z
      refine (AddSubgroup.mem_map_equiv (f := trZ ρ ρ' h)).trans ?_
      change z.1 ∈ B1 ρ ↔ z.1 ∈ B1 ρ'
      simp only [mem_coboundaries1, h])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trH_mk (z : Z1 ρ) : trH ρ ρ' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (trZ ρ ρ' h z) := rfl

/- English proof (translation)
The claim follows from `(Submodule.Quotient.mk_surjective _ x).imp fun _ hz => hz.symm`.
-/
theorem exists_mk (x : H1 ρ) : ∃ z : Z1 ρ, x = Submodule.Quotient.mk z :=
  (Submodule.Quotient.mk_surjective _ x).imp fun _ hz => hz.symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trH_symm_smul (t : O) (z : Z1 ρ') : (trH ρ ρ' h).symm (t • Submodule.Quotient.mk z) =
    Submodule.Quotient.mk ((trZ ρ ρ' h).symm (t • z)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trZ_symm_smul (t : O) (z : Z1 ρ') (g : G) : ((trZ ρ ρ' h).symm (t • z)).1 g = t • z.1 g := rfl

/- English proof (translation)
Rewrite using `[hw, hw', trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (funext hz)`.
-/
theorem trH_eq_smul (t : O) (w w' : H1 ρ) (z z' : Z1 ρ) (hz : ∀ g, z'.1 g = t • z.1 g)
    (hw : w = Submodule.Quotient.mk z) (hw' : w' = Submodule.Quotient.mk z') : trH ρ ρ' h w' = t • trH ρ ρ' h w := by
  rw [hw, hw', trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext hz)

include h in
/- English proof (translation)
Assemble the required witnesses or components as `⟨(trZ ρ ρ' h).symm (t • trZ ρ ρ' h z), fun _ => rfl⟩`.
-/
theorem exists_smul_cocycle (t : O) (z : Z1 ρ) : ∃ z' : Z1 ρ, ∀ g, z'.1 g = t • z.1 g :=
  ⟨(trZ ρ ρ' h).symm (t • trZ ρ ρ' h z), fun _ => rfl⟩

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← Submodule.Quotient.mk_smul, trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => hat _)`.
-/
theorem trH_smul (a : Λ) (t : O) (hat : ∀ m : M, a • m = t • m) (x : H1 ρ) :
    trH ρ ρ' h (a • x) = t • trH ρ ρ' h x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext fun g => hat _)

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem trH_res {J : Type} [Group J] [TopologicalSpace J] (φ : J →* G) (hφ : Continuous φ) (x : H1 ρ) :
    trH (ρ.comp φ) (ρ'.comp φ) (fun g m => h (φ g) m) (resH1 ρ φ hφ x) = resH1 ρ' φ hφ (trH ρ ρ' h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/- English proof (translation)
Establish `hJ : Continuous J.subtype` using `continuous_subtype_val`. Express the relevant statement in the definitionally equal form `resH1 ρ J.subtype hJ x = 0 ↔ resH1 ρ' J.subtype hJ (trH ρ ρ' h x) = 0`. Rewrite using `[← trH_res, AddEquiv.map_eq_zero_iff]`.
-/
theorem mem_H1ur_iff (J : Subgroup G) (x : H1 ρ) : x ∈ H1ur ρ J ↔ trH ρ ρ' h x ∈ H1ur ρ' J := by
  have hJ : Continuous J.subtype := continuous_subtype_val
  change resH1 ρ J.subtype hJ x = 0 ↔ resH1 ρ' J.subtype hJ (trH ρ ρ' h x) = 0
  rw [← trH_res, AddEquiv.map_eq_zero_iff]

end Transport

/- English proof (translation)
Establish `hJ : ∀ v, Continuous (Dec (F` using `F) (A.1 v)).subtype := fun _ => continuous_subtype_val`. Use `(mem_Sel ρ _ hJ _ _).trans (Iff.trans (forall_congr' fun v => ?_) (mem_Sel ρ' _ hJ _ _).symm)` and prove the remaining obligations. Rewrite using `[← trH_res]`. Unfold `Formalism.GaloisCohomology.bkCond`. Distinguish the cases in `h1 : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal`.

Simplify using `only [if_pos h1]`. Conclude with `hL v h1 _`. Distinguish the cases in `h2 : v ∈ Sig`. Simplify using `only [if_neg h1, if_pos h2, Submodule.mem_top]`. Simplify using `only [if_neg h1, if_neg h2]`.

Conclude with `mem_H1ur_iff _ _ _ _ _`.
-/
theorem mem_selAll_iff {F Ω Λ O M : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CommRing Λ] [CommRing O]
    [AddCommGroup M] [Module Λ M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul Λ M] [ContinuousConstSMul O M]
    (ρ : Representation Λ (G F Ω) M) (ρ' : Representation O (G F Ω) M) (h : ∀ g m, ρ g m = ρ' g m)
    (A : Formalism.GaloisCohomology.Places F Ω) (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype)))
    (L' : ∀ v, Submodule O (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)))
    (hL : ∀ v, ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ y, y ∈ L v ↔ trH _ _ (fun g m => h (Subgroup.subtype _ g) m) y ∈ L' v)
    (x : H1 ρ) :
    x ∈ Formalism.GaloisCohomology.SelAll ρ A (Formalism.GaloisCohomology.bkCond ρ A l Sig L) ↔
      trH ρ ρ' h x ∈ Formalism.GaloisCohomology.SelAll ρ' A (Formalism.GaloisCohomology.bkCond ρ' A l Sig L') := by
  have hJ : ∀ v, Continuous (Dec (F := F) (A.1 v)).subtype := fun _ => continuous_subtype_val
  refine (mem_Sel ρ _ hJ _ _).trans (Iff.trans (forall_congr' fun v => ?_) (mem_Sel ρ' _ hJ _ _).symm)
  rw [← trH_res]
  unfold Formalism.GaloisCohomology.bkCond
  by_cases h1 : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · simp only [if_pos h1]
    exact hL v h1 _
  · by_cases h2 : v ∈ Sig
    · simp only [if_neg h1, if_pos h2, Submodule.mem_top]
    · simp only [if_neg h1, if_neg h2]
      exact mem_H1ur_iff _ _ _ _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (h1 x hx)`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [hT]`. Conclude with `Submodule.smul_mem _ _ hx`.

Introduce `hx`. Establish `: ∀ y ∈ Submodule.span O S', ∀ t : O, T.symm (t • y) ∈ Submodule.span Λ S`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact fun t => Submodule.subset_span (h2 t x hx)`.

Consider the case `zero => intro t`. Rewrite using `[smul_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => intro t`. Rewrite using `[smul_add, map_add]`.

Conclude with `add_mem (hx t) (hy t)`. Consider the case `smul a x _ hx => intro t`. Rewrite using `[smul_smul]`. Conclude with `hx _`. Simplify using `using this _ hx 1`.
-/
theorem mem_span_iff {Λ O W W' : Type} [CommRing Λ] [CommRing O] [AddCommGroup W] [Module Λ W] [AddCommGroup W']
    [Module O W'] (T : W ≃+ W') (χ : Λ → O) (hT : ∀ a x, T (a • x) = χ a • T x) (S : Set W) (S' : Set W')
    (h1 : ∀ x ∈ S, T x ∈ S') (h2 : ∀ (t : O), ∀ y ∈ S', T.symm (t • y) ∈ S) (x : W) :
    x ∈ Submodule.span Λ S ↔ T x ∈ Submodule.span O S' := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (h1 x hx)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hT]; exact Submodule.smul_mem _ _ hx
  · intro hx
    have : ∀ y ∈ Submodule.span O S', ∀ t : O, T.symm (t • y) ∈ Submodule.span Λ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx => exact fun t => Submodule.subset_span (h2 t x hx)
      | zero => intro t; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro t; rw [smul_add, map_add]; exact add_mem (hx t) (hy t)
      | smul a x _ hx => intro t; rw [smul_smul]; exact hx _
    simpa using this _ hx 1

/- English proof (translation)
Set `f : K' →ₗ[O] S'` to `{ toFun := fun x => ⟨T (e ⟨x.1, (hK _).1 x.2⟩).1, (hS _).1 (e _).2⟩ map_add' := fun x y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `T _ = T _ + T _`. Rewrite using `[← map_add, ← Submodule.coe_add, ← map_add]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun t x => Subtype.ext (he t _ _ rfl) }`. Use `(LinearEquiv.ofBijective f ⟨fun x y hxy => ?_, fun y => ?_⟩).length_eq.symm` and prove the remaining obligations. Use `e.injective (Subtype.ext (T.injective (congrArg Subtype.val hxy)))` as an intermediate fact. Conclude with `Subtype.ext (congrArg (fun a : K => a.1) this)`. Take `⟨x, hx⟩` from `e.surjective ⟨T.symm y.1, (hS _).2 (by simpa using y.2)⟩`.

Use `⟨⟨x.1, (hK _).2 x.2⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T (e x).1 = _`. Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem length_eq_of_equiv {Λ O V W W' : Type} [CommRing Λ] [CommRing O] [AddCommGroup V] [Module Λ V] [Module O V]
    [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module O W'] (K : Submodule Λ V) (K' : Submodule O V)
    (S : Submodule Λ W) (S' : Submodule O W') (T : W ≃+ W') (e : K ≃ₗ[Λ] S) (hK : ∀ v, v ∈ K' ↔ v ∈ K)
    (hS : ∀ w, w ∈ S ↔ T w ∈ S') (he : ∀ (t : O) (x x' : K), x'.1 = t • x.1 → T (e x').1 = t • T (e x).1) :
    Module.length O S' = Module.length O K' := by
  let f : K' →ₗ[O] S' :=
    { toFun := fun x => ⟨T (e ⟨x.1, (hK _).1 x.2⟩).1, (hS _).1 (e _).2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change T _ = T _ + T _
        rw [← map_add, ← Submodule.coe_add, ← map_add]
        rfl
      map_smul' := fun t x => Subtype.ext (he t _ _ rfl) }
  refine (LinearEquiv.ofBijective f ⟨fun x y hxy => ?_, fun y => ?_⟩).length_eq.symm
  · have := e.injective (Subtype.ext (T.injective (congrArg Subtype.val hxy)))
    exact Subtype.ext (congrArg (fun a : K => a.1) this)
  · obtain ⟨x, hx⟩ := e.surjective ⟨T.symm y.1, (hS _).2 (by simpa using y.2)⟩
    refine ⟨⟨x.1, (hK _).2 x.2⟩, Subtype.ext ?_⟩
    change T (e x).1 = _
    rw [hx]
    simp

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) (k : ℕ)

/- English proof (translation)
Establish `: CharZero (FractionRing (X.O0 i))` using `(X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance`. Establish `: CharZero (X.O0 i)` using `(algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero`. Conclude with `Nat.cast_ne_zero.2 (X.lPrime i).out.ne_zero`.
-/
theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  exact Nat.cast_ne_zero.2 (X.lPrime i).out.ne_zero

/- English proof (translation)
The claim follows from `(X.Ok_inj i k).comp (X.O_inj i)`.
-/
theorem phiK_injective : Function.Injective (phiK X i k) := (X.Ok_inj i k).comp (X.O_inj i)

/- English proof (translation)
Use `X.Ok_fin i k` as an intermediate fact. Establish `: FaithfulSMul (X.O i) (X.Ok i k)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)`. Introduce `h`. Establish `h2 : IsUnit (algebraMap (X.O i) (X.Ok i k) (X.l i))` using `by simpa using h`. Conclude with `X.O_l i ((isUnit_map_iff _ _).1 h2)`.
-/
theorem l_not_unit : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) := by
  have := X.Ok_fin i k
  have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  intro h
  have h2 : IsUnit (algebraMap (X.O i) (X.Ok i k) (X.l i)) := by simpa using h
  exact X.O_l i ((isUnit_map_iff _ _).1 h2)

/- English proof (translation)
Introduce `h`. Apply `l_ne_zero i` to reduce the goal to its premises. Apply `((IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK_injective i k))` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, map_natCast, map_zero, h]`.
-/
theorem l_frac_ne_zero : ((X.l i : ℕ) : FractionRing (X.Ok i k)) ≠ 0 := by
  intro h
  apply l_ne_zero i
  apply ((IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK_injective i k))
  simp only [Function.comp_apply, map_natCast, map_zero, h]

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Take `⟨x, n, hx⟩` from `GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.linearMap_apply, ← hx, map_natCast, nsmul_eq_mul, mul_comm, Nat.cast_pow]`.
-/
theorem kmod_torsion (b : KmodO (X.Ok i k)) : ∃ n : ℕ, (X.l i ^ n) • b = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, n, hx⟩ := GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a
  refine ⟨n, ?_⟩
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨x, ?_⟩
  rw [Algebra.linearMap_apply, ← hx, map_natCast, nsmul_eq_mul, mul_comm, Nat.cast_pow]

variable (ψ : GE N →* (X.Ok i k)ˣ)

/- English proof (translation)
Simplify using `[Trep, twRep, matAct, Tgl_coe, Tmat, Finset.smul_sum, smul_smul, mul_assoc]`.
-/
theorem trep_apply (g : GE N) (x : Fin D.R.r → KmodO (X.Ok i k)) (a : Fin D.R.r) :
    Trep i s k ψ g x a = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) • ∑ b, phiK X i k
      (((Tgl i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) _) a b) • x b := by
  simp [Trep, twRep, matAct, Tgl_coe, Tmat, Finset.smul_sum, smul_smul, mul_assoc]

variable (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))

def intSet : Set (H1 ((Trep i s k ψ).comp (DecV N v).subtype)) :=
  {x | ∃ (z : Z1 ((Trep i s k ψ).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin D.R.r → X.O0 i) (b : KmodO (X.Ok i k)),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin D.R.r → KmodO (X.Ok i k)) g a = phiK X i k (y g a) • b) ∧
      x = Submodule.Quotient.mk z}

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Rewrite using `[bk, dif_pos hv]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `x ⟨z, c, y, hc, hy, hz, rfl⟩`. Set `Bw` to `bkP.br i v hv`. Use `haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK Bw.Kw`.

Take `⟨n, hn⟩` from `GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL c hc.1.1`. Set `f : ↥(DecV N v) → Fin D.R.r → X.O0 i` to `fun g j => Bw.eO.symm ⟨_, hn (Bw.e g) j⟩`. Establish `hf : ∀ g j, Bw.toLL (f g j) = (X.l i : Bw.LL.1) ^ n * c (Bw.e g) j`. Introduce `g j`. Use `show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _`.

Rewrite using `[RingEquiv.apply_symm_apply]`. Establish `hφ : Function.Injective ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k))` using `(IsFractionRing.injective _ _).comp (phiK_injective i k)`. Establish `hl1` using `l_frac_ne_zero i k`. Use `⟨z, ((X.l i : Bw.LL.1) ^ n) • c, f, Submodule.Quotient.mk (((X.l i : FractionRing (X.Ok i k)) ^ n)⁻¹), Submodule.smul_mem _ _ hc, fun g a => (hf g a).symm, fun g j => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hz, ← Submodule.Quotient.mk_smul, Algebra.smul_def]`.

Use `congr 1`. Take `⟨m, d, ⟨hd, h1⟩, h2⟩` from `hy g j`. Establish `h3 : d * f g j = (X.l i : X.O0 i) ^ n * m`. Apply `GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hf, map_pow, map_natCast, ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `congrArg ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k)) h3`. Rewrite `h4` using `[map_mul, map_mul, map_pow, map_natCast]`. Simplify using `only [RingHom.comp_apply] at h4`. Establish `hd' : algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0` using `fun h => hd (hφ (by rw [map_zero]; exact h))`.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hl1)]`. Apply `mul_left_cancel₀ hd'` to reduce the goal to its premises. Rewrite using `[h4, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bk_le : bk bkP i s k ψ v ≤ Submodule.span (X.Ok i k) (intSet bkP i s k ψ v hv) := by
  rw [bk, dif_pos hv]
  refine Submodule.span_mono ?_
  rintro x ⟨z, c, y, hc, hy, hz, rfl⟩
  let Bw := bkP.br i v hv
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK Bw.Kw
  obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL c hc.1.1
  let f : ↥(DecV N v) → Fin D.R.r → X.O0 i := fun g j => Bw.eO.symm ⟨_, hn (Bw.e g) j⟩
  have hf : ∀ g j, Bw.toLL (f g j) = (X.l i : Bw.LL.1) ^ n * c (Bw.e g) j := by
    intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply]
  have hφ : Function.Injective ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k)) :=
    (IsFractionRing.injective _ _).comp (phiK_injective i k)
  have hl1 := l_frac_ne_zero i k
  refine ⟨z, ((X.l i : Bw.LL.1) ^ n) • c, f, Submodule.Quotient.mk (((X.l i : FractionRing (X.Ok i k)) ^ n)⁻¹),
    Submodule.smul_mem _ _ hc, fun g a => (hf g a).symm, fun g j => ?_, rfl⟩
  rw [hz, ← Submodule.Quotient.mk_smul, Algebra.smul_def]
  congr 1
  obtain ⟨m, d, ⟨hd, h1⟩, h2⟩ := hy g j
  have h3 : d * f g j = (X.l i : X.O0 i) ^ n * m := by
    apply GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw
    rw [map_mul, map_mul, hf, map_pow, map_natCast, ← h1]
    ring
  have h4 := congrArg ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k)) h3
  rw [map_mul, map_mul, map_pow, map_natCast] at h4
  simp only [RingHom.comp_apply] at h4
  have hd' : algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0 := fun h =>
    hd (hφ (by rw [map_zero]; exact h))
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hl1)]
  apply mul_left_cancel₀ hd'
  rw [h4, ← h2]
  ring

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Rewrite using `[bk, dif_pos hv]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨z, c, f, b, hc, hy, hz, rfl⟩`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Take `⟨x, n, hx⟩` from `GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a`.

Establish `hf : GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s) f`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g j`. Rewrite using `[← hy, MulEquiv.apply_symm_apply]`.

Take `⟨d, hdd⟩ : ∃ d, d = ((X.l i : ℕ) : X.O0 i) ^ n` from `⟨_, rfl⟩`. Establish `hd : d ≠ 0` using `hdd ▸ pow_ne_zero _ (l_ne_zero i)`. Establish `hd' : phiK X i k d ≠ 0` using `(map_ne_zero_iff _ (phiK_injective i k)).2 hd`. Establish `hd1 : algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0` using `by simpa using hd'`. Establish `hd2 : (bkP.br i v hv).toLL d ≠ 0` using `(map_ne_zero_iff _ (GlobalTheory.BKIntegralToRational.toLL_injective _)).2 hd`.

Set `z' : Z1 ((Trep i s k ψ).comp (DecV N v).subtype)` to `⟨fun g j => Submodule.Quotient.mk (algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) / algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d)), continuous_pi fun j => (GlobalTheory.BKIntegralToRational.continuous_div_mk (X.twistBaseCoefficientRing_isAdic i) (phiK X i k) …`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.add_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, trep_apply, hψ g g.2, inv_one, Units.val_one, one_smul]`. Use `beta_reduce`. Rewrite using `[GlobalTheory.BKIntegralToRational.cocycle_of_crys _ _ hf g h j]`.

Simplify using `only [← Submodule.mkQ_apply, map_add, map_sum, map_mul, add_div, Finset.sum_div, mul_div_assoc, ← LinearMap.map_smul, Algebra.smul_def]⟩`. Establish `hzz : z = x • z'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g j`. Rewrite using `[hz, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]`.

Simplify using `only [z']`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, ← hx]`. Use `congr 1`. Simplify using `only [hdd, map_pow, map_natCast] at hd1 ⊢`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hzz, Submodule.Quotient.mk_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', ((bkP.br i v hv).toLL d)⁻¹ • c, fun g j => algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) / algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d), Submodule.smul_mem _ _ hc, fun g a => ⟨f g a, d, ⟨hd, ?_⟩, mul_div_ca …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(bkP.br i v hv).toLL d * (((bkP.br i v hv).toLL d)⁻¹ * c ((bkP.br i v hv).e g) a) = _`. Rewrite using `[hy, mul_inv_cancel_left₀ hd2]`.
-/
theorem le_bk (hψ : ∀ σ ∈ DecV N v, ψ σ = 1) :
    Submodule.span (X.Ok i k) (intSet bkP i s k ψ v hv) ≤ bk bkP i s k ψ v := by
  rw [bk, dif_pos hv]
  refine Submodule.span_le.2 ?_
  rintro x ⟨z, c, f, b, hc, hy, hz, rfl⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, n, hx⟩ := GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s) f := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle
    convert hc using 1
    funext g j
    rw [← hy, MulEquiv.apply_symm_apply]
  obtain ⟨d, hdd⟩ : ∃ d, d = ((X.l i : ℕ) : X.O0 i) ^ n := ⟨_, rfl⟩
  have hd : d ≠ 0 := hdd ▸ pow_ne_zero _ (l_ne_zero i)
  have hd' : phiK X i k d ≠ 0 := (map_ne_zero_iff _ (phiK_injective i k)).2 hd
  have hd1 : algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0 := by simpa using hd'
  have hd2 : (bkP.br i v hv).toLL d ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKIntegralToRational.toLL_injective _)).2 hd
  let z' : Z1 ((Trep i s k ψ).comp (DecV N v).subtype) := ⟨fun g j => Submodule.Quotient.mk
        (algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) /
          algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d)),
      continuous_pi fun j => (GlobalTheory.BKIntegralToRational.continuous_div_mk (X.twistBaseCoefficientRing_isAdic i) (phiK X i k) hd hd').comp
        (GlobalTheory.BKIntegralToRational.continuous_of_crys _ _ hf j), fun g h => by
      funext j
      rw [Pi.add_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, trep_apply, hψ g g.2, inv_one, Units.val_one,
        one_smul]
      beta_reduce
      rw [GlobalTheory.BKIntegralToRational.cocycle_of_crys _ _ hf g h j]
      simp only [← Submodule.mkQ_apply, map_add, map_sum, map_mul, add_div, Finset.sum_div, mul_div_assoc,
        ← LinearMap.map_smul, Algebra.smul_def]⟩
  have hzz : z = x • z' := by
    apply Subtype.ext
    funext g j
    rw [hz, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
    simp only [z']
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, ← hx]
    congr 1
    simp only [hdd, map_pow, map_natCast] at hd1 ⊢
    field_simp
  rw [hzz, Submodule.Quotient.mk_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', ((bkP.br i v hv).toLL d)⁻¹ • c,
    fun g j => algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) /
          algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d), Submodule.smul_mem _ _ hc,
    fun g a => ⟨f g a, d, ⟨hd, ?_⟩, mul_div_cancel₀ _ hd1⟩, fun _ _ => rfl, rfl⟩)
  change (bkP.br i v hv).toLL d * (((bkP.br i v hv).toLL d)⁻¹ * c ((bkP.br i v hv).e g) a) = _
  rw [hy, mul_inv_cancel_left₀ hd2]

section Char

variable {M : ℕ} {ι : Type} [Fintype ι] (u : ι → (X.Ok i k)ˣ) (hu : ∀ q, u q ^ (X.l i ^ M) = 1)

def delChar : Del X i M ι →* (X.Ok i k)ˣ where
  toFun δ := ∏ q, u q ^ (Multiplicative.toAdd δ q).val
  map_one' := by simp
  map_mul' δ δ' := by
    have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

def lamChar : abelian₂ X i M ι →+* X.Ok i k :=
  MonoidAlgebra.liftNCRingHom (phiK X i k) ((Units.coeHom _).comp (delChar i k u hu)) fun _ _ => Commute.all _ _

/- English proof (translation)
Simplify using `[lamChar, MonoidAlgebra.liftNCRingHom]`.
-/
theorem lamChar_single (δ : Del X i M ι) (c : X.O0 i) :
    lamChar i k u hu (MonoidAlgebra.single δ c) = phiK X i k c * (delChar i k u hu δ : (X.Ok i k)ˣ) := by
  simp [lamChar, MonoidAlgebra.liftNCRingHom]

/- English proof (translation)
Rewrite using `[MonoidAlgebra.coe_algebraMap, Function.comp_apply, lamChar_single]`. Simplify using the standard rewrite rules.
-/
theorem lamChar_algebraMap (c : X.O0 i) : lamChar i k u hu (algebraMap _ _ c) = phiK X i k c := by
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, lamChar_single]
  simp

/- English proof (translation)
Rewrite using `[MonoidAlgebra.of_apply, lamChar_single]`. Simplify using the standard rewrite rules.
-/
theorem lamChar_of (δ : Del X i M ι) :
    lamChar i k u hu (MonoidAlgebra.of _ _ δ) = (delChar i k u hu δ : (X.Ok i k)ˣ) := by
  rw [MonoidAlgebra.of_apply, lamChar_single]
  simp

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => rw [MvPolynomial.algHom_C, lamChar_algebraMap, MvPolynomial.eval₂_C]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, MvPolynomial.eval₂_add]`. Consider the case `mul_X p q hp`. Rewrite using `[map_mul, map_mul, hp, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, toLam, MvPolynomial.aeval_X, map_sub, map_one, lamChar_of]`.

Use `congr 3`. Express the relevant statement in the definitionally equal form `∏ q', u q' ^ _ = _`. Rewrite using `[Finset.prod_eq_single q (fun q' _ hq' => by simp [Pi.single_eq_of_ne hq']) (by simp)]`. Simplify using `only [toAdd_ofAdd, Pi.single_eq_same]`. Rewrite using `[ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]`.
-/
theorem lamChar_toLam (F : MvPolynomial ι (X.O0 i)) :
    lamChar i k u hu (toLam X i M ι F) =
      MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.algHom_C, lamChar_algebraMap, MvPolynomial.eval₂_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, MvPolynomial.eval₂_add]
  | mul_X p q hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, toLam, MvPolynomial.aeval_X, map_sub,
      map_one, lamChar_of]
    congr 3
    change ∏ q', u q' ^ _ = _
    rw [Finset.prod_eq_single q (fun q' _ hq' => by simp [Pi.single_eq_of_ne hq']) (by simp)]
    simp only [toAdd_ofAdd, Pi.single_eq_same]
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]

/- English proof (translation)
Establish `h : Units.map (lamChar i k u hu).toMonoidHom (delInv i M d g)⁻¹ = ψ g`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hψ]`. Conclude with `lamChar_of i k u hu (delAll X i M d g)`. Rewrite using `[← h, map_inv, inv_inv]`.

Both sides reduce to the same expression.
-/
theorem lamChar_delInv (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (hψ : ∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) (g : GE N) :
    lamChar i k u hu ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) := by
  have h : Units.map (lamChar i k u hu).toMonoidHom (delInv i M d g)⁻¹ = ψ g := by
    apply Units.ext
    rw [hψ]
    exact lamChar_of i k u hu (delAll X i M d g)
  rw [← h, map_inv, inv_inv]
  rfl

end Char

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `h : ∀ g m, repOn (Tgl i s) κ (KmodO (X.Ok i k)) g m = Trep i s k ψ g m`. Introduce `g m`. Use function extensionality and compare the values at `c`. Rewrite using `[trep_apply, ← hκ, ← hχ]`. Simplify using `only [← hχ0, ← hχ]`.

Both sides reduce to the same expression. Rewrite using `[RingHom.map_det, ← GlobalTheory.length_ker_matAct_kmod_eq_addVal_det]`. Use `length_eq_of_equiv _ _ _ _ (trH _ _ h) e (fun x => ?_) (fun w => ?_) (fun t x x' hx => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker]`. Use `Eq.congr_left (funext fun c => ?_)` and prove the remaining obligations.

Simplify using `[matAct, hχ]`. Use `mem_selAll_iff _ _ h _ _ _ _ _ (fun v hv y => ?_) w` and prove the remaining obligations. Establish `hv' : v ∈ placesOver D.host.E (X.l i)` using `hv`. Rewrite using `[le_antisymm (bk_le bkP i s k ψ v hv') (le_bk bkP i s k ψ v hv' (hψ v hv' _ (N.plOm.2 v))), bkOn, dif_pos hv']`. Use `mem_span_iff _ χ (fun c x => trH_smul _ _ _ c (χ c) (fun m => funext fun j => hχ c (m j)) x) _ _ ?_ ?_ y` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, c, y, b, hc, hy, hz, rfl⟩`. Conclude with `⟨trZ _ _ (fun g m => h (Subgroup.subtype _ g) m) z, c, y, b, hc, hy, fun g j => (hz g j).trans (by rw [hχ, hχ0]), trH_mk _ _ _ z⟩`. Introduce and unpack `t _ ⟨z, c, y, b, hc, hy, hz, rfl⟩`. Use `⟨(trZ _ _ (fun g m => h (Subgroup.subtype _ g) m)).symm (t • z), c, y, t • b, hc, hy, fun g j => ?_, trH_symm_smul _ _ _ t z⟩` and prove the remaining obligations. Rewrite using `[hχ, hχ0, smul_comm, ← hz]`.

Conclude with `congrFun (trZ_symm_smul _ _ _ t z g) j`. Establish `hex` using `exists_mk (repOn (Tgl i s) κ (KmodO (X.Ok i k))) (e x).1`. Use `hex.elim fun z hz => ?_` and prove the remaining obligations. Set `f : KmodO (X.Ok i k) →ₗ[Λ] KmodO (X.Ok i k)` to `{ toFun := fun b => t • b map_add' := smul_add t map_smul' := fun c b => by rw [RingHom.id_apply, hχ, hχ, smul_comm] }`. Use `(exists_smul_cocycle _ _ h t z).elim fun z' hz' => ?_` and prove the remaining obligations.

Establish `h1 : ∀ c, x'.1 c = f (x.1 c)` using `fun c => congrFun hx c`. Establish `h2 : ∀ g c, z'.1 g c = f (z.1 g c)` using `fun g c => congrFun (hz' g) c`. Conclude with `trH_eq_smul _ _ h t _ _ z z' hz' hz (he f x x' z z' h1 h2 hz)`.
-/
theorem length_selT {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [Module Λ (KmodO (X.Ok i k))] (χ : Λ →+* X.Ok i k)
    (hχ : ∀ (c : Λ) (b : KmodO (X.Ok i k)), c • b = χ c • b) (hχ0 : ∀ c, χ (algebraMap (X.O0 i) Λ c) = phiK X i k c)
    (κ : GE N →* Λˣ) (hκ : ∀ g, χ (κ g : Λˣ) = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k))
    (hψ : TrivAbove ψ (X.l i)) (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ)
    (e : ↥(LinearMap.ker (matAct (M := KmodO (X.Ok i k)) Φ)) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ (KmodO (X.Ok i k)) Q))
    (he : ∀ (f : KmodO (X.Ok i k) →ₗ[Λ] KmodO (X.Ok i k))
      (x x' : ↥(LinearMap.ker (matAct (M := KmodO (X.Ok i k)) Φ)))
      (z z' : Z1 (repOn (Tgl i s) κ (KmodO (X.Ok i k)))),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e x).1 = Submodule.Quotient.mk z → (e x').1 = Submodule.Quotient.mk z') :
    Module.length (X.Ok i k) (selT bkP i s k Q ψ) = IsDiscreteValuationRing.addVal (X.Ok i k) (χ Φ.det) := by
  have h : ∀ g m, repOn (Tgl i s) κ (KmodO (X.Ok i k)) g m = Trep i s k ψ g m := by
    intro g m
    funext c
    rw [trep_apply, ← hκ, ← hχ]
    simp only [← hχ0, ← hχ]
    rfl
  rw [RingHom.map_det, ← GlobalTheory.length_ker_matAct_kmod_eq_addVal_det]
  refine length_eq_of_equiv _ _ _ _ (trH _ _ h) e (fun x => ?_) (fun w => ?_) (fun t x x' hx => ?_)
  · rw [LinearMap.mem_ker, LinearMap.mem_ker]
    refine Eq.congr_left (funext fun c => ?_)
    simp [matAct, hχ]
  · refine mem_selAll_iff _ _ h _ _ _ _ _ (fun v hv y => ?_) w
    have hv' : v ∈ placesOver D.host.E (X.l i) := hv
    rw [le_antisymm (bk_le bkP i s k ψ v hv') (le_bk bkP i s k ψ v hv' (hψ v hv' _ (N.plOm.2 v))), bkOn, dif_pos hv']
    refine mem_span_iff _ χ (fun c x => trH_smul _ _ _ c (χ c) (fun m => funext fun j => hχ c (m j)) x) _ _ ?_ ?_ y
    · rintro _ ⟨z, c, y, b, hc, hy, hz, rfl⟩
      exact ⟨trZ _ _ (fun g m => h (Subgroup.subtype _ g) m) z, c, y, b, hc, hy,
        fun g j => (hz g j).trans (by rw [hχ, hχ0]), trH_mk _ _ _ z⟩
    · rintro t _ ⟨z, c, y, b, hc, hy, hz, rfl⟩
      refine ⟨(trZ _ _ (fun g m => h (Subgroup.subtype _ g) m)).symm (t • z), c, y, t • b, hc, hy, fun g j => ?_,
        trH_symm_smul _ _ _ t z⟩
      rw [hχ, hχ0, smul_comm, ← hz]
      exact congrFun (trZ_symm_smul _ _ _ t z g) j
  · have hex := exists_mk (repOn (Tgl i s) κ (KmodO (X.Ok i k))) (e x).1
    refine hex.elim fun z hz => ?_
    let f : KmodO (X.Ok i k) →ₗ[Λ] KmodO (X.Ok i k) :=
      { toFun := fun b => t • b
        map_add' := smul_add t
        map_smul' := fun c b => by rw [RingHom.id_apply, hχ, hχ, smul_comm] }
    refine (exists_smul_cocycle _ _ h t z).elim fun z' hz' => ?_
    have h1 : ∀ c, x'.1 c = f (x.1 c) := fun c => congrFun hx c
    have h2 : ∀ g c, z'.1 g c = f (z.1 g c) := fun g c => congrFun (hz' g) c
    exact trH_eq_smul _ _ h t _ _ z z' hz' hz (he f x x' z z' h1 h2 hz)

/- English proof (translation)
Introduce `D N X bkP i s M ι _ P d Q _ hA _ a Φ hC F hF k u ψ hu hψ`. Take `⟨e, he⟩` from `hC`. Use `letI : Module (abelian₂ X i M ι) (KmodO (X.Ok i k)) := Module.compHom _ (lamChar i k u hu)`. Establish `htr : TrivAbove ψ (X.l i)` using `fun v hv A hvA σ hσ => by`. Rewrite using `[hψ]`.

Conclude with `Finset.prod_eq_one fun q _ => by rw [(hA.2.2 q).2.2.1 v hv A hvA σ hσ]; simp`. Rewrite using `[sLen, lenN, valE, length_selT bkP i s k ψ (lamChar i k u hu) (fun _ _ => rfl) (lamChar_algebraMap i k u hu) (delInv i M d) (lamChar_delInv i k ψ u hu d hψ) htr Q Φ (e _ (kmod_torsion i k)) (he _ _ (kmod_torsion i k) (kmod_torsion i k)), ← hF, lamChar_toLam]`.
-/
theorem twisted_selmer_lengths_eq_determinant_valuation : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    SelmerLengthsByDeterminant bkP := by
  intro D N X bkP i s M ι _ P d Q _ hA _ a Φ hC F hF k u ψ hu hψ
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) (KmodO (X.Ok i k)) := Module.compHom _ (lamChar i k u hu)
  have htr : TrivAbove ψ (X.l i) := fun v hv A hvA σ hσ => by
    rw [hψ]
    exact Finset.prod_eq_one fun q _ => by rw [(hA.2.2 q).2.2.1 v hv A hvA σ hσ]; simp
  rw [sLen, lenN, valE, length_selT bkP i s k ψ (lamChar i k u hu) (fun _ _ => rfl) (lamChar_algebraMap i k u hu)
    (delInv i M d) (lamChar_delInv i k ψ u hu d hψ) htr Q Φ (e _ (kmod_torsion i k))
    (he _ _ (kmod_torsion i k) (kmod_torsion i k)), ← hF, lamChar_toLam]

end GlobalTheory.SelDetLength
