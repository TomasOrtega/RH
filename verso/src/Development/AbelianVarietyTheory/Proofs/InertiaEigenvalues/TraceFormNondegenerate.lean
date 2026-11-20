import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate

open Formalism.MainNotions.N GlobalTheory.TraceSemisimple

namespace GlobalTheory.SemisimpleTraceForm

/- English proof (translation)
Establish `hf : IsIdempotentElem (Matrix.toLin' e)`. Unfold `IsIdempotentElem`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]`. Establish `hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' e)) (Matrix.toLin' e)` using `⟨fun v => ⟨v, rfl⟩, by`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `congrArg (fun f : Module.End k (Fin n → k) => f v) hf⟩`. Establish `h1` using `hp.trace`. Rewrite `h1` using `[Matrix.trace_toLin'_eq, ht]`. Establish `h2 : Module.finrank k (LinearMap.range (Matrix.toLin' e)) = 0`. Conclude with `h1.symm` after adjusting the coercions.

Rewrite `h2` using `[Submodule.finrank_eq_zero, LinearMap.range_eq_bot]`. Conclude with `(LinearEquiv.map_eq_zero_iff _).1 h2`.
-/
theorem idem_eq_zero_of_trace {k : Type} [Field k] [CharZero k] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : e.trace = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' e)) (Matrix.toLin' e) :=
    ⟨fun v => ⟨v, rfl⟩, by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun f : Module.End k (Fin n → k) => f v) hf⟩
  have h1 := hp.trace
  rw [Matrix.trace_toLin'_eq, ht] at h1
  have h2 : Module.finrank k (LinearMap.range (Matrix.toLin' e)) = 0 := by
    exact_mod_cast h1.symm
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h2
  exact (LinearEquiv.map_eq_zero_iff _).1 h2

/- English proof (translation)
Set `φ : spanAlg ρ →+* Module.End k (Fin n → k)` to `((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp (spanAlg ρ).val).toRingHom`. Use `letI : Module (spanAlg ρ) (Fin n → k) := Module.compHom _ φ`. Establish `hs : ∀ (a : spanAlg ρ) (v : Fin n → k), a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v` using `fun _ _ => rfl`. Establish `hinv : ∀ W, IsInv ρ W → ∀ a : spanAlg ρ, ∀ v ∈ W, a • v ∈ W`. Introduce and unpack `W hW ⟨a, ha⟩ v hv`.

Rewrite using `[hs]`. Use `show a.mulVec v ∈ W`. Rewrite `ha` using `[mem_spanAlg]`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨g, rfl⟩ := hy`.

Conclude with `hW g v hv`. Consider the case `zero => rw [Matrix.zero_mulVec]`. Conclude with `W.zero_mem`. Consider the case `add y z _ _ hy hz => rw [Matrix.add_mulVec]`. Conclude with `W.add_mem hy hz`.

Consider the case `smul c y _ hy => rw [Matrix.smul_mulVec]`. Conclude with `W.smul_mem c hy`. Establish `hV : IsSemisimpleModule (spanAlg ρ) (Fin n → k)`. Rewrite using `[isSemisimpleModule_iff]`. Use `⟨fun U => ?_⟩` and prove the remaining obligations.

Set `W : Submodule k (Fin n → k)` to `{ toAddSubmonoid := U.toAddSubmonoid smul_mem' := fun c v hv => by`. Establish `h1 : (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v ∈ U` using `U.smul_mem (c • (1 : spanAlg ρ)) hv`. Rewrite `h1` using `[Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `h1 }`. Establish `hW : IsInv ρ W` using `fun g v hv => U.smul_mem ⟨(ρ g : GL (Fin n) k), Submodule.subset_span ⟨g, rfl⟩⟩ hv`.

Take `⟨W', hW', hc⟩` from `h W hW`. Set `U' : Submodule (spanAlg ρ) (Fin n → k)` to `{ toAddSubmonoid := W'.toAddSubmonoid smul_mem' := fun a v hv => hinv W' hW' a v hv }`. Use `⟨U', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Conclude with `fun v hv hv' => Submodule.disjoint_def.1 hc.disjoint v hv hv'`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Establish `hv : v ∈ W ⊔ W'` using `by rw [hc.sup_eq_top]; exact Submodule.mem_top`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hv`. Conclude with `Submodule.add_mem_sup hy hz`.

Set `ψ : spanAlg ρ →ₗ[spanAlg ρ] (Fin n → Fin n → k)` to `LinearMap.pi fun j => LinearMap.toSpanSingleton _ _ (Pi.single j 1)`. Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Use extensionality with `i j`.

Establish `h1 : (a : Matrix (Fin n) (Fin n) k).mulVec ((Pi.single j 1 : Fin n → k)) i = 0` using `congrFun (congrFun ha j) i`. Simplify using `using h1`. Establish `hP : IsSemisimpleModule (spanAlg ρ) (Fin n → Fin n → k)` using `instIsSemisimpleModuleForallOfFinite fun _ => Fin n → k`. Conclude with `IsSemisimpleModule.of_injective ψ hψ`.
-/
theorem semisimple_span {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (h : IsSSRep ρ) : IsSemisimpleRing (spanAlg ρ) := by
  let φ : spanAlg ρ →+* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  letI : Module (spanAlg ρ) (Fin n → k) := Module.compHom _ φ
  have hs : ∀ (a : spanAlg ρ) (v : Fin n → k),
      a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v := fun _ _ => rfl
  have hinv : ∀ W, IsInv ρ W → ∀ a : spanAlg ρ, ∀ v ∈ W, a • v ∈ W := by
    rintro W hW ⟨a, ha⟩ v hv
    rw [hs]
    show a.mulVec v ∈ W
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add y z _ _ hy hz => rw [Matrix.add_mulVec]; exact W.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mulVec]; exact W.smul_mem c hy
  have hV : IsSemisimpleModule (spanAlg ρ) (Fin n → k) := by
    rw [isSemisimpleModule_iff]
    refine ⟨fun U => ?_⟩
    let W : Submodule k (Fin n → k) :=
      { toAddSubmonoid := U.toAddSubmonoid
        smul_mem' := fun c v hv => by
          have h1 : (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v ∈ U :=
            U.smul_mem (c • (1 : spanAlg ρ)) hv
          rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h1
          exact h1 }
    have hW : IsInv ρ W := fun g v hv =>
      U.smul_mem ⟨(ρ g : GL (Fin n) k), Submodule.subset_span ⟨g, rfl⟩⟩ hv
    obtain ⟨W', hW', hc⟩ := h W hW
    let U' : Submodule (spanAlg ρ) (Fin n → k) :=
      { toAddSubmonoid := W'.toAddSubmonoid
        smul_mem' := fun a v hv => hinv W' hW' a v hv }
    refine ⟨U', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      exact fun v hv hv' => Submodule.disjoint_def.1 hc.disjoint v hv hv'
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
      exact Submodule.add_mem_sup hy hz
  let ψ : spanAlg ρ →ₗ[spanAlg ρ] (Fin n → Fin n → k) :=
    LinearMap.pi fun j => LinearMap.toSpanSingleton _ _ (Pi.single j 1)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    ext i j
    have h1 : (a : Matrix (Fin n) (Fin n) k).mulVec ((Pi.single j 1 : Fin n → k)) i = 0 :=
      congrFun (congrFun ha j) i
    simpa using h1
  have hP : IsSemisimpleModule (spanAlg ρ) (Fin n → Fin n → k) :=
    instIsSemisimpleModuleForallOfFinite fun _ => Fin n → k
  exact IsSemisimpleModule.of_injective ψ hψ

/- English proof (translation)
Introduce `Γ k _ _ _ n ρ h x hx ht`. Use `semisimple_span ρ h` as an intermediate fact. Establish `hA : ∀ a ∈ spanAlg ρ, (x * a).trace = 0`. Introduce `a ha`. Rewrite `ha` using `[mem_spanAlg]`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨g, rfl⟩ := hy`. Conclude with `ht g`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]`.

Consider the case `smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]`. Set `y : spanAlg ρ` to `⟨x, hx⟩`. Take `⟨C, hC⟩` from `exists_isCompl (Submodule.span (spanAlg ρ) {y})`. Establish `h1 : (1 : spanAlg ρ) ∈ Submodule.span (spanAlg ρ) {y} ⊔ C`. Rewrite using `[hC.sup_eq_top]`.

Conclude with `Submodule.mem_top`. Take `⟨e, he, f, hf, hef⟩` from `Submodule.mem_sup.1 h1`. Establish `key : ∀ z ∈ Submodule.span (spanAlg ρ) {y}, z * e = z`. Introduce `z hz`. Establish `h2 : z * f = z - z * e`.

Rewrite using `[eq_sub_iff_add_eq', ← mul_add, hef, mul_one]`. Establish `h3 : z * f = 0` using `Submodule.disjoint_def.1 hC.disjoint _ (h2 ▸ Submodule.sub_mem _ hz (Submodule.smul_mem _ z he)) (C.smul_mem z hf)`. Rewrite `h2` using `[h3]`. Conclude with `(sub_eq_zero.1 h2.symm).symm`. Establish `he0 : (e : Matrix (Fin n) (Fin n) k) = 0`.

Use `idem_eq_zero_of_trace _ (congrArg Subtype.val (key e he)) ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 he`. Use `show ((a : Matrix (Fin n) (Fin n) k) * x).trace = 0`. Rewrite using `[Matrix.trace_mul_comm]`. Conclude with `hA a a.2`.

Establish `h4 : x * (e : Matrix (Fin n) (Fin n) k) = x` using `congrArg Subtype.val (key y (Submodule.mem_span_singleton_self y))`. Rewrite using `[← h4, he0, mul_zero]`.
-/
theorem trace_form_nondegenerate :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (ρ : Γ →* GL (Fin n) k),
      IsSSRep ρ → ∀ x ∈ spanAlg ρ,
        (∀ g : Γ, Matrix.trace (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = 0) →
        x = 0 := by
  intro Γ k _ _ _ n ρ h x hx ht
  have := semisimple_span ρ h
  have hA : ∀ a ∈ spanAlg ρ, (x * a).trace = 0 := by
    intro a ha
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact ht g
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  let y : spanAlg ρ := ⟨x, hx⟩
  obtain ⟨C, hC⟩ := exists_isCompl (Submodule.span (spanAlg ρ) {y})
  have h1 : (1 : spanAlg ρ) ∈ Submodule.span (spanAlg ρ) {y} ⊔ C := by
    rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  have key : ∀ z ∈ Submodule.span (spanAlg ρ) {y}, z * e = z := by
    intro z hz
    have h2 : z * f = z - z * e := by
      rw [eq_sub_iff_add_eq', ← mul_add, hef, mul_one]
    have h3 : z * f = 0 :=
      Submodule.disjoint_def.1 hC.disjoint _
        (h2 ▸ Submodule.sub_mem _ hz (Submodule.smul_mem _ z he)) (C.smul_mem z hf)
    rw [h3] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  have he0 : (e : Matrix (Fin n) (Fin n) k) = 0 := by
    refine idem_eq_zero_of_trace _ (congrArg Subtype.val (key e he)) ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 he
    show ((a : Matrix (Fin n) (Fin n) k) * x).trace = 0
    rw [Matrix.trace_mul_comm]
    exact hA a a.2
  have h4 : x * (e : Matrix (Fin n) (Fin n) k) = x :=
    congrArg Subtype.val (key y (Submodule.mem_span_singleton_self y))
  rw [← h4, he0, mul_zero]

end GlobalTheory.SemisimpleTraceForm
