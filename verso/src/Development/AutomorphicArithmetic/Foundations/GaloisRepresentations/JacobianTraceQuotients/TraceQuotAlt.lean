import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Introduce `V W _ _ _ _ S _ B p T hB hBT hnil`. Establish `hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `⟨B v, hB v, hBT v hv⟩`. Establish `hBS : ∀ v ∈ S, B v ∈ S` using `fun v _ => hB v`.

Establish `hRS : LinearMap.range B ≤ S`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hB v`. Use `haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations.

Unfold `trIn`. Rewrite using `[dif_pos hTP]`. Establish `h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B))) = LinearMap.trace ℂ S (B.restrict hBS)`. Establish `key` using `LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype) (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)`. Rewrite using `[← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]`.

Use `congr 1`. Rewrite using `[h1]`. Use `set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef`. Establish `hq : Function.Surjective q` using `p.submoduleMap_surjective S`. Use `haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq`.

Take `⟨s, hs⟩` from `q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)`. Use `set BS := B.restrict hBS with hBSdef`. Use `set TP := T.restrict hTP with hTPdef`. Establish `hint : q ∘ₗ BS = TP ∘ₗ q`. Use extensionality with `x`.

Conclude with `hBT x.1 x.2`. Establish `hT : TP = q ∘ₗ (BS ∘ₗ s)`. Rewrite using `[← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]`. Rewrite using `[hT, LinearMap.trace_comp_comm']`. Use `set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef`.

Establish `hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E`. Use extensionality with `x`. Simplify using `[hEdef]`. Establish `hqs : ∀ y, q (s y) = y` using `fun y => LinearMap.congr_fun hs y`. Establish `hqB : ∀ y : S, q y = 0 → q (BS y) = 0`.

Introduce `y hy`. Use `LinearMap.congr_fun hint y` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, hy, map_zero]`. Establish `hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0`.

Rewrite using `[LinearMap.trace_comp_comm']`. Establish `hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q`. Introduce `x`. Simplify using `[hEdef, hqs]`. Rewrite using `[← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]`.

Use `set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Apply `LinearMap.isNilpotent_trace_of_isNilpotent` to reduce the goal to its premises. Rewrite using `[Module.End.isNilpotent_iff_of_finite]`. Introduce `k`.

Establish `hk0 : q k.1 = 0` using `k.2`. Establish `hpk : p k.1.1 = 0` using `congrArg Subtype.val hk0`. Take `⟨m, hm⟩` from `hnil k.1.1 k.1.2 hpk`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]`.

Establish `hy : q ((f ^ n) k).1 = 0` using `((f ^ n) k).2`. Use `show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1`. Rewrite using `[hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[step]`. Simplify using `using hm`. Use `conv_lhs => rw [hsplit]`. Rewrite using `[map_add, hzero, add_zero]`.
-/
theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dif_pos hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add, hzero, add_zero]
