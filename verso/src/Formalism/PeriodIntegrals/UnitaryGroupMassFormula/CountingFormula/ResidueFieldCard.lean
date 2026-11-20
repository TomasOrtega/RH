import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

/- English proof (translation)
Use `A.lf` as an intermediate fact. Establish `key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔ p.valuation F x ≤ p.valuation F y` using `fun x y => by`. Rewrite using `[← Valuation.vle_iff_le]`. Conclude with `A.val x y`. Establish `keyle1 : ∀ x : F, valuation A.Fp (A.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1` using `fun x => by`.

Establish `h` using `key x 1`. Rewrite `h` using `[map_one, map_one, map_one]`. Then use the resulting hypothesis. Establish `keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1` using `fun x => by`. Establish `h` using `key 1 x`. Rewrite `h` using `[map_one, map_one, map_one]`.

Rewrite using `[← not_le, ← not_le, h]`. Set `f : 𝓞 F →+* 𝒪[A.Fp]` to `{ toFun := fun x => ⟨A.ιF (algebraMap (𝓞 F) F x), (keyle1 _).2 (p.valuation_le_one (K := F) x)⟩ map_one' := by ext; simp map_mul' := by intro a b; ext; simp map_zero' := by ext; simp map_add' := by intro a b; ext; simp }`. Set `φ : 𝓞 F →+* 𝓀[A.Fp]` to `(IsLocalRing.residue 𝒪[A.Fp]).comp f`. Establish `hmax : ∀ w : 𝒪[A.Fp], w ∈ IsLocalRing.maximalIdeal 𝒪[A.Fp] ↔ valuation A.Fp (w : A.Fp) < 1` using `fun w => by`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one`. Establish `hker : RingHom.ker φ = p.asIdeal`. Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax]`. Conclude with `(keylt1 _).trans (p.valuation_lt_one_iff_mem (K := F) x)`.

Establish `hsurj : Function.Surjective φ`. Introduce `z0`. Take `⟨z, rfl⟩` from `IsLocalRing.residue_surjective z0`. Establish `hS : {w : A.Fp | valuation A.Fp (w - z) < 1} ∈ nhds (z : A.Fp)` using `(IsValuativeTopology.hasBasis_nhds' (z : A.Fp)).mem_of_mem one_ne_zero`. Take `⟨w, ⟨x', rfl⟩, hw⟩` from `A.dense.inter_nhds_nonempty hS`.

Establish `hw' : valuation A.Fp (A.ιF x' - z) < 1` using `hw`. Establish `hx' : p.valuation F x' ≤ 1`. Rewrite using `[← keyle1]`. Establish `hz : valuation A.Fp (z : A.Fp) ≤ 1` using `z.2`. Use `Valuation.map_add_le (valuation A.Fp) hw'.le hz` as an intermediate fact.

Simplify using `using this`. Take `⟨a, ha⟩` from `IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer (v := p) (K := F) hx' 1`. Establish `ha' : p.valuation F (algebraMap (𝓞 F) F a - x') < 1` using `by simpa using ha`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]`.

Establish `h1 : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F a - x')) < 1` using `(keylt1 _).2 ha'`. Establish `h2` using `Valuation.map_add_lt (valuation A.Fp) h1 hw'`. Establish `he : ((f a - z : 𝒪[A.Fp]) : A.Fp) = A.ιF (algebraMap (𝓞 F) F a - x') + (A.ιF x' - z)`. Simplify using `only [map_sub]`. Use `show A.ιF (algebraMap (𝓞 F) F a) - (z : A.Fp) = _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `h2`. Rewrite using `[← hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm`.
-/
theorem resCard_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Loc.LocAt F E sig p) :
    Nat.card 𝓀[A.Fp] = p.asIdeal.absNorm := by
  have := A.lf
  have key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← Valuation.vle_iff_le]; exact A.val x y
  have keyle1 : ∀ x : F, valuation A.Fp (A.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := fun x => by
    have h := key x 1
    rwa [map_one, map_one, map_one] at h
  have keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1 := fun x => by
    have h := key 1 x
    rw [map_one, map_one, map_one] at h
    rw [← not_le, ← not_le, h]
  let f : 𝓞 F →+* 𝒪[A.Fp] :=
    { toFun := fun x => ⟨A.ιF (algebraMap (𝓞 F) F x),
        (keyle1 _).2 (p.valuation_le_one (K := F) x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : 𝓞 F →+* 𝓀[A.Fp] := (IsLocalRing.residue 𝒪[A.Fp]).comp f
  have hmax : ∀ w : 𝒪[A.Fp], w ∈ IsLocalRing.maximalIdeal 𝒪[A.Fp] ↔ valuation A.Fp (w : A.Fp) < 1 :=
    fun w => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hker : RingHom.ker φ = p.asIdeal := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax]
    exact (keylt1 _).trans (p.valuation_lt_one_iff_mem (K := F) x)
  have hsurj : Function.Surjective φ := by
    intro z0
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z0
    have hS : {w : A.Fp | valuation A.Fp (w - z) < 1} ∈ nhds (z : A.Fp) :=
      (IsValuativeTopology.hasBasis_nhds' (z : A.Fp)).mem_of_mem one_ne_zero
    obtain ⟨w, ⟨x', rfl⟩, hw⟩ := A.dense.inter_nhds_nonempty hS
    have hw' : valuation A.Fp (A.ιF x' - z) < 1 := hw
    have hx' : p.valuation F x' ≤ 1 := by
      rw [← keyle1]
      have hz : valuation A.Fp (z : A.Fp) ≤ 1 := z.2
      have := Valuation.map_add_le (valuation A.Fp) hw'.le hz
      simpa using this
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
      (v := p) (K := F) hx' 1
    have ha' : p.valuation F (algebraMap (𝓞 F) F a - x') < 1 := by simpa using ha
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    have h1 : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F a - x')) < 1 := (keylt1 _).2 ha'
    have h2 := Valuation.map_add_lt (valuation A.Fp) h1 hw'
    have he : ((f a - z : 𝒪[A.Fp]) : A.Fp) =
        A.ιF (algebraMap (𝓞 F) F a - x') + (A.ιF x' - z) := by
      simp only [map_sub]
      show A.ιF (algebraMap (𝓞 F) F a) - (z : A.Fp) = _
      ring
    rw [he]
    exact h2
  rw [← hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

/- English proof (translation)
Introduce `D p` and use `resCard_loc _`.
-/
theorem residue_field_card : ResCard := fun D p => resCard_loc _

end PI.UnitaryGroupMassFormula.CntFormula
