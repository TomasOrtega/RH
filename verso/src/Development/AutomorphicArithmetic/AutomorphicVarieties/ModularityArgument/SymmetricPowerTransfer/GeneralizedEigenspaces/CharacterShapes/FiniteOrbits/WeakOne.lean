import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.WeakMultiplicityOne

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← Valuation.vle_one_iff]`. Use `show Valued.v x ≤ Valued.v 1 ↔ _`. Rewrite using `[map_one]`.
-/
private theorem mem_int (w : Plc L) (x : Kw w) : x ∈ 𝒪[Kw w] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
  show Valued.v x ≤ Valued.v 1 ↔ _
  rw [map_one]

/- English proof (translation)
Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer L w`. Use `set ϖ : Kw w := algebraMap L (Kw w) π with hϖdef`. Establish `hϖ : Valued.v ϖ = WithZero.exp (-1)` using `by rw [hϖdef, PI.FinOrdValD.WA.val_alg, hπ]`. Establish `hpow : Valued.v ϖ ^ n = WithZero.exp (-(n : ℤ))`. Rewrite using `[hϖ, ← WithZero.exp_nsmul]`.

Simplify using the standard rewrite rules. Establish `hexp1 : WithZero.exp (-(n : ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hlt1 : Valued.v ((y : Kw w) - 1) < 1` using `lt_of_lt_of_le h hexp1`.

Establish `hvy : Valued.v (y : Kw w) = 1`. Establish `e : (y : Kw w) = 1 + ((y : Kw w) - 1)` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_left]`. Conclude with `map_one _`. Rewrite using `[map_one]`.

Conclude with `hlt1`. Establish `hvyi : Valued.v ((y⁻¹ : (Kw w)ˣ) : Kw w) = 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hvy, inv_one]`. Establish `hyO : (y : Kw w) ∈ 𝒪[Kw w]` using `(mem_int w _).2 hvy.le`. Establish `hyiO : ((y⁻¹ : (Kw w)ˣ) : Kw w) ∈ 𝒪[Kw w]` using `(mem_int w _).2 hvyi.le`.

Set `u : 𝒪[Kw w]ˣ` to `⟨⟨y, hyO⟩, ⟨_, hyiO⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩`. Establish `hϖO : ϖ ∈ 𝒪[Kw w]` using `(mem_int w _).2 (by`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use the proof step `omega)`. Set `ϖ₀ : 𝒪[Kw w]` to `⟨ϖ, hϖO⟩`.

Establish `hϖne : ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ` using `[h0, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hm : ϖ₀ ∈ 𝓂[Kw w]`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨t, ht⟩`. Establish `h1 : ((t : 𝒪[Kw w]) : Kw w) * (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) = 1`. Rewrite using `[← Subring.coe_mul, t.mul_inv]`. Both sides reduce to the same expression.

Establish `hv : Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤ 1` using `(mem_int w _).1 ((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]).2`. Establish `h2` using `congrArg Valued.v h1`. Rewrite `h2` using `[map_mul, map_one, ht]`. Express the relevant statement in the definitionally equal form `Valued.v ϖ * _ = 1 at h2`. Rewrite `h2` using `[hϖ]`.

Establish `h3 : WithZero.exp (-1) * Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤ WithZero.exp (-1)` using `mul_le_of_le_one_right' hv`. Rewrite `h3` using `[h2, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hz : ((y : Kw w) - 1) / ϖ ^ n ∈ 𝒪[Kw w]` using `(mem_int w _).2 (by`. Rewrite using `[map_div₀, map_pow, hpow]`.

Conclude with `div_le_one_of_le₀ h.le zero_le')`. Use `⟨u, ?_, Units.ext rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (u : 𝒪[Kw w]) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`.

Establish `e : (u : 𝒪[Kw w]) - 1 = ϖ₀ ^ n * ⟨_, hz⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Express the relevant statement in the definitionally equal form `(y : Kw w) - 1 = ϖ ^ n * (((y : Kw w) - 1) / ϖ ^ n)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hm n)`.
-/
private theorem mem_Uc (w : Plc L) (n : ℕ) (y : (Kw w)ˣ)
    (h : Valued.v ((y : Kw w) - 1) < WithZero.exp (-(n : ℤ))) : y ∈ Uc (Kw w) n := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L w
  set ϖ : Kw w := algebraMap L (Kw w) π with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := by rw [hϖdef, PI.FinOrdValD.WA.val_alg, hπ]
  have hpow : Valued.v ϖ ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [hϖ, ← WithZero.exp_nsmul]
    simp
  have hexp1 : WithZero.exp (-(n : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt1 : Valued.v ((y : Kw w) - 1) < 1 := lt_of_lt_of_le h hexp1
  have hvy : Valued.v (y : Kw w) = 1 := by
    have e : (y : Kw w) = 1 + ((y : Kw w) - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hlt1
  have hvyi : Valued.v ((y⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvy, inv_one]
  have hyO : (y : Kw w) ∈ 𝒪[Kw w] := (mem_int w _).2 hvy.le
  have hyiO : ((y⁻¹ : (Kw w)ˣ) : Kw w) ∈ 𝒪[Kw w] := (mem_int w _).2 hvyi.le
  let u : 𝒪[Kw w]ˣ := ⟨⟨y, hyO⟩, ⟨_, hyiO⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hϖO : ϖ ∈ 𝒪[Kw w] := (mem_int w _).2 (by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  let ϖ₀ : 𝒪[Kw w] := ⟨ϖ, hϖO⟩
  have hϖne : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hm : ϖ₀ ∈ 𝓂[Kw w] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨t, ht⟩
    have h1 : ((t : 𝒪[Kw w]) : Kw w) * (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) = 1 := by
      rw [← Subring.coe_mul, t.mul_inv]
      rfl
    have hv : Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤ 1 :=
      (mem_int w _).1 ((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]).2
    have h2 := congrArg Valued.v h1
    rw [map_mul, map_one, ht] at h2
    change Valued.v ϖ * _ = 1 at h2
    rw [hϖ] at h2
    have h3 : WithZero.exp (-1) * Valued.v (((t⁻¹ : 𝒪[Kw w]ˣ) : 𝒪[Kw w]) : Kw w) ≤
        WithZero.exp (-1) := mul_le_of_le_one_right' hv
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    omega
  have hz : ((y : Kw w) - 1) / ϖ ^ n ∈ 𝒪[Kw w] := (mem_int w _).2 (by
    rw [map_div₀, map_pow, hpow]
    exact div_le_one_of_le₀ h.le zero_le')
  refine ⟨u, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk _ (u : 𝒪[Kw w]) = 1
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
  have e : (u : 𝒪[Kw w]) - 1 = ϖ₀ ^ n * ⟨_, hz⟩ := by
    apply Subtype.ext
    push_cast
    change (y : Kw w) - 1 = ϖ ^ n * (((y : Kw w) - 1) / ϖ ^ n)
    field_simp
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hm n)

end UpperTheory.V.Z.Sym.So.WeakMultiplicityOne

open UpperTheory.V.Z.Sym.So.WeakMultiplicityOne in
/- English proof (translation)
Introduce `L _ _ _ S hS x c`. Use `set cj := IsCMField.complexConj L with hcj`. Establish `hfr : Module.finrank (maximalRealSubfield L) L = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hsp : ∀ w ∈ S, ∃ u : Plc L, u ≠ w ∧ u ∉ S ∧ GlobalTheory.Mem.Chr.ConjPl cj.toRingEquiv w u`. Introduce `w hw`.

Take `⟨u, hne, hu⟩` from `hS.split w hw`. Use `⟨u, hne, fun huS => hne (hS.inj huS hw hu), ?_⟩` and prove the remaining obligations. Break down `(GlobalTheory.Mem.Chr.under_eq_iff_conjPl cj hfr (IsCMField.complexConj_ne_one L) w u).1 hu with h | h` into its components or cases. Conclude with `absurd h hne`. Conclude with `h`.

Use `choose! ub hub using hsp`. Use `set E : ℕ := ∑ w ∈ S, c w with hE`. Take `⟨a, ha, -⟩` from `PI.FinOrdValD.WA.weakApprox_units (S ∪ S.image ub) (fun v => if v ∈ S then x v else 1) (fun _ => (E : ℤ))`. Establish `hcc : cj (cj (a : L)) = a` using `IsCMField.complexConj_apply_apply L _`. Establish `ha0 : (a : L) ≠ 0` using `a.ne_zero`.

Establish `hca0 : cj (a : L) ≠ 0`. Introduce `h0`. Apply `ha0` to reduce the goal to its premises. Rewrite using `[← hcc, h0, map_zero]`. Set `ca : Lˣ` to `Units.mk0 (cj (a : L)) hca0`.

Use `⟨a * ca⁻¹, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, ca, Units.val_mk0, map_mul, map_inv₀, hcc]`. Clear the denominators using the available nonvanishing facts. Introduce `w hw`. Take `⟨hne, hnS, hconj⟩` from `hub w hw`.

Apply `mem_Uc w (c w)` to reduce the goal to its premises. Establish `hA` using `ha w (Finset.mem_union_left _ hw)`. Establish `hB` using `ha (ub w) (Finset.mem_union_right _ (Finset.mem_image_of_mem ub hw))`. Simplify using `only [hw, hnS, if_true, if_false, inv_one, Units.val_one, mul_one] at hA hB`. Establish `hB' : Valued.v (algebraMap L (Kw w) (cj a) - 1) < WithZero.exp (-(E : ℤ))`.

Establish `e1 : algebraMap L (Kw w) (cj a) - 1 = algebraMap L (Kw w) (cj ((a : L) - 1))`. Simplify using `[map_sub]`. Rewrite using `[e1, PI.FinOrdValD.WA.val_alg, ← hconj (cj ((a : L) - 1))]`. Express the relevant statement in the definitionally equal form `HeightOneSpectrum.valuation L (ub w) (cj (cj ((a : L) - 1))) < _`. Rewrite using `[IsCMField.complexConj_apply_apply, ← PI.FinOrdValD.WA.val_alg, map_sub, map_one]`.

Conclude with `hB`. Establish `hexp : WithZero.exp (-(E : ℤ)) ≤ WithZero.exp (-((c w : ℕ) : ℤ))`. Establish `hcw : c w ≤ E` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `hexp1 : WithZero.exp (-(E : ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hvB : Valued.v (algebraMap L (Kw w) (cj a)) = 1`. Establish `e : algebraMap L (Kw w) (cj a) = 1 + (algebraMap L (Kw w) (cj a) - 1)` using `by ring`.

Rewrite using `[e, Valuation.map_add_eq_of_lt_left]`. Conclude with `map_one _`. Rewrite using `[map_one]`. Conclude with `lt_of_lt_of_le hB' hexp1`. Establish `hB0 : algebraMap L (Kw w) (cj a) ≠ 0`.

Introduce `h0`. Rewrite `hvB` using `[h0, map_zero]`. Conclude with `zero_ne_one hvB`. Establish `hexpr : ((Units.map (algebraMap L (Kw w) : L →* Kw w) (a * ca⁻¹) / x w : (Kw w)ˣ) : Kw w) = (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹`. Simplify using `only [Units.val_div_eq_div_val, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val, ca, Units.val_mk0, MonoidHom.coe_coe, map_mul, map_inv₀, div_eq_mul_inv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexpr]`. Establish `e2 : (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹ - 1 = ((algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w) - 1) - (algebraMap L (Kw w) (cj a) - 1)) * (algebraMap L (Kw w) (cj a))⁻¹`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, map_mul, map_inv₀, hvB, inv_one, mul_one]`. Conclude with `lt_of_lt_of_le (Valuation.map_sub_lt _ hA hB') hexp`.
-/
theorem UpperTheory.V.Z.Sym.So.weakOne :
    UpperTheory.V.Z.Sym.So.WeakOne := by
  intro L _ _ _ S hS x c
  classical
  set cj := IsCMField.complexConj L with hcj
  have hfr : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsp : ∀ w ∈ S, ∃ u : Plc L, u ≠ w ∧ u ∉ S ∧ GlobalTheory.Mem.Chr.ConjPl cj.toRingEquiv w u := by
    intro w hw
    obtain ⟨u, hne, hu⟩ := hS.split w hw
    refine ⟨u, hne, fun huS => hne (hS.inj huS hw hu), ?_⟩
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl cj hfr (IsCMField.complexConj_ne_one L) w u).1 hu with h | h
    · exact absurd h hne
    · exact h
  choose! ub hub using hsp
  set E : ℕ := ∑ w ∈ S, c w with hE
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units (S ∪ S.image ub)
    (fun v => if v ∈ S then x v else 1) (fun _ => (E : ℤ))
  have hcc : cj (cj (a : L)) = a := IsCMField.complexConj_apply_apply L _
  have ha0 : (a : L) ≠ 0 := a.ne_zero
  have hca0 : cj (a : L) ≠ 0 := by
    intro h0
    apply ha0
    rw [← hcc, h0, map_zero]
  let ca : Lˣ := Units.mk0 (cj (a : L)) hca0
  refine ⟨a * ca⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, ca, Units.val_mk0, map_mul, map_inv₀, hcc]
    field_simp
  · intro w hw
    obtain ⟨hne, hnS, hconj⟩ := hub w hw
    apply mem_Uc w (c w)
    have hA := ha w (Finset.mem_union_left _ hw)
    have hB := ha (ub w) (Finset.mem_union_right _ (Finset.mem_image_of_mem ub hw))
    simp only [hw, hnS, if_true, if_false, inv_one, Units.val_one, mul_one] at hA hB
    have hB' : Valued.v (algebraMap L (Kw w) (cj a) - 1) < WithZero.exp (-(E : ℤ)) := by
      have e1 : algebraMap L (Kw w) (cj a) - 1 = algebraMap L (Kw w) (cj ((a : L) - 1)) := by
        simp [map_sub]
      rw [e1, PI.FinOrdValD.WA.val_alg, ← hconj (cj ((a : L) - 1))]
      change HeightOneSpectrum.valuation L (ub w) (cj (cj ((a : L) - 1))) < _
      rw [IsCMField.complexConj_apply_apply, ← PI.FinOrdValD.WA.val_alg, map_sub, map_one]
      exact hB
    have hexp : WithZero.exp (-(E : ℤ)) ≤ WithZero.exp (-((c w : ℕ) : ℤ)) := by
      have hcw : c w ≤ E := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
      rw [WithZero.exp_le_exp]
      omega
    have hexp1 : WithZero.exp (-(E : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hvB : Valued.v (algebraMap L (Kw w) (cj a)) = 1 := by
      have e : algebraMap L (Kw w) (cj a) = 1 + (algebraMap L (Kw w) (cj a) - 1) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left]
      · exact map_one _
      · rw [map_one]; exact lt_of_lt_of_le hB' hexp1
    have hB0 : algebraMap L (Kw w) (cj a) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hvB
      exact zero_ne_one hvB
    have hexpr : ((Units.map (algebraMap L (Kw w) : L →* Kw w) (a * ca⁻¹) / x w : (Kw w)ˣ) : Kw w) =
        (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹ := by
      simp only [Units.val_div_eq_div_val, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val, ca,
        Units.val_mk0, MonoidHom.coe_coe, map_mul, map_inv₀, div_eq_mul_inv]
      ring
    rw [hexpr]
    have e2 : (algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w)) * (algebraMap L (Kw w) (cj a))⁻¹ - 1
        = ((algebraMap L (Kw w) a * (((x w)⁻¹ : (Kw w)ˣ) : Kw w) - 1) -
          (algebraMap L (Kw w) (cj a) - 1)) * (algebraMap L (Kw w) (cj a))⁻¹ := by
      field_simp
      ring
    rw [e2, map_mul, map_inv₀, hvB, inv_one, mul_one]
    exact lt_of_lt_of_le (Valuation.map_sub_lt _ hA hB') hexp

end
