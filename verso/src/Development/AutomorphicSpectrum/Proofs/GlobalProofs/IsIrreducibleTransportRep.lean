import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff

open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

section Generators

variable (K : Type) [Field K] [Fintype K]

/- English proof (translation)
Establish `hN : 0 < N` using `Nat.pos_of_dvd_of_pos hNM hM`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Establish `hw' : IsPrimitiveRoot (w ^ (M / N)) N` using `hw.pow hM (Nat.div_mul_cancel hNM).symm`. Take `⟨a, -, ha, hza⟩` from `(hw'.isPrimitiveRoot_iff).1 hz`.

Take `⟨u, hu⟩` from `ZMod.unitsMap_surjective hNM (ZMod.unitOfCoprime a ha)`. Establish `h1 : ((u : ZMod M).val : ZMod N) = (a : ZMod N)`. Use `congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu` as an intermediate fact. Simplify `this` using `[ZMod.unitsMap_val]`. Use `⟨w ^ (u : ZMod M).val, hw.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm, pow_mul, ← hza]`. Conclude with `pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1) hw'.pow_eq_one`.
-/
theorem exists_root_over {F : Type} [Field F] {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) {z w : F}
    (hz : IsPrimitiveRoot z N) (hw : IsPrimitiveRoot w M) : ∃ z' : F, IsPrimitiveRoot z' M ∧ z' ^ (M / N) = z := by
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNM hM
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  have hw' : IsPrimitiveRoot (w ^ (M / N)) N := hw.pow hM (Nat.div_mul_cancel hNM).symm
  obtain ⟨a, -, ha, hza⟩ := (hw'.isPrimitiveRoot_iff).1 hz
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfCoprime a ha)
  have h1 : ((u : ZMod M).val : ZMod N) = (a : ZMod N) := by
    have := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
    simpa [ZMod.unitsMap_val] using this
  refine ⟨w ^ (u : ZMod M).val, hw.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← hza]
  exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1) hw'.pow_eq_one

/- English proof (translation)
The claim follows from `Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' Fintype.one_lt_card)`.
-/
theorem lev_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' Fintype.one_lt_card)

/- English proof (translation)
Establish `h1 : 1 ≤ Fintype.card K ^ d` using `Nat.one_le_pow _ _ Fintype.card_pos`. Establish `hq : ((Fintype.card K : ℕ) : AlgebraicClosure K) = 0`. Rewrite using `[← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.cast_card_eq_zero, map_zero]`. Use `haveI : NeZero ((Fintype.card K ^ d - 1 : ℕ) : AlgebraicClosure K) := ⟨by`. Rewrite using `[Nat.cast_sub h1, Nat.cast_pow, hq, zero_pow hd.ne']`.

Use the proof step `simp⟩`. Use `haveI : NeZero (Fintype.card K ^ d - 1) := ⟨(lev_pos K hd).ne'⟩`. Conclude with `HasEnoughRootsOfUnity.exists_primitiveRoot _ _`.
-/
theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ w : AlgebraicClosure K, IsPrimitiveRoot w (Fintype.card K ^ d - 1) := by
  have h1 : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
  have hq : ((Fintype.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.cast_card_eq_zero, map_zero]
  haveI : NeZero ((Fintype.card K ^ d - 1 : ℕ) : AlgebraicClosure K) := ⟨by
    rw [Nat.cast_sub h1, Nat.cast_pow, hq, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨(lev_pos K hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

noncomputable def tower : (k : ℕ) → {z : AlgebraicClosure K // IsPrimitiveRoot z (Fintype.card K ^ k.factorial - 1)}
  | 0 => ⟨(exists_prim K (Nat.factorial_pos 0)).choose, (exists_prim K (Nat.factorial_pos 0)).choose_spec⟩
  | k + 1 =>
    have h := exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec
    ⟨h.choose, h.choose_spec.1⟩

/- English proof (translation)
The claim follows from `(exists_root_over (lev_pos K (Nat.factorial_pos (k + 1))) (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower K k).2 (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec).choose_spec.2`.
-/
theorem tower_succ (k : ℕ) :
    (tower K (k + 1)).1 ^ ((Fintype.card K ^ (k + 1).factorial - 1) / (Fintype.card K ^ k.factorial - 1)) =
      (tower K k).1 :=
  (exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower K k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec).choose_spec.2

/- English proof (translation)
Proceed by induction on `l, h using Nat.le_induction with`. Consider the case `base => rw [Nat.div_self (lev_pos K (Nat.factorial_pos k)), pow_one]`. Consider the case `succ l hl ih`. Rewrite using `[← Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ l))) (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hl)), pow_mul, tower_succ, ih]`.
-/
theorem tower_le {k l : ℕ} (h : k ≤ l) :
    (tower K l).1 ^ ((Fintype.card K ^ l.factorial - 1) / (Fintype.card K ^ k.factorial - 1)) = (tower K k).1 := by
  induction l, h using Nat.le_induction with
  | base => rw [Nat.div_self (lev_pos K (Nat.factorial_pos k)), pow_one]
  | succ l hl ih =>
    rw [← Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ l)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hl)), pow_mul, tower_succ, ih]

/- English proof (translation)
Use `⟨fun d => (tower K d).1 ^ ((Fintype.card K ^ d.factorial - 1) / (Fintype.card K ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩` and prove the remaining obligations. Establish `hdv` using `Nat.pow_sub_one_dvd_pow_sub_one (Fintype.card K) (Nat.dvd_factorial hd le_rfl)`. Conclude with `((tower K d).2.pow (lev_pos K (Nat.factorial_pos d)) (Nat.div_mul_cancel hdv).symm).eq_orderOf.symm`. Establish `hle : d ≤ d'` using `Nat.le_of_dvd hd' hdd show ((tower K d').1 ^ _) ^ _ = (tower K d).1 ^ _`. Rewrite using `[← pow_mul, Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd' le_rfl)) (Nat.pow_sub_one_dvd_pow_sub_one _ hdd), ← tower_le K hle, ← pow_mul, Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hle)) (Nat.pow_sub_one_dvd_pow_sub_ …`.
-/
theorem exists_genSys : ∃ ζ : ℕ → AlgebraicClosure K, ∀ d, 0 < d → orderOf (ζ d) = Fintype.card K ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((Fintype.card K ^ d' - 1) / (Fintype.card K ^ d - 1)) = ζ d := by
  refine ⟨fun d => (tower K d).1 ^ ((Fintype.card K ^ d.factorial - 1) / (Fintype.card K ^ d - 1)),
    fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · have hdv := Nat.pow_sub_one_dvd_pow_sub_one (Fintype.card K) (Nat.dvd_factorial hd le_rfl)
    exact ((tower K d).2.pow (lev_pos K (Nat.factorial_pos d)) (Nat.div_mul_cancel hdv).symm).eq_orderOf.symm
  · have hle : d ≤ d' := Nat.le_of_dvd hd' hdd
    show ((tower K d').1 ^ _) ^ _ = (tower K d).1 ^ _
    rw [← pow_mul, Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd' le_rfl))
      (Nat.pow_sub_one_dvd_pow_sub_one _ hdd), ← tower_le K hle, ← pow_mul,
      Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hle))
        (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd le_rfl))]

/- English proof (translation)
Take `⟨θ, hθ⟩` from `GlobalTheory.CuspGL.TeichEmb.exists_teichmuller K`. Take `⟨ζ, hζ⟩` from `exists_genSys K`. Conclude with `⟨{ ι := θ, ι_inj := hθ, gen := ζ, gen_order := fun d hd => (hζ d hd).1 gen_norm := fun d e hd he => (hζ d hd).2 (d * e) (Dvd.intro _ rfl) (Nat.mul_pos hd he) }⟩`.
-/
theorem nonempty_labelConv [DecidableEq K] : Nonempty (Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.CuspGL.TeichEmb.exists_teichmuller K
  obtain ⟨ζ, hζ⟩ := exists_genSys K
  exact ⟨{ ι := θ, ι_inj := hθ, gen := ζ, gen_order := fun d hd => (hζ d hd).1
           gen_norm := fun d e hd he => (hζ d hd).2 (d * e) (Dvd.intro _ rfl) (Nat.mul_pos hd he) }⟩

/- English proof (translation)
Use `haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩`. Use `haveI : NeZero d := ⟨by omega⟩`. Set `E` to `FiniteField.Extension K (ringChar K) d`. Establish `hfin : Module.finrank K E = d` using `FiniteField.finrank_extension K (ringChar K) d`. Take `⟨β, hβ⟩` from `Field.exists_primitive_element K E`.

Choose the witnesses or unpack the hypotheses as in `⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ IntermediateField.adjoin K {α} = ⊤ := by`. Distinguish the cases in `h : β = 0`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality. Rewrite using `[IntermediateField.adjoin_one]`.

Rewrite `hβ` using `[IntermediateField.adjoin_zero]`. Then use the resulting hypothesis. Conclude with `⟨β, h, hβ⟩`. Establish `hint : IsIntegral K α` using `Algebra.IsIntegral.isIntegral α`. Use `⟨minpoly K α, minpoly.monic hint, minpoly.irreducible hint, fun h => hα0 ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `minpoly.aeval K α`.

Rewrite `h0` using `[h, aeval_X]`. Then use the resulting hypothesis. Rewrite using `[← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', hfin]`.
-/
theorem exists_monic_irreducible (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : NeZero d := ⟨by omega⟩
  let E := FiniteField.Extension K (ringChar K) d
  have hfin : Module.finrank K E = d := FiniteField.finrank_extension K (ringChar K) d
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ IntermediateField.adjoin K {α} = ⊤ := by
    by_cases h : β = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      subst h
      rw [IntermediateField.adjoin_one]
      rwa [IntermediateField.adjoin_zero] at hβ
    · exact ⟨β, h, hβ⟩
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly K α, minpoly.monic hint, minpoly.irreducible hint, fun h => hα0 ?_, ?_⟩
  · have h0 := minpoly.aeval K α
    rwa [h, aeval_X] at h0
  · rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', hfin]

end Generators

section Transport

variable {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def transportRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transportRep_apply (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

end Transport

/- English proof (translation)
Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨e.symm.toEquiv.nontrivial, fun U hU => ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ g, ∀ v ∈ U.comap e.toLinearMap, ρ g v ∈ U.comap e.toLinearMap`. Introduce `g v hv`. Establish `h1` using `hU g (e v) hv`. Rewrite `h1` using `[transportRep_apply, e.symm_apply_apply]`.

Conclude with `h1`. Break down `h _ hinv with h0 | h0` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun w hw => ?_` and prove the remaining obligations. Establish `h1 : e.symm w ∈ U.comap e.toLinearMap` using `by show e (e.symm w) ∈ U`.

Rewrite using `[e.apply_symm_apply]` and apply the resulting hypothesis. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Simplify using `using h1`. Use `right`. Use `(Submodule.eq_top_iff').2 fun w => ?_` and prove the remaining obligations.

Establish `h1 : e.symm w ∈ U.comap e.toLinearMap` using `by rw [h0]; trivial`. Establish `h2 : e (e.symm w) ∈ U` using `h1`. Rewrite `h2` using `[e.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem isIrreducible_transportRep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) : (transportRep ρ e).IsIrreducible := by
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨e.symm.toEquiv.nontrivial, fun U hU => ?_⟩
  have hinv : ∀ g, ∀ v ∈ U.comap e.toLinearMap, ρ g v ∈ U.comap e.toLinearMap := by
    intro g v hv
    have h1 := hU g (e v) hv
    rw [transportRep_apply, e.symm_apply_apply] at h1
    exact h1
  rcases h _ hinv with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by
      show e (e.symm w) ∈ U
      rwa [e.apply_symm_apply]
    rw [h0, Submodule.mem_bot] at h1
    simpa using h1
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by rw [h0]; trivial
    have h2 : e (e.symm w) ∈ U := h1
    rwa [e.apply_symm_apply] at h2

/- English proof (translation)
Rewrite using `[GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks]`. Introduce `a ha haN w hw`. Set `b : Fin N → Fin 2` to `fun i => if (i : ℕ) < a then 0 else 1`. Establish `hs : Function.Surjective b`. Introduce `c`.

Use `fin_cases c`. Conclude with `⟨⟨0, by omega⟩, by simp [b, ha]⟩`. Conclude with `⟨⟨a, haN⟩, by simp [b]⟩`. Establish `h0` using `h 2 b hs le_rfl (e.symm w) (fun u hu => ?_)`. Simplify using `using h0`.

Take `⟨⟨hUT, -⟩, hdiag⟩` from `hu`. Establish `hu' : u ∈ GlobalTheory.FiniteGL.unipRadical K (GlobalTheory.FiniteGL.twoBlocks N a)`. Introduce `i j hij`. Establish `hlt : b i = b j ∨ b j < b i`. Simplify using `only [b, GlobalTheory.FiniteGL.twoBlocks] at hij ⊢`.

Apply the tactic sequence `split_ifs at hij ⊢ <;> simp_all`. Break down `hlt with hb | hb` into its components or cases. Rewrite using `[Matrix.sub_apply, hdiag i j hb, Matrix.one_apply, sub_self]`. Establish `hne : i ≠ j` using `fun e' => by rw [e'] at hb; exact lt_irrefl _ hb`. Rewrite using `[Matrix.sub_apply, hUT i j hb, Matrix.one_apply_ne hne, sub_zero]`.

Establish `h1` using `hw u hu'`. Rewrite `h1` using `[transportRep_apply]`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[h1, e.apply_symm_apply]`.
-/
theorem isCuspidal_transportRep {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : FDRep ℂ (GL (Fin N) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) (e : τ ≃ₗ[ℂ] W) :
    GlobalTheory.FiniteGL.IsCuspidal (transportRep τ.ρ e) := by
  rw [GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks]
  intro a ha haN w hw
  let b : Fin N → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  have hs : Function.Surjective b := by
    intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [b, ha]⟩
    · exact ⟨⟨a, haN⟩, by simp [b]⟩
  have h0 := h 2 b hs le_rfl (e.symm w) (fun u hu => ?_)
  · simpa using h0
  · obtain ⟨⟨hUT, -⟩, hdiag⟩ := hu
    have hu' : u ∈ GlobalTheory.FiniteGL.unipRadical K (GlobalTheory.FiniteGL.twoBlocks N a) := by
      intro i j hij
      have hlt : b i = b j ∨ b j < b i := by
        simp only [b, GlobalTheory.FiniteGL.twoBlocks] at hij ⊢
        split_ifs at hij ⊢ <;> simp_all
      rcases hlt with hb | hb
      · rw [Matrix.sub_apply, hdiag i j hb, Matrix.one_apply, sub_self]
      · have hne : i ≠ j := fun e' => by rw [e'] at hb; exact lt_irrefl _ hb
        rw [Matrix.sub_apply, hUT i j hb, Matrix.one_apply_ne hne, sub_zero]
    have h1 := hw u hu'
    rw [transportRep_apply] at h1
    apply e.injective
    rw [h1, e.apply_symm_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

/- English proof (translation)
Introduce `k _ _ n`. Take `⟨C⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv k`. Take `⟨P, h1, h2, h3, h4⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible k (n + 1) (by omega)`. Take `⟨τ, hs, hc, -⟩` from `GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label k C (n + 1) (by omega) P h1 h2 h3 h4`. Establish `hI` using `(GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 _ τ).1 hs`.

Set `e` to `(Module.finBasis ℂ τ).equivFun`. Conclude with `⟨_, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.transportRep τ.ρ e, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isIrreducible_transportRep τ.ρ e hI.1 hI.2, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isCuspidal_transportRep τ hc e⟩`.
-/
theorem GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds : GlobalTheory.Published.CuspidalExists := by
  intro k _ _ n
  classical
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv k
  obtain ⟨P, h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible k (n + 1) (by omega)
  obtain ⟨τ, hs, hc, -⟩ := GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label k C (n + 1) (by omega) P h1 h2 h3 h4
  have hI := (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 _ τ).1 hs
  let e := (Module.finBasis ℂ τ).equivFun
  exact ⟨_, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.transportRep τ.ρ e,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isIrreducible_transportRep τ.ρ e hI.1 hI.2,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isCuspidal_transportRep τ hc e⟩
