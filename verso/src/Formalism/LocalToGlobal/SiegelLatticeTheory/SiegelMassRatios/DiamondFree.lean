import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct
import Formalism.LocalToGlobal.Columns.NonDeg

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.SG.DiamondFree

open Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory

namespace RamFunX

open Formalism.L2.Col.RamFun

variable (K : Type) [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, CommGroup (G i)]
  [∀ i, Fintype (G i)] (M : Type) [AddCommGroup M] [Module K M]

def fixF (i : ι) : Submodule K ((∀ i, G i) → M) :=
  ⨅ g : G i, LinearMap.ker (trl K M (Pi.mulSingle i g) - 1)

/- English proof (translation)
Unfold `fixF`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`.
-/
theorem mem_fixF (i : ι) (F : (∀ i, G i) → M) :
    F ∈ fixF K G M i ↔ ∀ g : G i, trl K M (Pi.mulSingle i g) F = F := by
  unfold fixF
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

/- English proof (translation)
Unfold `nmF`. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[trl_mul, ← Pi.mulSingle_mul]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)`.
-/
theorem trl_mulSingle_mul_nmF (i : ι) (g : G i) :
    trl K M (Pi.mulSingle i g) * nmF K M (G := G) i = nmF K M i := by
  unfold nmF
  rw [Finset.mul_sum]
  simp_rw [trl_mul, ← Pi.mulSingle_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)

/- English proof (translation)
Unfold `nmF`. Rewrite using `[LinearMap.sum_apply]`. Repeatedly rewrite using `[(mem_fixF K G M i F).1 hF]`. Rewrite using `[Finset.sum_const, Finset.card_univ]`.
-/
theorem nmF_apply_of_mem (i : ι) {F : (∀ i, G i) → M} (hF : F ∈ fixF K G M i) :
    nmF K M (G := G) i F = (Fintype.card (G i)) • F := by
  unfold nmF
  rw [LinearMap.sum_apply]
  simp_rw [(mem_fixF K G M i F).1 hF]
  rw [Finset.sum_const, Finset.card_univ]

variable [CharZero K]

/- English proof (translation)
Rewrite using `[mem_fixF]`. Introduce `g`. Rewrite using `[LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, trl_mulSingle_mul_nmF]`. Use `map_id F hF := by`. Establish `hc : (Fintype.card (G i) : K) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Rewrite using `[LinearMap.smul_apply, nmF_apply_of_mem K G M i hF, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem isProj_fixF (i : ι) :
    LinearMap.IsProj (fixF K G M i) (((Fintype.card (G i) : K)⁻¹) • nmF K M (G := G) i) where
  map_mem F := by
    rw [mem_fixF]
    intro g
    rw [LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, trl_mulSingle_mul_nmF]
  map_id F hF := by
    have hc : (Fintype.card (G i) : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [LinearMap.smul_apply, nmF_apply_of_mem K G M i hF, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      inv_mul_cancel₀ hc, one_smul]

variable [FiniteDimensional K M]

/- English proof (translation)
Unfold `nmF`. Rewrite using `[map_sum, Finset.sum_eq_single (1 : G i)]`. Rewrite using `[Pi.mulSingle_one, trl_one, LinearMap.trace_one]`. Introduce `g _ hg`. Apply `trace_trl` to reduce the goal to its premises.

Introduce `h`. Conclude with `hg ((Pi.mulSingle_eq_one_iff).1 h)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem trace_nmF (i : ι) :
    LinearMap.trace K _ (nmF K M (G := G) i) = (finrank K ((∀ i, G i) → M) : K) := by
  unfold nmF
  rw [map_sum, Finset.sum_eq_single (1 : G i)]
  · rw [Pi.mulSingle_one, trl_one, LinearMap.trace_one]
  · intro g _ hg
    apply trace_trl
    intro h
    exact hg ((Pi.mulSingle_eq_one_iff).1 h)
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h` using `(isProj_fixF K G M i).trace`. Rewrite `h` using `[map_smul, trace_nmF, smul_eq_mul]`. Establish `hc : (Fintype.card (G i) : K) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `: ((finrank K (fixF K G M i) * Fintype.card (G i) : ℕ) : K) = ((finrank K ((∀ i, G i) → M) : ℕ) : K)`. Use `push_cast`.

Rewrite using `[← h, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Conclude with `this` after adjusting the coercions.
-/
theorem finrank_fixF_mul (i : ι) :
    finrank K (fixF K G M i) * Fintype.card (G i) = finrank K ((∀ i, G i) → M) := by
  have h := (isProj_fixF K G M i).trace
  rw [map_smul, trace_nmF, smul_eq_mul] at h
  have hc : (Fintype.card (G i) : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : ((finrank K (fixF K G M i) * Fintype.card (G i) : ℕ) : K) =
      ((finrank K ((∀ i, G i) → M) : ℕ) : K) := by
    push_cast
    rw [← h, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact_mod_cast this

end RamFunX

section Scalars

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Scalars

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def DiaFreeCols (u : Pr.Word) : Prop := (colGSD W Ch u 0).FreeOnCl (DiaG X.E (Pr.vT u))

def FixPart (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) : Submodule X.K (MfV W Ch u) :=
  ⨅ c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ, LinearMap.ker (diaOp W Ch u 0 P c - 1)

def FixedDimCols (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) : Prop :=
  finrank X.K (FixPart W Ch u P) * (Pr.T u - 1) = finrank X.K (MfV W Ch u)

def IsDiamondFreeWord (u : Pr.Word) : Prop :=
  DiaFreeCols W Ch u ∧ ∀ P : {P // P ∈ Pr.vT u}, FixedDimCols W Ch u P

/- English proof (translation)
The claim follows from `hPr.vT_card u`.
-/
theorem card_places (hPr : Pr.Ok) (u : Pr.Word) : (Pr.vT u).card = X.f := hPr.vT_card u

/- English proof (translation)
The claim follows from `colDiaFree W Ch hX hPr hbig u`.
-/
theorem diaFreeCols_holds (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    DiaFreeCols W Ch u :=
  colDiaFree W Ch hX hPr hbig u

open Classical in
/- English proof (translation)
Set `_ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ` to `fun P => fintypeResU P.1`. Take `⟨σ⟩` from `(colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)`. Establish `: FiniteDimensional X.K ((colGSD W Ch u 0).restr σ.T).EqFun` using `GSD.finiteDimensional_EqFun _ ((colGSD W Ch u 0).restr_ok (colOk W Ch hX u 0) σ.T)`. Establish `hmap : (FixPart W Ch u P).map (σ.split : ColV W Ch u 0 →ₗ[X.K] _) = RamFunX.fixF X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ) ((colGSD W Ch u 0).restr σ.T).EqFun P`. Use extensionality with `F`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, hφ, rfl⟩`. Rewrite using `[RamFunX.mem_fixF]`. Introduce `g`. Establish `hfix : diaOp W Ch u 0 P g φ = φ`.

Use `(Submodule.mem_iInf _).1 hφ g` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `c`. Rewrite using `[RamFun.trl_apply]`. Use `(σ.split_dia (Pi.mulSingle P g) c φ).symm.trans ?_` and prove the remaining obligations.

Use `show σ.split (diaOp W Ch u 0 P g φ) c = σ.split φ c`. Rewrite using `[hfix]`. Introduce `hF`. Use `⟨σ.split.symm F, ?_, σ.split.apply_symm_apply F⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).2 fun g => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Apply `σ.split.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Establish `e` using `σ.split_dia (Pi.mulSingle P g) c (σ.split.symm F)`. Use `e.trans ?_` and prove the remaining obligations.

Rewrite using `[σ.split.apply_symm_apply]`. Conclude with `congrFun ((RamFunX.mem_fixF X.K _ _ P F).1 hF g) c`. Establish `h1` using `RamFunX.finrank_fixF_mul X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ) ((colGSD W Ch u 0).restr σ.T).EqFun P`. Rewrite `h1` using `[← hmap, LinearEquiv.finrank_map_eq]`. Unfold `FixedDimCols`.

Rewrite using `[σ.split.finrank_eq, ← h1, ← card_resU hPr u P, Nat.card_eq_fintype_card]`.
-/
theorem fixedDimCols_holds (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word)
    (P : {P // P ∈ Pr.vT u}) : FixedDimCols W Ch u P := by
  let _ : ∀ P : {P // P ∈ Pr.vT u}, Fintype (𝓞 X.E ⧸ P.1.asIdeal)ˣ := fun P => fintypeResU P.1
  obtain ⟨σ⟩ := (colGSD W Ch u 0).exists_slice (DiaG X.E (Pr.vT u)) (colDiaFree W Ch hX hPr hbig u)
  have : FiniteDimensional X.K ((colGSD W Ch u 0).restr σ.T).EqFun :=
    GSD.finiteDimensional_EqFun _ ((colGSD W Ch u 0).restr_ok (colOk W Ch hX u 0) σ.T)
  have hmap : (FixPart W Ch u P).map (σ.split : ColV W Ch u 0 →ₗ[X.K] _) =
      RamFunX.fixF X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
        ((colGSD W Ch u 0).restr σ.T).EqFun P := by
    ext F
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [RamFunX.mem_fixF]
      intro g
      have hfix : diaOp W Ch u 0 P g φ = φ := by
        have := (Submodule.mem_iInf _).1 hφ g
        rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      funext c
      rw [RamFun.trl_apply]
      refine (σ.split_dia (Pi.mulSingle P g) c φ).symm.trans ?_
      show σ.split (diaOp W Ch u 0 P g φ) c = σ.split φ c
      rw [hfix]
    · intro hF
      refine ⟨σ.split.symm F, ?_, σ.split.apply_symm_apply F⟩
      refine (Submodule.mem_iInf _).2 fun g => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      apply σ.split.injective
      funext c
      have e := σ.split_dia (Pi.mulSingle P g) c (σ.split.symm F)
      refine e.trans ?_
      rw [σ.split.apply_symm_apply]
      exact congrFun ((RamFunX.mem_fixF X.K _ _ P F).1 hF g) c
  have h1 := RamFunX.finrank_fixF_mul X.K (fun P : {P // P ∈ Pr.vT u} => (𝓞 X.E ⧸ P.1.asIdeal)ˣ)
    ((colGSD W Ch u 0).restr σ.T).EqFun P
  rw [← hmap, LinearEquiv.finrank_map_eq] at h1
  unfold FixedDimCols
  rw [σ.split.finrank_eq, ← h1, ← card_resU hPr u P, Nat.card_eq_fintype_card]

/- English proof (translation)
Assemble the required witnesses or components as `⟨diaFreeCols_holds W Ch hX hPr hbig u, fun P => fixedDimCols_holds W Ch hX hPr hbig u P⟩`.
-/
theorem diamondFree_holds (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    IsDiamondFreeWord W Ch u :=
  ⟨diaFreeCols_holds W Ch hX hPr hbig u, fun P => fixedDimCols_holds W Ch hX hPr hbig u P⟩

end Cols

end Formalism.L2.SG.DiamondFree
