import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentFiniteOfTriangularSignedIndicatorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMultisetSatakeEigenvalueEqStatement

noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp NumberField IsDedekindDomain

section Induced

variable {G M V : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T1Space M] [AddCommGroup V] [Module ℂ V] (P : LeviDatum G M) (χ : M →* ℂˣ) {K : Subgroup G}

/- English proof (translation)
Take `⟨S, p, hp⟩` from `h`. Establish `hS : IsSmooth S.toRepresentation` using `fun v => by`. Use `(congrArg IsOpen ?_).mpr (P.nInd_isSmooth (charRep χ) v.1)` and prove the remaining obligations. Use extensionality with `g`. Conclude with `Subtype.ext_iff`.

Rewrite `hx` using `[← GlobalTheory.LocGL.map_fixed_of_surjective hS hK hp]`. Take `⟨y, hy, rfl⟩` from `hx`. Set `ι : S.toSubmodule →ₗ[ℂ] (G → ℂ)` to `(Submodule.subtype _).comp ((Submodule.subtype _).comp S.toSubmodule.subtype)`. Establish `hι : Function.Injective ι` using `fun a b e => Subtype.ext (Subtype.ext (Subtype.ext e))`. Use `⟨ι y, fun e => h0 ?_, fun b g k hk => ?_, fun f hf c e => ?_⟩` and prove the remaining obligations.

Rewrite using `[hι (e.trans (map_zero ι).symm), map_zero]`. Establish `h1 : ι y (b * g * k) = ι y (b * g)` using `congrFun (congrArg ι (mem_fixed.1 hy k hk)) (b * g)`. Rewrite using `[h1]`. Conclude with `(LeviDatum.IndSpace.law P y.1 b g).trans (by rw [charRep_apply, smul_eq_mul, ← mul_assoc]; rfl)`. Rewrite `e` using `[← map_heckeVec (ρ := S.toRepresentation) hc hf ι (fun _ _ => rfl), ← map_smul]`.

Rewrite using `[← map_heckeVec (ρ := S.toRepresentation) hc hf p.toLinearMap (fun g v => p.isIntertwining _ _ g v), hι e, map_smul]`.
-/
theorem exists_fun_of_isSubquot (hK : IsCompact (K : Set G)) (hc : IsCommensurated K) {π : Representation ℂ G V}
    (h : IsSubquot π (P.nInd (charRep χ))) {x : V} (hx : x ∈ fixed π K) (h0 : x ≠ 0) :
    ∃ φ : G → ℂ, φ ≠ 0 ∧ (∀ (b : P.Q) g, ∀ k ∈ K, φ (b * g * k) = (P.deltaHalf b : ℂ) * χ (P.p b) * φ g) ∧
      ∀ f ∈ Hecke ℂ K, ∀ c : ℂ, heckeVec (rightReg ℂ G ℂ) K f φ = c • φ → heckeVec π K f x = c • x := by
  obtain ⟨S, p, hp⟩ := h
  have hS : IsSmooth S.toRepresentation := fun v => by
    refine (congrArg IsOpen ?_).mpr (P.nInd_isSmooth (charRep χ) v.1)
    ext g
    exact Subtype.ext_iff
  rw [← GlobalTheory.LocGL.map_fixed_of_surjective hS hK hp] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  let ι : S.toSubmodule →ₗ[ℂ] (G → ℂ) := (Submodule.subtype _).comp ((Submodule.subtype _).comp S.toSubmodule.subtype)
  have hι : Function.Injective ι := fun a b e => Subtype.ext (Subtype.ext (Subtype.ext e))
  refine ⟨ι y, fun e => h0 ?_, fun b g k hk => ?_, fun f hf c e => ?_⟩
  · rw [hι (e.trans (map_zero ι).symm), map_zero]
  · have h1 : ι y (b * g * k) = ι y (b * g) := congrFun (congrArg ι (mem_fixed.1 hy k hk)) (b * g)
    rw [h1]
    exact (LeviDatum.IndSpace.law P y.1 b g).trans (by rw [charRep_apply, smul_eq_mul, ← mul_assoc]; rfl)
  · rw [← map_heckeVec (ρ := S.toRepresentation) hc hf ι (fun _ _ => rfl), ← map_smul] at e
    rw [← map_heckeVec (ρ := S.toRepresentation) hc hf p.toLinearMap (fun g v => p.isIntertwining _ _ g v), hι e,
      map_smul]

/- English proof (translation)
Establish `hr : ∀ k ∈ K, ∀ g, φ (g * k) = φ g` using `fun k hk g => by simpa using hφ 1 g k hk`. Set `z : indSpace P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p))` to `⟨φ, fun b g => by`. Use `hφ b g 1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, twist_apply, MonoidHom.comp_apply, charRep_apply, smul_eq_mul, mul_assoc]⟩`.

Establish `hz : z ∈ smoothPart (ind P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p)))` using `GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem _)) fun g hg => Subtype.ext (funext (hr g hg)))`. Set `ι : P.IndSpace (charRep χ) →ₗ[ℂ] (G → ℂ)` to `(Submodule.subtype _).comp (Submodule.subtype _)`. Establish `hι : Function.Injective ι` using `fun a b e => Subtype.ext (Subtype.ext e)`. Use `⟨⟨z, hz⟩, mem_fixed.2 fun k hk => hι (funext (hr k hk)), fun e => h0 (congrArg ι e), fun f hf c e => hι ?_⟩` and prove the remaining obligations. Rewrite using `[map_heckeVec (ρ' := rightReg ℂ G ℂ) hc hf ι (fun _ _ => rfl), map_smul]`.

Conclude with `e`.
-/
theorem exists_fixed_of_fun (hK : IsOpen (K : Set G)) (hc : IsCommensurated K) {φ : G → ℂ} (h0 : φ ≠ 0)
    (hφ : ∀ (b : P.Q) g, ∀ k ∈ K, φ (b * g * k) = (P.deltaHalf b : ℂ) * χ (P.p b) * φ g) :
    ∃ y ∈ fixed (P.nInd (charRep χ)) K, y ≠ 0 ∧ ∀ f ∈ Hecke ℂ K, ∀ c : ℂ,
      heckeVec (rightReg ℂ G ℂ) K f φ = c • φ → heckeVec (P.nInd (charRep χ)) K f y = c • y := by
  have hr : ∀ k ∈ K, ∀ g, φ (g * k) = φ g := fun k hk g => by simpa using hφ 1 g k hk
  let z : indSpace P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p)) := ⟨φ, fun b g => by
    have := hφ b g 1 (one_mem _)
    rw [mul_one] at this
    rw [this, twist_apply, MonoidHom.comp_apply, charRep_apply, smul_eq_mul, mul_assoc]⟩
  have hz : z ∈ smoothPart (ind P.Q (LGrp.twist P.deltaHalf ((charRep χ).comp P.p))) :=
    GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem _)) fun g hg =>
      Subtype.ext (funext (hr g hg)))
  let ι : P.IndSpace (charRep χ) →ₗ[ℂ] (G → ℂ) := (Submodule.subtype _).comp (Submodule.subtype _)
  have hι : Function.Injective ι := fun a b e => Subtype.ext (Subtype.ext e)
  refine ⟨⟨z, hz⟩, mem_fixed.2 fun k hk => hι (funext (hr k hk)), fun e => h0 (congrArg ι e), fun f hf c e => hι ?_⟩
  rw [map_heckeVec (ρ' := rightReg ℂ G ℂ) hc hf ι (fun _ _ => rfl), map_smul]
  exact e

end Induced

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GU σ n) V} {α : Fin (n / 2) → ℂˣ}

end Unitary

section Linear

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
  {B : Multiset ℂˣ}

/- English proof (translation)
Introduce `h0` and use `by simp [IsUnifV, h0] at h`.
-/
theorem ne_zero_of_isUnifV {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at h

/- English proof (translation)
Establish `hp` using `Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))`. Rewrite `hp` using `[Multiset.card_map, hB]`. Simplify using `[satEig, Multiset.esymm, hp]`.
-/
theorem satEig_self_ne_zero (hB : B.card = n) : satEig (qV E w) n B n ≠ 0 := by
  have hp := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
  rw [Multiset.card_map, hB] at hp
  simp [satEig, Multiset.esymm, hp]

/- English proof (translation)
Establish `hK : IsCommensurated (KGL w n)` using `Final.GLintComm E w n`. Take `⟨ϖ, hu⟩` from `exists_isUnifV w`. Establish `h0` using `ne_zero_of_isUnifV hu`. Set `A : Submodule ℂ (GL (Fin n) (w.adicCompletion E) → ℂ)` to `{ carrier := {f | f ∈ Hecke ℂ (KGL w n) ∧ ∃ c : ℂ, heckeVec π (KGL w n) f x = c • x ∧ heckeVec ρ (KGL w n) f y = c • y} zero_mem' := ⟨zero_mem _, 0, by simp [heckeVec_zero_left]⟩ add_mem' := by`. Introduce and unpack `f f' ⟨hf, c, e1, e2⟩ ⟨hf', c', e1', e2'⟩`.

Conclude with `⟨add_mem hf hf', c + c', by rw [heckeVec_add_left hK hf hf', e1, e1', add_smul], by rw [heckeVec_add_left hK hf hf', e2, e2', add_smul]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a f ⟨hf, c, e1, e2⟩`. Conclude with `⟨Submodule.smul_mem _ a hf, a * c, by rw [heckeVec_smul_left hK hf, e1, mul_smul], by rw [heckeVec_smul_left hK hf, e2, mul_smul]⟩ }`. Establish `hT : ∀ j ≤ n, Tj ℂ n (Ov E w) ϖ j ∈ A` using `fun j hj => ⟨Tj_mem_hecke hu j, _, hx.2.2.2 ϖ hu j hj, hy.2.2.2 ϖ hu j hj⟩`.

Establish `hc : ∀ f ∈ A, ∀ f' ∈ A, conv (KGL w n) f f' ∈ A`. Introduce and unpack `f ⟨hf, c, e1, e2⟩ f' ⟨hf', c', e1', e2'⟩`. Conclude with `⟨Final.HeckeConvMem _ _ ℂ hK _ hf _ hf', c' * c, by rw [heckeVec_conv hK hf hf' hx.2.1, e1', heckeVec_smul hK hf, e1, mul_smul], by rw [heckeVec_conv hK hf hf' hy.2.1, e2', heckeVec_smul hK hf, e2, mul_smul]⟩`. Establish `hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1)`. Rewrite using `[Tj_eq h0]`.

Simplify using the standard rewrite rules. Establish `shift : ∀ g, dosetInd ℂ (KGL w n) (tor h0 (fun _ => 1) * g) ∈ A → dosetInd ℂ (KGL w n) g ∈ A`. Introduce `g hg`. Establish `hz` using `Final.DosetIndMem _ (KGL w n) ℂ (tor h0 fun _ => 1)`. Establish `hg'` using `Final.DosetIndMem _ (KGL w n) ℂ g`.

Establish `hcv : conv (KGL w n) (dosetInd ℂ (KGL w n) g) (dosetInd ℂ (KGL w n) (tor h0 fun _ => 1)) ∈ A`. Use `mem_of_supp A (Final.HeckeConvMem _ _ ℂ hK _ hg' _ hz) fun x hx => ?_` and prove the remaining obligations. Take `⟨y, z, ⟨a, ha, b, hb, rfl⟩, ⟨c, hc, d, hd, rfl⟩, rfl⟩` from `conv_supp hK hx`. Rewrite using `[dosetInd_congr ⟨a, ha, b * c * d, mul_mem (mul_mem hb hc) hd, ?_⟩]` and apply the resulting hypothesis. Use `tor_const_comm h0 1 (g * b * c)` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Take `⟨-, c, e1, e2⟩` from `hcv`. Establish `hne` using `satEig_self_ne_zero (w := w) hx.2.2.1`. Rewrite `e1` using `[heckeVec_conv hK hg' hz hx.2.1, ← hTn, hx.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg']`. Rewrite `e2` using `[heckeVec_conv hK hg' hz hy.2.1, ← hTn, hy.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg']`.

Conclude with `⟨hg', (satEig (qV E w) n B n)⁻¹ * c, by rw [mul_smul, ← e1, inv_smul_smul₀ hne], by rw [mul_smul, ← e2, inv_smul_smul₀ hne]⟩`. Establish `hall : ∀ (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) → dosetInd ℂ (KGL w n) (tor h0 a) ∈ A`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`.

Introduce `a ha ha0`. Take `⟨d, rfl⟩ : ∃ d : Fin n → ℕ, a = fun i => (d i : ℤ)` from `⟨fun i => (a i).toNat, funext fun i => (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩`. Conclude with `gen_nat h0 hu A hT hc _ _ d (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl`. Consider the case `succ N ih`. Introduce `a ha ha0`.

Use `shift _ ?_` and prove the remaining obligations. Rewrite using `[← tor_add]`. Use `ih _ (fun i j hij => ?_) fun i => ?_` and prove the remaining obligations. Use `ha hij` as an intermediate fact. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers. Use `ha0 i` as an intermediate fact. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Introduce `h hh`.

Use `(mem_of_supp A hh fun g _ => ?_).2` and prove the remaining obligations. Take `⟨a, ha, hg⟩` from `cartan h0 hu g`. Rewrite using `[dosetInd_congr hg]`. Use `hall (∑ i, (a i).natAbs) a ha fun i => ?_` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_eigenvalue_GL {x : V} {y : W} (hx : IsSatVecGL w π x B) (hy : IsSatVecGL w ρ y B) :
    ∀ f ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, heckeVec π (KGL w n) f x = c • x ∧ heckeVec ρ (KGL w n) f y = c • y := by
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  let A : Submodule ℂ (GL (Fin n) (w.adicCompletion E) → ℂ) :=
    { carrier := {f | f ∈ Hecke ℂ (KGL w n) ∧
        ∃ c : ℂ, heckeVec π (KGL w n) f x = c • x ∧ heckeVec ρ (KGL w n) f y = c • y}
      zero_mem' := ⟨zero_mem _, 0, by simp [heckeVec_zero_left]⟩
      add_mem' := by
        rintro f f' ⟨hf, c, e1, e2⟩ ⟨hf', c', e1', e2'⟩
        exact ⟨add_mem hf hf', c + c', by rw [heckeVec_add_left hK hf hf', e1, e1', add_smul],
          by rw [heckeVec_add_left hK hf hf', e2, e2', add_smul]⟩
      smul_mem' := by
        rintro a f ⟨hf, c, e1, e2⟩
        exact ⟨Submodule.smul_mem _ a hf, a * c, by rw [heckeVec_smul_left hK hf, e1, mul_smul],
          by rw [heckeVec_smul_left hK hf, e2, mul_smul]⟩ }
  have hT : ∀ j ≤ n, Tj ℂ n (Ov E w) ϖ j ∈ A := fun j hj =>
    ⟨Tj_mem_hecke hu j, _, hx.2.2.2 ϖ hu j hj, hy.2.2.2 ϖ hu j hj⟩
  have hc : ∀ f ∈ A, ∀ f' ∈ A, conv (KGL w n) f f' ∈ A := by
    rintro f ⟨hf, c, e1, e2⟩ f' ⟨hf', c', e1', e2'⟩
    exact ⟨Final.HeckeConvMem _ _ ℂ hK _ hf _ hf', c' * c,
      by rw [heckeVec_conv hK hf hf' hx.2.1, e1', heckeVec_smul hK hf, e1, mul_smul],
      by rw [heckeVec_conv hK hf hf' hy.2.1, e2', heckeVec_smul hK hf, e2, mul_smul]⟩
  have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
    rw [Tj_eq h0]; simp
  have shift : ∀ g, dosetInd ℂ (KGL w n) (tor h0 (fun _ => 1) * g) ∈ A → dosetInd ℂ (KGL w n) g ∈ A := by
    intro g hg
    have hz := Final.DosetIndMem _ (KGL w n) ℂ (tor h0 fun _ => 1)
    have hg' := Final.DosetIndMem _ (KGL w n) ℂ g
    have hcv : conv (KGL w n) (dosetInd ℂ (KGL w n) g) (dosetInd ℂ (KGL w n) (tor h0 fun _ => 1)) ∈ A := by
      refine mem_of_supp A (Final.HeckeConvMem _ _ ℂ hK _ hg' _ hz) fun x hx => ?_
      obtain ⟨y, z, ⟨a, ha, b, hb, rfl⟩, ⟨c, hc, d, hd, rfl⟩, rfl⟩ := conv_supp hK hx
      rwa [dosetInd_congr ⟨a, ha, b * c * d, mul_mem (mul_mem hb hc) hd, ?_⟩]
      have := tor_const_comm h0 1 (g * b * c)
      calc a * g * b * (c * tor h0 (fun _ => 1) * d) = a * (g * b * c * tor h0 (fun _ => 1)) * d := by group
        _ = _ := by rw [← this]; group
    obtain ⟨-, c, e1, e2⟩ := hcv
    have hne := satEig_self_ne_zero (w := w) hx.2.2.1
    rw [heckeVec_conv hK hg' hz hx.2.1, ← hTn, hx.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg'] at e1
    rw [heckeVec_conv hK hg' hz hy.2.1, ← hTn, hy.2.2.2 ϖ hu n le_rfl, heckeVec_smul hK hg'] at e2
    exact ⟨hg', (satEig (qV E w) n B n)⁻¹ * c, by rw [mul_smul, ← e1, inv_smul_smul₀ hne],
      by rw [mul_smul, ← e2, inv_smul_smul₀ hne]⟩
  have hall : ∀ (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) →
      dosetInd ℂ (KGL w n) (tor h0 a) ∈ A := by
    intro N
    induction N with
    | zero =>
      intro a ha ha0
      obtain ⟨d, rfl⟩ : ∃ d : Fin n → ℕ, a = fun i => (d i : ℤ) :=
        ⟨fun i => (a i).toNat, funext fun i => (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩
      exact gen_nat h0 hu A hT hc _ _ d (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl
    | succ N ih =>
      intro a ha ha0
      refine shift _ ?_
      rw [← tor_add]
      refine ih _ (fun i j hij => ?_) fun i => ?_
      · have := ha hij
        simp only [Pi.add_apply]; omega
      · have := ha0 i
        simp only [Pi.add_apply]; omega
  intro h hh
  refine (mem_of_supp A hh fun g _ => ?_).2
  obtain ⟨a, ha, hg⟩ := cartan h0 hu g
  rw [dosetInd_congr hg]
  refine hall (∑ i, (a i).natAbs) a ha fun i => ?_
  have := Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

variable (w n) in
/- English proof (translation)
Use `letI := GlobalTheory.LocalData.complRel w`. Use `haveI := GlobalTheory.LocalData.isLocalField w`. Rewrite using `[KGL, ← GlobalTheory.SmGL.SphCompletion.KO_completion w n]`. Conclude with `⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩`.
-/
theorem isOpen_isCompact_KGL : IsOpen (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) ∧
    IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  rw [KGL, ← GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField w Formalism.UG.IsSpherical E w (fun i => (α i : ℂ)) φ ↔ ∀ (b : (borelGL (w.adicCompletion E) (Fin n)).Q) g, ∀ k ∈ KGL w n, φ (b * g * k) = ((borelGL (w.adicCompletion E) (Fin n)).deltaHalf b : ℂ) * unrTorus (vZ (w.adicCompletion E)) α ((borelGL …`.
-/
theorem isSphericalGL_iff (α : Fin n → ℂˣ) (φ : GL (Fin n) (w.adicCompletion E) → ℂ) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    Formalism.UG.IsSpherical E w (fun i => (α i : ℂ)) φ ↔
      ∀ (b : (borelGL (w.adicCompletion E) (Fin n)).Q) g, ∀ k ∈ KGL w n, φ (b * g * k) =
        ((borelGL (w.adicCompletion E) (Fin n)).deltaHalf b : ℂ) *
          unrTorus (vZ (w.adicCompletion E)) α ((borelGL (w.adicCompletion E) (Fin n)).p b) * φ g := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have e0 : unrTorus (vZ (w.adicCompletion E)) α = unrTorus
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α := by
    refine MonoidHom.ext fun t => ?_
    rw [unrTorus_apply, unrTorus_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [unrChar_eq, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
    rfl
  have e := GlobalTheory.LGrp.BorelCompletion.deltaHalf_mul_unrTorus E w n α
  rw [e0]
  constructor
  · intro h b g k hk
    rw [h b g k (fun _ _ hij => b.2 hij) hk, ← e b]
  · intro h b g k hb hk
    rw [h ⟨b, fun _ _ hij => hb _ _ hij⟩ g k hk, ← e ⟨b, fun _ _ hij => hb _ _ hij⟩]

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField w HasSatakeGL π B → HasSatGL w π B := by letI := GlobalTheory.LocalData.complRel w haveI := GlobalTheory.LocalData.isLocalField w rintro ⟨⟨α, rfl, -, hq⟩, hs⟩ rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hs refine ⟨hs, fun x hx h0 …`.
-/
theorem hasSatGL_of_hasSatakeGL :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B → HasSatGL w π B := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  rintro ⟨⟨α, rfl, -, hq⟩, hs⟩
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hs
  refine ⟨hs, fun x hx h0 => ⟨h0, hx, by simp, fun ϖ hϖ j hj => ?_⟩⟩
  obtain ⟨φ, hφ0, hφ, ht⟩ := exists_fun_of_isSubquot _ _ (isOpen_isCompact_KGL w n).2 (Final.GLintComm E w n) hq hx h0
  exact ht _ (Tj_mem_hecke hϖ j) _ ((isSatVecGL_of_isSpherical ((isSphericalGL_iff α φ).2 hφ) hφ0).2.2.2 ϖ hϖ j hj)

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField w HasSatakeGL π B := by letI := GlobalTheory.LocalData.complRel w haveI := GlobalTheory.LocalData.isLocalField w obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by obtain ⟨l, rfl⟩ := Quot.exists_rep B obtain rfl : l.length = n …`.
-/
theorem hasSatakeGL_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (hx : IsSatVecGL w π x B) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  refine ⟨⟨α, rfl, hπ, GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
    hx.1 y hy hy0 fun f hf => ?_⟩, ?_⟩
  · obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
    exact ⟨c, e1, ht f hf c e2⟩
  · rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField w HasSatakeGL π B ↔ IsIrrSmooth π ∧ HasSatGL w π B := ⟨fun h => ⟨h.1.choose_spec.2.1, hasSatGL_of_hasSatakeGL h⟩, fun h => by obtain ⟨x, hx⟩ := h.2.exists_vec exact hasSatakeGL_of_isSatVecGL h.1 hx⟩`.
-/
theorem hasSatakeGL_iff :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatakeGL π B ↔ IsIrrSmooth π ∧ HasSatGL w π B :=
  ⟨fun h => ⟨h.1.choose_spec.2.1, hasSatGL_of_hasSatakeGL h⟩, fun h => by
    obtain ⟨x, hx⟩ := h.2.exists_vec
    exact hasSatakeGL_of_isSatVecGL h.1 hx⟩

/- English proof (translation)
Establish `hK : IsCommensurated (KGL w n)` using `Final.GLintComm E w n`. Take `⟨ϖ, hu⟩` from `exists_isUnifV w`. Establish `h0` using `ne_zero_of_isUnifV hu`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hs`. Use `choose c hc using fun j => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (isOpen_isCompact_KGL w n).2 hK (Final.HeckeCommGL E w n ℂ) hπ hf _ (Tj_mem_hecke hu j)`.

Establish `c0 : c 0 = 1`. Establish `e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w n) 1`. Rewrite using `[Tj_eq h0]`. Use `congr 1`. Use `smul_left_injective ℂ hx0 ?_` and prove the remaining obligations.

Simplify using `only [← hc 0 x hx, e, heckeVec_one hK hx, one_smul]`. Establish `cn : c n ≠ 0`. Introduce `e`. Establish `h1` using `hc n x hx`. Establish `hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1)`.

Rewrite using `[Tj_eq h0]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton]`. Conclude with `hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)`. Introduce `γ hγ`.

Conclude with `mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩`. Introduce `g hg`. Take `⟨a, ha, b, hb, rfl⟩` from `mem_doset.1 hg`. Use `⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩` and prove the remaining obligations. Rewrite using `[← tor_const_comm, mul_assoc, inv_mul_cancel_left]`.

Conclude with `mul_mem ha hb`. Take `⟨B, hB, hBc⟩` from `GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn`. Use `⟨B, hs, fun y hy hy0 => ⟨hy0, hy, hB, fun ϖ' hu' j hj => ?_⟩⟩` and prove the remaining obligations. Establish `hv : Valued.v (ϖ' / ϖ) = 1`. Rewrite using `[map_div₀, hu, hu', div_self WithZero.coe_ne_zero]`.

Establish `e` using `Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)`. Rewrite `e` using `[div_mul_cancel₀ _ h0]`. Rewrite using `[e, hc j y hy, hBc j hj]`.
-/
theorem exists_hasSatGL (hπ : IsIrrSmooth π) (hf : FiniteDimensional ℂ (fixed π (KGL w n)))
    (hs : LGrp.IsSpherical π (KGL w n)) : ∃ B, HasSatGL w π B := by
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  choose c hc using fun j => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (isOpen_isCompact_KGL w n).2 hK (Final.HeckeCommGL E w n ℂ) hπ hf _
    (Tj_mem_hecke hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w n) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0 x hx, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n x hx
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w n) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hs, fun y hy hy0 => ⟨hy0, hy, hB, fun ϖ' hu' j hj => ?_⟩⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j y hy, hBc j hj]

end Linear

section Characters

/- English proof (translation)
Establish `hs : Function.Surjective χ` using `fun c => ⟨algebraMap ℂ B c, by simp⟩`. Use `haveI := RingHom.ker_isMaximal_of_surjective χ.toRingHom hs`. Take `⟨Q, hQ, e⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (RingHom.ker χ.toRingHom) (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]`. Conclude with `bot_le)`.

Establish `key : ∀ b : B, Ideal.Quotient.mk Q b = algebraMap ℂ (A ⧸ Q) (χ b)` using `fun b => by`. Establish `: b - algebraMap ℂ B (χ b) ∈ Q.comap (algebraMap B A)`. Rewrite using `[e, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Conclude with `Ideal.Quotient.eq.2 this`.

Use `letI := Ideal.Quotient.field Q`. Use `haveI : Algebra.IsIntegral ℂ (A ⧸ Q) := ⟨fun z => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `(Algebra.IsIntegral.isIntegral (R := B) a).map_of_comp_eq χ.toRingHom (Ideal.Quotient.mk Q) (RingHom.ext fun b => (key b).symm)⟩`. Set `i` to `AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ Q)) IsAlgClosed.algebraMap_bijective_of_isIntegral`.

Use `⟨i.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q), fun b => ?_⟩` and prove the remaining obligations. Conclude with `i.symm_apply_eq.2 (key b)`.
-/
theorem exists_algHom_extend {A : Type} [CommRing A] [Algebra ℂ A] (B : Subalgebra ℂ A) [Module.Finite B A]
    (χ : B →ₐ[ℂ] ℂ) : ∃ ψ : A →ₐ[ℂ] ℂ, ∀ b : B, ψ b = χ b := by
  have hs : Function.Surjective χ := fun c => ⟨algebraMap ℂ B c, by simp⟩
  haveI := RingHom.ker_isMaximal_of_surjective χ.toRingHom hs
  obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (RingHom.ker χ.toRingHom) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
  have key : ∀ b : B, Ideal.Quotient.mk Q b = algebraMap ℂ (A ⧸ Q) (χ b) := fun b => by
    have : b - algebraMap ℂ B (χ b) ∈ Q.comap (algebraMap B A) := by
      rw [e, RingHom.mem_ker]; simp
    exact Ideal.Quotient.eq.2 this
  letI := Ideal.Quotient.field Q
  haveI : Algebra.IsIntegral ℂ (A ⧸ Q) := ⟨fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (Algebra.IsIntegral.isIntegral (R := B) a).map_of_comp_eq χ.toRingHom (Ideal.Quotient.mk Q)
      (RingHom.ext fun b => (key b).symm)⟩
  let i := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ Q)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨i.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q), fun b => ?_⟩
  exact i.symm_apply_eq.2 (key b)

variable {m : ℕ}

def ev (α : Fin m → ℂˣ) : AddMonoidAlgebra ℂ (Fin m → ℤ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)
    { toFun := fun a => ∏ i, (α i : ℂ) ^ a.toAdd i
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add₀, Finset.prod_mul_distrib] }

/- English proof (translation)
Rewrite using `[ev, AddMonoidAlgebra.lift_apply]`. Both sides reduce to the same expression.
-/
theorem ev_apply (α : Fin m → ℂˣ) (s : AddMonoidAlgebra ℂ (Fin m → ℤ)) :
    ev α s = s.coeff.sum fun a c => c * ∏ i, (α i : ℂ) ^ a i := by
  rw [ev, AddMonoidAlgebra.lift_apply]
  rfl

/- English proof (translation)
Take `⟨F, rfl⟩` from `(AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)).surjective ψ`. Use `⟨fun i => F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)), congrArg _ (MonoidHom.ext fun a => ?_)⟩` and prove the remaining obligations. Establish `: a = ∏ i, Multiplicative.ofAdd (Pi.single i 1 : Fin m → ℤ) ^ a.toAdd i`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[toAdd_prod]`.

Use `conv_lhs => rw [← Finset.univ_sum_single a.toAdd]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[toAdd_zpow, toAdd_ofAdd, ← Pi.single_smul, smul_eq_mul, mul_one]`. Use `show F a = ∏ i, ((F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)) : ℂˣ) : ℂ) ^ a.toAdd i`. Use `conv_lhs => rw [this, ← F.coe_toHomUnits, map_prod, Units.coe_prod]`.

Simplify using `only [map_zpow, Units.val_zpow_eq_zpow_val]`.
-/
theorem exists_eq_ev (ψ : AddMonoidAlgebra ℂ (Fin m → ℤ) →ₐ[ℂ] ℂ) : ∃ α, ψ = ev α := by
  obtain ⟨F, rfl⟩ := (AddMonoidAlgebra.lift ℂ ℂ (Fin m → ℤ)).surjective ψ
  refine ⟨fun i => F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)), congrArg _ (MonoidHom.ext fun a => ?_)⟩
  have : a = ∏ i, Multiplicative.ofAdd (Pi.single i 1 : Fin m → ℤ) ^ a.toAdd i := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    conv_lhs => rw [← Finset.univ_sum_single a.toAdd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toAdd_zpow, toAdd_ofAdd, ← Pi.single_smul, smul_eq_mul, mul_one]
  show F a = ∏ i, ((F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)) : ℂˣ) : ℂ) ^ a.toAdd i
  conv_lhs => rw [this, ← F.coe_toHomUnits, map_prod, Units.coe_prod]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val]

end Characters

section Existence

open GlobalTheory.InertThetaCompare GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}

/- English proof (translation)
Take `⟨x, h0, hx, e⟩` from `(hasSatU_psFunU hU α).exists_vec`. Establish `hK` using `P.isCommensurated_integral_unitary_of_unramified hU n`. Use `⟨fun f hf f' hf' => smul_left_injective ℂ h0 ?_, fun c f hf => smul_left_injective ℂ h0 ?_, smul_left_injective ℂ h0 ?_⟩` and prove the remaining obligations. Simplify using `only [← e _ (add_mem hf hf'), heckeVec_add_left hK hf hf', e _ hf, e _ hf', add_smul]`. Simplify using `only [← e _ (Submodule.smul_mem _ c hf), heckeVec_smul_left hK hf, e _ hf, mul_smul]`.

Simplify using `only [← e _ (Final.DosetIndMem _ _ ℂ 1), heckeVec_one hK hx, one_smul]`.
-/
theorem satU_laws (hU : IsUnramInv ϖ σ q) (α : Fin (n / 2) → ℂˣ) :
    (∀ f ∈ Hecke ℂ (KU σ n), ∀ f' ∈ Hecke ℂ (KU σ n), SatU ϖ q (f + f') (fun i => (α i : ℂ)) =
      SatU ϖ q f (fun i => (α i : ℂ)) + SatU ϖ q f' (fun i => (α i : ℂ))) ∧
    (∀ (c : ℂ), ∀ f ∈ Hecke ℂ (KU σ n), SatU ϖ q (c • f) (fun i => (α i : ℂ)) = c * SatU ϖ q f (fun i => (α i : ℂ))) ∧
    SatU ϖ q (dosetInd ℂ (KU σ n) 1) (fun i => (α i : ℂ)) = 1 := by
  obtain ⟨x, h0, hx, e⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  refine ⟨fun f hf f' hf' => smul_left_injective ℂ h0 ?_, fun c f hf => smul_left_injective ℂ h0 ?_,
    smul_left_injective ℂ h0 ?_⟩
  · simp only [← e _ (add_mem hf hf'), heckeVec_add_left hK hf hf', e _ hf, e _ hf', add_smul]
  · simp only [← e _ (Submodule.smul_mem _ c hf), heckeVec_smul_left hK hf, e _ hf, mul_smul]
  · simp only [← e _ (Final.DosetIndMem _ _ ℂ 1), heckeVec_one hK hx, one_smul]

omit [CompleteSpace L] in
/- English proof (translation)
Unfold `labInd dosetInd`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[GlobalTheory.WeylGL.mem_doset, ← ht]`. Simplify using `only [Set.mem_setOf_eq, ← Units.val_mul, Units.val_inj, ← Subgroup.coe_mul, Subtype.val_inj]`.
-/
theorem labInd_eq {d : List ℤ} {t : GU σ n}
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i : Fin n => ϖ ^ d.getD i.1 0) :
    labInd σ n ϖ d = dosetInd ℂ (KU σ n) t := by
  unfold labInd dosetInd
  congr 1
  ext g
  rw [GlobalTheory.WeylGL.mem_doset, ← ht]
  simp only [Set.mem_setOf_eq, ← Units.val_mul, Units.val_inj, ← Subgroup.coe_mul, Subtype.val_inj]

/- English proof (translation)
Take `⟨d, hd, a, ha, b, hb, e⟩` from `GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary L ϖ σ q n hU g`. Take `⟨t, ht⟩` from `exists_diag hU hd`. Use `⟨d, hd, (labInd_eq ht).trans (GlobalTheory.WeylGL.dosetInd_congr ?_).symm⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))`.
-/
theorem exists_labInd_eq (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ d, Good n d ∧ labInd σ n ϖ d = dosetInd ℂ (KU σ n) g := by
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := exists_diag hU hd
  refine ⟨d, hd, (labInd_eq ht).trans (GlobalTheory.WeylGL.dosetInd_congr ?_).symm⟩
  exact GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))

/- English proof (translation)
Establish `hm : ∀ d, Good n d → labInd σ n ϖ d ∈ Hecke ℂ (KU σ n)` using `fun d hd => by`. Take `⟨t, ht⟩` from `exists_diag hU hd`. Rewrite using `[labInd_eq ht]`. Conclude with `Final.DosetIndMem _ _ ℂ t`. Establish `h1 : f ∈ Submodule.span ℂ (labInd σ n ϖ '' {d | Good n d})` using `GlobalTheory.WeylGL.mem_of_supp _ hf fun g _ => Submodule.subset_span (exists_labInd_eq hU g)`.

Take `⟨s, hs, c, rfl⟩` from `(Submodule.mem_span_image_iff_exists_fun ℂ).1 h1`. Set `c' : List ℤ → ℂ` to `fun d => if h : d ∈ s then c ⟨d, h⟩ else 0`. Establish `e : ∑ i : s, c i • labInd σ n ϖ i = ∑ d ∈ s, c' d • labInd σ n ϖ d`. Rewrite using `[← Finset.sum_coe_sort s]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp [c']`.

Rewrite `h`, the goal using `[e]`. Establish `h2 : ∀ (α : Fin (n / 2) → ℂˣ) (s' : Finset (List ℤ)), (∀ d ∈ s', Good n d) → SatU ϖ q (∑ d ∈ s', c' d • labInd σ n ϖ d) (fun i => (α i : ℂ)) = ∑ d ∈ s', c' d * SatU ϖ q (labInd σ n ϖ d) (fun i => (α i : ℂ))` using `fun α s' => by`. Take `⟨ha, hb, -⟩` from `satU_laws (n := n) hU α`. Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty => intro _`.

Simplify using `using hb 0 0 (zero_mem _)`. Consider the case `insert d s' hd ih`. Introduce `hg`. Establish `g1` using `hm d (hg d (Finset.mem_insert_self _ _))`. Establish `g2` using `fun d hd => hg d (Finset.mem_insert_of_mem hd)`.

Rewrite using `[Finset.sum_insert hd, Finset.sum_insert hd, ha _ (Submodule.smul_mem _ _ g1) _ (Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (hm d (g2 d hd))), hb _ _ g1, ih g2]`. Establish `h3` using `GlobalTheory.InertThetaCompare.satU_indep hU s c' (fun d hd => hs hd) fun α hα => (h2 (fun i => Units.mk0 _ (hα i)) s fun d hd => hs hd).symm.trans (h _)`. Conclude with `Finset.sum_eq_zero fun d hd => by rw [h3 d hd, zero_smul]`.
-/
theorem eq_zero_of_satU (hU : IsUnramInv ϖ σ q) {f : GU σ n → ℂ} (hf : f ∈ Hecke ℂ (KU σ n))
    (h : ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q f (fun i => (α i : ℂ)) = 0) : f = 0 := by
  have hm : ∀ d, Good n d → labInd σ n ϖ d ∈ Hecke ℂ (KU σ n) := fun d hd => by
    obtain ⟨t, ht⟩ := exists_diag hU hd
    rw [labInd_eq ht]
    exact Final.DosetIndMem _ _ ℂ t
  have h1 : f ∈ Submodule.span ℂ (labInd σ n ϖ '' {d | Good n d}) :=
    GlobalTheory.WeylGL.mem_of_supp _ hf fun g _ => Submodule.subset_span (exists_labInd_eq hU g)
  obtain ⟨s, hs, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun ℂ).1 h1
  classical
  let c' : List ℤ → ℂ := fun d => if h : d ∈ s then c ⟨d, h⟩ else 0
  have e : ∑ i : s, c i • labInd σ n ϖ i = ∑ d ∈ s, c' d • labInd σ n ϖ d := by
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => by simp [c']
  rw [e] at h ⊢
  have h2 : ∀ (α : Fin (n / 2) → ℂˣ) (s' : Finset (List ℤ)), (∀ d ∈ s', Good n d) →
      SatU ϖ q (∑ d ∈ s', c' d • labInd σ n ϖ d) (fun i => (α i : ℂ)) =
        ∑ d ∈ s', c' d * SatU ϖ q (labInd σ n ϖ d) (fun i => (α i : ℂ)) := fun α s' => by
    obtain ⟨ha, hb, -⟩ := satU_laws (n := n) hU α
    induction s' using Finset.induction_on with
    | empty => intro _; simpa using hb 0 0 (zero_mem _)
    | insert d s' hd ih =>
      intro hg
      have g1 := hm d (hg d (Finset.mem_insert_self _ _))
      have g2 := fun d hd => hg d (Finset.mem_insert_of_mem hd)
      rw [Finset.sum_insert hd, Finset.sum_insert hd, ha _ (Submodule.smul_mem _ _ g1) _
        (Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (hm d (g2 d hd))), hb _ _ g1, ih g2]
  have h3 := GlobalTheory.InertThetaCompare.satU_indep hU s c' (fun d hd => hs hd) fun α hα =>
    (h2 (fun i => Units.mk0 _ (hα i)) s fun d hd => hs hd).symm.trans (h _)
  exact Finset.sum_eq_zero fun d hd => by rw [h3 d hd, zero_smul]

/- English proof (translation)
Establish `hK` using `P.isCommensurated_integral_unitary_of_unramified hU n`. Establish `law` using `satU_laws (n := n) hU`. Establish `hmul` using `fun (α : Fin (n / 2) → ℂˣ) => Final.SatMul L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ)) fun i => (α i).ne_zero`. Set `R : AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ) → Hecke ℂ (KU σ n) → Prop` to `fun b f => ∀ α : Fin (n / 2) → ℂˣ, ev α b = SatU ϖ q f.1 fun i => (α i : ℂ)`. Establish `Radd : ∀ {a b f g}, R a f → R b g → R (a + b) (f + g)` using `fun {a b f g} e e' α => by`.

Rewrite using `[map_add, e, e']`. Conclude with `((law α).1 _ f.2 _ g.2).symm`. Establish `Rmul : ∀ {a b f g}, R a f → R b g → R (a * b) ⟨_, Final.HeckeConvMem _ _ ℂ hK _ f.2 _ g.2⟩` using `fun {a b f g} e e' α => by rw [map_mul, e, e']; exact (hmul α _ f.2 _ g.2).symm`. Establish `Ralg : ∀ c : ℂ, R (algebraMap ℂ _ c) (c • ⟨_, Final.DosetIndMem _ _ ℂ 1⟩)` using `fun c α => by`. Rewrite using `[AlgHom.commutes]`.

Conclude with `(((law α).2.1 c _ (Final.DosetIndMem _ _ ℂ 1)).trans (by rw [(law α).2.2, mul_one]; rfl)).symm`. Establish `Runiq : ∀ {a f g}, R a f → R a g → f = g` using `fun {a f g} e e' => by`. Use `sub_eq_zero.1 (Subtype.ext (eq_zero_of_satU hU (f - g).2 fun α => ?_))` and prove the remaining obligations. Use `(law α).1 _ (f - g).2 _ g.2` as an intermediate fact. Rewrite `this` using `[← Submodule.coe_add, sub_add_cancel, ← e, ← e']`.

Conclude with `right_eq_add.1 this`. Set `B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ))` to `{ carrier := {b | ∃ f, R b f} mul_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Rmul e e'⟩ add_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Radd e e'⟩ algebraMap_mem' := fun c => ⟨_, Ralg c⟩ }`. Use `choose φ hφ using fun b : B => b.2`. Set `χ : B →ₐ[ℂ] ℂ` to `{ toFun := fun b => l (φ b) map_one' := by rw [Runiq (hφ 1) (Ralg 1), one_smul, h1] map_mul' := fun a b => by rw [Runiq (hφ (a * b)) (Rmul (hφ a) (hφ b)), hm] map_zero' := by rw [Runiq (hφ 0) (by simpa using Ralg 0 : R 0 0), map_zero] map_add' := fun a b => by rw [Runiq (hφ (a + …`. Establish `hR : ∀ (f : Hecke ℂ (KU σ n)) (s : (Fin (n / 2) → ℤ) →₀ ℂ), (∀ α : Fin (n / 2) → ℂ, SatU ϖ q f.1 α = s.sum fun a c => c * ∏ i, α i ^ a i) → R (.ofCoeff s) f` using `fun f s e α => by rw [ev_apply, e]`.

Use `haveI : Module.Finite B (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ)) := by`. Use `GlobalTheory.T.laurent_finite_of_triangular_signed_indicators _ B fun ε hε => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `P.fSatake_tMat_exists (n := n) hU (Nat.mul_div_le n 2) ε`. Take `⟨s, e, hs, ht'⟩` from `GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ (Final.DosetIndMem _ (KU σ n) ℂ t)`. Use `⟨.ofCoeff s, ⟨_, hR ⟨_, Final.DosetIndMem _ (KU σ n) ℂ t⟩ s e⟩, ht' t ε ht rfl, fun κ hκ => ?_⟩` and prove the remaining obligations.

Take `⟨g, hg, u, hu, k, hk, eg⟩` from `hs κ hκ`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g = a * t * b := by`. Assume the negation of the conclusion as `h0`. Conclude with `hg (GlobalTheory.WeylGL.dosetInd_of_not h0)`. Conclude with `GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset L ϖ σ q n hU ε κ u k a b hε hu hk ha hb (by rw [← eg, ← ht]; rfl)`.

Take `⟨ψ, hψ⟩` from `exists_algHom_extend B χ`. Take `⟨α, rfl⟩` from `exists_eq_ev ψ`. Use `⟨α, fun f => ?_⟩` and prove the remaining obligations. Take `⟨s, e, -⟩` from `GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ f.2`. Establish `r` using `hR f s e`.

Rewrite using `[← r α, hψ ⟨_, f, r⟩]`. Conclude with `congrArg l (Runiq r (hφ ⟨_, f, r⟩))`.
-/
theorem exists_satU_eq (hU : IsUnramInv ϖ σ q) (l : Hecke ℂ (KU σ n) →ₗ[ℂ] ℂ)
    (h1 : l ⟨_, Final.DosetIndMem _ _ ℂ 1⟩ = 1)
    (hm : ∀ f f' : Hecke ℂ (KU σ n),
      l ⟨_, Final.HeckeConvMem _ _ ℂ (P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f') :
    ∃ α : Fin (n / 2) → ℂˣ, ∀ f : Hecke ℂ (KU σ n), l f = SatU ϖ q f.1 fun i => (α i : ℂ) := by
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := satU_laws (n := n) hU
  have hmul := fun (α : Fin (n / 2) → ℂˣ) => Final.SatMul L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  let R : AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ) → Hecke ℂ (KU σ n) → Prop := fun b f =>
    ∀ α : Fin (n / 2) → ℂˣ, ev α b = SatU ϖ q f.1 fun i => (α i : ℂ)
  have Radd : ∀ {a b f g}, R a f → R b g → R (a + b) (f + g) := fun {a b f g} e e' α => by
    rw [map_add, e, e']; exact ((law α).1 _ f.2 _ g.2).symm
  have Rmul : ∀ {a b f g}, R a f → R b g → R (a * b) ⟨_, Final.HeckeConvMem _ _ ℂ hK _ f.2 _ g.2⟩ :=
    fun {a b f g} e e' α => by rw [map_mul, e, e']; exact (hmul α _ f.2 _ g.2).symm
  have Ralg : ∀ c : ℂ, R (algebraMap ℂ _ c) (c • ⟨_, Final.DosetIndMem _ _ ℂ 1⟩) := fun c α => by
    rw [AlgHom.commutes]
    exact (((law α).2.1 c _ (Final.DosetIndMem _ _ ℂ 1)).trans (by rw [(law α).2.2, mul_one]; rfl)).symm
  have Runiq : ∀ {a f g}, R a f → R a g → f = g := fun {a f g} e e' => by
    refine sub_eq_zero.1 (Subtype.ext (eq_zero_of_satU hU (f - g).2 fun α => ?_))
    have := (law α).1 _ (f - g).2 _ g.2
    rw [← Submodule.coe_add, sub_add_cancel, ← e, ← e'] at this
    exact right_eq_add.1 this
  let B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ)) :=
    { carrier := {b | ∃ f, R b f}
      mul_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Rmul e e'⟩
      add_mem' := fun ⟨_, e⟩ ⟨_, e'⟩ => ⟨_, Radd e e'⟩
      algebraMap_mem' := fun c => ⟨_, Ralg c⟩ }
  choose φ hφ using fun b : B => b.2
  let χ : B →ₐ[ℂ] ℂ :=
    { toFun := fun b => l (φ b)
      map_one' := by rw [Runiq (hφ 1) (Ralg 1), one_smul, h1]
      map_mul' := fun a b => by rw [Runiq (hφ (a * b)) (Rmul (hφ a) (hφ b)), hm]
      map_zero' := by rw [Runiq (hφ 0) (by simpa using Ralg 0 : R 0 0), map_zero]
      map_add' := fun a b => by rw [Runiq (hφ (a + b)) (Radd (hφ a) (hφ b)), map_add]
      commutes' := fun c => by rw [Runiq (hφ (algebraMap ℂ B c)) (Ralg c), map_smul, h1]; simp }
  have hR : ∀ (f : Hecke ℂ (KU σ n)) (s : (Fin (n / 2) → ℤ) →₀ ℂ),
      (∀ α : Fin (n / 2) → ℂ, SatU ϖ q f.1 α = s.sum fun a c => c * ∏ i, α i ^ a i) → R (.ofCoeff s) f :=
    fun f s e α => by rw [ev_apply, e]
  haveI : Module.Finite B (AddMonoidAlgebra ℂ (Fin (n / 2) → ℤ)) := by
    refine GlobalTheory.T.laurent_finite_of_triangular_signed_indicators _ B fun ε hε => ?_
    obtain ⟨t, ht⟩ := P.fSatake_tMat_exists (n := n) hU (Nat.mul_div_le n 2) ε
    obtain ⟨s, e, hs, ht'⟩ := GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ (Final.DosetIndMem _ (KU σ n) ℂ t)
    refine ⟨.ofCoeff s, ⟨_, hR ⟨_, Final.DosetIndMem _ (KU σ n) ℂ t⟩ s e⟩, ht' t ε ht rfl, fun κ hκ => ?_⟩
    obtain ⟨g, hg, u, hu, k, hk, eg⟩ := hs κ hκ
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g = a * t * b := by
      by_contra h0
      exact hg (GlobalTheory.WeylGL.dosetInd_of_not h0)
    exact GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset L ϖ σ q n hU ε κ u k a b hε hu hk ha hb (by rw [← eg, ← ht]; rfl)
  obtain ⟨ψ, hψ⟩ := exists_algHom_extend B χ
  obtain ⟨α, rfl⟩ := exists_eq_ev ψ
  refine ⟨α, fun f => ?_⟩
  obtain ⟨s, e, -⟩ := GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial L ϖ σ q n hU _ f.2
  have r := hR f s e
  rw [← r α, hψ ⟨_, f, r⟩]
  exact congrArg l (Runiq r (hφ ⟨_, f, r⟩))

variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GU σ n) V}

/- English proof (translation)
Establish `hK` using `P.isCommensurated_integral_unitary_of_unramified hU n`. Take `⟨x, hx, h0⟩` from `(Submodule.ne_bot_iff _).1 hs`. Use `choose c hc using fun f : Hecke ℂ (KU σ n) => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints L ϖ σ q n hU).2 hK (GlobalTheory.UnitarySwap.heckeCommU L ϖ σ q n ℂ hU) hπ hf _ f.2`. Set `l : Hecke ℂ (KU σ n) →ₗ[ℂ] ℂ` to `{ toFun := c map_add' := fun f g => smul_left_injective ℂ h0 (by`. Simplify using `only [add_smul, ← hc _ x hx]`.

Conclude with `heckeVec_add_left hK f.2 g.2 x)`. Use the proof step `map_smul' := fun a f => smul_left_injective ℂ h0 (by`. Simplify using `only [RingHom.id_apply, smul_eq_mul, mul_smul, ← hc _ x hx]`. Conclude with `heckeVec_smul_left hK f.2 a x) }`. Take `⟨α, hα⟩` from `exists_satU_eq hU l (smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_one hK hx).trans (one_smul _ _).symm))) fun f g => smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_conv hK f.2 g.2 hx).trans (by`.

Rewrite using `[hc g x hx, heckeVec_smul hK f.2, hc f x hx, smul_smul, mul_comm]`. Use the proof step `rfl)))`. Conclude with `⟨α, hs, fun y hy hy0 => ⟨hy0, hy, fun f hf => (hc ⟨f, hf⟩ y hy).trans (by rw [← hα ⟨f, hf⟩]; rfl)⟩⟩`.
-/
theorem exists_hasSatU (hU : IsUnramInv ϖ σ q) (hπ : IsIrrSmooth π) (hf : FiniteDimensional ℂ (fixed π (KU σ n)))
    (hs : LGrp.IsSpherical π (KU σ n)) : ∃ α, HasSatU ϖ q π α := by
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hs
  choose c hc using fun f : Hecke ℂ (KU σ n) => GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors _ _ π _ (GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints L ϖ σ q n hU).2 hK
    (GlobalTheory.UnitarySwap.heckeCommU L ϖ σ q n ℂ hU) hπ hf _ f.2
  let l : Hecke ℂ (KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun f g => smul_left_injective ℂ h0 (by
        simp only [add_smul, ← hc _ x hx]; exact heckeVec_add_left hK f.2 g.2 x)
      map_smul' := fun a f => smul_left_injective ℂ h0 (by
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul, ← hc _ x hx]; exact heckeVec_smul_left hK f.2 a x) }
  obtain ⟨α, hα⟩ := exists_satU_eq hU l
    (smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_one hK hx).trans (one_smul _ _).symm)))
    fun f g => smul_left_injective ℂ h0 ((hc _ x hx).symm.trans ((heckeVec_conv hK f.2 g.2 hx).trans (by
      rw [hc g x hx, heckeVec_smul hK f.2, hc f x hx, smul_smul, mul_comm]; rfl)))
  exact ⟨α, hs, fun y hy hy0 => ⟨hy0, hy, fun f hf => (hc ⟨f, hf⟩ y hy).trans (by rw [← hα ⟨f, hf⟩]; rfl)⟩⟩

end Existence

end GlobalTheory.LFun.SatCompare

end
