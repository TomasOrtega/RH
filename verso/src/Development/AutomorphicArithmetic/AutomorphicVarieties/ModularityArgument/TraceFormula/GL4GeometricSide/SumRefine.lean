import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAverage

noncomputable section

open NumberField Matrix Finset
open GlobalTheory.CuspRep
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Avg

variable {K M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]

private def av (ρ : K →* Module.End ℂ M) (S : Subgroup K) (m : M) : M :=
  ((S.index : ℂ)⁻¹) • ∑ᶠ q : K ⧸ S, ρ q.out m

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsAverage.exists_avg ρ hs`.
-/
private theorem exists_avg [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (ρ : K →* Module.End ℂ M)
    (hs : ∀ m, IsOpen {k | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ m k, ρ k (P m) = P m) ∧ (∀ m, (∀ k, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ k m, T (ρ k m) = ρ k (T m)) → ∀ m, T (P m) = P (T m) :=
  _root_.UpperTheory.Reformulated.B.ExistsAverage.exists_avg ρ hs

end Avg

section Core

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
The claim follows from `Subtype.ext (by show finRep E n g (finRep E n k x.1) = finRep E n (g * k) x.1 rw [map_mul, Module.End.mul_apply])`.
-/
private theorem fin_op (π : CuspSub E n) (g k : GL (Fin n) (Af E)) (x : π.V) :
    π.finPart g (π.op (.fin k) x) = π.finPart (g * k) x :=
  Subtype.ext (by
    show finRep E n g (finRep E n k x.1) = finRep E n (g * k) x.1
    rw [map_mul, Module.End.mul_apply])

/- English proof (translation)
The claim follows from `Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) x.1)`.
-/
private theorem lie_fin (π : CuspSub E n) (X : Lie E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.lie X) (π.finPart g x) = π.finPart g (π.op (.lie X) x) :=
  Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) x.1)

/- English proof (translation)
The claim follows from `Subtype.ext (by have h := congrArg (rt E n) (infGL_comm (Unitary.toUnits c) g) rw [map_mul, map_mul] at h exact LinearMap.congr_fun h x.1)`.
-/
private theorem cpt_fin (π : CuspSub E n) (c : Kinf E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.cpt c) (π.finPart g x) = π.finPart g (π.op (.cpt c) x) :=
  Subtype.ext (by
    have h := congrArg (rt E n) (infGL_comm (Unitary.toUnits c) g)
    rw [map_mul, map_mul] at h
    exact LinearMap.congr_fun h x.1)

/- English proof (translation)
Simplify using `only [PositivityTheory.S2.Clozel.EopV, LinearMap.smul_apply, LinearMap.sub_apply, lie_fin, map_smul, map_sub]`.
-/
private theorem eop_fin (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) (g : GL (Fin n) (Af E)) (x : π.V) :
    PositivityTheory.S2.Clozel.EopV π τ i j (π.finPart g x) = π.finPart g (PositivityTheory.S2.Clozel.EopV π τ i j x) := by
  simp only [PositivityTheory.S2.Clozel.EopV, LinearMap.smul_apply, LinearMap.sub_apply, lie_fin, map_smul, map_sub]

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc`. Set `ρ : K →* Module.End ℂ π.V` to `MonoidHom.comp π.finPart K.subtype`. Establish `hρ : ∀ (k : K) m, ρ k m = π.finPart k.1 m` using `fun _ _ => rfl`. Establish `hs : ∀ m, IsOpen {k : K | ρ k m = m}` using `fun m => by`. Establish `h1` using `(π.cusp m.1 m.2).1.level`.

Use `h1.preimage continuous_subtype_val using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Conclude with `Subtype.ext_iff`. Take `⟨P, hPinv, hPfix, hPT⟩` from `exists_avg ρ hs`. Establish `hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → ∀ m, T (P m) = P (T m)` using `fun T hT => hPT T fun k m => hT k.1 m`.

Set `W0 : Submodule ℂ π.V` to `⨅ g, LinearMap.ker (P ∘ₗ π.finPart g)`. Establish `mem : ∀ x, x ∈ W0 ↔ ∀ g, P (π.finPart g x) = 0` using `fun x => by`. Simplify using `[W0, Submodule.mem_iInf]`. Establish `stable : IsStable (W0.map π.V.subtype)`. Introduce and unpack `o _ ⟨x, hx, rfl⟩`.

Use `⟨π.op o x, ?_, rfl⟩` and prove the remaining obligations. Establish `hx'` using `(mem x).1 hx`. Use `(mem _).2 fun g => ?_` and prove the remaining obligations. Consider the cases of `o with`. Consider the case `fin k => rw [fin_op]`.

Conclude with `hx' _`. Consider the case `cpt c => rw [← cpt_fin, ← hcomm _ (fun g x => cpt_fin π c g x), hx', map_zero]`. Consider the case `lie X => rw [← lie_fin, ← hcomm _ (fun g x => lie_fin π X g x), hx', map_zero]`. Break down `π.irred _ (Submodule.map_subtype_le _ _) stable with h | h` into its components or cases. Establish `hn : ψ ∉ W0` using `fun hm => by`.

Establish `h1 : ψ.1 ∈ W0.map π.V.subtype` using `⟨ψ, hm, rfl⟩`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hψ (Subtype.ext h1)`. Rewrite `hn` using `[mem]`. Use `push_neg at hn`.

Take `⟨g, hg⟩` from `hn`. Use `⟨P (π.finPart g ψ), hg, fun k hk => hPinv _ ⟨k, hk⟩, fun T c hT hc => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomm T hT, hT, hc, map_smul, map_smul]`. It suffices to derive a contradiction. Establish `h1 : v0.1 ∈ W0.map π.V.subtype`.

Rewrite using `[h]`. Conclude with `v0.2`. Take `⟨y, hy, e⟩` from `h1`. Establish `hy0 : y = v0` using `Subtype.ext e`. Substitute `hy0` using the available equality.

Establish `h2` using `(mem y).1 hy 1`. Rewrite `h2` using `[map_one, Module.End.one_apply, hPfix y fun k => hfix k.1 k.2]`. Conclude with `hv0 h2`.
-/
private theorem core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    (v0 ψ : π.V) (hv0 : v0 ≠ 0) (hfix : ∀ k ∈ K, π.finPart k v0 = v0) (hψ : ψ ≠ 0) :
    ∃ v : π.V, v ≠ 0 ∧ (∀ k ∈ K, π.finPart k v = v) ∧ ∀ (T : Module.End ℂ π.V) (c : ℂ),
      (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → T ψ = c • ψ → T v = c • v := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let ρ : K →* Module.End ℂ π.V := MonoidHom.comp π.finPart K.subtype
  have hρ : ∀ (k : K) m, ρ k m = π.finPart k.1 m := fun _ _ => rfl
  have hs : ∀ m, IsOpen {k : K | ρ k m = m} := fun m => by
    have h1 := (π.cusp m.1 m.2).1.level
    convert h1.preimage continuous_subtype_val using 1
    ext k
    exact Subtype.ext_iff
  obtain ⟨P, hPinv, hPfix, hPT⟩ := exists_avg ρ hs
  have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) →
      ∀ m, T (P m) = P (T m) := fun T hT => hPT T fun k m => hT k.1 m
  let W0 : Submodule ℂ π.V := ⨅ g, LinearMap.ker (P ∘ₗ π.finPart g)
  have mem : ∀ x, x ∈ W0 ↔ ∀ g, P (π.finPart g x) = 0 := fun x => by
    simp [W0, Submodule.mem_iInf]
  have stable : IsStable (W0.map π.V.subtype) := by
    rintro o _ ⟨x, hx, rfl⟩
    refine ⟨π.op o x, ?_, rfl⟩
    have hx' := (mem x).1 hx
    refine (mem _).2 fun g => ?_
    cases o with
    | fin k => rw [fin_op]; exact hx' _
    | cpt c => rw [← cpt_fin, ← hcomm _ (fun g x => cpt_fin π c g x), hx', map_zero]
    | lie X => rw [← lie_fin, ← hcomm _ (fun g x => lie_fin π X g x), hx', map_zero]
  rcases π.irred _ (Submodule.map_subtype_le _ _) stable with h | h
  · have hn : ψ ∉ W0 := fun hm => by
      have h1 : ψ.1 ∈ W0.map π.V.subtype := ⟨ψ, hm, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      exact hψ (Subtype.ext h1)
    rw [mem] at hn
    push_neg at hn
    obtain ⟨g, hg⟩ := hn
    refine ⟨P (π.finPart g ψ), hg, fun k hk => hPinv _ ⟨k, hk⟩, fun T c hT hc => ?_⟩
    rw [hcomm T hT, hT, hc, map_smul, map_smul]
  · exfalso
    have h1 : v0.1 ∈ W0.map π.V.subtype := by
      rw [h]
      exact v0.2
    obtain ⟨y, hy, e⟩ := h1
    have hy0 : y = v0 := Subtype.ext e
    subst hy0
    have h2 := (mem y).1 hy 1
    rw [map_one, Module.End.one_apply, hPfix y fun k => hfix k.1 k.2] at h2
    exact hv0 h2

end Core

/- English proof (translation)
Introduce `_ hL`. Unfold `RlLow ForRl`. Introduce `E _ _ _ n hn π _ K _ hKc _ _ _ μf _ D hreg hnt w lam hanti hch`. Take `⟨ν, ψ, hψ, hψ0, hk, hc⟩` from `hL E n hn π hreg w lam hanti hch`. Take `⟨u0, hu0⟩` from `exists_ne (0 : D.U)`.

Establish `hv0 : D.i u0 ≠ 0` using `fun e => hu0 (D.inj (by rw [e, map_zero]))`. Establish `hfix0 : ∀ k ∈ K, π.finPart k (D.i u0) = D.i u0` using `fun k hk' => Subtype.ext ((D.rng (D.i u0)).1 ⟨u0, rfl⟩ k hk')`. Set `ψ' : π.V` to `⟨ψ, hψ⟩`. Establish `hψ' : ψ' ≠ 0` using `fun e => hψ0 (congrArg Subtype.val e)`. Take `⟨v, hv, hfix, hT⟩` from `core π K hKc (D.i u0) ψ' hv0 hfix0 hψ'`.

Take `⟨u, hu⟩` from `(D.rng v).2 fun k hk' => congrArg Subtype.val (hfix k hk')`. Establish `hune : u ≠ 0` using `fun e => hv (by rw [← hu, e, map_zero])`. Set `T : Fin n → Fin n → Module.End ℂ π.V` to `fun a b => PositivityTheory.S2.Clozel.EopV π w.embedding a b - PositivityTheory.S2.Clozel.EopV π (ComplexEmbedding.conjugate w.embedding) b a`. Establish `hTval : ∀ a b (x : π.V), (T a b x).1 = eopW w true a b x.1 - eopW w false b a x.1` using `fun a b x => by`. Simplify using `[T, eopW, GlobalTheory.CompanionTheory.ClozelPurity.EopV_val]`.

Establish `hTc : ∀ a b g (x : π.V), T a b (π.finPart g x) = π.finPart g (T a b x)` using `fun a b g x => by`. Simplify using `only [T, LinearMap.sub_apply, eop_fin, map_sub]`. Establish `hTu : ∀ a b, D.i (kF (D.E1 w) (D.E2 w) a b u) = T a b v` using `fun a b => Subtype.ext (by`. Rewrite using `[hTval, ← hu]`. Simplify using `only [kF, LinearMap.add_apply, map_add, Submodule.coe_add, D.hE1, D.hE2]`.

Use the proof step `abel)`. Establish `hmem : u ∈ hwSp (D.E1 w) (D.E2 w) ν`. Use `⟨fun a => D.inj ?_, fun a b hab he => D.inj ?_⟩` and prove the remaining obligations. Establish `h1 : T a a ψ' = (ν a : ℂ) • ψ'` using `Subtype.ext (by`. Rewrite using `[hTval]`.

Conclude with `hk.1 a)`. Rewrite using `[hTu, hT _ _ (hTc a a) h1, map_smul, hu]`. Establish `h1 : T a b ψ' = (0 : ℂ) • ψ'` using `Subtype.ext (by`. Rewrite using `[hTval, zero_smul]`. Conclude with `hk.2 a b hab he)`.

Rewrite using `[hTu, hT _ _ (hTc a b) h1, zero_smul, map_zero]`. Conclude with `⟨ν, fun e => hune (by`. Establish `h1` using `hmem`. Rewrite `h1` using `[e, Submodule.mem_bot]`. Conclude with `h1), hc⟩`.
-/
theorem rlLow : HeckeMem → LowType → RlLow := by
  intro _ hL
  unfold RlLow ForRl
  intro E _ _ _ n hn π _ K _ hKc _ _ _ μf _ D hreg hnt w lam hanti hch
  obtain ⟨ν, ψ, hψ, hψ0, hk, hc⟩ := hL E n hn π hreg w lam hanti hch
  obtain ⟨u0, hu0⟩ := exists_ne (0 : D.U)
  have hv0 : D.i u0 ≠ 0 := fun e => hu0 (D.inj (by rw [e, map_zero]))
  have hfix0 : ∀ k ∈ K, π.finPart k (D.i u0) = D.i u0 := fun k hk' =>
    Subtype.ext ((D.rng (D.i u0)).1 ⟨u0, rfl⟩ k hk')
  let ψ' : π.V := ⟨ψ, hψ⟩
  have hψ' : ψ' ≠ 0 := fun e => hψ0 (congrArg Subtype.val e)
  obtain ⟨v, hv, hfix, hT⟩ := core π K hKc (D.i u0) ψ' hv0 hfix0 hψ'
  obtain ⟨u, hu⟩ := (D.rng v).2 fun k hk' => congrArg Subtype.val (hfix k hk')
  have hune : u ≠ 0 := fun e => hv (by rw [← hu, e, map_zero])
  let T : Fin n → Fin n → Module.End ℂ π.V := fun a b =>
    PositivityTheory.S2.Clozel.EopV π w.embedding a b - PositivityTheory.S2.Clozel.EopV π (ComplexEmbedding.conjugate w.embedding) b a
  have hTval : ∀ a b (x : π.V), (T a b x).1 = eopW w true a b x.1 - eopW w false b a x.1 := fun a b x => by
    simp [T, eopW, GlobalTheory.CompanionTheory.ClozelPurity.EopV_val]
  have hTc : ∀ a b g (x : π.V), T a b (π.finPart g x) = π.finPart g (T a b x) := fun a b g x => by
    simp only [T, LinearMap.sub_apply, eop_fin, map_sub]
  have hTu : ∀ a b, D.i (kF (D.E1 w) (D.E2 w) a b u) = T a b v := fun a b => Subtype.ext (by
    rw [hTval, ← hu]
    simp only [kF, LinearMap.add_apply, map_add, Submodule.coe_add, D.hE1, D.hE2]
    abel)
  have hmem : u ∈ hwSp (D.E1 w) (D.E2 w) ν := by
    refine ⟨fun a => D.inj ?_, fun a b hab he => D.inj ?_⟩
    · have h1 : T a a ψ' = (ν a : ℂ) • ψ' := Subtype.ext (by
        rw [hTval]
        exact hk.1 a)
      rw [hTu, hT _ _ (hTc a a) h1, map_smul, hu]
    · have h1 : T a b ψ' = (0 : ℂ) • ψ' := Subtype.ext (by
        rw [hTval, zero_smul]
        exact hk.2 a b hab he)
      rw [hTu, hT _ _ (hTc a b) h1, zero_smul, map_zero]
  exact ⟨ν, fun e => hune (by
    have h1 := hmem
    rw [e, Submodule.mem_bot] at h1
    exact h1), hc⟩

end UpperTheory.V.Z.GSp4Splitting
