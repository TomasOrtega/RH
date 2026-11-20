import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `x y`. Use `show LinearMap.trace ℂ W (ρ (y⁻¹ * x * y)) = LinearMap.trace ℂ W (ρ x)`. Rewrite using `[map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, mul_inv_cancel, map_one, one_mul]`.
-/
private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl fun g => LinearMap.trace ℂ W (ρ g) := by
  intro x y
  show LinearMap.trace ℂ W (ρ (y⁻¹ * x * y)) = LinearMap.trace ℂ W (ρ x)
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, mul_inv_cancel,
    map_one, one_mul]

/- English proof (translation)
Introduce `hM hF hJ hC hT hCI hTF hSQ hSS k _ _ _ _ _ θ hθ N V _ _ π S hS hfix`. Take `⟨s, x, hd, hmap, hsub⟩` from `hSS k N V π S hS`. Establish `hmem : ∀ a, x a ∈ S` using `fun a => by`. Rewrite using `[← hmap]`. Conclude with `Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)`.

Establish `hcusp : ∀ a, (x a).IsCusp` using `fun a => hS.isCusp (hmem a)`. Establish `hdz : ∀ y ∈ S, UpperTheory.Zero.LLC.DZ y`. Take `⟨h, x', hx', hcs⟩` from `id hS`. Introduce `y hy`. Rewrite `hy` using `[← hx']`.

Take `⟨a, -, rfl⟩` from `Multiset.mem_map.1 hy`. Establish `hv : ∃ v ∈ fixed π (KOne k (Fin N)), v ≠ 0` using `Submodule.exists_mem_ne_zero_of_ne_bot hfix`. Take `⟨v, hv, hv0⟩` from `UpperTheory.Zero.LLC.Pr.dzs k N ⟨V, π, hS.isSmooth, hS.isIrreducible⟩ h (fun a => (x' a).fst) (fun a => ⟨(x' a).snd.rep.V, (x' a).rep, (x' a).snd.rep.smooth, (x' a).snd.rep.irr⟩) hcs hv a`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩`. Establish `hdzx : ∀ a, UpperTheory.Zero.LLC.DZ (x a)` using `fun a => hdz _ (hmem a)`.

Establish `hci` using `fun a => hCI k (x a) (hcusp a) (hdzx a)`. Establish `hch : ∀ a, ∃ j, Reg (Nat.card 𝓀[k]) (x a).fst j ∧ ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).fst j γ`. Introduce `a`. Use `haveI := (hci a).1`. Conclude with `hC 𝓀[k] θ hθ (x a).fst (hcusp a).1 _ (levelZero (x a).rep) (hci a).2.1 (hci a).2.2`.

Use `choose c hreg htr using hch`. Use `⟨s, x, c, hmap, fun a => ⟨hcusp a, hdzx a, hreg a, htr a⟩, ?_⟩` and prove the remaining obligations. Use `haveI : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) := fun a => (hci a).1`. Use `haveI hfinV : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by`. Take `⟨-, hadm⟩` from `UpperTheory.Zero.LLC.Pr.adm k N V π hS.isSmooth hS.isIrreducible`.

Use `hadm (levelPre ⊥) (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)` as an intermediate fact. Rewrite `this` using `[levelPre_bot]`. Then use the resulting hypothesis. Take `⟨Φ, hΦ1, hΦ2⟩` from `hTF k s (fun a => (x a).fst) (fun a => (x a).snd.rep.V) (fun a => (x a).rep) (fun a => (x a).snd.rep.smooth)`. Take `⟨ψ, hψ0, hψ⟩` from `hSQ k N s (fun a => (x a).fst) hd _ V _ (piTensor fun a => (x a).rep) π (piTensor fun a => levelZero (x a).rep) Φ hΦ1 hΦ2 hsub hfix`. Take `⟨hfinZ, htrZ⟩` from `hT s (fun a => GL (Fin (x a).fst) 𝓀[k]) (fun a => fixed (x a).rep (KOne k (Fin (x a).fst))) (fun a => levelZero (x a).rep)`.

Take `⟨c0, hc0, hfr⟩` from `hF 𝓀[k] s (fun a => (x a).fst) N hd`. Establish `hmeet` using `((hM (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _ ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)).subtype) ((piTensor fun a => levelZero (x a).rep).comp (leviProj 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)))).1).2 ⟨ψ, hψ0, fun p v => hψ p v⟩`. Establish `hJD : JD θ [] (List.ofFn fun a => ((x a).fst, c a)) N = hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N`. Rewrite using `[(hJ 𝓀[k] θ).1]`. Simplify using `[List.map_ofFn, Function.comp_def]`.

Use `⟨⟨Finite.one_lt_card, by simp, ?_⟩, rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Rewrite `hp` using `[List.mem_ofFn]`. Take `⟨a, rfl⟩` from `hp`. Conclude with `⟨(hcusp a).1, hreg a⟩`.

Simplify using `[Lbl.rk, GlobalTheory.Shin.deg, List.sum_ofFn, hd]`. Unfold `Meets at hmeet ⊢`. Rewrite using `[hJD, hfr _ _ (isCl_trace _)]`. Use `mul_ne_zero hc0 ?_` and prove the remaining obligations. Use `hmeet using 1` and compare the differences between its conclusion and the goal.

Use `finsum_congr fun p => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype, htrZ, htr]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.lblOf :
    MeetsIff → FrobL → JDEq → CuspChar → TensTr → CuspIrr → TensFix → SubqMap → SuppStd → LblOf := by
  intro hM hF hJ hC hT hCI hTF hSQ hSS k _ _ _ _ _ θ hθ N V _ _ π S hS hfix
  obtain ⟨s, x, hd, hmap, hsub⟩ := hSS k N V π S hS
  have hmem : ∀ a, x a ∈ S := fun a => by
    rw [← hmap]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
  have hcusp : ∀ a, (x a).IsCusp := fun a => hS.isCusp (hmem a)
  have hdz : ∀ y ∈ S, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨h, x', hx', hcs⟩ := id hS
    intro y hy
    rw [← hx'] at hy
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
    have hv : ∃ v ∈ fixed π (KOne k (Fin N)), v ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hfix
    obtain ⟨v, hv, hv0⟩ := UpperTheory.Zero.LLC.Pr.dzs k N ⟨V, π, hS.isSmooth, hS.isIrreducible⟩ h
      (fun a => (x' a).fst)
      (fun a => ⟨(x' a).snd.rep.V, (x' a).rep, (x' a).snd.rep.smooth, (x' a).snd.rep.irr⟩) hcs hv a
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have hdzx : ∀ a, UpperTheory.Zero.LLC.DZ (x a) := fun a => hdz _ (hmem a)
  have hci := fun a => hCI k (x a) (hcusp a) (hdzx a)
  have hch : ∀ a, ∃ j, Reg (Nat.card 𝓀[k]) (x a).fst j ∧
      ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).fst j γ := by
    intro a
    haveI := (hci a).1
    exact hC 𝓀[k] θ hθ (x a).fst (hcusp a).1 _ (levelZero (x a).rep) (hci a).2.1 (hci a).2.2
  choose c hreg htr using hch
  refine ⟨s, x, c, hmap, fun a => ⟨hcusp a, hdzx a, hreg a, htr a⟩, ?_⟩
  haveI : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) := fun a => (hci a).1
  haveI hfinV : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    obtain ⟨-, hadm⟩ := UpperTheory.Zero.LLC.Pr.adm k N V π hS.isSmooth hS.isIrreducible
    have := hadm (levelPre ⊥) (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
    rwa [levelPre_bot] at this
  obtain ⟨Φ, hΦ1, hΦ2⟩ := hTF k s (fun a => (x a).fst) (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  obtain ⟨ψ, hψ0, hψ⟩ := hSQ k N s (fun a => (x a).fst) hd _ V _ (piTensor fun a => (x a).rep) π
    (piTensor fun a => levelZero (x a).rep) Φ hΦ1 hΦ2 hsub hfix
  obtain ⟨hfinZ, htrZ⟩ := hT s (fun a => GL (Fin (x a).fst) 𝓀[k])
    (fun a => fixed (x a).rep (KOne k (Fin (x a).fst))) (fun a => levelZero (x a).rep)
  obtain ⟨c0, hc0, hfr⟩ := hF 𝓀[k] s (fun a => (x a).fst) N hd
  have hmeet := ((hM (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _
    ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)).subtype)
    ((piTensor fun a => levelZero (x a).rep).comp
      (leviProj 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)))).1).2 ⟨ψ, hψ0, fun p v => hψ p v⟩
  have hJD : JD θ [] (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJ 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  refine ⟨⟨Finite.one_lt_card, by simp, ?_⟩, rfl, ?_, ?_⟩
  · intro p hp
    rw [List.mem_ofFn] at hp
    obtain ⟨a, rfl⟩ := hp
    exact ⟨(hcusp a).1, hreg a⟩
  · simp [Lbl.rk, GlobalTheory.Shin.deg, List.sum_ofFn, hd]
  · unfold Meets at hmeet ⊢
    rw [hJD, hfr _ _ (isCl_trace _)]
    refine mul_ne_zero hc0 ?_
    convert hmeet using 1
    refine finsum_congr fun p => ?_
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, htrZ, htr]
