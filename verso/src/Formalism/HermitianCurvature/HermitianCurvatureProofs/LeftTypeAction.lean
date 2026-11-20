import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Left

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

/- English proof (translation)
Take `⟨hgG, hgD⟩` from `hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢`. Use `⟨?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]`. Conclude with `hh.2.1 a`. Establish `h1z' : (1 : Mx k r) ∈ UWset k r z'` using `by simp [UWset, UH]`. Establish `h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r)` using `by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]`.

Establish `hS` using `hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩`. Simplify using `using hS`.
-/
theorem mem_left (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS

/- English proof (translation)
Establish `h1z : (1 : Mx k r) ∈ UWset k r z` using `by simp [UWset, UH]`. Establish `h1z' : (1 : Mx k r) ∈ UWset k r z'` using `by simp [UWset, UH]`. Simplify using `only [FFl, Set.mem_setOf_eq] at hJ`. Establish `e1` using `hJ.2.2.2 g hg 1 h1z 1 h1z'`. Establish `e2` using `hJ.2.2.2 g hg h hh 1 h1z'`.

Rewrite `e1` using `[one_mul, mul_one, hπ.1]`. Establish `e1' : J g ∘SL π' 1 = J g`. Use extensionality with `x`. Conclude with `(congrArg (fun T => T x) e1).symm`. Rewrite `e2` using `[mul_one]`.

Rewrite using `[e2, e1']`.
-/
theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg h hh 1 h1z'
  rw [one_mul, mul_one, hπ.1] at e1
  have e1' : J g ∘SL π' 1 = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [mul_one] at e2
  rw [e2, e1']

/- English proof (translation)
Establish `hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) = fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g)`. Use function extensionality and compare the values at `t`. Establish `hu` using `exp_uw hX t`. Rewrite using `[hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]`. Unfold `LdV`.

Rewrite using `[hfun]`. Establish `hd` using `dOp_hasDeriv hπ hc hX`. Set `L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)` to `(((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ`. Establish `key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g)) ((B.comp (dOp π X)).comp (J g)) 0`. Establish `h2` using `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | (ext; rfl)`. Conclude with `key.deriv`.
-/
theorem ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by
  have hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold LdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g))
      ((B.comp (dOp π X)).comp (J g)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

/- English proof (translation)
Unfold `LZ`. Rewrite using `[ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]`. Use extensionality with `v`. Simplify using `[ecOp]`.
-/
theorem lz_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (ecOp π Z)).comp (J g) := by
  unfold LZ
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp [ecOp]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => intro F B hF g hg v`. Simplify using `[hF g hg]`. Consider the case `cons p L ih`. Introduce `F B hF g hg v`.

Take `⟨h1, h2⟩` from `hL p (by simp)`. Establish `hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D, (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g)`. Introduce `g hg`. Rewrite using `[Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Use `ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v` as an intermediate fact. Simplify using `only [List.map_cons, List.foldl_cons, List.foldr_cons]`. Rewrite using `[this]`. Simplify using `[ecRep_eq hπ hc h1 h2]`.
-/
theorem fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil => intro F B hF g hg v; simp [hF g hg]
  | cons p L ih =>
    intro F B hF g hg v
    obtain ⟨h1, h2⟩ := hL p (by simp)
    have hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g) := by
      intro g hg
      rw [Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]
      ext x
      simp
    have := ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [this]
    simp [ecRep_eq hπ hc h1 h2]

end Left

end QrD

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v`. Unfold `capLft capRep qmFrev qmF`. Establish `key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v, ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v = (Contin …` using `fun σ => QrD.fold_left hD hπ hc hJ _ (by`. Introduce `p hp`. Simplify using `only [List.mem_ofFn] at hp`.

Take `⟨j, rfl⟩` from `hp`. Conclude with `QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)`. Simplify using `only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key`. Simplify using `only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[key σ g hg v]`.
-/
theorem left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
      ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v =
        (ContinuousLinearMap.id ℂ Wp)
          (((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
            fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) :=
    fun σ => QrD.fold_left hD hπ hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [key σ g hg v]

end Formalism.FourierDecayAlt.P
