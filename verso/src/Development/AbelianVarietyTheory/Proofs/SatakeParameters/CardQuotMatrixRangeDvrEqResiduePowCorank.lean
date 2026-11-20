import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

namespace GlobalTheory.IdxRank

/- English proof (translation)
Establish `h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial`.
-/
theorem mem_smul_top_of_forall_mem {O : Type} [CommRing O] (I : Ideal O) {r : ℕ}
    (z : Fin r → O) (hz : ∀ i, z i ∈ I) : z ∈ I • (⊤ : Submodule O (Fin r → O)) := by
  have h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial

/- English proof (translation)
Use `set F := IsLocalRing.ResidueField O with hF`. Use `set res : O →+* F := IsLocalRing.residue O with hres`. Use `set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb`. Use `set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR`. Set `π : (Fin r → O) →ₗ[O] (Fin r → F)` to `(Algebra.linearMap O F).compLeft (Fin r)`.

Establish `hπ : ∀ x i, π x i = res (x i)` using `fun x i => rfl`. Establish `hπs : Function.Surjective π`. Introduce `y`. Use `⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Conclude with `(IsLocalRing.residue_surjective (y i)).choose_spec`. Establish `hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x)`. Introduce `x`. Use extensionality with `i`. Establish `h2 : π x = res ∘ x` using `rfl`.

Rewrite using `[h2, hπ]`. Conclude with `RingHom.map_mulVec res A x i`. Set `φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R)` to `(R.mkQ.restrictScalars O).comp π`. Establish `hφs : Function.Surjective φ` using `(Submodule.mkQ_surjective R).comp hπs`. Establish `hker : LinearMap.ker φ = LinearMap.range A.mulVecLin`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : π x ∈ R`. Establish `: R.mkQ (π x) = 0` using `hx`.

Simplify using `using this`. Take `⟨y, hy⟩` from `hx'`. Take `⟨y', rfl⟩` from `hπs y`. Establish `hy2 : π (A.mulVec y') = π x`. Rewrite using `[hπA]`.

Conclude with `hy`. Establish `hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin`. Apply `hA` to reduce the goal to its premises. Apply `mem_smul_top_of_forall_mem` to reduce the goal to its premises. Introduce `i`.

Establish `h1 : π (x - A.mulVec y') i = 0`. Rewrite using `[map_sub, hy2, sub_self]`. Both sides reduce to the same expression. Rewrite `h1` using `[hπ]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).1 h1`.

Establish `: x = (x - A.mulVec y') + A.mulVecLin y'`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hz ⟨y', rfl⟩`. Introduce and unpack `⟨y, rfl⟩ show R.mkQ (π (A.mulVec y)) = 0`.

Rewrite using `[hπA]`. Simplify using `only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨π y, rfl⟩`. Establish `e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R)` using `((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφs)).toEquiv`. Rewrite using `[Nat.card_congr e]`.

Establish `hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r`. Use `Submodule.finrank_quotient_add_finrank R` as an intermediate fact. Simplify using `using this`. Establish `hrank : Ab.rank = Module.finrank F R` using `rfl`. Establish `hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank`.

Use linear arithmetic over natural numbers and integers. Establish `: Finite ((Fin r → F) ⧸ R)` using `Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)`. Rewrite using `[Module.natCard_eq_pow_finrank (K := F), hdim]`. Both sides reduce to the same expression.
-/
theorem card_quot_range (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O)
    (hA : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤
      LinearMap.range A.mulVecLin) :
    Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) =
      qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  classical
  set F := IsLocalRing.ResidueField O with hF
  set res : O →+* F := IsLocalRing.residue O with hres
  set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb
  set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR
  let π : (Fin r → O) →ₗ[O] (Fin r → F) := (Algebra.linearMap O F).compLeft (Fin r)
  have hπ : ∀ x i, π x i = res (x i) := fun x i => rfl
  have hπs : Function.Surjective π := by
    intro y
    refine ⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩
    ext i
    exact (IsLocalRing.residue_surjective (y i)).choose_spec
  have hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x) := by
    intro x
    ext i
    have h2 : π x = res ∘ x := rfl
    rw [h2, hπ]
    exact RingHom.map_mulVec res A x i
  let φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R) := (R.mkQ.restrictScalars O).comp π
  have hφs : Function.Surjective φ :=
    (Submodule.mkQ_surjective R).comp hπs
  have hker : LinearMap.ker φ = LinearMap.range A.mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : π x ∈ R := by
        have : R.mkQ (π x) = 0 := hx
        simpa using this
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨y', rfl⟩ := hπs y
      have hy2 : π (A.mulVec y') = π x := by
        rw [hπA]; exact hy
      have hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin := by
        apply hA
        apply mem_smul_top_of_forall_mem
        intro i
        have h1 : π (x - A.mulVec y') i = 0 := by
          rw [map_sub, hy2, sub_self]; rfl
        rw [hπ] at h1
        exact (IsLocalRing.residue_eq_zero_iff _).1 h1
      have : x = (x - A.mulVec y') + A.mulVecLin y' := by
        simp
      rw [this]
      exact Submodule.add_mem _ hz ⟨y', rfl⟩
    · rintro ⟨y, rfl⟩
      show R.mkQ (π (A.mulVec y)) = 0
      rw [hπA]
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨π y, rfl⟩
  have e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hφs)).toEquiv
  rw [Nat.card_congr e]
  have hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r := by
    have := Submodule.finrank_quotient_add_finrank R
    simpa using this
  have hrank : Ab.rank = Module.finrank F R := rfl
  have hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank := by
    omega
  have : Finite ((Fin r → F) ⧸ R) := Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  rfl

end GlobalTheory.IdxRank
