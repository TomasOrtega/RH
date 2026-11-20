import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.EigOcc

open Module Module.End

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/- English proof (translation)
Take `⟨y, hyU, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU`. Establish `hy` using `hle hyU`. Rewrite `hy` using `[mem_maxGenEigenspace]`. Establish `hP : ∃ n : ℕ, ((a - c • (1 : End K V)) ^ n) y = 0` using `hy`. Establish `hm : ((a - c • 1) ^ Nat.find hP) y = 0` using `Nat.find_spec hP`.

Establish `hm0 : Nat.find hP ≠ 0`. Introduce `h`. Rewrite `hm` using `[h, pow_zero, Module.End.one_apply]`. Conclude with `hy0 hm`. Take `⟨m', hm'⟩ : ∃ m', Nat.find hP = m' + 1` from `⟨Nat.find hP - 1, by omega⟩`.

Establish `hne : ((a - c • 1) ^ m') y ≠ 0` using `Nat.find_min hP (by omega)`. Establish `hinv' : ∀ k : ℕ, ((a - c • 1) ^ k) y ∈ U`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hyU`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `U.sub_mem (hinv _ ih) (U.smul_mem c ih)`. Introduce `hbot`. Apply `hne` to reduce the goal to its premises.

Establish `hmem : ((a - c • 1) ^ m') y ∈ U ⊓ LinearMap.ker (a - c • 1)`. Use `⟨hinv' m', ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', ← hm']`. Conclude with `hm`. Rewrite `hmem` using `[hbot]`.

Conclude with `(Submodule.mem_bot K).1 hmem`.
-/
theorem inf_ker_ne_bot {a : End K V} {c : K} {U : Submodule K V} (hU : U ≠ ⊥)
    (hle : U ≤ a.maxGenEigenspace c) (hinv : ∀ y ∈ U, a y ∈ U) :
    U ⊓ LinearMap.ker (a - c • 1) ≠ ⊥ := by
  classical
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hy := hle hyU
  rw [mem_maxGenEigenspace] at hy
  have hP : ∃ n : ℕ, ((a - c • (1 : End K V)) ^ n) y = 0 := hy
  have hm : ((a - c • 1) ^ Nat.find hP) y = 0 := Nat.find_spec hP
  have hm0 : Nat.find hP ≠ 0 := by
    intro h
    rw [h, pow_zero, Module.End.one_apply] at hm
    exact hy0 hm
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hP = m' + 1 := ⟨Nat.find hP - 1, by omega⟩
  have hne : ((a - c • 1) ^ m') y ≠ 0 := Nat.find_min hP (by omega)
  have hinv' : ∀ k : ℕ, ((a - c • 1) ^ k) y ∈ U := by
    intro k
    induction k with
    | zero => simpa using hyU
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hinv _ ih) (U.smul_mem c ih)
  intro hbot
  apply hne
  have hmem : ((a - c • 1) ^ m') y ∈ U ⊓ LinearMap.ker (a - c • 1) := by
    refine ⟨hinv' m', ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', ← hm']
    exact hm
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).1 hmem

/- English proof (translation)
Establish `hP : ∃ n, ∃ U : Submodule K V, U ≤ W0 ∧ U ≠ ⊥ ∧ (∀ a ∈ S, ∀ y ∈ U, a y ∈ U) ∧ finrank K U = n` using `⟨_, W0, le_rfl, hW, hinv, rfl⟩`. Take `⟨U, hUW, hU0, hUinv, hUn⟩` from `Nat.find_spec hP`. Establish `key : ∀ a ∈ S, U ≤ LinearMap.ker (a - χ a • 1)`. Introduce `a ha`. Establish `hU'0 : U ⊓ LinearMap.ker (a - χ a • 1) ≠ ⊥` using `inf_ker_ne_bot hU0 (hUW.trans (hle a ha)) (hUinv a ha)`.

Establish `hU'inv : ∀ b ∈ S, ∀ y ∈ U ⊓ LinearMap.ker (a - χ a • 1), b y ∈ U ⊓ LinearMap.ker (a - χ a • 1)`. Introduce and unpack `b hb y ⟨hyU, hyk⟩`. Use `⟨hUinv b hb y hyU, ?_⟩` and prove the remaining obligations. Rewrite `hyk` using `[SetLike.mem_coe, LinearMap.mem_ker]`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`.

Establish `hc : Commute (a - χ a • 1) b` using `(hS a ha b hb).sub_left ((Commute.one_left b).smul_left _)`. Rewrite using `[← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hyk, map_zero]`. Establish `hle' : finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker (a - χ a • 1))`. Rewrite using `[hUn]`. Conclude with `Nat.find_min' hP ⟨_, inf_le_left.trans hUW, hU'0, hU'inv, rfl⟩`.

Establish `heq : U ⊓ LinearMap.ker (a - χ a • 1) = U` using `Submodule.eq_of_le_of_finrank_le inf_le_left hle'`. Rewrite using `[← heq]`. Conclude with `inf_le_right`. Take `⟨u, huU, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU0`. Use `⟨u, hUW huU, hu0, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `h` using `key a ha huU`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `h`.
-/
theorem exists_common_eigvec (S : Set (End K V)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (χ : End K V → K)
    (W0 : Submodule K V) (hW : W0 ≠ ⊥) (hle : ∀ a ∈ S, W0 ≤ a.maxGenEigenspace (χ a))
    (hinv : ∀ a ∈ S, ∀ y ∈ W0, a y ∈ W0) :
    ∃ u ∈ W0, u ≠ 0 ∧ ∀ a ∈ S, a u = χ a • u := by
  classical
  have hP : ∃ n, ∃ U : Submodule K V, U ≤ W0 ∧ U ≠ ⊥ ∧ (∀ a ∈ S, ∀ y ∈ U, a y ∈ U) ∧ finrank K U = n :=
    ⟨_, W0, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU0, hUinv, hUn⟩ := Nat.find_spec hP
  have key : ∀ a ∈ S, U ≤ LinearMap.ker (a - χ a • 1) := by
    intro a ha
    have hU'0 : U ⊓ LinearMap.ker (a - χ a • 1) ≠ ⊥ := inf_ker_ne_bot hU0 (hUW.trans (hle a ha)) (hUinv a ha)
    have hU'inv : ∀ b ∈ S, ∀ y ∈ U ⊓ LinearMap.ker (a - χ a • 1), b y ∈ U ⊓ LinearMap.ker (a - χ a • 1) := by
      rintro b hb y ⟨hyU, hyk⟩
      refine ⟨hUinv b hb y hyU, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hyk
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hc : Commute (a - χ a • 1) b := (hS a ha b hb).sub_left ((Commute.one_left b).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hyk, map_zero]
    have hle' : finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker (a - χ a • 1)) := by
      rw [hUn]
      exact Nat.find_min' hP ⟨_, inf_le_left.trans hUW, hU'0, hU'inv, rfl⟩
    have heq : U ⊓ LinearMap.ker (a - χ a • 1) = U := Submodule.eq_of_le_of_finrank_le inf_le_left hle'
    rw [← heq]
    exact inf_le_right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine ⟨u, hUW huU, hu0, fun a ha => ?_⟩
  have h := key a ha huU
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Lin

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

/- English proof (translation)
Rewrite using `[heckeEig, Submodule.mem_iInf]`. Introduce `f`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Take `⟨g, hgT⟩` from `f`. Establish `hg : g ∈ Algebra.adjoin O G` using `hT ▸ hgT`.

Proceed by induction on `hg using Algebra.adjoin_induction with`. Consider the case `mem g hg' => exact hG ⟨g, hgT⟩ hg'`. Consider the case `algebraMap r`. Establish `e1 : (⟨algebraMap O (X → O) r, hgT⟩ : T) = algebraMap O T r` using `rfl`. Rewrite using `[e1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.smul_apply, Module.End.one_apply, ← algebraMap_smul (FractionRing O) r z]`.

Both sides reduce to the same expression. Consider the case `add g1 g2 h1 h2 ih1 ih2`. Establish `m1 : g1 ∈ T` using `hT ▸ h1`. Establish `m2 : g2 ∈ T` using `hT ▸ h2`. Establish `e1 : (⟨g1 + g2, hgT⟩ : T) = ⟨g1, m1⟩ + ⟨g2, m2⟩` using `rfl`.

Rewrite using `[e1, map_add, LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2]`. Simplify using `only [Subalgebra.coe_add, Pi.add_apply, map_add, add_smul]`. Consider the case `mul g1 g2 h1 h2 ih1 ih2`. Establish `m1 : g1 ∈ T` using `hT ▸ h1`. Establish `m2 : g2 ∈ T` using `hT ▸ h2`.

Establish `e1 : (⟨g1 * g2, hgT⟩ : T) = ⟨g1, m1⟩ * ⟨g2, m2⟩` using `rfl`. Rewrite using `[e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1, smul_smul]`. Simplify using `only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, mul_comm]`.
-/
theorem mem_heckeEig_of_gen {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) (G : Set (X → O))
    (hT : T = Algebra.adjoin O G) (z : TensorProduct O (FractionRing O) M)
    (hG : ∀ f : T, (f : X → O) ∈ G →
      ((act f).baseChange (FractionRing O)) z = algebraMap O (FractionRing O) ((f : X → O) x) • z) :
    z ∈ heckeEig T act x := by
  rw [heckeEig, Submodule.mem_iInf]
  intro f
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨g, hgT⟩ := f
  have hg : g ∈ Algebra.adjoin O G := hT ▸ hgT
  induction hg using Algebra.adjoin_induction with
  | mem g hg' => exact hG ⟨g, hgT⟩ hg'
  | algebraMap r =>
    have e1 : (⟨algebraMap O (X → O) r, hgT⟩ : T) = algebraMap O T r := rfl
    rw [e1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      LinearMap.smul_apply, Module.End.one_apply, ← algebraMap_smul (FractionRing O) r z]
    rfl
  | add g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 + g2, hgT⟩ : T) = ⟨g1, m1⟩ + ⟨g2, m2⟩ := rfl
    rw [e1, map_add, LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2]
    simp only [Subalgebra.coe_add, Pi.add_apply, map_add, add_smul]
  | mul g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 * g2, hgT⟩ : T) = ⟨g1, m1⟩ * ⟨g2, m2⟩ := rfl
    rw [e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1, smul_smul]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, mul_comm]

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `haveI := hd (jOf B i) (wOf B i)`. Set `S : Set (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)))` to `{f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k}`. Set `χ : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) → FractionRing (OOf B i)` to `fun a => if h : a ∈ hAlg B i then NCov.pt x.1 ⟨a, h⟩ else 0`. Establish `hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b` using `std_comm (j := jOf B i) (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1`. Establish `hmem : ∀ a ∈ S, a ∈ hAlg B i` using `fun a ha => Algebra.subset_adjoin ha`.

Establish `hχ : ∀ a (ha : a ∈ S), χ a = NCov.pt x.1 ⟨a, hmem a ha⟩` using `fun a ha => dif_pos (hmem a ha)`. Take `⟨u, huW, hu0, hu⟩` from `exists_common_eigvec S hSc χ (NCov.W (hAlg B i) (NCov.pt x.1)) x.2.2 (fun a ha => by`. Rewrite using `[hχ a ha]`. Conclude with `NCov.W_le (hAlg B i) (NCov.pt x.1) ⟨a, hmem a ha⟩)`. Use the proof step `(fun a ha y hy => by`.

Rewrite `hy`, the goal using `[NCov.W, Submodule.mem_iInf]`. Introduce `t`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm (NCov.commute_adjoin hSc t.2 (hmem a ha)) _ (hy t))`. Establish `hpart : u ∈ NCov.part (hAlg B i) i.2.1` using `(le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ)) x.1 x.2.1) huW`. Take `⟨z, hz⟩` from `(PsiC_range B (partCompl_of hs hd) hL i u).1 hpart`.

Establish `hG : ∀ f : TOf B i, (f : XOf B i → OOf B i) ∈ {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k} → ((actC B (partCompl_of hs hd) hAct i f).baseChange (FractionRing (OOf B i))) z = algebraMap (OOf B i) (FractionRing (OOf B i)) ((f : XOf B i → OOf B i) x) • z`. Introduce and unpack `f ⟨v, k, hvk, hf⟩`. Establish `e1 : f = hTOf B i v k` using `Subtype.ext (by rw [hf]; simp [hTOf, dif_pos hvk])`. Substitute `e1` using the available equality. Apply `PsiC_inj B (partCompl_of hs hd) hL i` to reduce the goal to its premises.

Rewrite using `[hH i v k hvk z, hz, map_smul, hz, hu _ ⟨v, k, hvk, rfl⟩, hχ _ ⟨v, k, hvk, rfl⟩]`. Conclude with `congrArg (· • u) (congrArg (algebraMap (OOf B i) (FractionRing (OOf B i))) (ptX_val B i v k hvk x).symm)`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[map_zero]`.

Conclude with `hu0 hz.symm`. Introduce `hbot`. Apply `hz0` to reduce the goal to its premises. Establish `hzm : z ∈ heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x` using `mem_heckeEig_of_gen (TOf B i) (actC B (partCompl_of hs hd) hAct i) x _ rfl z hG`. Rewrite `hzm` using `[hbot]`.

Conclude with `(Submodule.mem_bot _).1 hzm`.
-/
theorem heckeEig_ne_bot (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd))
    (hAct : ActEx B (partCompl_of hs hd)) (hH : ActHK B hs hd hL hAct) (i : LocT B) (x : XOf B i) :
    heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  classical
  haveI := hd (jOf B i) (wOf B i)
  let S : Set (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) :=
    {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k}
  let χ : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) → FractionRing (OOf B i) :=
    fun a => if h : a ∈ hAlg B i then NCov.pt x.1 ⟨a, h⟩ else 0
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := std_comm (j := jOf B i) (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1
  have hmem : ∀ a ∈ S, a ∈ hAlg B i := fun a ha => Algebra.subset_adjoin ha
  have hχ : ∀ a (ha : a ∈ S), χ a = NCov.pt x.1 ⟨a, hmem a ha⟩ := fun a ha => dif_pos (hmem a ha)
  obtain ⟨u, huW, hu0, hu⟩ := exists_common_eigvec S hSc χ (NCov.W (hAlg B i) (NCov.pt x.1)) x.2.2
    (fun a ha => by
      rw [hχ a ha]
      exact NCov.W_le (hAlg B i) (NCov.pt x.1) ⟨a, hmem a ha⟩)
    (fun a ha y hy => by
      rw [NCov.W, Submodule.mem_iInf] at hy ⊢
      intro t
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (NCov.commute_adjoin hSc t.2 (hmem a ha)) _ (hy t))
  have hpart : u ∈ NCov.part (hAlg B i) i.2.1 :=
    (le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ))
      x.1 x.2.1) huW
  obtain ⟨z, hz⟩ := (PsiC_range B (partCompl_of hs hd) hL i u).1 hpart
  have hG : ∀ f : TOf B i, (f : XOf B i → OOf B i) ∈ {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k} →
      ((actC B (partCompl_of hs hd) hAct i f).baseChange (FractionRing (OOf B i))) z =
        algebraMap (OOf B i) (FractionRing (OOf B i)) ((f : XOf B i → OOf B i) x) • z := by
    rintro f ⟨v, k, hvk, hf⟩
    have e1 : f = hTOf B i v k := Subtype.ext (by rw [hf]; simp [hTOf, dif_pos hvk])
    subst e1
    apply PsiC_inj B (partCompl_of hs hd) hL i
    rw [hH i v k hvk z, hz, map_smul, hz, hu _ ⟨v, k, hvk, rfl⟩, hχ _ ⟨v, k, hvk, rfl⟩]
    exact congrArg (· • u) (congrArg (algebraMap (OOf B i) (FractionRing (OOf B i))) (ptX_val B i v k hvk x).symm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hu0 hz.symm
  intro hbot
  apply hz0
  have hzm : z ∈ heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x :=
    mem_heckeEig_of_gen (TOf B i) (actC B (partCompl_of hs hd) hAct i) x _ rfl z hG
  rw [hbot] at hzm
  exact (Submodule.mem_bot _).1 hzm

end Main

end GlobalTheory.EigOcc
